# 6 — The Interpreter

The interpreter is the third stage of the pipeline. It takes the well-typed
`Contract` AST and executes the requested method, producing an updated
repository state and an optional return value.

---

## A Worked Example: Evaluating `storage.count + by`

After parsing and type checking, `storage.count + by` becomes this tree:

```
        Add
       /   \
FieldAccess  Var "by"
   /      \
StorageExpr  "count"
```

The interpreter evaluates this tree by calling `evalExpr` recursively:

```
evalExpr(Add)
  ├── evalExpr(FieldAccess StorageExpr "count")
  │     ├── evalExpr(StorageExpr)  →  Record [("count", CInt 10), ("enabled", CBool True)]
  │     └── lookup "count"        →  CInt 10
  └── evalExpr(Var "by")          →  CInt 3
  →  CInt 10 + CInt 3  =  CInt 13
```

Final result: `CInt 13`. This "walk the tree and compute a value at each node"
approach is called a **tree-walking interpreter**.

---

## Runtime State: `Runtime`

Every method executes inside a `Runtime` record:

```haskell
data Runtime = Runtime
  { rtStorage :: Maybe Expr              -- current storage value (Nothing until first write)
  , rtParams  :: Map Name Expr           -- parameter bindings (read-only)
  , rtLocals  :: Map Name Binding        -- local var/val bindings
  , rtMethods :: Map Name MethodDecl     -- callable @private methods
  }
```

`rtStorage` holds the entire storage as a single `Expr` — always a `Record`
once initialised. Reading `storage.count` evaluates `StorageExpr` to this
record, then navigates to the `"count"` field. Writing `storage.count = 13`
replaces the `"count"` field inside the record and stores the updated record
back in `rtStorage`.

`rtMethods` is populated from the contract's `@private` methods when a method
is first invoked (by `execMethod` / `execMethodWithInitialStorage`). It is
passed unchanged into every inner `Runtime` created for a private-method call,
so helpers can themselves call other helpers.

### Bindings

```haskell
data Binding = Binding
  { bindingMutable :: Bool  -- True for var, False for val
  , bindingValue   :: Expr
  }
```

At runtime, every local is a `Binding`. The `bindingMutable` flag mirrors the
`var` / `val` distinction. After type checking, assigning to an immutable
binding is an `interpretBug` — it cannot happen in a well-typed program.

---

## The Evaluation Monad

Both expression evaluation and statement execution use a shared monad:

```haskell
type EvalM = StateT Runtime (Either String)
```

`Runtime` is threaded implicitly through every computation. Reads use `get` or
`gets`; writes use `modify`. User-visible errors (e.g. division by zero) are
`lift (Left msg)`; impossible post-type-check cases call `interpretBug`
(a Haskell `error`).

## Executing Statements

`execStmt :: Stmt -> EvalM (Maybe Expr)`

The result is the return value (`Nothing` if execution continues normally,
`Just v` if a `return` was reached). Storage mutations and new local bindings
are accumulated in the `EvalM` state.

| Statement | What happens |
|-----------|-------------|
| `SequenceStmt ss` | Execute each statement left to right; short-circuit on `Just v`. |
| `ReturnStmt e` | Evaluate `e`; return `Just v`. |
| `VarDeclStmt n _ e` | Evaluate `e`; insert mutable binding for `n`. |
| `ValDeclStmt n _ e` | Evaluate `e`; insert immutable binding for `n`. |
| `AssignmentStmt lv e` | Evaluate `e`; navigate `lv` and write the value. |
| `IfStmt cond thn mel` | Evaluate `cond`; execute the matching branch. |
| `WhileStmt cond body` | Loop: evaluate `cond`, execute `body` until cond is false or return. |

### How `return` propagates

`ReturnStmt e` produces `Just v`. `SequenceStmt` checks after each step and
stops immediately if it sees `Just v`:

```haskell
execSequence [] = return Nothing
execSequence (s:ss) = do
  ret <- execStmt s
  case ret of
    Just v  -> return (Just v)   -- short-circuit
    Nothing -> execSequence ss   -- keep going; state already updated
```

A `while` loop does the same inside its iteration loop.

---

## Private Method Calls

`Call name args` is an expression that invokes a `@private` method. The
interpreter handles it inside `evalExpr`:

1. Look up `name` in `rtMethods` (a bug if absent — the type checker already
   verified the call).
2. Evaluate each argument expression left-to-right inside the current `EvalM`
   state, so any storage mutations from argument evaluation are visible
   immediately.
3. Snapshot the current `Runtime`, replace `rtParams` with the argument
   bindings, clear `rtLocals`, and run `execStmt` on the callee body inside
   that inner `Runtime` using `runStateT`.
4. After the callee returns, copy its final `rtStorage` back into the outer
   `Runtime` via `modify`. The callee's local bindings are discarded.
5. Return the callee's return value (`interpretBug` if it did not return).

This mechanism allows private helpers to both compute values and mutate
storage, with all mutations visible to the caller.

---

## Mutating Storage via LValues

Assignments to `storage` fields are the primary way a contract persists state.
The interpreter navigates nested field paths using `assignLValue`:

```
storage.pos.x = 10
```

This flattens to root `LStorage` + path `["pos", "x"]`. The interpreter:

1. Reads the current storage record.
2. Navigates to `"pos"`, gets the nested record.
3. Sets `"x"` to `CInt 10` in that nested record.
4. Writes the updated `"pos"` record back into storage.
5. Writes the updated storage back into `rtStorage`.

The same mechanism works for `var` locals of record type: `myRecord.enabled =
false` navigates and updates the local's `Binding` value.

---

## Originate vs Call

Two high-level functions in `Interpreter.hs` correspond to the two CLI
commands:

### `originateWithJsonArgs`

```haskell
originateWithJsonArgs
  :: RepositoryState
  -> Contract
  -> String          -- source text (for address generation)
  -> Value           -- JSON args
  -> Either String (Address, RepositoryState)
```

1. Finds the `@originate` method.
2. Decodes JSON args by parameter name and type.
3. Runs the method body with an empty `rtStorage`.
4. Requires that `rtStorage` is `Just s` after execution (the originate method
   must write storage).
5. Generates a new address from the source hash and the current repo size.
6. Inserts the new `ContractInstance` into the repository map.

### `callEntrypointWithJsonArgs`

```haskell
callEntrypointWithJsonArgs
  :: RepositoryState
  -> Contract
  -> Address
  -> Name            -- entrypoint name
  -> String          -- source text (for hash verification)
  -> Value           -- JSON args
  -> Either String (Maybe Expr, RepositoryState)
```

1. Looks up the address in the repository.
2. Verifies the source hash embedded in the address matches the file on disk
   (see [07-cli.md](07-cli.md)).
3. Checks the contract name matches.
4. Finds the named `@entrypoint`.
5. Decodes JSON args.
6. Runs the method body with the current stored `Expr` as `rtStorage`.
7. Requires that `rtStorage` is still `Just s` after execution.
8. Writes the updated storage back into the repository map.
9. Returns the method's return value (if any).

---

## JSON Serialisation and Deserialisation

Storage values are serialised to JSON when writing `state.json` and
deserialised when loading it.

### `Expr → JSON` (`exprToJson`)

| SmartTS value | JSON |
|---------------|------|
| `CInt n` | number |
| `CBool b` | boolean |
| `Record fields` | object |
| `Unit` | null |

### `JSON → Expr` (`jsonToExprByType`)

The typed decoder uses the contract's declared storage type to guide
decoding. A `TRecord` type causes the decoder to expect a JSON object with
matching field names; each field value is decoded recursively against its
declared type. This ensures that persisted storage is always structurally
valid before the interpreter touches it.

---

## Key Design Decision: `interpretBug` vs `Left`

After a successful type check, certain cases in the interpreter are
impossible. For example, `evalInt` expects a `CInt`; it will never see a
`CBool` in a well-typed program. Rather than returning `Left "internal error"`,
these cases call `interpretBug`, which throws a Haskell `error` with a
message that says "please report". This makes the distinction clear:

- `Left String` — a user-visible error (bad JSON, unknown address, etc.)
- `interpretBug` — an impossible case that indicates a bug in the SmartTS
  implementation itself

---

**What to read next →** [07-cli.md](07-cli.md)
