module SmartTS.Parser where

import SmartTS.IR.AST
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Data.Void

type Parser = Parsec Void String

-- Lexer helpers
spaceConsumer :: Parser ()
spaceConsumer = L.space space1 lineComment blockComment
  where
    lineComment = L.skipLineComment "//"
    blockComment = L.skipBlockComment "/*" "*/"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: String -> Parser String
symbol = L.symbol spaceConsumer

-- Keywords and identifiers
reservedWords :: [String]
reservedWords =
  [ "contract"
  , "storage"
  , "int"
  , "bool"
  , "unit"
  , "return"
  , "if"
  , "else"
  , "while"
  , "var"
  , "val"
  , "true"
  , "false"
  , "map"
  , "empty_map"
  , "mem"
  , "remove"
  ]

identifier :: Parser String
identifier = lexeme $ do
  first <- letterChar <|> char '_'
  rest <- many (alphaNumChar <|> char '_')
  let name = first : rest
  if name `elem` reservedWords
    then fail $ "reserved word: " ++ name
    else return name

reserved :: String -> Parser String
reserved = symbol

-- Types
parseType :: Parser Type
parseType = parseMapType <|> parseRecordType <|> parsePrimitiveType
  where
    parsePrimitiveType :: Parser Type
    parsePrimitiveType =
      (reserved "int" >> return TInt)
        <|> (reserved "bool" >> return TBool)
        <|> (reserved "unit" >> return TUnit)

    parseRecordType :: Parser Type
    parseRecordType = do
      fields <- braces $ sepBy parseTypeField (symbol ",")
      return $ TRecord fields

    parseTypeField :: Parser (Name, Type)
    parseTypeField = do
      name <- parseName
      _ <- symbol ":"
      typ <- parseType
      return (name, typ)

    parseMapType :: Parser Type
    parseMapType = do
      _ <- reserved "map"
      _ <- symbol "<"
      kTyp <- parseType
      _ <- symbol ","
      vTyp <- parseType
      _ <- symbol ">"
      return $ TMap kTyp vTyp

-- Names
parseName :: Parser Name
parseName = identifier

-- Expressions
parseExpr :: Parser ParsedExpr
parseExpr = makeExprParser parseTerm operators

operators :: [[Operator Parser ParsedExpr]]
operators =
  [ [ Prefix (Not () <$ symbol "!") ]
  , [ InfixL (Mul () <$ symbol "*")
    , InfixL (Div () <$ symbol "/")
    , InfixL (Mod () <$ symbol "%")
    ]
  , [ InfixL (Add () <$ symbol "+")
    , InfixL (Sub () <$ symbol "-")
    ]
  , [ InfixN (Eq () <$ symbol "==")
    , InfixN (Neq () <$ symbol "!=")
    , InfixN (Lte () <$ symbol "<=")
    , InfixN (Gte () <$ symbol ">=")
    , InfixN (Lt () <$ symbol "<")
    , InfixN (Gt () <$ symbol ">")
    ]
  , [ InfixL (And () <$ symbol "&&") ]
  , [ InfixL (Or () <$ symbol "||") ]
  ]

data Accessor = AccField Name | AccMap ParsedExpr

parseAccessor :: Parser Accessor
parseAccessor =
      (AccField <$> (symbol "." *> parseName))
  <|> (AccMap   <$> (symbol "[" *> parseExpr <* symbol "]"))

parseTerm :: Parser ParsedExpr
parseTerm = do
  base <- parseAtomOrStorage
  accessors <- many parseAccessor
  return $ foldl applyAccessor base accessors
  where
    applyAccessor b (AccField f) = FieldAccess () b f
    applyAccessor b (AccMap e)   = MapAccess () b e

parseAtomOrStorage :: Parser ParsedExpr
parseAtomOrStorage =
  parseStorageExpr
    <|> parseAtom

parseAtom :: Parser ParsedExpr
parseAtom =
  parseUnit
    <|> parseRecordExpr
    <|> (reserved "empty_map" >> return (MapEmpty ()))
    <|> parseMapMem
    <|> parseMapRemove
    <|> parseBool
    <|> parseInt
    <|> parseVarOrCall
    <|> parens parseExpr

parseStorageExpr :: Parser ParsedExpr
parseStorageExpr = do
  _ <- reserved "storage"
  return (StorageExpr ())

parseInt :: Parser ParsedExpr
parseInt = CInt () <$> lexeme L.decimal

parseVarOrCall :: Parser ParsedExpr
parseVarOrCall = do
  name <- parseName
  maybeArgs <- optional (parens (sepBy parseExpr (symbol ",")))
  return $ case maybeArgs of
    Nothing -> Var () name
    Just args -> Call () name args

parseBool :: Parser ParsedExpr
parseBool =
  (reserved "true" >> return (CBool () True))
    <|> (reserved "false" >> return (CBool () False))

parseRecordExpr :: Parser ParsedExpr
parseRecordExpr = do
  fields <- braces $ sepBy parseRecordField (symbol ",")
  return $ Record () fields

parseRecordField :: Parser (Name, ParsedExpr)
parseRecordField = do
  name <- parseName
  _ <- symbol ":"
  expr <- parseExpr
  return (name, expr)

parseUnit :: Parser ParsedExpr
parseUnit = do
  _ <- symbol "()"
  return (Unit ())

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

-- Statements
parseStmt :: Parser ParsedStmt
parseStmt =
  parseIfStmt
    <|> parseWhileStmt
    <|> parseVarDeclStmt
    <|> parseValDeclStmt
    <|> parseReturn
    <|> parseAssignment
    <|> parseBlock

parseVarDeclStmt :: Parser ParsedStmt
parseVarDeclStmt = do
  _ <- reserved "var"
  name <- parseName
  _ <- symbol ":"
  typ <- parseType
  _ <- symbol "="
  expr <- parseExpr
  _ <- symbol ";"
  return $ VarDeclStmt name typ expr

parseValDeclStmt :: Parser ParsedStmt
parseValDeclStmt = do
  _ <- reserved "val"
  name <- parseName
  _ <- symbol ":"
  typ <- parseType
  _ <- symbol "="
  expr <- parseExpr
  _ <- symbol ";"
  return $ ValDeclStmt name typ expr

parseIfStmt :: Parser ParsedStmt
parseIfStmt = do
  _ <- reserved "if"
  cond <- parens parseExpr
  thenBranch <- parseStmt
  elseBranch <- optional $ do
    _ <- reserved "else"
    parseStmt
  return $ IfStmt cond thenBranch elseBranch

parseWhileStmt :: Parser ParsedStmt
parseWhileStmt = do
  _ <- reserved "while"
  cond <- parens parseExpr
  body <- parseStmt
  return $ WhileStmt cond body

parseAssignment :: Parser ParsedStmt
parseAssignment = do
  target <- parseLValue
  _ <- symbol "="
  expr <- parseExpr
  _ <- symbol ";"
  return $ AssignmentStmt target expr

parseLValue :: Parser ParsedLValue
parseLValue = do
  base <- parseAssignableBase
  accessors <- many parseLValueAccessor
  return $ foldl applyAccessor base accessors
  where
    applyAccessor b (AccField f) = LField b f
    applyAccessor b (AccMap e)   = LMapAccess b e

parseLValueAccessor :: Parser Accessor
parseLValueAccessor =
      (AccField <$> (symbol "." *> parseName))
  <|> (AccMap   <$> (symbol "[" *> parseExpr <* symbol "]"))

parseAssignableBase :: Parser ParsedLValue
parseAssignableBase =
  (reserved "storage" >> return LStorage) <|> (LVar <$> parseName)

parseReturn :: Parser ParsedStmt
parseReturn = do
  _ <- reserved "return"
  expr <- parseExpr
  _ <- symbol ";"
  return $ ReturnStmt expr

parseBlock :: Parser ParsedStmt
parseBlock = do
  stmts <- braces (many parseStmt)
  return $ SequenceStmt stmts

-- Storage
parseStorage :: Parser Storage
parseStorage = do
  _ <- reserved "storage"
  _ <- symbol ":"
  fields <- braces parseStorageFields
  _ <- symbol ";"
  return fields

parseStorageFields :: Parser Storage
parseStorageFields = sepBy parseStorageField (symbol ",")

parseStorageField :: Parser (Name, Type)
parseStorageField = do
  name <- parseName
  _ <- symbol ":"
  typ <- parseType
  return (name, typ)

parseMapMem :: Parser ParsedExpr
parseMapMem = do
  _ <- reserved "mem"
  _ <- symbol "("
  mapExpr <- parseExpr
  _ <- symbol ","
  keyExpr <- parseExpr
  _ <- symbol ")"
  return $ MapMemCheck () mapExpr keyExpr

parseMapRemove :: Parser ParsedExpr
parseMapRemove = do
  _ <- reserved "remove"
  _ <- symbol "("
  mapExpr <- parseExpr
  _ <- symbol ","
  keyExpr <- parseExpr
  _ <- symbol ")"
  return $ MapRem () mapExpr keyExpr

-- Method decorators
parseMethodKind :: Parser MethodKind
parseMethodKind =
  (symbol "@originate" >> return Originate)
    <|> (symbol "@entrypoint" >> return EntryPoint)
    <|> (symbol "@private" >> return Private)

-- Formal parameters
parseFormalParameter :: Parser FormalParameter
parseFormalParameter = do
  name <- parseName
  _ <- symbol ":"
  FormalParameter name <$> parseType

parseFormalParameters :: Parser [FormalParameter]
parseFormalParameters = parens $ sepBy parseFormalParameter (symbol ",")

-- Methods
parseMethod :: Parser (MethodDecl ())
parseMethod = do
  decorators <- many parseMethodKind
  name <- parseName
  params <- parseFormalParameters
  _ <- symbol ":"
  returnType <- parseType
  body <- parseBlock
  let kind
        | Originate `elem` decorators = Originate
        | EntryPoint `elem` decorators = EntryPoint
        | otherwise = Private
  return $ MethodDecl kind name params returnType body

-- Contract
parseContract :: Parser ParsedContract
parseContract = do
  _ <- reserved "contract"
  name <- parseName
  _ <- symbol "{"
  storage <- parseStorage
  methods <- many parseMethod
  _ <- symbol "}"
  return $ Contract name storage methods

-- Top-level parser
parseProgram :: Parser ParsedContract
parseProgram = spaceConsumer >> parseContract <* eof

-- Public API
parseContractFromString :: String -> Either (ParseErrorBundle String Void) ParsedContract
parseContractFromString = parse parseProgram ""
