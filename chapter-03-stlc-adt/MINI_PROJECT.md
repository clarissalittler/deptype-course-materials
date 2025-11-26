# Chapter 3 Mini-Project: JSON Validator

## Overview

Build a **JSON validator** using ADTs that validates JSON structure against a schema defined in your type system.

**Time estimate**: 3-4 hours

---

## Learning Objectives

- Apply ADTs to a real parsing problem
- Practice pattern matching extensively
- Understand how types model data

---

## The Project

### Define JSON as an ADT

```haskell
data JSON
  = JNull
  | JBool Bool
  | JNum Double
  | JStr String
  | JArr [JSON]
  | JObj [(String, JSON)]
```

### Define a Schema Language

```haskell
data Schema
  = SNull
  | SBool
  | SNum
  | SStr
  | SArr Schema          -- Array of schema
  | SObj [(String, Schema)]  -- Object with fields
  | SAny                 -- Any JSON value
  | SOneOf [Schema]      -- Union type
  | SOptional Schema     -- Optional field
```

### Validate JSON Against Schema

```haskell
validate :: Schema -> JSON -> Either ValidationError ()
```

---

## Example

### Schema
```haskell
userSchema :: Schema
userSchema = SObj
  [ ("name", SStr)
  , ("age", SNum)
  , ("email", SOptional SStr)
  , ("role", SOneOf [SStr, SArr SStr])
  ]
```

### Valid JSON
```json
{
  "name": "Alice",
  "age": 30,
  "role": ["admin", "user"]
}
```

### Invalid JSON
```json
{
  "name": "Bob",
  "age": "thirty"
}
```

### Error Output
```
Validation Error at $.age:
  Expected: number
  Got: string "thirty"
```

---

## Specification

### Step 1: JSON Parser (or use library)

```haskell
parseJSON :: String -> Either ParseError JSON
```

### Step 2: Schema Definition

```haskell
data Schema = ...  -- As shown above

-- Smart constructors
string :: Schema
string = SStr

number :: Schema
number = SNum

object :: [(String, Schema)] -> Schema
object = SObj

array :: Schema -> Schema
array = SArr

optional :: Schema -> Schema
optional = SOptional

oneOf :: [Schema] -> Schema
oneOf = SOneOf
```

### Step 3: Validator

```haskell
data ValidationError = ValidationError
  { path :: JSONPath
  , expected :: Schema
  , got :: JSON
  }

type JSONPath = [PathElement]
data PathElement = Key String | Index Int

validate :: Schema -> JSON -> Either [ValidationError] ()
```

---

## Starter Code

```haskell
module JSONValidator where

-- JSON ADT
data JSON
  = JNull
  | JBool Bool
  | JNum Double
  | JStr String
  | JArr [JSON]
  | JObj [(String, JSON)]
  deriving (Show, Eq)

-- Schema ADT
data Schema
  = SNull
  | SBool
  | SNum
  | SStr
  | SArr Schema
  | SObj [(String, Schema)]
  | SAny
  | SOneOf [Schema]
  | SOptional Schema
  deriving (Show, Eq)

-- Validation result
data ValidationError = ValidationError
  { path :: [String]
  , message :: String
  }
  deriving (Show)

-- Main validation function
validate :: Schema -> JSON -> Either [ValidationError] ()
validate schema json = validateAt [] schema json

validateAt :: [String] -> Schema -> JSON -> Either [ValidationError] ()
validateAt path schema json = case (schema, json) of
  (SAny, _) -> Right ()

  (SNull, JNull) -> Right ()
  (SNull, other) -> Left [mismatch path "null" other]

  (SBool, JBool _) -> Right ()
  (SBool, other) -> Left [mismatch path "boolean" other]

  (SNum, JNum _) -> Right ()
  (SNum, other) -> Left [mismatch path "number" other]

  (SStr, JStr _) -> Right ()
  (SStr, other) -> Left [mismatch path "string" other]

  (SArr elemSchema, JArr elems) ->
    -- Validate each element
    undefined  -- Your implementation!

  (SObj fieldSchemas, JObj fields) ->
    -- Validate each field
    undefined  -- Your implementation!

  (SOneOf schemas, json) ->
    -- Try each schema
    undefined  -- Your implementation!

  (SOptional _, JNull) -> Right ()
  (SOptional inner, json) -> validateAt path inner json

  (_, _) -> Left [mismatch path (show schema) json]

mismatch :: [String] -> String -> JSON -> ValidationError
mismatch path expected got = ValidationError
  { path = path
  , message = "Expected " ++ expected ++ " but got " ++ describe got
  }

describe :: JSON -> String
describe JNull = "null"
describe (JBool b) = "boolean " ++ show b
describe (JNum n) = "number " ++ show n
describe (JStr s) = "string " ++ show s
describe (JArr _) = "array"
describe (JObj _) = "object"
```

---

## Extension Ideas

### 1. Schema from Example
Generate schema from example JSON:
```haskell
inferSchema :: JSON -> Schema
```

### 2. Default Values
Add default values to schema:
```haskell
data Schema = ... | SDefault JSON Schema
```

### 3. Constraints
Add value constraints:
```haskell
data Schema = ...
  | SNumRange Double Double
  | SStrPattern String  -- Regex
  | SArrayLen Int Int
```

### 4. JSON Schema Compatibility
Parse actual JSON Schema format.

---

## Testing

```haskell
-- Test schemas
personSchema = SObj
  [ ("name", SStr)
  , ("age", SNum)
  ]

-- Test data
validPerson = JObj [("name", JStr "Alice"), ("age", JNum 30)]
invalidPerson = JObj [("name", JStr "Bob"), ("age", JStr "old")]

main = do
  print $ validate personSchema validPerson    -- Right ()
  print $ validate personSchema invalidPerson  -- Left [error]
```

---

## Grading Rubric

| Criteria | Points |
|----------|--------|
| Basic types validate | 25 |
| Arrays validate | 20 |
| Objects validate | 25 |
| Good error messages | 15 |
| Extension implemented | 15 |
