# CToLean

Lean 4 library for parsing and reasoning about Cerberus Core IR.

## Building

```bash
lake build
```

## Testing

Run the parser against the Cerberus test suite:

```bash
../scripts/test_parser.sh --quick  # First 100 tests
../scripts/test_parser.sh          # Full suite (~5500 files, ~12 min)
```

## Structure

- `CToLean/Core/` - Core AST types matching Cerberus IR
  - `Types.lean` - Base types, object types, operators
  - `Value.lean` - Values (integers, pointers, structs, etc.)
  - `Expr.lean` - Pure and effectful expressions
  - `File.lean` - Program structure (functions, globals, tags)
- `CToLean/Parser.lean` - JSON parser for Cerberus output
- `CToLean/Test.lean` - Simple test utility
- `CToLean/TestBatch.lean` - Batch testing for the parser

## Usage

```lean
import CToLean.Parser

-- Parse JSON from Cerberus
let json := IO.FS.readFile "output.json"
match CToLean.Parser.parseFileFromString json with
| .ok file =>
  IO.println s!"Parsed {file.funs.size} functions"
| .error e =>
  IO.println s!"Parse error: {e}"
```

## Status

- **Parser**: 100% success rate on 1817 Cerberus test files
- **Interpreter**: Not yet implemented
- **Pretty-printer**: Not yet implemented
