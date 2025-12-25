# CToLean

Lean 4 library for parsing and reasoning about Cerberus Core IR.

## Building

```bash
lake build
```

## Testing

From the project root, use the Makefile:

```bash
make test              # Run all quick tests (parser + pretty-printer)
make test-parser-full  # Full parser test (~5500 files, ~12 min)
```

Or run the scripts directly:

```bash
../scripts/test_parser.sh --quick  # Parser: first 100 files
../scripts/test_parser.sh          # Parser: full suite
../scripts/test_pp.sh --max 100    # Pretty-printer comparison
```

## Structure

- `CToLean/Core/` - Core AST types matching Cerberus IR
  - `Types.lean` - Base types, object types, operators
  - `Value.lean` - Values (integers, pointers, structs, etc.)
  - `Expr.lean` - Pure and effectful expressions
  - `File.lean` - Program structure (functions, globals, tags)
- `CToLean/Parser.lean` - JSON parser for Cerberus output
- `CToLean/PrettyPrint.lean` - Pretty-printer matching Cerberus format
- `CToLean/Test*.lean` - Test utilities

## Usage

```lean
import CToLean.Parser
import CToLean.PrettyPrint

-- Parse JSON from Cerberus
let json ← IO.FS.readFile "output.json"
match CToLean.Parser.parseFileFromString json with
| .ok file =>
  -- Pretty-print back to Core syntax
  IO.println (CToLean.PrettyPrint.ppFile file)
| .error e =>
  IO.eprintln s!"Parse error: {e}"
```

## Status

- **Parser**: 100% success rate on 5500+ Cerberus test files
- **Pretty-printer**: ~60% match rate with Cerberus output (in progress)
- **Interpreter**: Not yet implemented
