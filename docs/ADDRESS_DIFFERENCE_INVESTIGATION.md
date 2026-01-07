# Address Difference Investigation

**Date:** 2026-01-06
**Status:** Open - needs further investigation

## Problem

Our memory allocator produces addresses that differ from Cerberus by exactly 4608 bytes for the first local variable allocation in `main()`.

- **Cerberus result:** 706040 (mod 1000000)
- **Lean result:** 710648 (mod 1000000)
- **Difference:** 4608 bytes = 0x1200

## What We Know

### 1. Both use the same initial address
- Cerberus: `last_address = 0xFFFFFFFFFFFF` (impl_mem.ml:508)
- Lean: `lastAddress = 0xFFFFFFFFFFFF` (Types.lean:202)

### 2. Both use the same allocation algorithm
Cerberus allocator (impl_mem.ml:1247-1265):
```ocaml
let z = sub st.last_address size in
let (q,m) = quomod z align in
let z' = sub z (if less q zero then negate m else m)
```

Our allocator (Concrete.lean:333-336):
```lean
let addrAfterSize := st.lastAddress - size
let alignedAddr := alignDown addrAfterSize align
```

These are mathematically equivalent for positive addresses.

### 3. Expected first allocation address
For `int a` (size=4, align=4) starting from 0xFFFFFFFFFFFF:
- z = 281474976710655 - 4 = 281474976710651
- z % 4 = 3
- aligned = 281474976710651 - 3 = 281474976710648
- 281474976710648 % 1000000 = **710648** ← matches our result!

### 4. Cerberus is lower by 4608 bytes
This means Cerberus has allocated 4608 bytes of memory BEFORE the first local variable in main().

## Hypotheses

### H1: Cerberus runtime allocations
Cerberus may allocate memory for runtime structures before executing main():
- Return value storage
- Stack frame bookkeeping
- Signal handlers or other runtime state

### H2: Global data we can't see
There might be implicit global allocations from:
- The Cerberus runtime library
- Startup code that runs before main()
- String literals or other constants

### H3: Different execution model
Cerberus might use a different execution model where:
- The interpreter itself uses the same address space
- Debug/tracing structures consume memory

## Impact

**For UB detection:** No impact. Both interpreters correctly detect UB024 for pointer-to-integer conversions when the address doesn't fit in the target type.

**For exact value matching:** Tests that compare raw address values will differ by ~4608 bytes. This affects tests like `intfromptr-05-to-long.c` and `intfromptr-07-check-addr.c`.

## Next Steps

1. **Trace Cerberus execution** - Add debug output to Cerberus allocator to see what allocations happen before main()
2. **Check for hidden globals** - Look for any implicit allocations in Cerberus's execution setup
3. **Compare allocation sequences** - Run both interpreters with allocation logging to see the exact sequence

## Test Cases

The following debug tests show the difference:
- `tests/debug/intfromptr-07-check-addr.c` - Returns address mod 1000000
- `tests/debug/intfromptr-09-first-alloc.c` - Simplest case, one int

## Files Modified

- `lean/CToLean/Memory/Types.lean` - Changed to allocate downward from 0xFFFFFFFFFFFF
- `lean/CToLean/Memory/Concrete.lean` - Updated allocator to grow downward
- `lean/CToLean/Memory/Layout.lean` - Added `integerTypeMax`/`integerTypeMin` helpers
