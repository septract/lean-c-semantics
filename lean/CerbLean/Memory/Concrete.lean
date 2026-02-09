/-
  Concrete memory model implementation
  Corresponds to: cerberus/memory/concrete/impl_mem.ml:277-3015

  This implements allocation-ID provenance tracking for:
  - Bounds checking
  - Dangling pointer detection (use-after-free)
  - Read-only memory protection

  The concrete memory model uses:
  - Provenance based on allocation IDs (Prov_some alloc_id)
  - Address-based bounds checking
  - Byte-level memory representation

  CRITICAL: This implementation must match Cerberus exactly for differential testing.
-/

import CerbLean.Memory.Interface

namespace CerbLean.Memory

open CerbLean.Core

/-! ## IEEE 754 Float Conversion Helpers

Lean's Float is always 64-bit (double precision). We need to convert
between 32-bit (float) and 64-bit (double) IEEE 754 representations.
-/

/-- Convert 64-bit IEEE 754 double bits to 32-bit IEEE 754 float bits.
    This truncates precision from double to float. -/
def doubleBitsToFloat32Bits (doubleBits : UInt64) : UInt32 :=
  -- IEEE 754 double: sign(1) | exponent(11) | mantissa(52)
  -- IEEE 754 float:  sign(1) | exponent(8)  | mantissa(23)
  let sign := (doubleBits >>> 63) &&& 1
  let exp := (doubleBits >>> 52) &&& 0x7FF  -- 11-bit exponent
  let mant := doubleBits &&& 0xFFFFFFFFFFFFF  -- 52-bit mantissa

  -- Handle special cases
  if exp == 0x7FF then
    -- Infinity or NaN
    let float32Sign := sign.toUInt32 <<< 31
    let float32Exp : UInt32 := (0xFF : UInt32) <<< 23  -- All 1s exponent
    if mant == 0 then
      -- Infinity
      float32Sign ||| float32Exp
    else
      -- NaN - preserve quiet NaN bit
      float32Sign ||| float32Exp ||| (0x400000 : UInt32)  -- Set quiet NaN bit
  else if exp == 0 then
    -- Zero or denormal - just return zero (denormals are rare)
    sign.toUInt32 <<< 31
  else
    -- Normal number
    -- Convert exponent: double bias is 1023, float bias is 127
    -- new_exp = exp - 1023 + 127 = exp - 896
    let expVal := exp.toNat
    if expVal < 897 then
      -- Underflow to zero
      sign.toUInt32 <<< 31
    else if expVal > 1150 then
      -- Overflow to infinity
      (sign.toUInt32 <<< 31) ||| ((0xFF : UInt32) <<< 23)
    else
      let float32Exp := (expVal - 896 : Nat).toUInt32
      let float32Mant := (mant >>> 29).toUInt32  -- Keep top 23 bits
      (sign.toUInt32 <<< 31) ||| (float32Exp <<< 23) ||| float32Mant

/-- Convert 32-bit IEEE 754 float bits to 64-bit IEEE 754 double bits.
    This widens precision from float to double. -/
def float32BitsToDoubleBits (float32Bits : UInt32) : UInt64 :=
  -- IEEE 754 float:  sign(1) | exponent(8)  | mantissa(23)
  -- IEEE 754 double: sign(1) | exponent(11) | mantissa(52)
  let sign := (float32Bits >>> 31) &&& 1
  let exp := (float32Bits >>> 23) &&& 0xFF  -- 8-bit exponent
  let mant := float32Bits &&& 0x7FFFFF  -- 23-bit mantissa

  -- Handle special cases
  if exp == 0xFF then
    -- Infinity or NaN
    let doubleSign := sign.toUInt64 <<< 63
    let doubleExp : UInt64 := (0x7FF : UInt64) <<< 52  -- All 1s exponent
    if mant == 0 then
      -- Infinity
      doubleSign ||| doubleExp
    else
      -- NaN - preserve quiet NaN
      doubleSign ||| doubleExp ||| (mant.toUInt64 <<< 29)
  else if exp == 0 then
    -- Zero or denormal
    if mant == 0 then
      -- Zero
      sign.toUInt64 <<< 63
    else
      -- Denormal - convert to normalized double
      -- This is complex, just return zero for now
      sign.toUInt64 <<< 63
  else
    -- Normal number
    -- Convert exponent: float bias is 127, double bias is 1023
    -- new_exp = exp - 127 + 1023 = exp + 896
    let doubleExp := (exp.toNat + 896 : Nat).toUInt64
    let doubleMant := mant.toUInt64 <<< 29  -- Extend mantissa
    (sign.toUInt64 <<< 63) ||| (doubleExp <<< 52) ||| doubleMant

/-! ## Concrete Memory Monad

Corresponds to: memM monad in impl_mem.ml:277
The monad combines state (for memory) with reader (for type environment).
-/

/-- Concrete memory monad with type environment.
    Corresponds to: memM type in impl_mem.ml:277 -/
abbrev ConcreteMemM := ReaderT TypeEnv MemM

/-! ## Helper Functions

Internal utilities for the concrete memory model.
-/

/-- Get allocation ID from provenance.
    Audited: 2026-01-01
    Deviations: None -/
def toAllocId (prov : Provenance) : Nat :=
  match prov with
  | .some id => id
  | .none => panic! "toAllocId: provenance is none"
  | .symbolic iota => panic! s!"toAllocId: provenance is symbolic (iota={iota})"
  | .device => panic! "toAllocId: provenance is device"

/-- Check if a Ctype is atomic.
    Corresponds to: AilTypesAux.is_atomic in Cerberus -/
def isAtomicType (ty : Ctype) : Bool :=
  match ty.ty with
  | .atomic _ => true
  | _ => false

/-- Check if this is an atomic member access (UB042).
    Corresponds to: is_atomic_member_access in impl_mem.ml:689-705
    Audited: 2026-01-02
    Deviations: None

    Returns true if we're accessing a member of an atomic struct/union.
    Accessing the whole atomic object at base address with matching size is allowed. -/
def isAtomicMemberAccess (alloc : Allocation) (addr : Nat) (accessSize : Nat) (accessTy : Ctype) : Bool :=
  match alloc.ty with
  | some allocTy =>
    if isAtomicType allocTy then
      -- If accessing at base with same size and type, it's the whole object - allowed
      if addr == alloc.base && accessSize == alloc.size && allocTy == accessTy then
        false
      else
        -- Otherwise it's a member access - UB
        true
    else
      false
  | none =>
    -- Dynamic allocation (malloc) - not atomic
    false

/-- Check if an allocation is still live (not freed).
    Corresponds to: is_dead check in impl_mem.ml (negated)
    Audited: 2026-01-01
    Deviations: None -/
def isAllocLive (st : MemState) (allocId : Nat) : Bool :=
  st.allocations.contains allocId && !st.deadAllocations.contains allocId

/-- Get allocation for a pointer, checking validity.
    Corresponds to: get_allocation in impl_mem.ml
    Audited: 2026-01-01
    Deviations: Simplified error handling -/
def getAllocation (ptr : PointerValue) : ConcreteMemM Allocation := do
  let st ← get
  match ptr.prov with
  | .none =>
    -- Corresponds to: impl_mem.ml:1609,1716-1717 — Prov_none throws OutOfBoundPtr
    throw (.access .outOfBoundPtr none)
  | .some allocId =>
    if st.deadAllocations.contains allocId then
      throw (.access .deadPtr (some allocId))
    match st.allocations[allocId]? with
    | some alloc => pure alloc
    | none => throw (.access .noProvPtr (some allocId))
  | .symbolic _ =>
    throw (.typeError "symbolic provenance not supported")
  | .device =>
    throw (.typeError "device memory not supported")

/-- Check if address is within allocation bounds.
    Corresponds to: is_within_bound in impl_mem.ml
    Audited: 2026-01-01
    Deviations: None -/
def isInBounds (alloc : Allocation) (addr : Nat) (size : Nat) : Bool :=
  addr >= alloc.base && addr + size <= alloc.base + alloc.size

/-- Check if a type is _Bool.
    Corresponds to: AilTypesAux.is_Bool in impl_mem.ml:1579
    Audited: 2026-01-16
    Deviations: None -/
def isBoolType (ty : Ctype) : Bool :=
  match ty.ty with
  | .basic (.integer .bool) => true
  | _ => false

/-- Check if a _Bool value is a trap representation.
    A _Bool trap representation is any value other than 0 or 1, or unspecified.
    Corresponds to: impl_mem.ml:1576-1586
    Audited: 2026-01-16
    Deviations: None -/
def isBoolTrapRepresentation (mval : MemValue) : Bool :=
  match mval with
  | .unspecified _ => true
  | .integer _ iv =>
    -- Trap if not 0 or 1
    iv.val != 0 && iv.val != 1
  | _ => false

/-! ## Byte-Level Operations

Corresponds to: fetch_bytes and write_bytes in impl_mem.ml:708-737
-/

/-- Write bytes to memory.
    Corresponds to: write_bytes in impl_mem.ml:725-737
    Audited: 2026-01-01
    Deviations: None -/
def writeBytes (addr : Nat) (bytes : List AbsByte) : ConcreteMemM Unit := do
  let st ← get
  let newBytemap := bytes.foldl (init := (addr, st.bytemap)) fun (a, bm) byte =>
    (a + 1, bm.insert a byte)
  set { st with bytemap := newBytemap.2 }

/-- Write raw bytes with uniform provenance to memory.
    Helper for allocation initialization. -/
def writeBytesWithProv (addr : Nat) (bytes : List (Option UInt8)) (prov : Provenance) : ConcreteMemM Unit := do
  let absBytes := bytes.map fun mbyte => { prov := prov, copyOffset := none, value := mbyte : AbsByte }
  writeBytes addr absBytes

/-- Read bytes from memory.
    Corresponds to: fetch_bytes in impl_mem.ml:708-722
    Audited: 2026-01-01
    Deviations: None (little-endian byte order matches) -/
def readBytes (addr : Nat) (size : Nat) : ConcreteMemM (List AbsByte) := do
  let st ← get
  let bytes := List.range size |>.map fun i =>
    match st.bytemap[addr + i]? with
    | some b => b
    | none => panic! s!"readBytes: address {addr + i} not in bytemap (reading {size} bytes from {addr})"
  pure bytes

/-! ## Value Serialization

Corresponds to: bytes_of_int and int_of_bytes in impl_mem.ml:739-758
and repr/abst in impl_mem.ml:916-1219

Convert memory values to/from byte sequences using little-endian representation.
-/

/-- Convert integer to little-endian bytes (two's complement).
    Corresponds to: bytes_of_int (implicit in repr) impl_mem.ml
    Audited: 2026-01-01
    Deviations: None -/
def intToBytes (val : Int) (size : Nat) : List (Option UInt8) :=
  -- Convert negative numbers to two's complement representation
  let totalBits := size * 8
  let modulusVal := 1 <<< totalBits
  let unsigned := if val < 0 then modulusVal + val else val
  List.range size |>.map fun i =>
    let shifted := unsigned >>> (i * 8)
    some (shifted.toNat % 256).toUInt8

/-- Convert little-endian bytes to integer.
    Corresponds to: int_of_bytes in impl_mem.ml:739-758
    Audited: 2026-01-01
    Deviations: None -/
def bytesToInt (bytes : List AbsByte) (signed : Bool) : Option Int :=
  if bytes.any (·.value.isNone) then
    none  -- Uninitialized bytes
  else
    let rec go (bs : List AbsByte) (i : Nat) (acc : Int) : Int :=
      match bs with
      | [] => acc
      | b :: rest =>
        let contribution := match b.value with
          | some v => (v.toNat : Int) <<< (i * 8)
          | none => panic! "bytesToInt: unexpected none value (should have been caught earlier)"
        go rest (i + 1) (acc + contribution)
    let unsigned := go bytes 0 0
    if signed && bytes.length > 0 then
      let bits := bytes.length * 8
      let signBit := 1 <<< (bits - 1)
      if unsigned >= signBit then
        some (unsigned - (1 <<< bits))
      else
        some unsigned
    else
      some unsigned

/-- Get the provenance from bytes (for pointer loads).
    Corresponds to: provenance extraction in abst impl_mem.ml
    Audited: 2026-01-01
    Deviations: Simplified - takes first non-none provenance -/
def bytesProvenance (bytes : List AbsByte) : Provenance :=
  -- Take provenance from first byte with provenance
  bytes.findSome? (fun b =>
    match b.prov with
    | .none => none
    | p => some p
  ) |>.getD .none

/-- Helper to create AbsByte with no provenance -/
def mkAbsByte (v : Option UInt8) : AbsByte :=
  { prov := .none, copyOffset := none, value := v }

/-- Helper to create AbsByte with provenance -/
def mkAbsByteWithProv (prov : Provenance) (i : Nat) (v : Option UInt8) : AbsByte :=
  { prov := prov, copyOffset := some i, value := v }

/-- Convert raw bytes to AbsBytes with no provenance -/
def rawToAbsBytes (bytes : List (Option UInt8)) : List AbsByte :=
  bytes.map mkAbsByte

/-- Serialize memory value to abstract bytes.
    Corresponds to: repr in impl_mem.ml:1139-1219
    Audited: 2026-01-16
    Deviations:
    - Function pointer encoding simplified -/
partial def memValueToBytes (env : TypeEnv) (val : MemValue) : List AbsByte :=
  match val with
  | .unspecified ty =>
    List.replicate (sizeof env ty) (mkAbsByte none)
  | .integer ity iv =>
    -- Integer bytes carry the integer's provenance (for pointer-derived integers)
    let rawBytes := intToBytes iv.val (integerTypeSize ity)
    rawBytes.mapIdx fun i v => { prov := iv.prov, copyOffset := some i, value := v }
  | .floating fty fv =>
    -- Store float as IEEE 754 bit representation
    -- Corresponds to: impl_mem.ml float storing (repr for floating types)
    -- Note: Cerberus stores ALL floating types as 8-byte 64-bit doubles
    let size := floatingTypeSize fty  -- Always 8 (Cerberus uses 8 for all floats)
    match fv with
    | .finite f =>
      -- Convert float to IEEE 754 64-bit bits (always double precision)
      let bits := f.toBits.toNat
      rawToAbsBytes (intToBytes bits size)
    | .nan =>
      -- IEEE 754 quiet NaN: exponent all 1s, mantissa MSB = 1
      let bits := 0x7FF8000000000000  -- 64-bit NaN
      rawToAbsBytes (intToBytes bits size)
    | .posInf =>
      -- IEEE 754 +Infinity: sign=0, exponent all 1s, mantissa all 0s
      let bits := 0x7FF0000000000000  -- 64-bit +Infinity
      rawToAbsBytes (intToBytes bits size)
    | .negInf =>
      -- IEEE 754 -Infinity: sign=1, exponent all 1s, mantissa all 0s
      let bits := 0xFFF0000000000000  -- 64-bit -Infinity
      rawToAbsBytes (intToBytes bits size)
    | .unspecified =>
      -- Unspecified float value - store as unspecified bytes
      List.replicate size (mkAbsByte none)
  | .pointer _ pv =>
    -- Pointer bytes carry the pointer's provenance
    -- Corresponds to: impl_mem.ml:1187 - AbsByte.v prov ~copy_offset:(Some i)
    let (rawBytes, prov) := match pv.base with
      | .null _ => (intToBytes 0 targetPtrSize, Provenance.none)
      | .function sym => (intToBytes sym.id targetPtrSize, pv.prov)
      | .concrete _ addr => (intToBytes addr targetPtrSize, pv.prov)
    rawBytes.mapIdx fun i v => mkAbsByteWithProv prov i v
  | .array elems =>
    elems.flatMap (memValueToBytes env)
  | .struct_ tag members =>
    -- Layout struct with padding
    match env.lookupTag tag with
    | some (.struct_ fields _) =>
      let offsets := structOffsets env fields
      let size := structSize env fields
      let bytes := List.replicate size (mkAbsByte (some 0))
      members.foldl (init := bytes) fun acc (name, _, mval) =>
        match offsets.find? (·.1 == name) with
        | some (_, offset) =>
          let memberBytes := memValueToBytes env mval
          -- Insert member bytes at offset
          acc.mapIdx fun i b =>
            if i >= offset && i < offset + memberBytes.length then
              memberBytes[i - offset]!
            else b
        | none => panic! s!"memValueToBytes: member {name.name} not found in struct {tag.name}"
    | some (.union_ _) => panic! s!"memValueToBytes: expected struct but found union for tag {tag.name}"
    | none => panic! s!"memValueToBytes: undefined struct tag {tag.name}"
  | .union_ tag _ mval =>
    -- Union uses size of largest member
    let memberBytes := memValueToBytes env mval
    match env.lookupTag tag with
    | some (.union_ fields) =>
      let size := unionSize env fields
      memberBytes ++ List.replicate (size - memberBytes.length) (mkAbsByte (some 0))
    | some (.struct_ _ _) => panic! s!"memValueToBytes: expected union but found struct for tag {tag.name}"
    | none => panic! s!"memValueToBytes: undefined union tag {tag.name}"

/-- Collect all function pointer symbols from a MemValue.
    Used to register function pointers in funptrmap before serialization.
    Corresponds to: repr in impl_mem.ml which updates funptrmap as it serializes -/
partial def collectFunPtrs (val : MemValue) : List Sym :=
  match val with
  | .pointer _ pv =>
    match pv.base with
    | .function sym => [sym]
    | _ => []
  | .array elems => elems.flatMap collectFunPtrs
  | .struct_ _ members => members.flatMap fun (_, _, mval) => collectFunPtrs mval
  | .union_ _ _ mval => collectFunPtrs mval
  | _ => []

/-- Register function pointers in funptrmap.
    Corresponds to: IntMap.add in repr for function pointers (impl_mem.ml:1171) -/
def registerFunPtrs (syms : List Sym) : MemM Unit := do
  let st ← get
  let newMap := syms.foldl (init := st.funptrmap) fun m sym =>
    m.insert sym.id sym
  set { st with funptrmap := newMap }

/-! ## Core Memory Operations

Corresponds to: allocate_object, load, store, kill in impl_mem.ml:1288-1550
-/

/-- Align address down to alignment boundary. -/
def alignDown (addr : Nat) (align : Nat) : Nat :=
  addr - (addr % align)

/-- Allocate memory and return pointer.
    Corresponds to: allocate_object in impl_mem.ml:1288-1347
                   and allocator in impl_mem.ml:1247-1265
    Audited: 2026-01-06
    Deviations:
    - No thread_id parameter (sequential only)
    - No Symbol.prefix (simplified to String)
    - No cerb::with_address support yet

    Address allocation grows DOWNWARD from lastAddress (matching Cerberus):
    - Cerberus: impl_mem.ml:1252-1254
        let z = sub st.last_address size in
        let (q,m) = quomod z align in
        let z' = sub z (if less q zero then negate m else m)
    - This subtracts size, then aligns down to alignment boundary -/
def allocateImpl (name : String) (size : Nat) (ty : Option Ctype)
    (align : Nat) (readonly : ReadonlyStatus) (init : Option MemValue) : ConcreteMemM PointerValue := do
  let env ← read
  let st ← get

  -- Compute aligned base address (growing downward)
  -- Corresponds to: impl_mem.ml:1252-1254
  let addrAfterSize := st.lastAddress - size
  let alignedAddr := alignDown addrAfterSize align

  -- Check for out of memory
  if alignedAddr == 0 then
    throw (.other "allocator: out of memory")

  -- Create allocation record
  let allocId := st.nextAllocId
  let alloc : Allocation := {
    base := alignedAddr
    size := size
    ty := ty
    isReadonly := readonly
    name := name
  }

  -- Update state
  set {
    st with
    nextAllocId := allocId + 1
    lastAddress := alignedAddr
    allocations := st.allocations.insert allocId alloc
  }

  -- Initialize memory if provided
  -- Corresponds to: impl_mem.ml:1304-1322 (allocate_object init handling)
  -- Audited: 2026-01-06
  match init with
  | some val =>
    let bytes := memValueToBytes env val
    writeBytes alignedAddr bytes
  | none =>
    -- Write unspecified bytes (NOT zero-initialized)
    -- Corresponds to: impl_mem.ml:1317-1322 (init_opt = None case, no SW_zero_initialised)
    --   calls repr (MVunspecified ty) at line 1318
    --   which at impl_mem.ml:1142-1144 produces:
    --     List.init (sizeof ty) (fun _ -> AbsByte.v Prov_none None)
    -- We use `size` which equals `sizeof ty` from caller
    let unspecifiedBytes := List.replicate size { prov := .none, copyOffset := none, value := none : AbsByte }
    writeBytes alignedAddr unspecifiedBytes

  pure (concretePtrval allocId alignedAddr)

/-- Reconstruct memory value from bytes.
    Corresponds to: abst in impl_mem.ml:916-1093
    Audited: 2026-01-01
    Deviations:
    - Float reconstruction simplified
    - No PNVI-ae-udi taint handling
    - Struct reconstruction simplified -/
partial def reconstructValue (env : TypeEnv) (ty : Ctype) (bytes : List AbsByte) : ConcreteMemM MemValue := do
  match ty.ty with
  | .basic (.integer ity) =>
    let signed := match ity with
      | .signed _ => true
      | .char => true  -- Assuming signed char
      | .ptrdiff_t => true
      | _ => false
    match bytesToInt bytes signed with
    | some n =>
      let prov := bytesProvenance bytes
      pure (.integer ity { val := n, prov := prov })
    | none =>
      pure (.unspecified ty)

  | .basic (.floating fty) =>
    -- Reconstruct float from IEEE 754 bit representation
    -- Corresponds to: impl_mem.ml float loading (abst for floating types)
    -- Note: Cerberus stores ALL floating types as 8-byte 64-bit doubles
    match bytesToInt bytes false with
    | some n =>
      -- Convert IEEE 754 64-bit bits back to Float
      let bits : UInt64 := n.toNat.toUInt64
      pure (.floating fty (.finite (Float.ofBits bits)))
    | none =>
      pure (.unspecified ty)

  | .pointer quals pointeeTy =>
    let pointeeCty : Ctype := { ty := pointeeTy }
    match bytesToInt bytes false with
    | some 0 =>
      pure (.pointer (Ctype.pointer quals pointeeCty) (nullPtrval pointeeCty))
    | some addr =>
      -- Check if this address is a function pointer
      -- Corresponds to: IntMap.find_opt in abst for function pointers (impl_mem.ml:1010-1014)
      let st ← get
      match st.funptrmap[addr.toNat]? with
      | some sym =>
        -- This is a function pointer - reconstruct with function base
        let prov := bytesProvenance bytes
        pure (.pointer (Ctype.pointer quals pointeeCty) { prov := prov, base := .function sym })
      | none =>
        -- Regular concrete pointer
        let prov := bytesProvenance bytes
        pure (.pointer (Ctype.pointer quals pointeeCty) { prov := prov, base := .concrete none addr.toNat })
    | none =>
      pure (.unspecified ty)

  | .array elemTy (some n) =>
    -- Corresponds to: abst in impl_mem.ml:986-994 (Array case)
    -- Audited: 2026-01-06
    let elemCty : Ctype := { ty := elemTy }
    let elemSize := sizeof env elemCty
    let elems ← List.range n |>.mapM fun i => do
      let start := i * elemSize
      let elemBytes := bytes.drop start |>.take elemSize
      reconstructValue env elemCty elemBytes
    pure (.array elems)

  | .array _ none =>
    throw (.typeError "reconstructValue: flexible array member (incomplete array type)")
  | .void =>
    throw (.typeError "reconstructValue: void type cannot be loaded")
  | .function .. =>
    throw (.typeError "reconstructValue: function type cannot be loaded")
  | .functionNoParams .. =>
    throw (.typeError "reconstructValue: function type cannot be loaded")
  | .struct_ tag =>
    -- Reconstruct struct by extracting and reconstructing each member
    -- Corresponds to: abst in impl_mem.ml:1062-1072 (Struct case)
    -- Algorithm:
    --   1. Split bytes at sizeof(struct) to get bs1 (struct bytes) and bs2 (remaining)
    --   2. Fold over offsetsof results: (memb_ident, memb_ty, memb_offset)
    --   3. For each member: compute pad = memb_offset - previous_offset
    --   4. Drop pad bytes, recursively reconstruct member
    --   5. Track previous_offset = memb_offset + sizeof(memb_ty)
    --   6. Return MVstruct with members list
    -- Audited: 2026-01-06
    match env.lookupTag tag with
    | some (.struct_ fields _) =>
      let structSize := structSize env fields
      let structBytes := bytes.take structSize
      let memberInfo := structMemberInfo env fields
      -- Fold over members, tracking previous offset like Cerberus
      let (_, revMembers) ← memberInfo.foldlM (init := (0, [])) fun (prevOffset, acc) (membIdent, membTy, membOffset) => do
        -- Corresponds to: let pad = N.to_int (N.sub memb_offset previous_offset) in
        let _pad := membOffset - prevOffset
        -- Corresponds to: let (taint, mval, acc_bs') = self ~offset:pad memb_ty (L.drop pad acc_bs) in
        let membSize := sizeof env membTy
        let membBytes := structBytes.drop membOffset |>.take membSize
        let membVal ← reconstructValue env membTy membBytes
        -- Corresponds to: N.add memb_offset (sizeof memb_ty)
        let newPrevOffset := membOffset + sizeof env membTy
        pure (newPrevOffset, (membIdent, membTy, membVal) :: acc)
      -- Corresponds to: MVstruct (tag_sym, List.rev rev_xs)
      pure (.struct_ tag revMembers.reverse)
    | some (.union_ _) =>
      throw (.typeError s!"struct reconstruction: expected struct but found union for tag {tag.name}")
    | none =>
      throw (.typeError s!"struct reconstruction: undefined tag {tag.name}")

  | .union_ tag =>
    -- Reconstruct union - use first member's type for reconstruction
    -- Corresponds to: abst in impl_mem.ml:1073-1093 (Union case)
    -- Algorithm:
    --   1. Split bytes at sizeof(union) to get bs1, bs2
    --   2. Look up union member from unionmap (we don't track this, so use first member)
    --   3. Recursively reconstruct the member
    --   4. Return MVunion (tag_sym, membr_ident, mval)
    -- Note: Cerberus uses `last_used_union_members` map to track which member was stored.
    --       We don't track this, so we always use the first member (matches line 1083).
    -- Audited: 2026-01-06
    match env.lookupTag tag with
    | some (.union_ fields) =>
      match fields.head? with
      | some field =>
        -- Corresponds to: let (taint, mval, _ ) = self membr_ty bs1 in
        let memberVal ← reconstructValue env field.ty bytes
        -- Corresponds to: MVunion (tag_sym, membr_ident, mval)
        pure (.union_ tag field.name memberVal)
      | none =>
        throw (.typeError s!"union reconstruction: empty union {tag.name}")
    | some (.struct_ _ _) =>
      throw (.typeError s!"union reconstruction: expected union but found struct for tag {tag.name}")
    | none =>
      throw (.typeError s!"union reconstruction: undefined tag {tag.name}")

  | .atomic innerTy =>
    -- For atomic types, reconstruct the underlying type
    -- Corresponds to: abst in impl_mem.ml:1059-1061 (Atomic case)
    -- Cerberus: self atom_ty bs (just recurse on the inner type)
    -- Audited: 2026-01-06
    let innerCty : Ctype := { ty := innerTy }
    reconstructValue env innerCty bytes

  | .byte =>
    -- Byte type (std::byte in C++) is treated like unsigned char
    -- Corresponds to: abst in impl_mem.ml:961-973 (Byte case)
    -- Cerberus: MVinteger (Char, mk_ival prov (int_of_bytes false cs))
    -- Audited: 2026-01-06
    let (bs1, _) := bytes.splitAt 1
    match bytesToInt bs1 false with
    | some n =>
      let prov := bytesProvenance bs1
      -- Cerberus uses Char (which is char type), we use unsigned ichar
      pure (.integer .char { val := n, prov := prov })
    | none =>
      pure (.unspecified ty)

/-- Load value from memory.
    Corresponds to: load in impl_mem.ml:1552-1603
    Audited: 2026-01-16
    Deviations:
    - No PNVI-ae-udi symbolic provenance resolution
    - No device memory support -/
def loadImpl (ty : Ctype) (ptr : PointerValue) : ConcreteMemM (Footprint × MemValue) := do
  let env ← read

  -- Check for null pointer
  match ptr.base with
  | .null _ => throw (.access .nullPtr none)
  | .function _ => throw (.access .functionPtr none)
  | .concrete _ addr =>
    -- Check allocation validity
    let alloc ← getAllocation ptr

    let size := sizeof env ty
    -- Check bounds
    if !isInBounds alloc addr size then
      throw (.access .outOfBoundPtr (some addr))

    -- Check for atomic member access (UB042)
    -- Corresponds to: is_atomic_member_access check in impl_mem.ml:1633, 1658
    if isAtomicMemberAccess alloc addr size ty then
      throw (.access .atomicMemberof (some addr))

    -- Read bytes and reconstruct value
    let bytes ← readBytes addr size
    let footprint : Footprint := { kind := .read, base := addr, size := size }

    -- Reconstruct value from bytes
    let val ← reconstructValue env ty bytes

    -- Check for _Bool trap representation
    -- Corresponds to: impl_mem.ml:1576-1586
    if isBoolType ty && isBoolTrapRepresentation val then
      throw (.trapRepresentation .read)

    pure (footprint, val)

/-- Store value to memory.
    Corresponds to: store in impl_mem.ml:1667-1789
    Audited: 2026-01-01
    Deviations:
    - No PNVI-ae-udi symbolic provenance resolution
    - No device memory support
    - isLocking locks entire allocation (Cerberus is more granular) -/
def storeImpl (ty : Ctype) (isLocking : Bool) (ptr : PointerValue) (val : MemValue) : ConcreteMemM Footprint := do
  let env ← read

  match ptr.base with
  | .null _ => throw (.access .nullPtr none)
  | .function _ => throw (.access .functionPtr none)
  | .concrete unionMem addr =>
    let alloc ← getAllocation ptr

    -- Check read-only
    match alloc.isReadonly with
    | .readonly _ => throw .readonlyWrite
    | .writable => pure ()

    let size := sizeof env ty
    -- Check bounds
    if !isInBounds alloc addr size then
      throw (.access .outOfBoundPtr (some addr))

    -- Check for atomic member access (UB042)
    -- Corresponds to: is_atomic_member_access check in impl_mem.ml:1741, 1772
    if isAtomicMemberAccess alloc addr size ty then
      throw (.access .atomicMemberof (some addr))

    -- Register any function pointers in funptrmap before serialization
    -- Corresponds to: repr updating funptrmap in impl_mem.ml:1171
    let funPtrs := collectFunPtrs val
    registerFunPtrs funPtrs

    -- Serialize and write
    -- Note: memValueToBytes now returns List AbsByte with proper provenance
    let bytes := memValueToBytes env val
    writeBytes addr bytes

    -- Update last used union member if pointer has union member annotation
    -- Corresponds to: impl_mem.ml:1695-1698
    match unionMem with
    | some membr =>
      let st ← get
      set { st with lastUsedUnionMembers := st.lastUsedUnionMembers.insert addr membr }
    | none => pure ()

    -- Lock if requested
    -- Corresponds to: impl_mem.ml:1749-1784 (is_locking branch)
    -- Derives readonly kind from allocation prefix (impl_mem.ml:1704-1710 select_ro_kind)
    if isLocking then
      let st ← get
      let allocId := toAllocId ptr.prov
      match st.allocations[allocId]? with
      | some allocRec =>
        let roKind := match allocRec.name with
          | "PrefStringLiteral" => ReadonlyKind.stringLiteral
          | "PrefTemporaryLifetime" => ReadonlyKind.temporaryLifetime
          | _ => ReadonlyKind.constQualified
        set { st with allocations := st.allocations.insert allocId { allocRec with isReadonly := .readonly roKind } }
      | none => panic! s!"storeImpl: allocation {allocId} not found when trying to lock"

    pure { kind := .write, base := addr, size := size }

/-- Deallocate memory.
    Corresponds to: kill in impl_mem.ml:1464-1550
    Audited: 2026-01-01
    Deviations:
    - No PNVI-ae-udi symbolic provenance resolution
    - No SW_zap_dead_pointers support
    - No SW_forbid_nullptr_free switch (free(NULL) always allowed) -/
def killImpl (isDynamic : Bool) (ptr : PointerValue) : ConcreteMemM Unit := do
  match ptr.base with
  | .null _ =>
    -- free(NULL) is allowed for dynamic
    if isDynamic then pure ()
    else throw (.free .nonMatching)
  | .function _ =>
    throw (.free .nonMatching)
  | .concrete _ addr =>
    match ptr.prov with
    | .some allocId =>
      let st ← get
      -- Check not already freed
      if st.deadAllocations.contains allocId then
        throw (.free .deadAllocation)
      -- Check allocation exists and address matches base
      match st.allocations[allocId]? with
      | some alloc =>
        if addr != alloc.base then
          throw (.free .outOfBound)
        -- Validate dynamic allocation for free()
        -- Corresponds to: impl_mem.ml:1516-1526
        if isDynamic then
          if !st.dynamicAddrs.contains alloc.base then
            throw (.free .nonMatching)
        -- Mark as dead and remove from allocations
        -- Corresponds to: impl_mem.ml:1539-1542
        set { st with
          deadAllocations := allocId :: st.deadAllocations
          allocations := st.allocations.erase allocId
        }
      | none =>
        throw (.free .nonMatching)
    | _ =>
      throw (.free .nonMatching)

/-! ## Pointer Operations

Corresponds to: eq_ptrval, diff_ptrval, eff_array_shift_ptrval, etc. in impl_mem.ml
-/

/-- Pointer equality.
    Corresponds to: impl_eq_ptrval in defacto_memory.lem:1418-1503
    Audited: 2026-01-06
    Deviations: We use provenance-based comparison (matches Cerberus standard mode) -/
def eqPtrvalImpl (p1 p2 : PointerValue) : ConcreteMemM Bool := do
  match p1.base, p2.base with
  -- STD §6.5.9#6: null pointers compare equal
  | .null _, .null _ => pure true
  | .null _, _ => pure false
  | _, .null _ => pure false
  -- Function pointers compare by symbol
  | .function s1, .function s2 => pure (s1 == s2)
  -- Function pointer vs concrete: check funptrmap
  -- Corresponds to: impl_mem.ml:1839-1847
  | .function sym, .concrete _ addr =>
    let st ← get
    match st.funptrmap[addr]? with
    | some mappedSym => pure (sym == mappedSym)
    | none => pure false
  | .concrete _ addr, .function sym =>
    let st ← get
    match st.funptrmap[addr]? with
    | some mappedSym => pure (sym == mappedSym)
    | none => pure false
  | .concrete _ a1, .concrete _ a2 =>
    -- For concrete pointers, check provenance
    -- Corresponds to: impl_mem.ml:1851-1880 (eq_ptrval)
    -- Step 1: Check if provenances "match"
    let provsMatch : ConcreteMemM Bool := match p1.prov, p2.prov with
      | .none, .none =>
        -- impl_mem.ml:1855-1856: (Prov_none, Prov_none) -> return true
        pure true
      | .some alloc1, .some alloc2 =>
        -- impl_mem.ml:1857-1858: (Prov_some id1, Prov_some id2) -> return (equal id1 id2)
        pure (alloc1 == alloc2)
      | .device, .device =>
        -- impl_mem.ml:1859-1860: (Prov_device, Prov_device) -> return true
        pure true
      | .symbolic iota1, .symbolic iota2 =>
        -- impl_mem.ml:1861-1870: symbolic lookup (simplified: just compare iotas)
        pure (iota1 == iota2)
      | _, _ =>
        -- impl_mem.ml:1871-1872: _ -> return false (mixed provenance types)
        pure false
    -- Step 2: Based on provenance match result
    -- impl_mem.ml:1873-1880
    provsMatch >>= fun provMatch =>
      if provMatch then
        -- Provenances match: honest address comparison
        -- impl_mem.ml:1874-1875: true -> return (equal addr1 addr2)
        pure (a1 == a2)
      else
        -- Provenances don't match: nondeterministic in Cerberus
        -- impl_mem.ml:1876-1879: msum ["using provenance" -> false, "ignoring provenance" -> addr_eq]
        -- In --exec mode, Cerberus picks "using provenance" which returns false
        pure false

/-- Pointer difference.
    Corresponds to: diff_ptrval in impl_mem.ml
    Audited: 2026-02-08
    Deviations: None -/
def diffPtrvalImpl (elemTy : Ctype) (p1 p2 : PointerValue) : ConcreteMemM IntegerValue := do
  let env ← read
  match p1.base, p2.base with
  | .concrete _ a1, .concrete _ a2 =>
    -- Check same allocation for defined behavior
    match p1.prov, p2.prov with
    | .some id1, .some id2 =>
      if id1 != id2 then
        -- Different allocations — Cerberus fails with MerrPtrdiff
        -- Corresponds to: impl_mem.ml:1954-2063
        throw .ptrdiff
      else
        let elemSize := sizeof env elemTy
        if elemSize == 0 then
          throw (.typeError "pointer difference with zero-sized element")
        let diff := (a1 : Int) - (a2 : Int)
        -- Use truncated division to match Cerberus's integerDiv_t
        pure (integerIval (diff.tdiv elemSize))
    | _, _ =>
      throw (.access .noProvPtr none)
  | _, _ =>
    throw (.typeError "pointer difference requires concrete pointers")

/-- Effectful array shift with bounds checking.
    Corresponds to: eff_array_shift_ptrval in impl_mem.ml
    Audited: 2026-01-01
    Deviations: None -/
def effArrayShiftPtrvalImpl (ptr : PointerValue) (elemTy : Ctype) (n : IntegerValue) : ConcreteMemM PointerValue := do
  let env ← read
  match ptr.base with
  | .null _ =>
    -- Corresponds to: impl_mem.ml:2248-2252 — fail on NULL
    throw .arrayShift
  | .function sym => pure { ptr with base := .function sym }
  | .concrete unionMem addr =>
    let elemSize := sizeof env elemTy
    let offset := n.val * elemSize
    let newAddr := (addr : Int) + offset

    if newAddr < 0 then
      throw .ptrArithOverflow

    -- Check bounds if we have provenance
    match ptr.prov with
    | .some allocId =>
      let st ← get
      match st.allocations[allocId]? with
      | some alloc =>
        -- Allow one-past-the-end
        let newAddrNat := newAddr.toNat
        if newAddrNat < alloc.base || newAddrNat > alloc.base + alloc.size then
          throw (.access .outOfBoundPtr (some newAddrNat))
        pure { ptr with base := .concrete unionMem newAddrNat }
      | none =>
        throw (.access .noProvPtr (some addr))
    | .none =>
      -- No provenance, just do the arithmetic (no bounds checking possible)
      pure { ptr with base := .concrete unionMem newAddr.toNat }
    | .symbolic iota =>
      panic! s!"effArrayShiftPtrvalImpl: symbolic provenance not implemented (iota={iota})"
    | .device =>
      panic! "effArrayShiftPtrvalImpl: device provenance not implemented"

/-- Effectful member shift.
    Corresponds to: eff_member_shift_ptrval in impl_mem.ml
    Audited: 2026-01-01
    Deviations: None -/
def effMemberShiftPtrvalImpl (ptr : PointerValue) (tag : Sym) (member : Identifier) : ConcreteMemM PointerValue := do
  let env ← read
  pure (memberShiftPtrval env ptr tag member)

/-- Integer to pointer conversion.
    Corresponds to: ptrfromint in impl_mem.ml
    Audited: 2026-01-01
    Deviations: Simplified - no PNVI-ae-udi iota creation -/
def ptrfromintImpl (_fromTy : IntegerType) (toTy : Ctype) (n : IntegerValue) : ConcreteMemM PointerValue := do
  if n.val == 0 then
    pure (nullPtrval toTy)
  else
    -- Wrap integer to pointer range [0, 2^(8*sizeof_pointer) - 1]
    -- Corresponds to: impl_mem.ml:2126-2173
    let env ← read
    let ptrSize := sizeof env (Ctype.mk' (.pointer {} .void))
    let ptrRange : Int := 2 ^ (8 * ptrSize)
    let wrappedAddr := ((n.val % ptrRange) + ptrRange) % ptrRange
    pure { prov := n.prov, base := .concrete none wrappedAddr.toNat }

/-- Pointer to integer conversion.
    Corresponds to: intfromptr in impl_mem.ml:2439-2461
    Audited: 2026-01-06

    Range check: impl_mem.ml:2456-2459
      let IV (_, ity_max) = max_ival ity in
      let IV (_, ity_min) = min_ival ity in
      if N.(less addr ity_min || less ity_max addr) then
        fail ~loc MerrIntFromPtr -/
def intfromPtrImpl (_fromTy : Ctype) (toTy : IntegerType) (ptr : PointerValue) : ConcreteMemM IntegerValue := do
  match ptr.base with
  | .null _ =>
    -- Corresponds to: impl_mem.ml:2441-2442
    --   PVnull _ -> return (mk_ival prov Nat_big_num.zero)
    pure (integerIvalWithProv 0 ptr.prov)
  | .function sym =>
    -- Corresponds to: impl_mem.ml:2443-2444
    --   PVfunction (Symbol.Symbol (_, n, _)) -> return (mk_ival prov (Nat_big_num.of_int n))
    -- Convert function symbol ID to integer
    pure (integerIvalWithProv sym.id ptr.prov)
  | .concrete _ addr =>
    -- Corresponds to: impl_mem.ml:2445-2461
    -- Range check: fail with MerrIntFromPtr if address out of range
    let ityMax := integerTypeMax toTy
    let ityMin := integerTypeMin toTy
    let addrInt : Int := addr
    if addrInt < ityMin || addrInt > ityMax then
      -- UB024_out_of_range_pointer_to_integer_conversion
      throw (.intFromPtr)
    else
      pure (integerIvalWithProv addr ptr.prov)

/-- Check pointer alignment.
    Corresponds to: isWellAligned_ptrval in impl_mem.ml
    Audited: 2026-01-01
    Deviations: None -/
def isWellAlignedImpl (ty : Ctype) (ptr : PointerValue) : ConcreteMemM Bool := do
  let env ← read
  match ptr.base with
  | .null _ => pure true  -- NULL is well-aligned
  | .function _ => pure true
  | .concrete _ addr =>
    let align := alignof env ty
    pure (addr % align == 0)

/-- Check pointer validity for dereference.
    Corresponds to: validForDeref_ptrval in impl_mem.ml:2086-2123
    Audited: 2026-01-06

    IMPORTANT: This checks liveness and alignment ONLY, not bounds!
    Bounds checking is done in load/store operations.

    Cerberus logic:
    - null/function → false
    - device → isWellAligned only
    - Prov_some alloc_id → is_dead? then false, else isWellAligned
    - Prov_none → false -/
def validForDerefImpl (ty : Ctype) (ptr : PointerValue) : ConcreteMemM Bool := do
  match ptr.base with
  | .null _ => pure false
  | .function _ => pure false
  | .concrete _ _ =>
    match ptr.prov with
    | .some allocId =>
      let st ← get
      if st.deadAllocations.contains allocId then
        pure false
      else
        -- Only check alignment, not bounds (bounds checked at load/store)
        isWellAlignedImpl ty ptr
    | _ => pure false

/-! ## Memory Functions

Corresponds to: memcpy, memcmp, realloc in impl_mem.ml
-/

/-- Memory copy.
    Corresponds to: memcpy in impl_mem.ml
    Audited: 2026-01-01
    Deviations: Simplified overlap detection -/
def memcpyImpl (dst src : PointerValue) (n : IntegerValue) : ConcreteMemM PointerValue := do
  match dst.base, src.base with
  | .concrete _ dstAddr, .concrete _ srcAddr =>
    let size := n.val.toNat

    -- Check for overlap
    let overlap := (dstAddr < srcAddr + size) && (srcAddr < dstAddr + size)
    if overlap && dstAddr != srcAddr then
      throw (.memcpy .overlap)

    -- Read source bytes
    let bytes ← readBytes srcAddr size

    -- Write to destination (preserves provenance from source bytes)
    writeBytes dstAddr bytes

    pure dst
  | _, _ =>
    throw (.memcpy .nonObject)

/-- Memory compare.
    Corresponds to: memcmp in impl_mem.ml
    Audited: 2026-01-01
    Deviations: None -/
def memcmpImpl (p1 p2 : PointerValue) (n : IntegerValue) : ConcreteMemM IntegerValue := do
  match p1.base, p2.base with
  | .concrete _ a1, .concrete _ a2 =>
    let size := n.val.toNat
    let bytes1 ← readBytes a1 size
    let bytes2 ← readBytes a2 size

    -- Compare byte by byte
    let rec cmp : List AbsByte → List AbsByte → Int
      | [], [] => 0
      | [], _ => -1
      | _, [] => 1
      | b1::bs1, b2::bs2 =>
        match b1.value, b2.value with
        | some v1, some v2 =>
          if v1 < v2 then -1
          else if v1 > v2 then 1
          else cmp bs1 bs2
        | none, none => cmp bs1 bs2
        | none, _ => -1
        | _, none => 1

    pure (integerIval (cmp bytes1 bytes2))
  | _, _ =>
    throw (.memcpy .nonObject)

/-- Realloc.
    Corresponds to: realloc in impl_mem.ml
    Audited: 2026-01-01
    Deviations: Simplified - no thread_id -/
def reallocImpl (align : IntegerValue) (ptr : PointerValue) (newSize : IntegerValue) : ConcreteMemM PointerValue := do
  let size := newSize.val.toNat

  -- Handle NULL pointer case (acts like malloc)
  match ptr.base with
  | .null _ =>
    allocateImpl "realloc" size none align.val.toNat .writable none

  | .concrete _ oldAddr =>
    -- Get old allocation
    let alloc ← getAllocation ptr
    let oldSize := alloc.size

    -- Allocate new region
    let newPtr ← allocateImpl "realloc" size alloc.ty align.val.toNat .writable none

    -- Copy old data (preserves provenance from source bytes)
    let copySize := min oldSize size
    let bytes ← readBytes oldAddr copySize
    match newPtr.base with
    | .concrete _ newAddr =>
      writeBytes newAddr bytes
    | .null _ => panic! "reallocImpl: allocateImpl returned null pointer"
    | .function _ => panic! "reallocImpl: allocateImpl returned function pointer"

    -- Free old allocation
    killImpl true ptr

    pure newPtr

  | .function _ =>
    throw (.free .nonMatching)

/-- Validate pointers for relational comparison (lt, gt, le, ge).
    Corresponds to: impl_mem.ml:1886-1951 (strict pointer relationals)
    Note: Always uses strict mode (SW_strict_pointer_relationals). Cerberus's --exec
    default may be permissive, which would just compare addresses without checking
    allocation provenance. If differential testing shows mismatches, a non-strict
    fallback path may need to be added.
    Returns the two concrete addresses if comparison is valid. -/
private def validateRelationalPtrs (p1 p2 : PointerValue) : ConcreteMemM (Nat × Nat) := do
  match p1.base, p2.base with
  | .null _, _ | _, .null _ =>
    -- Null pointer relational comparison is undefined
    -- Corresponds to: impl_mem.ml:1891-1893
    throw .ptrComparison
  | .concrete _ a1, .concrete _ a2 =>
    -- Check same allocation
    -- Corresponds to: impl_mem.ml:1915-1935
    match p1.prov, p2.prov with
    | .some id1, .some id2 =>
      if id1 != id2 then throw .ptrComparison
      pure (a1, a2)
    | _, _ => throw .ptrComparison
  | _, _ => throw .ptrComparison

/-! ## MemoryOps Instance

This provides the concrete implementation of the MemoryOps typeclass.
Corresponds to: Memory module implementation in impl_mem.ml
Audited: 2026-01-01
-/

instance : MemoryOps ConcreteMemM where
  getTypeEnv := read

  -- Corresponds to: allocate_object in impl_mem.ml:1288
  -- Cerberus computes size from sizeof(ty), not from parameter
  allocateObject name align ty requestedAddr init := do
    let env ← read
    let sz := sizeof env ty
    let al := align.val.toNat
    allocateImpl name sz (some ty) al .writable init

  allocateRegion name size align := do
    let sz := size.val.toNat
    let al := align.val.toNat
    allocateImpl name sz none al .writable none

  load := loadImpl
  store := storeImpl
  kill := killImpl

  eqPtrval := eqPtrvalImpl
  nePtrval p1 p2 := do let r ← eqPtrvalImpl p1 p2; pure (!r)
  -- Pointer relational comparisons with strict validation
  -- Corresponds to: impl_mem.ml:1886-1951
  ltPtrval p1 p2 := do
    let (a1, a2) ← validateRelationalPtrs p1 p2
    pure (a1 < a2)
  gtPtrval p1 p2 := do
    let (a1, a2) ← validateRelationalPtrs p1 p2
    pure (a1 > a2)
  lePtrval p1 p2 := do
    let (a1, a2) ← validateRelationalPtrs p1 p2
    pure (a1 <= a2)
  gePtrval p1 p2 := do
    let (a1, a2) ← validateRelationalPtrs p1 p2
    pure (a1 >= a2)

  diffPtrval := diffPtrvalImpl
  effArrayShiftPtrval := effArrayShiftPtrvalImpl
  effMemberShiftPtrval := effMemberShiftPtrvalImpl

  ptrfromint := ptrfromintImpl
  intfromptr := intfromPtrImpl
  validForDeref := validForDerefImpl
  isWellAligned := isWellAlignedImpl

  memcpy := memcpyImpl
  memcmp := memcmpImpl
  realloc := reallocImpl

/-! ## Running Concrete Memory Operations

Utilities for executing concrete memory operations.
-/

/-- Run a concrete memory operation.
    Audited: 2026-01-01
    Deviations: None -/
def runConcreteMemM (env : TypeEnv) (m : ConcreteMemM α) (st : MemState := {}) : Except MemError (α × MemState) :=
  (m.run env).run st

/-- Run a concrete memory operation, discarding final state.
    Audited: 2026-01-01
    Deviations: None -/
def runConcreteMemM' (env : TypeEnv) (m : ConcreteMemM α) (st : MemState := {}) : Except MemError α :=
  (·.1) <$> runConcreteMemM env m st

end CerbLean.Memory
