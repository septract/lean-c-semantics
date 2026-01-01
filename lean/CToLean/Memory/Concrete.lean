/-
  Concrete memory model implementation
  Based on cerberus/memory/concrete/impl_mem.ml

  This implements allocation-ID provenance tracking for:
  - Bounds checking
  - Dangling pointer detection (use-after-free)
  - Read-only memory protection
-/

import CToLean.Memory.Interface

namespace CToLean.Memory

open CToLean.Core

/-! ## Concrete Memory Monad

We use a reader for the type environment and state for memory.
-/

/-- Concrete memory monad with type environment -/
abbrev ConcreteMemM := ReaderT TypeEnv MemM

/-! ## Helper Functions -/

/-- Get allocation ID from provenance -/
def toAllocId (prov : Provenance) : Nat :=
  match prov with
  | .some id => id
  | _ => 0

/-- Check if an allocation is still live (not freed) -/
def isAllocLive (st : MemState) (allocId : Nat) : Bool :=
  st.allocations.contains allocId && !st.deadAllocations.contains allocId

/-- Get allocation for a pointer, checking validity -/
def getAllocation (ptr : PointerValue) : ConcreteMemM Allocation := do
  let st ← get
  match ptr.prov with
  | .none =>
    throw (.access .noProvPtr (some 0))
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

/-- Check if address is within allocation bounds -/
def isInBounds (alloc : Allocation) (addr : Nat) (size : Nat) : Bool :=
  addr >= alloc.base && addr + size <= alloc.base + alloc.size

/-- Get address from pointer value -/
def ptrAddr (ptr : PointerValue) : Option Nat :=
  match ptr.base with
  | .concrete _ addr => some addr
  | _ => none

/-! ## Byte-Level Operations -/

/-- Write bytes to memory -/
def writeBytes (addr : Nat) (bytes : List (Option UInt8)) (prov : Provenance) : ConcreteMemM Unit := do
  let st ← get
  let newBytemap := bytes.foldl (init := (addr, st.bytemap)) fun (a, bm) mbyte =>
    let byte : AbsByte := { prov := prov, copyOffset := none, value := mbyte }
    (a + 1, bm.insert a byte)
  set { st with bytemap := newBytemap.2 }

/-- Read bytes from memory -/
def readBytes (addr : Nat) (size : Nat) : ConcreteMemM (List AbsByte) := do
  let st ← get
  let bytes := List.range size |>.map fun i =>
    st.bytemap[addr + i]?.getD { prov := .none, copyOffset := none, value := none }
  pure bytes

/-! ## Value Serialization

Convert memory values to/from byte sequences.
-/

/-- Convert integer to little-endian bytes -/
def intToBytes (val : Int) (size : Nat) : List (Option UInt8) :=
  List.range size |>.map fun i =>
    let shifted := val >>> (i * 8)
    some (shifted.toNat.toUInt8)

/-- Convert little-endian bytes to integer -/
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
          | none => 0
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

/-- Get the provenance from bytes (for pointer loads) -/
def bytesProvenance (bytes : List AbsByte) : Provenance :=
  -- Take provenance from first byte with provenance
  bytes.findSome? (fun b =>
    match b.prov with
    | .none => none
    | p => some p
  ) |>.getD .none

/-- Serialize memory value to bytes -/
partial def memValueToBytes (env : TypeEnv) (val : MemValue) : List (Option UInt8) :=
  match val with
  | .unspecified ty =>
    List.replicate (sizeof env ty) none
  | .integer ity iv =>
    intToBytes iv.val (integerTypeSize ity)
  | .floating fty fv =>
    -- Simplified: just use size, actual float encoding would be more complex
    let size := floatingTypeSize fty
    match fv with
    | .finite f =>
      -- This is a simplification - proper IEEE 754 encoding needed
      intToBytes f.toUInt64.toNat size
    | _ => List.replicate size none
  | .pointer _ pv =>
    match pv.base with
    | .null _ => intToBytes 0 targetPtrSize
    | .function _ => intToBytes 0 targetPtrSize  -- Function pointers need special handling
    | .concrete _ addr => intToBytes addr targetPtrSize
  | .array elems =>
    elems.flatMap (memValueToBytes env)
  | .struct_ tag members =>
    -- Layout struct with padding
    match env.lookupTag tag with
    | some (.struct_ fields _) =>
      let offsets := structOffsets env fields
      let size := structSize env fields
      let bytes := List.replicate size (some 0 : Option UInt8)
      members.foldl (init := bytes) fun acc (name, _, mval) =>
        match offsets.find? (·.1 == name) with
        | some (_, offset) =>
          let memberBytes := memValueToBytes env mval
          -- Insert member bytes at offset
          acc.mapIdx fun i b =>
            if i >= offset && i < offset + memberBytes.length then
              memberBytes[i - offset]!
            else b
        | none => acc
    | _ => []
  | .union_ tag _ mval =>
    -- Union uses size of largest member
    let memberBytes := memValueToBytes env mval
    match env.lookupTag tag with
    | some (.union_ fields) =>
      let size := unionSize env fields
      memberBytes ++ List.replicate (size - memberBytes.length) (some 0)
    | _ => memberBytes

/-! ## Core Memory Operations -/

/-- Allocate memory and return pointer -/
def allocateImpl (name : String) (size : Nat) (ty : Option Ctype)
    (align : Nat) (readonly : ReadonlyStatus) (init : Option MemValue) : ConcreteMemM PointerValue := do
  let env ← read
  let st ← get

  -- Compute aligned base address
  let alignedAddr := alignUp st.nextAddr align

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
    nextAddr := alignedAddr + size
    allocations := st.allocations.insert allocId alloc
  }

  -- Initialize memory if provided
  match init with
  | some val =>
    let bytes := memValueToBytes env val
    writeBytes alignedAddr bytes (.some allocId)
  | none =>
    -- Zero-initialize
    writeBytes alignedAddr (List.replicate size (some 0)) (.some allocId)

  pure (concretePtrval allocId alignedAddr)

/-- Reconstruct memory value from bytes -/
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
    -- Simplified float reconstruction
    match bytesToInt bytes false with
    | some n =>
      pure (.floating fty (.finite (Float.ofScientific n.toNat true 0)))
    | none =>
      pure (.unspecified ty)

  | .pointer quals pointeeTy =>
    let pointeeCty : Ctype := { ty := pointeeTy }
    match bytesToInt bytes false with
    | some 0 =>
      pure (.pointer (Ctype.pointer quals pointeeCty) (nullPtrval pointeeCty))
    | some addr =>
      let prov := bytesProvenance bytes
      pure (.pointer (Ctype.pointer quals pointeeCty) { prov := prov, base := .concrete none addr.toNat })
    | none =>
      pure (.unspecified ty)

  | .array elemTy (some n) =>
    let elemCty : Ctype := { ty := elemTy }
    let elemSize := sizeof env elemCty
    let elems ← List.range n |>.mapM fun i => do
      let start := i * elemSize
      let elemBytes := bytes.drop start |>.take elemSize
      reconstructValue env elemCty elemBytes
    pure (.array elems)

  | _ =>
    pure (.unspecified ty)

/-- Load value from memory -/
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

    -- Read bytes and reconstruct value
    let bytes ← readBytes addr size
    let footprint : Footprint := { kind := .read, base := addr, size := size }

    -- Reconstruct value from bytes
    let val ← reconstructValue env ty bytes
    pure (footprint, val)

/-- Store value to memory -/
def storeImpl (ty : Ctype) (isLocking : Bool) (ptr : PointerValue) (val : MemValue) : ConcreteMemM Footprint := do
  let env ← read

  match ptr.base with
  | .null _ => throw (.access .nullPtr none)
  | .function _ => throw (.access .functionPtr none)
  | .concrete _ addr =>
    let alloc ← getAllocation ptr

    -- Check read-only
    match alloc.isReadonly with
    | .readonly _ => throw .readonlyWrite
    | .writable => pure ()

    let size := sizeof env ty
    -- Check bounds
    if !isInBounds alloc addr size then
      throw (.access .outOfBoundPtr (some addr))

    -- Serialize and write
    let bytes := memValueToBytes env val
    let prov := match ptr.prov with
      | .some id => .some id
      | _ => .none
    writeBytes addr bytes prov

    -- Lock if requested
    if isLocking then
      let st ← get
      let allocId := toAllocId ptr.prov
      match st.allocations[allocId]? with
      | some allocRec =>
        set { st with allocations := st.allocations.insert allocId { allocRec with isReadonly := .readonly .ordinary } }
      | none => pure ()

    pure { kind := .write, base := addr, size := size }

/-- Deallocate memory -/
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
        -- Mark as dead
        set { st with deadAllocations := allocId :: st.deadAllocations }
      | none =>
        throw (.free .nonMatching)
    | _ =>
      throw (.free .nonMatching)

/-! ## Pointer Operations -/

/-- Pointer equality -/
def eqPtrvalImpl (p1 p2 : PointerValue) : ConcreteMemM Bool := do
  match p1.base, p2.base with
  | .null _, .null _ => pure true
  | .null _, _ => pure false
  | _, .null _ => pure false
  | .function s1, .function s2 => pure (s1 == s2)
  | .function _, _ => pure false
  | _, .function _ => pure false
  | .concrete _ a1, .concrete _ a2 =>
    -- For concrete pointers, compare addresses
    -- Note: comparing pointers from different allocations is implementation-defined
    pure (a1 == a2)

/-- Pointer difference -/
def diffPtrvalImpl (elemTy : Ctype) (p1 p2 : PointerValue) : ConcreteMemM IntegerValue := do
  let env ← read
  match p1.base, p2.base with
  | .concrete _ a1, .concrete _ a2 =>
    -- Check same allocation for defined behavior
    match p1.prov, p2.prov with
    | .some id1, .some id2 =>
      if id1 != id2 then
        -- Different allocations - implementation defined
        pure (integerIval 0)
      else
        let elemSize := sizeof env elemTy
        if elemSize == 0 then
          throw (.typeError "pointer difference with zero-sized element")
        let diff := (a1 : Int) - (a2 : Int)
        pure (integerIval (diff / elemSize))
    | _, _ =>
      throw (.access .noProvPtr none)
  | _, _ =>
    throw (.typeError "pointer difference requires concrete pointers")

/-- Effectful array shift with bounds checking -/
def effArrayShiftPtrvalImpl (ptr : PointerValue) (elemTy : Ctype) (n : IntegerValue) : ConcreteMemM PointerValue := do
  let env ← read
  match ptr.base with
  | .null ty => pure { ptr with base := .null ty }
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
    | _ =>
      -- No provenance, just do the arithmetic
      pure { ptr with base := .concrete unionMem newAddr.toNat }

/-- Effectful member shift -/
def effMemberShiftPtrvalImpl (ptr : PointerValue) (tag : Sym) (member : Identifier) : ConcreteMemM PointerValue := do
  let env ← read
  pure (memberShiftPtrval env ptr tag member)

/-- Integer to pointer conversion -/
def ptrfromintImpl (_fromTy : IntegerType) (toTy : Ctype) (n : IntegerValue) : ConcreteMemM PointerValue := do
  if n.val == 0 then
    pure (nullPtrval toTy)
  else
    -- Implementation-defined: create pointer with provenance from integer
    pure { prov := n.prov, base := .concrete none n.val.toNat }

/-- Pointer to integer conversion -/
def intfromPtrImpl (_fromTy : Ctype) (_toTy : IntegerType) (ptr : PointerValue) : ConcreteMemM IntegerValue := do
  match ptr.base with
  | .null _ => pure (integerIvalWithProv 0 ptr.prov)
  | .function _ => throw (.typeError "cannot convert function pointer to integer")
  | .concrete _ addr => pure (integerIvalWithProv addr ptr.prov)

/-- Check pointer validity for dereference -/
def validForDerefImpl (ty : Ctype) (ptr : PointerValue) : ConcreteMemM Bool := do
  let env ← read
  match ptr.base with
  | .null _ => pure false
  | .function _ => pure false
  | .concrete _ addr =>
    match ptr.prov with
    | .some allocId =>
      let st ← get
      if st.deadAllocations.contains allocId then
        pure false
      else
        match st.allocations[allocId]? with
        | some alloc =>
          let size := sizeof env ty
          pure (isInBounds alloc addr size)
        | none => pure false
    | _ => pure false

/-- Check pointer alignment -/
def isWellAlignedImpl (ty : Ctype) (ptr : PointerValue) : ConcreteMemM Bool := do
  let env ← read
  match ptr.base with
  | .null _ => pure true  -- NULL is well-aligned
  | .function _ => pure true
  | .concrete _ addr =>
    let align := alignof env ty
    pure (addr % align == 0)

/-! ## Memory Functions -/

/-- Memory copy -/
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

    -- Write to destination
    let byteVals := bytes.map (·.value)
    let prov := match dst.prov with
      | .some id => .some id
      | _ => .none
    writeBytes dstAddr byteVals prov

    pure dst
  | _, _ =>
    throw (.memcpy .nonObject)

/-- Memory compare -/
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

/-- Realloc -/
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

    -- Copy old data
    let copySize := min oldSize size
    let bytes ← readBytes oldAddr copySize
    match newPtr.base with
    | .concrete _ newAddr =>
      let byteVals := bytes.map (·.value)
      writeBytes newAddr byteVals newPtr.prov
    | _ => pure ()

    -- Free old allocation
    killImpl true ptr

    pure newPtr

  | .function _ =>
    throw (.free .nonMatching)

/-! ## MemoryOps Instance -/

instance : MemoryOps ConcreteMemM where
  getTypeEnv := read

  allocateObject name size ty align init := do
    let env ← read
    let sz := size.val.toNat
    let al := align.getD (alignof env ty)
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
  ltPtrval p1 p2 := do
    match p1.base, p2.base with
    | .concrete _ a1, .concrete _ a2 => pure (a1 < a2)
    | _, _ => pure false
  gtPtrval p1 p2 := do
    match p1.base, p2.base with
    | .concrete _ a1, .concrete _ a2 => pure (a1 > a2)
    | _, _ => pure false
  lePtrval p1 p2 := do
    match p1.base, p2.base with
    | .concrete _ a1, .concrete _ a2 => pure (a1 <= a2)
    | _, _ => pure false
  gePtrval p1 p2 := do
    match p1.base, p2.base with
    | .concrete _ a1, .concrete _ a2 => pure (a1 >= a2)
    | _, _ => pure false

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

/-! ## Running Concrete Memory Operations -/

/-- Run a concrete memory operation -/
def runConcreteMemM (env : TypeEnv) (m : ConcreteMemM α) (st : MemState := {}) : Except MemError (α × MemState) :=
  (m.run env).run st

/-- Run a concrete memory operation, discarding final state -/
def runConcreteMemM' (env : TypeEnv) (m : ConcreteMemM α) (st : MemState := {}) : Except MemError α :=
  (·.1) <$> runConcreteMemM env m st

end CToLean.Memory
