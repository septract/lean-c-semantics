/-
  Memory model interface and implementations

  This module provides:
  - Memory types (MemState, Allocation, Footprint, errors)
  - Type layout computation (sizeof, alignof, offsetsof)
  - Abstract memory interface (MemoryOps type class)
  - Concrete memory model with allocation-ID provenance
-/

import CToLean.Memory.Types
import CToLean.Memory.Layout
import CToLean.Memory.Interface
import CToLean.Memory.Concrete
