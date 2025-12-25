(Investigation by Gemini 3 Deep Research - 2025-12-24)

# **Architecting the Semantic Bridge: A Comprehensive Analysis of Translating Cerberus Core to Lean 4 Idioms**

## **1\. Introduction: The Semantics of Migration**

The translation of legacy systems programming languages into formal verification environments represents one of the most formidable challenges in modern software correctness. The C programming language, despite its ubiquity in critical infrastructure, suffers from a notoriously ambiguous specification where behavior is often defined not by the ISO standard, but by the de facto consensus of compiler implementations and hardware architectures.1 Consequently, any attempt to migrate C code into a rigorous theorem proving environment like **Lean 4** must first grapple with the "semantic gap"—the chasm between the untyped, permissive, and often undefined nature of the C abstract machine, and the strongly typed, constructive, and logically consistent Calculus of Constructions that underpins Lean.3  
The user’s proposed methodology—exporting C code into **Cerberus Core** and subsequently translating this intermediate representation (IR) into Lean—is a scientifically sound and logically robust approach. Cerberus acts as a semantic elaborator, transforming the implicit complexities of C source text (such as syntactic sugar, type inference, and control flow desugaring) into **Core**, a formally defined lambda calculus extended with primitives for memory interactions.1 By targeting Core rather than raw C abstract syntax trees (ASTs), the translation tool bypasses the immense difficulty of parsing and disambiguating C, allowing the translator to focus purely on the semantic mapping between the two execution models.  
However, the user’s specific query regarding "layers" or "idioms" beyond the standard Std.Do notation reveals a critical architectural decision point. While Std.Do provides a syntactic veneer of imperative programming within Lean—supporting mutable variables, loops, and early returns—it remains a shallow embedding of imperative syntax into a functional logic.5 It does not inherently model the complex memory object semantics, pointer provenance, or undefined behavior states that Cerberus Core explicates. Therefore, relying solely on Std.Do risks producing a translation that is syntactically isomorphic to the C source but semantically vacuous regarding the safety properties one wishes to verify.  
This report provides an exhaustive analysis of the architectural layers required to bridge Cerberus Core and Lean 4\. It argues that the "layer" the user seeks is not a single library, but a composite **Monadic Stack** that simulates the C memory model (Computational Layer), coupled with a **Separation Logic Framework** (Verification Layer) to reason about it. We explore three distinct integration strategies:

1. **The Computational Layer:** Utilizing Lean’s **State Transformer (ST)** monad and **ByteArray** primitives to construct a high-performance, executable simulation of the C heap that respects Lean’s "functional but in-place" optimization paradigm.6  
2. **The Verification Layer:** Adopting the **Iris-Lean** framework to map Cerberus Core’s memory operations into **HeapLang**\-style separation logic propositions, enabling rigorous proofs of correctness regarding pointer provenance and aliasing.8  
3. **The Interoperability Layer:** Leveraging the **Alloy** and **CTypes** libraries to provide a standardized, ABI-compatible type system (c\_int, size\_t) that serves as the vocabulary for the translated code, ensuring seamless interoperability with foreign function interfaces (FFI).10

This document details the theoretical underpinnings, practical implementation strategies, and comparative advantages of each approach, ultimately proposing a hybrid architecture that satisfies the requirement for Lean idioms while maintaining fidelity to the Cerberus semantics.

## ---

**2\. The Source Semantics: Deconstructing Cerberus Core**

To design an effective translation layer, one must first possess a rigorous understanding of the input. Cerberus Core is not merely a simplified version of C; it is a disambiguated explication of the C abstract machine. Understanding its specific features is prerequisite to selecting the appropriate Lean idioms.

### **2.1 The Nature of Cerberus Core and the "De Facto" Standard**

The central thesis of the Cerberus project is that the ISO C standard is insufficient for precise formalization due to its reliance on prose and its failure to fully specify the memory model.1 Compiler implementers (GCC, Clang) and systems programmers (Linux Kernel developers) often operate on a "de facto" standard that is more concrete than ISO C but more abstract than assembly. Cerberus captures this by providing an executable semantics that is parametric over different memory models.2  
The translation pipeline begins with **Cabs** (C Abstract Syntax) and **Ail** (Annotated Intermediate Language), which handle parsing and type checking. The result is elaborated into **Core**, which explicates all implicit C behaviors. For a Lean translator, the critical aspects of Core are:

* **Explicit Evaluation Order:** C expressions often have unspecified evaluation orders. Core explicitly sequences these operations. A Lean translation must respect this sequencing, typically via the bind operator (\>\>=) in a monad.2  
* **The Memory Object Model:** Unlike LLVM IR, which views memory as a flat array of bytes, Cerberus Core views memory as a collection of discrete *allocations*. Each allocation has a unique ID (provenance). A pointer is not just an integer address; it is a tuple of (provenance\_id, offset). This distinction is vital because it makes pointer arithmetic valid only within the bounds of a single allocation object.12  
* **Undefined Behavior (UB) as a State:** In Cerberus Core, operations that trigger UB (like reading uninitialized memory or a data race) do not crash the interpreter immediately; they transition the abstract machine into an explicit "undefined" state. The Lean translation must model this state, likely using an error monad (ExceptT or Option) to distinguish between "valid execution" and "semantics breakdown".13

### **2.2 The Challenge of Pointer Provenance**

One of the most complex features of Cerberus is its handling of **Pointer Provenance**.1 Provenance is the metadata associated with a pointer that authorizes it to access a specific region of memory.

* *Scenario:* Consider two memory allocations, A and B, which happen to be adjacent in physical memory. In C, if you increment a pointer to the end of A, it might physically point to the start of B. However, the standard says dereferencing this pointer is UB because it lacks the *provenance* to access B.  
* *Lean Implication:* If the Lean translation models memory simply as a ByteArray (flat memory), it loses this provenance information, potentially validating unsafe C code. If it models memory as a Map ID (Array Byte), it preserves provenance but complicates pointer arithmetic (casting an integer to a pointer becomes difficult). The "layer" chosen must make a definitive choice on this trade-off.

### **2.3 The Core Primitives**

Cerberus Core reduces C to a lambda calculus with specific primitives. The translator must provide a Lean implementation (or axiom) for each:

* create(n, val): Allocates n bytes initialized to val.  
* kill(ptr): Deallocates the object at ptr.  
* load(ptr, type): Reads a value of type from ptr.  
* store(ptr, val): Writes val to ptr.  
* run\_function(name, args): Handles function invocation.

The following table summarizes the semantic gap between Cerberus Core concepts and standard Lean concepts, highlighting where the "translation layer" is necessary.

| Cerberus Core Concept | Standard Lean Concept | The Semantic Gap |
| :---- | :---- | :---- |
| **Mutable Heap** | Immutable Values | Lean variables are immutable; let x := 5 binds a value, not a memory cell. |
| **Pointer (int\*)** | Inductive Types | A pointer in C allows arithmetic; a reference in Lean (ST.Ref) is opaque. |
| **Global State** | Local Scope | C functions affect global state; Lean functions are pure and stateless. |
| **Control Flow** | Structured Recursion | C has goto; Lean requires well-founded recursion (termination proofs). |
| **Undefined Behavior** | Total Functions | Lean functions must return a value for all inputs; C functions may not. |

## ---

**3\. The Lean 4 Runtime and Idioms: Beyond Std.Do**

The user specifically enquired about Std.Do and potential alternatives. To answer this, we must analyze the mechanics of Std.Do and why it is often a "false friend" for systems C translation.

### **3.1 The Mechanics of Std.Do**

In Lean 4, do notation is a syntactic macro that facilitates monadic programming. It is not a distinct imperative language; it is a transformation layer that converts imperative-looking code into functional chains of bind (\>\>=) calls.5

* **let mut:** This syntax desugars into a state-passing mechanism or, in the case of the ST or IO monads, into operations on mutable references.  
* **for loops:** These are desugared into applications of ForIn typeclass methods.  
* **return:** This is handled via the MonadExcept class, throwing a "return" exception that is caught at the function boundary.

While Std.Do is powerful for writing *new* code in Lean, it assumes the **Lean Abstract Machine**. It assumes that variables are scoped lexically, that memory is managed automatically (via Reference Counting), and that types are safe.

### **3.2 The "False Friend" of Std.Do for C Translation**

Using Std.Do directly to translate C code leads to the **Shallow Embedding** problem.5

* *Example:* In C, int x \= 5; int \*p \= \&x; \*p \= 6; return x; returns 6\.  
* *Translation:* In Std.Do, let mut x := 5 creates a local variable. There is no way to take the address of x (\&x) because x is not a memory object; it is a value in a register or stack slot managed by the Lean compiler. You cannot create a pointer p that aliases x.  
* *Consequence:* To simulate C, every variable that *might* have its address taken must be allocated on a simulated heap, not as a let mut local variable. Std.Do's variable management is orthogonal to C's addressable memory requirement.

### **3.3 The Functional But In-Place (FBIP) Paradigm**

Lean 4 utilizes a memory management strategy called **Functional But In-Place (FBIP)**.16 When the runtime detects that a value (like an Array) has a reference count of 1 (it is uniquely owned), operations that would conceptually create a copy (like array.push) instead modify the memory in place.

* **Relevance:** This is the key to performant C simulation. If the translation layer models the C heap as a Lean Array or ByteArray and passes it through a StateT monad, Lean's optimizer can often compile this down to code that mutates the array in place, achieving performance comparable to C.18 This validates the feasibility of a "Computational Layer" using standard Lean data structures.

## ---

**4\. Architectural Layer 1: The Computational Substrate (The ST Monad)**

If the user's goal is to produce a tool that *executes* the translated C code (i.e., a simulator or a port), the most idiomatic Lean layer is the **State Transformer (ST) Monad**. This monad provides the closest semantic equivalent to the C abstract machine's mutable state within a pure functional language.

### **4.1 The ST Monad Semantics**

The ST monad (ST σ α) is designed to encapsulate mutable state. It uses a rank-2 polymorphic type index σ (the "thread region") to ensure that mutable references (ST.Ref) created within a computation cannot escape that computation.6 This guarantee allows ST computations to be run via runST and return a pure result, making them referentially transparent despite using internal mutation.  
**Why ST is the Correct Layer:**

1. **Mutable References:** ST.Ref maps directly to the concept of a "memory cell."  
2. **Performance:** ST operations are primitives in the Lean runtime, often mapping directly to C++ pointer operations or optimized RC updates.17  
3. **Determinism:** Unlike the IO monad, ST is deterministic. This is crucial for formal verification; it proves that the C code (if it doesn't use syscalls) is a pure function from Input to Output.

### **4.2 Modeling the C Heap: ByteArray vs. Map**

A critical design decision for this layer is the backing data structure for the simulated heap.

#### **Strategy A: The ByteArray Monolith (High Performance)**

In this model, the entire C heap is represented as a single ByteArray (or a collection of them for pages) wrapped in an ST.Ref.7

* **Mechanism:** A pointer is simply a Nat (index). malloc returns an index and increments a bump pointer.  
* **Cerberus Integration:** This corresponds to a "Concrete" memory model. It is fast but discards provenance.  
* **Lean Idioms:** Uses ByteArray.get\!, ByteArray.set\!, and bitwise operations (UInt8, UInt32) from the standard library.

#### **Strategy B: The Structured Map (High Fidelity)**

In this model, the heap is ST.Ref (Std.HashMap Addr Allocation).

* **Mechanism:** Addr is a structured ID (provenance). Allocation is a ByteArray representing just that object.  
* **Cerberus Integration:** This aligns perfectly with Cerberus Core's object model. It catches out-of-bounds errors (provenance violations) at runtime.  
* **Trade-off:** Slower than the monolithic array but safer and semantically closer to Core.

### **4.3 Implementing the Core Primitives in ST**

The "Layer" the user builds would be a library of functions lifting Core operations into the ST monad.

* **Core.alloc(size) Implementation:**  
  Lean  
  \-- Conceptual Lean code  
  def coreAlloc (size : Nat) : ST σ Pointer := do  
    let heap ← heapRef.get  
    let (newPtr, newHeap) := heap.allocate size  
    heapRef.set newHeap  
    return newPtr

* **Core.store(ptr, val) Implementation:**  
  Lean  
  def coreStore (ptr : Pointer) (val : Byte) : ST σ Unit := do  
    let heap ← heapRef.get  
    \-- Check provenance if using Strategy B  
    if heap.isValid ptr then  
      heapRef.modify (fun h \=\> h.set ptr val)  
    else  
      throw (CError.UB "Invalid Write")

**Insight:** This computational layer satisfies the "Lean Idiom" requirement by using **Monad Transformers**. The actual stack would likely be StateT Heap (ExceptT UB (ST σ)). This allows the use of do notation while correctly propagating undefined behavior errors (via ExceptT) and managing memory (via StateT).21

## ---

**5\. Architectural Layer 2: The Verification Framework (Iris-Lean)**

The user’s prompt asks for a layer to "make it easier to migrate." If the intent of migration is **Formal Verification** (proving the code is correct, not just running it), the computational layer is insufficient. The most robust, cutting-edge option in the Lean ecosystem is **Iris-Lean**.

### **5.1 The Logic of Iris**

Iris is a framework for **Concurrent Separation Logic (CSL)**. Originally developed in Coq, it has been ported to Lean 4\.8 Separation logic is the "native logic" of pointers. It solves the frame problem (reasoning about what *doesn't* change) and aliasing problems inherent in C.

* **Resources (iProp):** In Iris, facts about memory are resources. l ↦ v means "I own the memory location l, and it contains v."  
* **The Frame Rule:** This rule states that if a function f operates safely on resource P, it also operates safely on P \* R (where R is any separate resource), without touching R.23 This is essential for verifying C functions in isolation.

### **5.2 Mapping Cerberus Core to Iris**

Cerberus Core is an operational semantics. Iris provides a program logic *for* an operational semantics. The standard language verified in Iris is **HeapLang** (a simple ML-like language with references).  
**The Migration Strategy:**

1. **Translate Cerberus Core $\\rightarrow$ HeapLang:** Since Core is effectively a lambda calculus with memory primitives, it maps relatively cleanly to HeapLang (which is also a lambda calculus with memory primitives).  
2. **Verify in Iris:** Use the Iris-Lean tactics (which are improving rapidly with Lean 4's metaprogramming capabilities) to prove Hoare triples {P} code {Q} about the translated code.

### **5.3 Why Iris is the "Missing Layer"**

Using Iris allows the tool to convert the implicit assumptions of the C code into explicit logical propositions.

* *C Code:* int \*p \= malloc(4); \*p \= 10;  
* *Computational Layer:* heap\[next\_free\] \= 10;  
* *Verification Layer (Iris):*  
  Lean  
  \-- Conceptual Proposition  
  {{{ True }}}  
    alloc 4  
  {{{ p, RET p; p ↦? }}}

  This layer captures the **provenance** semantics of Cerberus rigorously. A pointer is valid only if you own the l ↦ v resource associated with it. If you try to access memory you don't own (a provenance violation), the proof fails.

**Status of Iris-Lean:** The port includes MoSeL (the proof interface) and UPred (the base logic).8 While less mature than the Coq version, it is the designated future for separation logic in Lean and represents the "state of the art" idiom for this domain.

## ---

**6\. Architectural Layer 3: Interoperability and ABI (Alloy & CTypes)**

A major challenge in migrating C is preserving the Application Binary Interface (ABI) and type layout. If the Lean translation must interact with other C libraries (via FFI) or if the migration is incremental, the types used in Lean must match C's types (e.g., int is 32-bit, long is 64-bit on x86\_64). Standard Lean types (Nat, Int) are arbitrary precision and do not match C semantics.18

### **6.1 The Alloy Library**

**Alloy** is a library that embeds C code into Lean 4\.11 While typically used for writing FFI shims, it defines a set of Lean types that mirror C types precisely.

* **The Layer:** Alloy.C  
* **Components:** c\_int, c\_uint, c\_long, c\_size\_t, c\_void.  
* **Use Case:** The translation tool should target these types. Instead of translating C int to Lean Int, translate it to Alloy.C.c\_int. This ensures that overflow behaviors (if modeled) and storage sizes are semantically accurate.

### **6.2 The CTypes Library**

**CTypes** provides a dynamic FFI layer.10 It includes a Pointer type that supports arithmetic, dereferencing, and casting.

* **Idiom:** CTypes allows the user to define Struct layouts in Lean that match C layouts (padding, alignment).  
* **Integration:** If the Cerberus Core export contains complex struct definitions, generating CTypes definitions in Lean is an automated way to preserve that layout logic without manually recalculating offsets.

## ---

**7\. Synthesis: The "Cerberus-Lean" Monad Architecture**

To satisfy the user's request for "a layer... that would make it easier to migrate," we propose a synthesized architecture. This architecture combines the **Computational Layer** (for execution) with the **Verification Layer** (for correctness), utilizing standard Lean idioms.

### **7.1 The Monadic Stack (The "CL" Layer)**

We define a domain-specific monad stack, let's call it CL (Cerberus-Lean), which serves as the target for the translation.

Lean

\-- 1\. Define the Context (Read-only Global Environment)  
structure CLContext where  
  globals : HashMap String Addr  
  functions : HashMap String CLFunction

\-- 2\. Define the State (Memory Model)  
structure CLState where  
  heap : ByteArray             \-- Concrete data storage  
  provenance : HashMap Addr AllocationID \-- Shadow memory for validity checks  
  next\_alloc : Addr            \-- Bump pointer

\-- 3\. Define Errors (Undefined Behavior)  
inductive CLError where

| UB : String \-\> CLError      \-- "Use after free", "Out of bounds"  
| OOM : CLError               \-- "Out of memory"

\-- 4\. The Monad Definition  
abbrev CL (α : Type) := ReaderT CLContext (StateT CLState (ExceptT CLError IO)) α

### **7.2 Why this is Idiomatic**

* **ReaderT:** Standard idiom for passing read-only configuration (globals, function tables).25  
* **StateT:** Standard idiom for mutable state. By wrapping ByteArray, we get performance. By including provenance, we respect Cerberus semantics.21  
* **ExceptT:** Standard idiom for error handling. It forces the translation to handle UB explicitly (e.g., propagating it or halting).26  
* **IO:** allows for FFI calls and debug logging. If determinism is required, this can be swapped for ST (as CL is parametric over the base monad).

### **7.3 Integrating Control Flow**

Cerberus Core desugars C loops and gotos into a control flow graph (CFG) or mutually recursive functions.

* *Idiom:* Lean 4 supports **Partial Functions** via the partial keyword, which allows general recursion without termination proofs. For a migration tool, generating partial def functions is acceptable initially.  
* *Advanced Idiom:* For verification, one should use **Well-Founded Recursion**. The tool could generate termination hints (e.g., decreasing fuel/gas) to satisfy Lean’s termination checker.

### **7.4 Table: Comparison of Translation Layers**

The following table summarizes the three layers discussed, helping the user choose based on their specific goals (Verification vs. Execution).

| Feature | Std.Do (Baseline) | ST Monad (Computational) | Iris-Lean (Verification) | Alloy/CTypes (Interoperability) |
| :---- | :---- | :---- | :---- | :---- |
| **Primary Goal** | Writing Algorithms | Simulation / Execution | Formal Proofs | FFI / ABI Compatibility |
| **Memory Model** | Local Variables | Mutable References (Ref) | Logical Resources (↦) | C-compatible Types |
| **Pointer Arithmetic** | Impossible | Via ByteArray Indexing | Via Separation Logic | Via Pointer type |
| **Undefined Behavior** | Unhandled (Assumed Safe) | Modeled as Exceptions | Proved Impossible | Unhandled (Runtime Crash) |
| **Lean Idiom** | Macros / bind | ST / StateT | iProp / Tactics | structure / FFI |
| **Cerberus Alignment** | Low | Medium (Manual mapping) | High (Logical mapping) | High (Type mapping) |

## ---

**8\. Case Study: Implementing malloc and free**

To demonstrate the "Layer" concept concretely, we examine how the fundamental C memory operations would be implemented in the proposed CL monad, satisfying the user's request for specific libraries and idioms.

### **8.1 The Allocation (malloc)**

In Cerberus Core, alloc creates a new object with a new provenance ID.

Lean

\-- Using the CL Monad defined in Section 7.1  
def cl\_malloc (size : Nat) : CL Addr := do  
  let s ← get \-- Access current state  
  let ptr := s.next\_alloc  
    
  \-- 1\. Update Heap (Computational)  
  \-- In a real implementation, we would resize the ByteArray or use a page allocator  
  let new\_heap := s.heap.grow ptr size   
    
  \-- 2\. Update Provenance (Semantic)  
  let new\_prov := s.provenance.insert ptr (AllocationID.fresh)  
    
  \-- 3\. Update State  
  set { s with heap := new\_heap, provenance := new\_prov, next\_alloc := ptr \+ size }  
    
  return ptr

* *Idioms Used:* get, set (from MonadState), record update syntax ({ s with... }).

### **8.2 The Deallocation (free)**

free is critical because it introduces the possibility of "Use-After-Free" (UB).

Lean

def cl\_free (ptr : Addr) : CL Unit := do  
  let s ← get  
    
  \-- 1\. Check Provenance (Verification/Safety)  
  match s.provenance.find? ptr with

| some allocId \=\>   
      \-- 2\. "Kill" the object (remove provenance)  
      let new\_prov := s.provenance.erase ptr  
      set { s with provenance := new\_prov }  
      \-- Note: We might not physically zero the bytes immediately, simulating C

| none \=\>  
      \-- 3\. Trigger Undefined Behavior  
      throw (CLError.UB s\!"Double free or invalid pointer: {ptr}")

* *Idioms Used:* match, throw (from MonadExcept), String interpolation (s\!"").

## ---

**9\. Future Outlook and Related Work**

The field of C verification in Lean is active and evolving. The user should be aware of parallel efforts that inform this "Layer" strategy.

* **Verified Compilation:** The work on "Verified Compilation from Lean to C" demonstrates that mapping Lean concepts to C is feasible and performant.27 This project essentially goes the other way (Lean $\\rightarrow$ C), but the shared data structures and memory models are relevant.  
* **AI-Assisted Formalization:** Recent projects like **LeanDojo** and **LeanAide** use LLMs to translate natural language to Lean.28 While the user is translating *code*, the techniques for generating idiomatic Lean proofs from intermediate representations (like Cerberus Core) may converge with these AI approaches, particularly for generating the loop invariants required by Iris.  
* **The "CN" Project:** While currently focused on Coq, the "CN" refinement type system for C represents the gold standard for this type of work.30 A "CN-Lite" implemented in Lean 4 using standard attributes (macros) to annotate C functions with pre/post-conditions would be a highly valuable contribution to the ecosystem.

## ---

**10\. Conclusion**

The request to translate C code to Lean 4 using "Lean idioms" requires a nuanced understanding of both the source and target semantics. **Cerberus Core** provides the necessary explication of C's obscure corners. **Lean 4** provides the runtime and logical capabilities to model them.  
The "Layer" Recommendation:  
There is no single "import C\_Semantics" library in Lean 4 today that solves this instantly. However, the architectural components exist to build the perfect layer:

1. **For Semantics:** Use a **Monad Transformer Stack** (ReaderT \+ StateT \+ ExceptT) to model the C Abstract Machine. This is the standard Lean idiom for complex, stateful, fallible computations.  
2. **For Data:** Use **ByteArray** backed by **ST.Ref** for high-performance memory simulation, respecting Lean's FBIP optimizations.  
3. **For Types:** Use **Alloy** types (c\_int, pointer) to ensure ABI correctness.  
4. **For Correctness:** Target **Iris-Lean** if the goal is verification.

By exporting Cerberus Core and lifting it into this specified Monadic Stack, the user leverages the full power of Lean—its type system, its macro system (Std.Do), and its verification logic—while remaining faithful to the complex reality of the C programming language. This approach moves beyond a mere syntactic translation to a true **Semantic Embedding**.

#### **Works cited**

1. The Cerberus C semantics \- Apollo \- University of Cambridge, accessed December 24, 2025, [https://www.repository.cam.ac.uk/items/ea7fff60-301b-450f-afbc-bd82a2704989](https://www.repository.cam.ac.uk/items/ea7fff60-301b-450f-afbc-bd82a2704989)  
2. Cerberus, and the Memory Object Semantics for ISO and De Facto C \- LLVM, accessed December 24, 2025, [https://llvm.org/devmtg/2018-04/slides/Sewell-The\_Cerberus\_Memory\_Object\_Semantics.pdf](https://llvm.org/devmtg/2018-04/slides/Sewell-The_Cerberus_Memory_Object_Semantics.pdf)  
3. Learn — Lean Lang, accessed December 24, 2025, [https://lean-lang.org/learn/](https://lean-lang.org/learn/)  
4. Lean (proof assistant) \- Wikipedia, accessed December 24, 2025, [https://en.wikipedia.org/wiki/Lean\_(proof\_assistant)](https://en.wikipedia.org/wiki/Lean_\(proof_assistant\))  
5. Lean \- 'do' Unchained: Embracing Local Imperativity in a Purely Functional Language (Functional Pearl), accessed December 24, 2025, [https://lean-lang.org/papers/do.pdf](https://lean-lang.org/papers/do.pdf)  
6. 15.4. Mutable References \- Lean, accessed December 24, 2025, [https://lean-lang.org/doc/reference/latest/IO/Mutable-References/](https://lean-lang.org/doc/reference/latest/IO/Mutable-References/)  
7. LeanWasm: An Intrinsically-Typed Interpreter for WebAssembly \- Utrecht University Student Theses Repository Home, accessed December 24, 2025, [https://studenttheses.uu.nl/bitstream/handle/20.500.12932/46861/LeanWasm.pdf?sequence=1\&isAllowed=y](https://studenttheses.uu.nl/bitstream/handle/20.500.12932/46861/LeanWasm.pdf?sequence=1&isAllowed=y)  
8. leanprover-community/iris-lean: Lean 4 port of Iris, a higher ... \- GitHub, accessed December 24, 2025, [https://github.com/leanprover-community/iris-lean](https://github.com/leanprover-community/iris-lean)  
9. Eileen: A plan for Iris in Lean \- Markus de Medeiros, accessed December 24, 2025, [https://www.markusde.ca/pages/eileen.html](https://www.markusde.ca/pages/eileen.html)  
10. alexf91/lean4-ctypes: FFI for Lean 4 \- GitHub, accessed December 24, 2025, [https://github.com/alexf91/lean4-ctypes](https://github.com/alexf91/lean4-ctypes)  
11. CheckedShapes \- University of Washington, accessed December 24, 2025, [https://courses.cs.washington.edu/courses/cse503/25wi/final-reports/CheckedShapes.pdf](https://courses.cs.washington.edu/courses/cse503/25wi/final-reports/CheckedShapes.pdf)  
12. Exploring C semantics and pointer provenance \- Kent Academic Repository, accessed December 24, 2025, [https://kar.kent.ac.uk/78086/](https://kar.kent.ac.uk/78086/)  
13. Monads for the Curious Programmer: Part 2 | Bartosz Milewski's Programming Cafe, accessed December 24, 2025, [https://bartoszmilewski.com/2011/03/14/monads-for-the-curious-programmer-part-2/](https://bartoszmilewski.com/2011/03/14/monads-for-the-curious-programmer-part-2/)  
14. 14.3. Syntax \- Lean, accessed December 24, 2025, [https://lean-lang.org/doc/reference/latest/Functors\_\_\_-Monads-and--do--Notation/Syntax/](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Syntax/)  
15. What is a deep embedding vs a shallow embedding? With examples? \- Proof Assistants Stack Exchange, accessed December 24, 2025, [https://proofassistants.stackexchange.com/questions/2499/what-is-a-deep-embedding-vs-a-shallow-embedding-with-examples](https://proofassistants.stackexchange.com/questions/2499/what-is-a-deep-embedding-vs-a-shallow-embedding-with-examples)  
16. Lean 4 export Code into another languages \- Stack Overflow, accessed December 24, 2025, [https://stackoverflow.com/questions/74301506/lean-4-export-code-into-another-languages](https://stackoverflow.com/questions/74301506/lean-4-export-code-into-another-languages)  
17. Compiling Lean programs with Rocq's extraction pipeline \- Normale sup, accessed December 24, 2025, [https://www.normalesup.org/\~sdima/2025\_extraction\_report.pdf](https://www.normalesup.org/~sdima/2025_extraction_report.pdf)  
18. Special Types \- Functional Programming in Lean, accessed December 24, 2025, [https://leanprover.github.io/functional\_programming\_in\_lean/programs-proofs/special-types.html](https://leanprover.github.io/functional_programming_in_lean/programs-proofs/special-types.html)  
19. How does the ST monad work? \- Stack Overflow, accessed December 24, 2025, [https://stackoverflow.com/questions/12468622/how-does-the-st-monad-work](https://stackoverflow.com/questions/12468622/how-does-the-st-monad-work)  
20. Init.Prelude \- Lean community, accessed December 24, 2025, [https://leanprover-community.github.io/mathlib4\_docs/Init/Prelude.html](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html)  
21. Confusion about StateT, State and MonadState \- Stack Overflow, accessed December 24, 2025, [https://stackoverflow.com/questions/43438875/confusion-about-statet-state-and-monadstate](https://stackoverflow.com/questions/43438875/confusion-about-statet-state-and-monadstate)  
22. Trying to understand StateRefT, ST.Ref, STWorld \- Zulip Chat Archive, accessed December 24, 2025, [https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Trying.20to.20understand.20StateRefT.2C.20ST.2ERef.2C.20STWorld.html](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Trying.20to.20understand.20StateRefT.2C.20ST.2ERef.2C.20STWorld.html)  
23. Lecture 33: Separation Logic, accessed December 24, 2025, [https://course.ccs.neu.edu/cs2800sp23/l33.html](https://course.ccs.neu.edu/cs2800sp23/l33.html)  
24. Topic: IntellISense for Language Embeddings? \- Zulip Chat Archive, accessed December 24, 2025, [https://leanprover-community.github.io/archive/stream/270676-lean4/topic/IntellISense.20for.20Language.20Embeddings.3F.html](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/IntellISense.20for.20Language.20Embeddings.3F.html)  
25. 14.5. Varieties of Monads \- Lean, accessed December 24, 2025, [https://lean-lang.org/doc/reference/latest/Functors\_\_\_-Monads-and--do--Notation/Varieties-of-Monads/](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Varieties-of-Monads/)  
26. Monads \- Functional Programming in Lean, accessed December 24, 2025, [https://leanprover.github.io/functional\_programming\_in\_lean/monads.html](https://leanprover.github.io/functional_programming_in_lean/monads.html)  
27. (PDF) Verified Compilation from Lean to C: A Proof- Carrying Pipeline with Minimal Trust, accessed December 24, 2025, [https://www.researchgate.net/publication/397883522\_Verified\_Compilation\_from\_Lean\_to\_C\_A\_Proof-\_Carrying\_Pipeline\_with\_Minimal\_Trust](https://www.researchgate.net/publication/397883522_Verified_Compilation_from_Lean_to_C_A_Proof-_Carrying_Pipeline_with_Minimal_Trust)  
28. AI-Driven Formal Theorem Proving in the Lean Ecosystem, accessed December 24, 2025, [https://leandojo.org/](https://leandojo.org/)  
29. Topic: LeanAide translation: Natural language to Lean 4 \- Zulip Chat Archive, accessed December 24, 2025, [https://leanprover-community.github.io/archive/stream/113488-general/topic/LeanAide.20translation.3A.20Natural.20language.20to.20Lean.204.html](https://leanprover-community.github.io/archive/stream/113488-general/topic/LeanAide.20translation.3A.20Natural.20language.20to.20Lean.204.html)  
30. CN: Verifying Systems C Code with Separation-Logic Refinement Types \- ResearchGate, accessed December 24, 2025, [https://www.researchgate.net/publication/367062551\_CN\_Verifying\_Systems\_C\_Code\_with\_Separation-Logic\_Refinement\_Types](https://www.researchgate.net/publication/367062551_CN_Verifying_Systems_C_Code_with_Separation-Logic_Refinement_Types)