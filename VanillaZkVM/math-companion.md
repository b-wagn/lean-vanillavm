# Math companion

The pen-and-paper statements matching the Lean, kept in lockstep with the code
(CONVENTIONS.md §7). For each frozen-kernel definition and headline theorem this
states it in ordinary mathematical notation with its paper citation, so a reviewer can
compare **paper ↔ companion ↔ Lean** without reading proof internals. The companion,
`docs/CORRESPONDENCE.md`, and the Lean must agree; a discrepancy is a review blocker.

Every later issue appends its layer to this file. This first section is **Issue 0**: the
frozen kernel (`docs/INVARIANTS.md` I4).

Paper: the canonical `zkvm-whitepaper/sampleVM/ch01-execution-model.tex` through
`ch05-security.tex` at `a0f5e0b63395a2fddce3f949c4de1df9264a174b`; see
`docs/PAPER_REVISION.md`. Anchors below cite chapters/labels.

---

## 0. Frozen kernel (Issue 0)

### 0.1 Relations and argument systems

**Relation.** A relation is a triple `R = (Stmt, Wit, rel)` with `rel ⊆ Stmt × Wit`.
We write `(x ; w) ∈ R` for `rel x w`.
*Lean:* `Relation`. *Paper:* the statement/witness relations throughout ch03–ch05.

**Argument system** (ch05, `Π = (Prove, Verify)`). For a relation `R`, an argument
system is `AS = (Proof, verify)` with `verify : Stmt × Proof → {0,1}`, phrased as a
predicate `verify x π`. Only the verifier is modeled — the prover plays no role in
soundness, so it is omitted.
*Lean:* `ArgumentSystem R`.

**Extractor.** `E : Stmt × Proof → Wit`, straight-line (no rewinding, no access to the
adversary's code).
*Lean:* `Extractor R AS`.

**Knowledge soundness** (`def:extractable`, ch05). `AS` is knowledge-sound iff there
exists a single universal straight-line extractor `E` such that

    ∀ x, π.   verify x π = 1  ⟹  (x ; E(x, π)) ∈ R.

This is the **perfect / probability-free** form (INVARIANTS.md I8): the bad event
"verifies but extraction fails" simply never occurs.
*Lean:* `KnowledgeSound AS`.

**Non-vacuity (consistency floor, I6).** The *trivial* argument system for `R` — a proof
*is* a witness, and `verify x w := ((x ; w) ∈ R)` — is knowledge-sound via the identity
extractor. This shows `KnowledgeSound` is not `False`; it is **not** a claim that a
succinct SNARK meets it.
*Lean:* `trivialAS`, `knowledgeSound_trivialAS` (in `Preliminaries/ArgumentSystemSanity.lean`).

### 0.2 The abstract zkVM and correct-trace extractability

**VM state** (ch01, `S = (pc, regs, mem)`). Parameterized by a memory representation
`Mem`: `S = (pc ∈ Word, regs : ℕ → Word, mem ∈ Mem)`. The full state uses
`Mem = (Addr → Byte)`; the committed state `Ŝ` (ch02) uses `Mem = Com` (a memory
commitment).
*Lean:* `VMStateWith Mem`, `VMState`, `CommittedVMState VC`.

**Abstract zkVM.** `V = (State, step, T, Stmt, initial, terminal, Proof, verify)` where
`step ⊆ State × State`, `T ∈ ℕ` is fixed within this zkVM instance,
`initial, terminal : Stmt → State` are the boundary projections, and
`verify : Stmt × Proof → {0,1}` is the final verifier. The Lean model has no
security parameter; the paper's family may choose a polynomially bounded `T`
as a system parameter for each security parameter.
*Lean:* `ZkVM`.

The fixed `T` follows the pinned correction to `def:cte`: program code and `T`
are system parameters, while the adversary selects boundary states and a proof.

**Trace validity.** A candidate trace `tr : ℕ → State` is valid for statement `x` iff

    tr(0) = initial(x)  ∧  tr(T) = terminal(x)  ∧  ∀ i < T. step(tr(i), tr(i+1)).

*Lean:* `ZkVM.TraceValid`.

**Correct-execution relation `R*`** (ch03). Statements are boundary claims `x`,
witnesses are traces `tr`, and `(x ; tr) ∈ R*` iff `tr` is valid for `x`.
*Lean:* `ZkVM.Rstar`. The final argument system viewed over `R*` is `ASstar`.

This is the abstract trace-validity skeleton only. It neither requires `Stmt` to
contain full-memory boundary states nor constrains `verify` to commit them as in
the concrete verification algorithm immediately following `eq:relation-star`.
The full Vanilla VM instance must supply that boundary/verifier package in
Issue 7; hence the current correspondence row is faithful but incomplete.

**Correct-trace extractability `CTE`** (`def:cte`, ch05). `V` is CTE iff there is a
trace-extractor `E : Stmt × Proof → (ℕ → State)` such that

    ∀ x, π.   verify x π = 1  ⟹  E(x, π) is a valid T-step trace for x.

*Lean:* `ZkVM.CTE`.

**Keystone: CTE ⇔ KS** (`rem:cte-ks`, ch05). For every abstract zkVM `V`,

    CTE(V)  ⟺  KnowledgeSound(ASstar(V)).

Both sides are "∃ extractor, ∀ accepting `(x, π)`, output is a valid trace"; the proof
is structural repackaging (bare function ↔ `Extractor` record). This is the equivalence
concrete systems use: instantiate `ZkVM`, prove `KnowledgeSound ASstar`, conclude `CTE`.
*Lean:* `ZkVM.cte_iff_knowledgeSound`.

---

## 0.3 Step-interface contract

The plain execution predicate is not duplicated:

    stepPlain(S₁,S₂) := V.step(S₁,S₂).

A `StepInterface V` supplies a committed-state type `CState`, a representation
predicate `Rep ⊆ CState × V.State`, and

    stepCommitted : CState × CState → Prop.

Issue 5 supplies `StepAux`, which contains one segment's bus and one
transition's `MemStep`, and

    stepWithBus : CState × CState × StepAux → Prop.

The **memory bridge** (`StepInterface.MemoryBridge`) is

    Rep(Ĉ₁,S₁) ∧ stepCommitted(Ĉ₁,Ĉ₂)
      ⟹ ∃ S₂. Rep(Ĉ₂,S₂) ∧ V.step(S₁,S₂).

The existential construction of `S₂` is what lets Issue 1 establish `Rep` for
successive states by induction. Assuming `Rep(Ĉ₂,S₂)` as a premise would prove
only a conditional one-step refinement and would not reconstruct a trace.

The **bus bridge** (`StepInterface.BusBridge stepWithBus`) is

    stepWithBus(Ĉ₁,Ĉ₂,b) ⟹ stepCommitted(Ĉ₁,Ĉ₂).

The segment theorem first uses collision resistance of `Com_bus` to put the
step and chip checks on one bus. Once `stepWithBus` holds, the concrete
two-layer instance proves this implication directly from the ISA definitions;
the bridge itself needs no additional cryptographic assumption.

These are Lean-only coordination propositions whose concrete instances target
`prop:memory-extractability` and `lem:segment`; they are not additional paper
claims.

**Non-vacuity.** `VMs/StepSanity.lean` gives an accepting one-step Boolean toggle
zkVM whose committed/plain representation is equality and which satisfies CTE
and both bridge propositions. This is only a consistency floor, not a model of
the Vanilla ISA or its cryptography.

---

## Provisional (not frozen — commitment layer)

Stated here for completeness but **expected to change** (I4); see the note in
`docs/CORRESPONDENCE.md`.

**Vector commitment** (ch02, `Com_mem`). `VC = (Value, Index, Com, OpenProof, commit,
openProof, verify)`; a vector is a total map `Index → Value`; `verify C i v π` checks
position `i` of the committed vector holds `v`.
*Lean:* `VectorCommitment`.

**Completeness** (instruction preceding `def:binding`, ch05). Every honest opening
verifies:

    verify (commit m) i (m i) (openProof m i).

*Lean:* `VectorCommitment.Complete`.

**Position binding** (`def:binding`, ch05). No commitment admits two accepted openings
of different values at the same position:

    verify C i v π  ∧  verify C i v' π'  ⟹  v = v'.

*Lean:* `VectorCommitment.PositionBinding`.

**Update binding** (`def:binding`, ch05). One opening `π` that verifies
`m(addr)` against `commit m` and verifies `x` against a candidate commitment
`C'` at the same address forces `C'` to equal the commitment of the point
update:

    m'(addr) = x
    ∧ (∀ j ≠ addr, m'(j) = m(j))
    ∧ verify (commit m) addr (m(addr)) π
    ∧ verify C' addr x π
      ⟹ C' = commit m'.

Position binding and update binding are **independent requirements** in the
paper. The append-bit model in `MemorySanity` satisfies completeness, position
binding, and agreement of accepted openings away from the updated address, but
fails update binding. It therefore demonstrates that those properties do not
guarantee that a verifier-accepted candidate equals `commit m` for some memory
`m`; it does not establish an implication in the other direction.
*Lean:* `VectorCommitment.UpdateBinding`; countermodel
`MemorySanity.appendBitVC_not_updateBinding`.

**Hash commitment / collision resistance** (`Com_bus`, `Adv^cr`, ch02). `H = (Domain,
Digest, hash)`; collision resistance (perfect) is injectivity of `hash`.
*Lean:* `HashCommitment`, `CollisionResistant`.

---

## Trace concatenation (shared helper)

Not part of the frozen kernel, but used by every multi-segment layer. `concatTrace`
glues `m` length-`Nseg` sub-chains with matching boundary states `d(0), …, d(m)` into
one length-`m·Nseg` trace; `chain_flatten` proves that if each segment is a valid
`Nseg`-step `step`-chain from `d(i)` to `d(i+1)`, the glued trace is a valid
`m·Nseg`-step chain from `d(0)` to `d(m)`.
*Lean:* `concatTrace`, `chain_flatten` (in `Preliminaries/Trace.lean`).

---

## 1. Committed memory → full memory (Issue 1)

Paper: `prop:memory-extractability` and `rem:mem-inheritance` (ch05);
`eq:op-mem-comm-read`/`eq:op-mem-comm-write` (ch03);
`eq:mem-op-read`/`eq:mem-op-write` (ch01).

### 1.1 State relation and memory step predicates

For a vector commitment `VC`, a full state has
`mem : VC.Index → VC.Value`, while a committed state has `mem̂ : VC.Com`.
The relation between them is

    CommitInv(Ŝ, S)
      := Ŝ.pc = S.pc ∧ Ŝ.regs = S.regs ∧ Ŝ.mem = commit(S.mem).

Thus `Ŝ` and `S` describe the same VM state: they have identical control and
register data, while `Ŝ` stores a commitment where `S` stores the complete
memory map. Reconstruction proves this relation at every trace position.

*Lean:* `FullVMState`, `CommitInv`.

Each transition carries a memory-step witness `w : MemStep VC`:

    w ::= read(addr, v, π)
        | write(addr, v_new, v_old, π)
        | other.

For an abstract non-memory predicate `φ'` on the two PCs and register files:

    CommittedMemory.read(Ŝ₁, Ŝ₂, addr, v, π)
      := φ'(Ŝ₁, Ŝ₂)
         ∧ Ŝ₁.mem = Ŝ₂.mem
         ∧ verify Ŝ₁.mem addr v π,

    CommittedMemory.write(Ŝ₁, Ŝ₂, addr, v_new, v_old, π)
      := φ'(Ŝ₁, Ŝ₂)
         ∧ verify Ŝ₁.mem addr v_old π
         ∧ verify Ŝ₂.mem addr v_new π,

    FullMemory.read(S₁, S₂, addr, v)
      := φ'(S₁, S₂) ∧ S₁.mem(addr) = v ∧ S₂.mem = S₁.mem,

    FullMemory.write(S₁, S₂, addr, v_new)
      := φ'(S₁, S₂)
         ∧ S₂.mem(addr) = v_new
         ∧ ∀ j ≠ addr, S₂.mem(j) = S₁.mem(j).

`CommittedMemory.step` and `FullMemory.step` select these equations by `w`; `.other` preserves memory.
When a caller needs only a relation between the two committed states, it says
that some accepted `MemStep` exists:

    committedStep(Ŝ₁,Ŝ₂) := ∃ w : MemStep VC, CommittedMemory.step(Ŝ₁,Ŝ₂,w).

This is deliberately the **memory-only component**. By itself it does not connect
`addr` and `v` to specific registers, decode the concrete ISA, or model the
bus. `ISA.System.committedOperation` below adds the program/register requirements;
Issue 5 adds the bus condition.
*Lean:* `MemStep`, `CommittedMemory.read`, `CommittedMemory.write`, `FullMemory.read`, `FullMemory.write`, `CommittedMemory.step`, `FullMemory.step`,
`committedStep`.

### 1.2 One-step memory extraction

Completeness plus position binding imply injectivity of commitments produced by
`commit`:

    commit(m₁) = commit(m₂) ⟹ m₁ = m₂.

Given `VC.Complete`, `VC.PositionBinding`, `VC.UpdateBinding`, `CommitInv` for
both endpoint states, and a committed-memory step,

    CommitInv(Ŝ₁,S₁) ∧ CommitInv(Ŝ₂,S₂) ∧ CommittedMemory.step(Ŝ₁,Ŝ₂,w)
      ⟹ FullMemory.step(S₁,S₂,w).

Reads compare the supplied opening with the opening produced by `openProof` and
use commitment injectivity to preserve memory. Writes use position binding to
identify the old and new leaves, update binding to identify the second
committed-memory state's commitment with the point-updated memory, and
injectivity to identify the supplied second full memory.
*Lean:* `mem_eq_of_commit_eq`, `step_mem_extract`.

### 1.3 Inductive reconstruction

Starting with `CommitInv(Ŝ₀,S₀)`, reconstruct the next full state by keeping
memory for reads/other steps and point-updating it for writes. Update binding
establishes `CommitInv` for the next state in the write case:

    CommitInv(Ŝₖ,Sₖ) ∧ CommittedMemory.step(Ŝₖ,Ŝₖ₊₁,wₖ)
      ⟹ CommitInv(Ŝₖ₊₁,Sₖ₊₁)
          ∧ FullMemory.step(Sₖ,Sₖ₊₁,wₖ).

The public theorem `step_reconstruct_exact` states this implication for the
same supplied `wₖ`. Keeping that value is necessary when a later layer must
also prove that its constructor, address, and value agree with the instruction
selected by the program.

If the caller only needs to know that some `MemStep` exists, the theorem has
the frozen memory-bridge shape:

    CommitInv(Ŝ₁,S₁) ∧ committedStep(Ŝ₁,Ŝ₂)
      ⟹ ∃ S₂. CommitInv(Ŝ₂,S₂) ∧ ∃ w : MemStep VC. FullMemory.step(S₁,S₂,w).

The memory-only theorem above remains useful independently of an ISA. In the
two-step `ZkVM`, the committed relation is strengthened to require that the
same `MemStep` agrees with `code[pc]`; `memoryBridge` uses the exact theorem and
the ISA correspondence lemma to conclude the single `stepPlain` predicate used
as `ZkVM.step`.
It still constructs `S₂` rather than assuming `CommitInv(Ŝ₂,S₂)`.

Induction over `k < T` yields both:

    ∀ k ≤ T, CommitInv(Ŝₖ,Sₖ),
    ∀ k < T, FullMemory.step(Sₖ,Sₖ₊₁,wₖ).

This is the perfect, memory-only version of the paper's
memory-extractability reduction and its `CommitInv` relation. It assumes
the binding properties directly; explicit bad-event reductions and advantage
accounting remain assigned to Issues 6 and 10.
*Lean:* public `step_reconstruct_exact`, `step_reconstruct`, `reconstructTrace`, and
`trace_mem_extract` (the root-update and single-step lemmas are private),
`TwoStep.System.memoryStepInterface`, `TwoStep.System.memoryBridge`.

### 1.4 Full-memory CTE for the two-step toy

The toy has a single zkVM instantiation, with

    V.step := ISA.System.stepPlain.

Its verifier commits the full boundary memories and calls the final verifier.
The committed layer appears only as an intermediate: a trace of committed
states whose steps satisfy `ISA.System.committedStep`, extracted from the two
SNARK layers, with no zkVM of its own. Each explicit segment witness is checked
by `ISA.System.committedOperation`, so the chosen memory action and its
address/value agree with the fixed program.
Assuming non-empty segments, knowledge soundness of the segment and final
argument systems, and all three memory-commitment properties, the committed-trace
extractor followed by reconstruction is a `CTE` extractor for the zkVM.

The terminal full state is not assumed during reconstruction: `CommitInv` for
the extracted committed terminal state and commitment injectivity identify it
with the full terminal state in the statement.
*Lean:* `TwoStep.System.toZkVM`, `CommittedTraceValid`,
`committedTrace_extract`, `traceValid_full`, `cte`.

`VMs/TwoStep/TwoStepSanity.lean` permanently checks non-vacuity: a one-segment, one-step
system over `MemorySanity.exactVC` has identity knowledge extractors, an
accepting final proof, and satisfies `cte`'s complete hypothesis bundle.
`VMs/MemorySanity.lean` also instantiates the append-bit attack at the bridge level:
the initial full-memory state represents the first committed-memory state and
the committed-memory write verifies, but the second commitment has no
full-memory representative. Thus dropping update binding would
make the frozen bridge conclusion false, not merely harder to prove.

This is not yet the full VanillaVM theorem. The representative ISA remains
abstract inside each operation's PC/register predicate, and the bus, recursion,
and explicit quantitative reductions remain separate layers in `docs/PLAN.md`.

---

## 3. Representative ISA operations (Issue 3)

Paper: `eq:phiop`, `eq:phi-read-decomp`, and `eq:phi-write-decomp` (ch01),
and the operation taxonomy and `eq:step` (ch03). The formalization deliberately
uses the five operation classes required by Issue 3 rather than the paper's
complete RV32IM/precompile taxonomy.

### 3.1 Fixed program and memory-free predicates

Let

    OperationClass := {read, write, arith, hash, bin}.

An ISA system fixes the operation class at each program counter:

    code : Word → OperationClass

and converts register words to the memory's address and value types:

    indexOfWord : Word → Index,
    valueOfWord : Word → Value.

For the paper's ordinary `VMState`, `Index = Addr` and `Value = Byte`; both
maps are the identity because all three are currently represented by `ℕ`.
The parameters also let the same ISA predicate act directly on
`FullVMState VC` for a general commitment scheme. Both names still use the same
Lean structure with `pc`, `regs`, and `mem` fields.

Here `code(pc)` records only the class of the instruction at `pc`; it is not an
opcode decoder. A family `φ'_op` of predicates over the two program counters
and register files supplies the remaining requirements. Because these
predicates receive `pc`, they may still describe the exact fixed instruction at
that location. This issue deliberately leaves their internal arithmetic and
hash computations unspecified.
For reads and writes, this is also where the address-bound check belongs: it
depends on the address register, not on memory contents.

*Lean:* `ISA.OperationClass`, `ISA.System`, and `ISA.System.memFreePred`.

### 3.2 Full operation predicates

For full states `S₁=(pc₁,regs₁,mem₁)` and
`S₂=(pc₂,regs₂,mem₂)`, every operation predicate includes the fetch equation
`code(pc₁)=op`. The memory operations are

    φ_read(S₁,S₂)
      := code(pc₁)=read
         ∧ φ'_read(pc₁,regs₁,pc₂,regs₂)
         ∧ mem₁(indexOfWord(regs₁(0)))=valueOfWord(regs₂(1))
         ∧ mem₂=mem₁,

    φ_write(S₁,S₂)
      := code(pc₁)=write
         ∧ φ'_write(pc₁,regs₁,pc₂,regs₂)
         ∧ mem₂(indexOfWord(regs₁(0)))=valueOfWord(regs₁(1))
         ∧ ∀ j≠indexOfWord(regs₁(0)), mem₂(j)=mem₁(j).

The write equation is the pointwise form of
`mem₂ = mem₁[indexOfWord(regs₁(0)) ↦ valueOfWord(regs₁(1))]`. For
`op ∈ {arith,hash,bin}`,

    φ_op(S₁,S₂)
      := code(pc₁)=op
         ∧ φ'_op(pc₁,regs₁,pc₂,regs₂)
         ∧ mem₂=mem₁.

The read and write cases reuse `FullMemory.read` and `FullMemory.write`; they
are not second copies of the Issue 1 memory equations.

The pinned paper's `eq:phi-read-decomp` omits the explicit `mem₂=mem₁`
condition, although `eq:mem-op-read` and ch03 say that a read does not change
memory. The Lean definition makes that intended behavior explicit. The
whitepaper's current `proof` branch makes the same correction in commit
`aa33ed3`; updating the normative pin remains a human review decision.

*Lean:* `ISA.System.operation`.

### 3.3 Plain step predicate

The single plain-state step used as `ZkVM.step` is the five-way disjunction

    stepPlain(S₁,S₂)
      := φ_read(S₁,S₂) ∨ φ_write(S₁,S₂) ∨ φ_arith(S₁,S₂)
         ∨ φ_hash(S₁,S₂) ∨ φ_bin(S₁,S₂).

Because each `φ_op` contains `code(pc₁)=op` and `code` is a function, this is
equivalent to the single selected predicate

    stepPlain(S₁,S₂) ↔ φ_code(pc₁)(S₁,S₂).

The disjunction therefore does not let a witness choose an instruction
independently of the fixed program.

Consequently, whenever `φ_op(S₁,S₂)` holds and `op ≠ write`, memory is
unchanged. In particular, a read cannot silently alter memory.

*Lean:* `ISA.System.stepPlain`, `ISA.System.stepPlain_iff_operation_at_pc`,
`ISA.System.operation_preserves_memory_unless_write`.

### 3.4 Committed operations and the two-step VM

For committed states and an explicit `MemStep w`, define

    committedOperation(Ŝ₁,Ŝ₂,w)
      := CommittedMemory.step(φ'_{code(Ŝ₁.pc)},Ŝ₁,Ŝ₂,w)
         ∧ the following condition for the constructor of w,

where the second condition requires:

- a `read(addr,v,π)` only when `code(Ŝ₁.pc)=read`, with
  `addr=indexOfWord(Ŝ₁.regs(0))` and
  `v=valueOfWord(Ŝ₂.regs(1))`;
- a `write(addr,v,vOld,π)` only when `code(Ŝ₁.pc)=write`, with
  `addr=indexOfWord(Ŝ₁.regs(0))` and
  `v=valueOfWord(Ŝ₁.regs(1))`;
- `.other` only when the selected class is `arith`, `hash`, or `bin`.

When a caller only needs a relation between the two committed states, it says
that some accepted `MemStep` exists:

    committedStep(Ŝ₁,Ŝ₂) := ∃ w, committedOperation(Ŝ₁,Ŝ₂,w).

If both committed states represent full states, memory reconstruction proves
`FullMemory.step` for the same `w`, and `committedOperation` proves that its
fields agree with the selected instruction. Therefore

    committedOperation(Ŝ₁,Ŝ₂,w)
      ∧ CommitInv(Ŝ₁,S₁) ∧ CommitInv(Ŝ₂,S₂)
      ∧ FullMemory.step(S₁,S₂,w)
      ⟹ stepPlain(S₁,S₂).

This is why `TwoStep.System.toZkVM.step` can be `stepPlain`: the explicit
memory-opening witness remains inside the committed extraction relation rather
than becoming the public program semantics.

*Lean:* `ISA.System.selectedMemFreePred`,
`ISA.System.committedOperation`, `ISA.System.committedStep`,
`ISA.System.committedOperation_stepPlain`, and `TwoStep.System.toZkVM`.

`ISASanity.lean` gives private accepted examples for a read and a write whose
output memory differs from its input. It also rejects a step when the program
contains a different operation class and rejects a write with the wrong output
memory. Finally, it instantiates a private `ZkVM` whose `step` field is
`ISA.System.stepPlain`. `TwoStepSanity.lean` additionally checks the public
two-step construction using the same predicate. The next section adds the bus
evidence required by hash/precompile operations; this section does not verify
concrete RV32IM opcode implementations.

---

## 4. Segment buses and one complete execution (Issue 5)

Paper: the bus layout in ch02; `eq:step-expanded`, `eq:step-bus2`, the four
inner relations and `R_1` in ch03--ch04; `lem:segment`; and Steps 4--5 of
`thm:main` in ch05. As in the rest of the current development, collision
resistance and knowledge soundness use their perfect, probability-free forms.

### 4.1 Bus entries and checks postponed to the bus

Write `ctrl(S) := (S.pc,S.regs)` for the part of a state that a hash or range
check reads. One segment bus is a record containing three lists:

    B := (B_keccak, B_poseidon, B_range),

where `B_keccak` and `B_poseidon` contain pairs
`(ctrl(S₁),ctrl(S₂))`, and `B_range` contains values `ctrl(S₁)`. Memory is not
duplicated in these entries because every hash and range-checked transition
separately requires the memory commitment to remain unchanged.

The paper calls the bus a collection without fixing its data representation.
Lean uses lists, so order and duplicates are part of the value hashed by
`Com_bus`; the predicates themselves check entries through list membership.
Every deferred operation must add its required entry, and every stored entry
must pass its chip check, but the relation does not require each call to occur
exactly once. Additional valid entries and duplicates are therefore allowed,
as in the discussion following `eq:step-expanded`.

The Issue 3 ISA has one representative class `hash`, so the fixed program also
supplies

    hashChipAt : Word → {keccak, poseidon}

to say which chip checks the hash instruction at a given program counter. Its
representative `bin` class stands for operations with a range check. The ISA
description supplies predicates `φ'_bin,inline` and `φ_range` satisfying

    φ'_bin(pc₁,regs₁,pc₂,regs₂)
      ↔ φ'_bin,inline(pc₁,regs₁,pc₂,regs₂) ∧ φ_range(pc₁,regs₁).

This is the five-class form of the paper's decomposition of arithmetic with a
range check.

For a committed transition and its explicit memory witness `w`, define the
segment-trace predicate `stepBus(Ŝ₁,Ŝ₂,w,B)` by the operation selected by
`code(Ŝ₁.pc)`:

- `read`, `write`, and `arith` are checked completely by
  `committedOperation(Ŝ₁,Ŝ₂,w)`;
- `hash` requires `w=other`, unchanged committed memory, and the call
  `(ctrl(Ŝ₁),ctrl(Ŝ₂))` in the Keccak or Poseidon list selected by
  `hashChipAt(Ŝ₁.pc)`;
- `bin` requires `w=other`, `φ'_bin,inline`, unchanged committed memory, and
  `ctrl(Ŝ₁) ∈ B_range`.

The three chip predicates check every entry in their respective lists:

    keccakChip(B)
      := ∀ call ∈ B_keccak,
           code(call.input.pc)=hash
           ∧ hashChipAt(call.input.pc)=keccak
           ∧ φ'_hash(call.input,call.output),

    poseidonChip(B)
      := ∀ call ∈ B_poseidon,
           code(call.input.pc)=hash
           ∧ hashChipAt(call.input.pc)=poseidon
           ∧ φ'_hash(call.input,call.output),

    rangeChip(B)
      := ∀ state ∈ B_range, φ_range(state).

The first two predicates therefore cannot exchange Keccak and Poseidon entries,
even though Issue 3 gives both operations the same representative `hash`
class.

The complete transition, including the checks performed through the bus, is

    stepWithBus(Ŝ₁,Ŝ₂,(B,w))
      := stepBus(Ŝ₁,Ŝ₂,w,B)
         ∧ keccakChip(B) ∧ poseidonChip(B) ∧ rangeChip(B).

Membership supplies the particular chip fact required by a hash or `bin`
transition. Consequently,

    stepWithBus(Ŝ₁,Ŝ₂,(B,w)) ⟹ committedStep(Ŝ₁,Ŝ₂).

This is proved first for `committedOperation` using the exact memory witness
`w` recovered from the segment. A concrete VM then uses that same `w` to prove
the `StepInterface.BusBridge` statement that a suitable witness exists; the
non-recursive demonstration does so in
`VMs/TwoStep/WithBus.lean`. The conclusion is therefore the existing Issue 3
committed relation, not a second VM execution semantics.

*Lean:* `Bus.BusState`, `Bus.HashCall`, `Bus.SegmentBus`, `Bus.StepAux`,
`Bus.System.stepBus`, `Bus.System.keccakChip`, `Bus.System.poseidonChip`,
`Bus.System.rangeChip`, `Bus.System.stepWithBus`, and
`Bus.System.stepWithBus_committedOperation`. The concrete interface
theorem is `Bus.TwoStepSystem.busBridge`.

### 4.2 Inner proofs and why their recovered buses agree

Let `Com_bus(B) := busHash(B)`. The inner segment-trace relation is

    R_(0,step)((Ŝin,Ŝout,C); (B,Ŝ,w)) :=
      Ŝ(0)=Ŝin
      ∧ Ŝ(Nseg)=Ŝout
      ∧ ∀ j<Nseg, stepBus(Ŝ(j),Ŝ(j+1),w(j),B)
      ∧ C=Com_bus(B).

For `chip ∈ {keccak,poseidon,range}`, the corresponding inner relation is

    R_(0,chip)(C;B) := chipPredicate(B) ∧ C=Com_bus(B).

The segment relation `R_1` has public input `(Ŝin,Ŝout)`. Its witness contains
one digest `C` and four inner proofs, and it requires all four verifiers to
accept under that same `C`.

Suppose the five argument systems are knowledge-sound: `R_1` and the four
inner relations. Extraction first obtains the four inner proofs from the `R_1`
witness and then extracts buses

    B_step, B_keccak, B_poseidon, B_range.

Each bus hashes to `C`. Perfect collision resistance is injectivity of
`Com_bus`, hence

    B_step = B_keccak = B_poseidon = B_range.

After rewriting the three chip checks using these equalities, choose
`B := B_step`. Every recovered transition then satisfies `stepWithBus` using
the same bus for that segment. This is `lem:segment` in the current perfect
model.

The equality is only among the four buses extracted for this one segment. If a
second segment uses digest `C'` and bus `B'`, neither the relation nor the proof
requires `C=C'` or `B=B'`.

*Lean:* `Bus.System.RInnerStep`, `RInnerKeccak`, `RInnerPoseidon`,
`RInnerRange`, `RSegment`, `Assumptions`, `segmentValid`, and
`segment_extract`.

### 4.3 Connecting separately extracted segments in the non-recursive VM

The definitions and theorem in §§4.1--4.2 form the reusable segment-bus layer;
they do not mention `TwoStep` or choose how segment proofs are combined. Issue 5
also requires a bus-backed `ZkVM` and whole-execution demonstration, which are
provided separately by `Bus.TwoStepSystem`. This separation lets the final
recursive VanillaVM reuse `segment_extract` as its leaf result without taking a
dependency on the non-recursive demonstration.

Let the final extractor recover boundary states `d(0),...,d(m)` and one
accepted segment proof for each `i<m`. Apply the segment extractor separately:

    segment_i = (B_i, Ŝ_i, w_i),

with

    Ŝ_i(0)=d(i),
    Ŝ_i(Nseg)=d(i+1),
    ∀ j<Nseg,
      stepWithBus(Ŝ_i(j),Ŝ_i(j+1),(B_i,w_i(j))).

The recovered execution keeps the function `i ↦ segment_i`; in particular it
keeps the separate values `B_i`. Apply `BusBridge` to each transition and then
the shared theorem for joining traces:

    trace := concatTrace(Nseg,d,(i,j) ↦ Ŝ_i(j),m),

    chain_flatten ⟹
      trace(0)=d(0)
      ∧ trace(m·Nseg)=d(m)
      ∧ ∀ k<m·Nseg, committedStep(trace(k),trace(k+1)).

The buses themselves are not concatenated, and buses from different segments
do not need to be equal. The boundary equalities alone join the state traces.
Finally, the existing memory reconstruction theorem turns this committed trace
into a full-memory trace satisfying `ISA.System.stepPlain`, proving CTE for the
two-step VM whose segment proofs use buses.
The convert/combine/embed recursion layers are still deferred to Issue 4 and
the final assembly to Issue 7.

*Lean:* `Bus.TwoStepSystem`, `Bus.TwoStepSystem.Execution`,
`Execution.trace`, `Execution.Valid`, `execution_extract`, `toZkVM`, and `cte`.
`VMs/TwoStep/WithBusSanity.lean` supplies a private two-segment model whose segment
buses are deliberately unequal, while all assumptions and the CTE theorem
remain satisfiable. It separately exercises the Poseidon and range-check
transition branches and rejects buses missing the required hash or range
entry.
