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

Issue 5 later supplies a bus-evidence type `BEvidence` packaging the unified
per-step bus/chip data and

    stepWithBus : CState × CState × BEvidence → Prop.

The **memory bridge** (`StepInterface.MemoryBridge`) is

    Rep(Ĉ₁,S₁) ∧ stepCommitted(Ĉ₁,Ĉ₂)
      ⟹ ∃ S₂. Rep(Ĉ₂,S₂) ∧ V.step(S₁,S₂).

The existential construction of `S₂` is what lets Issue 1 establish `Rep` for
successive states by induction. Assuming `Rep(Ĉ₂,S₂)` as a premise would prove
only a conditional one-step refinement and would not reconstruct a trace.

The **bus bridge** (`StepInterface.BusBridge stepWithBus`) is

    stepWithBus(Ĉ₁,Ĉ₂,b) ⟹ stepCommitted(Ĉ₁,Ĉ₂).

Issue 5 may first prove an extract-or-collision statement and obtain this
implication as the collision-resistant corollary.

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
The public binary committed relation hides the `MemStep` witness existentially:

    committedStep(Ŝ₁,Ŝ₂) := ∃ w : MemStep VC, CommittedMemory.step(Ŝ₁,Ŝ₂,w).

This is deliberately the **memory-only component**. It does not yet connect
`addr` and `v` to specific registers, decode the concrete ISA, or model the
bus. Those semantic conjuncts belong to Issues 3 and 5.
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

After hiding the `MemStep` witness, the existential statement has exactly the
frozen memory-bridge shape:

    CommitInv(Ŝ₁,S₁) ∧ committedStep(Ŝ₁,Ŝ₂)
      ⟹ ∃ S₂. CommitInv(Ŝ₂,S₂) ∧ ∃ w : MemStep VC. FullMemory.step(S₁,S₂,w).

For the two-step full-memory `ZkVM`, `V.step` is the final existential above,
so `memoryStepInterface` sets `represents := CommitInv` and
`stepCommitted := committedStep`; `memoryBridge` proves
`StepInterface.MemoryBridge` without assuming `CommitInv(Ŝ₂,S₂)`.

Induction over `k < T` yields both:

    ∀ k ≤ T, CommitInv(Ŝₖ,Sₖ),
    ∀ k < T, FullMemory.step(Sₖ,Sₖ₊₁,wₖ).

This is the perfect, memory-only counterpart of the paper's
memory-extractability reduction and its `CommitInv` relation. It assumes
the binding properties directly; explicit bad-event reductions and advantage
accounting remain assigned to Issues 2 and 6.
*Lean:* public `step_reconstruct`, `reconstructTrace`, and
`trace_mem_extract` (the root-update and single-step lemmas are private),
`TwoStep.System.memoryStepInterface`, `TwoStep.System.memoryBridge`.

### 1.4 Full-memory CTE for the two-step toy

The toy has a committed instantiation whose step is `committedStep`,

and a full-memory instantiation with step `∃ w, FullMemory.step(S₁,S₂,w)`. The latter's
verifier commits the full boundary memories and calls the same final verifier.
Assuming non-empty segments, knowledge soundness of the segment and final
argument systems, and all three memory-commitment properties, the committed
trace extractor followed by reconstruction is a `CTE` extractor for the
full-memory instance.

The terminal full state is not assumed during reconstruction: `CommitInv` for
the extracted committed terminal state and commitment injectivity identify it
with the full terminal state in the statement.
*Lean:* `TwoStep.System.toZkVMFullMemory`, `traceValid_full`, `cte_fullMemory`.

`VMs/TwoStep/TwoStepSanity.lean` permanently checks non-vacuity: a one-segment, one-step
system over `MemorySanity.exactVC` has identity knowledge extractors, an
accepting final proof, and satisfies `cte_fullMemory`'s complete hypothesis bundle.
`VMs/MemorySanity.lean` also instantiates the append-bit attack at the bridge level:
the initial full-memory state represents the first committed-memory state and
the committed-memory write verifies, but the second commitment has no
full-memory representative. Thus dropping update binding would
make the frozen bridge conclusion false, not merely harder to prove.

This is not yet the full VanillaVM theorem: `memFreePred` is abstract, and the
concrete ISA, bus, recursion, and explicit quantitative reductions are later
issues in `docs/PLAN.md`.
