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
*Lean:* `trivialAS`, `knowledgeSound_trivialAS` (in `CryptoSanity.lean`).

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

The existential construction of `S₂` is what lets Issue 1 preserve the
commitment invariant inductively. Assuming `Rep(Ĉ₂,S₂)` as a premise would prove
only a conditional one-step refinement and would not reconstruct a trace.

The **bus bridge** (`StepInterface.BusBridge stepWithBus`) is

    stepWithBus(Ĉ₁,Ĉ₂,b) ⟹ stepCommitted(Ĉ₁,Ĉ₂).

Issue 5 may first prove an extract-or-collision statement and obtain this
implication as the collision-resistant corollary.

These are Lean-only coordination propositions whose concrete instances target
`prop:memory-extractability` and `lem:segment`; they are not additional paper
claims.

**Non-vacuity.** `ZkvmSanity.lean` gives an accepting one-step Boolean toggle
zkVM whose committed/plain representation is equality and which satisfies CTE
and both bridge propositions. This is only a consistency floor, not a model of
the Vanilla ISA or its cryptography.

---

## Provisional (not frozen — commitment layer)

Stated here for completeness but **expected to change** (I4); see the note in
`docs/CORRESPONDENCE.md`. `UpdateBinding` supersedes the earlier punctured-binding
notion, which was insufficient (Issue 1).

**Vector commitment** (ch02, `Com_mem`). `VC = (Value, Index, Com, OpenProof, commit,
openProof, verify)`; a vector is a total map `Index → Value`; `verify C i v π` checks
position `i` of the committed vector holds `v`.
*Lean:* `VectorCommitment`.

**Completeness** (ch02). An honest opening always verifies:
`verify (commit m) i (m i) (openProof m i)`. Provides the honest opening that the
binding notions compare an adversarial opening against.
*Lean:* `Complete`.

**Position binding** (`def:binding`, ch02). No commitment admits two accepted openings
of different values at the same position:

    verify C i v π  ∧  verify C i v' π'  ⟹  v = v'.

*Lean:* `PositionBinding`.

**Update binding** (`def:binding`, ch02; Issue 1, replaces punctured binding). One
opening `π` that opens an honest root `commit m` at `addr` (necessarily to `m addr`)
and also opens some `C'` at `addr` to `x` forces `C'` to be the honest commitment of `m`
point-updated at `addr` to `x`:

    verify (commit m) addr (m addr) π  ∧  verify C' addr x π
      ∧  m' addr = x  ∧  (∀ j ≠ addr. m' j = m j)   ⟹   C' = commit m'.

Unlike position binding (which only bounds what a root *opens to*), this pins a
*reconstructed* post-write root into the image of `commit` — the property full-memory
reconstruction needs. It is strictly stronger than position binding: `appendBitVC`
(`MemorySanity`) satisfies position binding but not this.
*Lean:* `UpdateBinding`; separation witness `MemorySanity.appendBitVC_not_updateBinding`.

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
*Lean:* `concatTrace`, `chain_flatten` (in `Trace.lean`).

---

## 1. Committed memory → full memory (Issue 1)

Paper: `prop:memory-extractability` (ch05 §5.2); `φ̂_read`/`φ̂_write` and
`φ_read`/`φ_write` (ch03); `Com_mem` (ch02). Realizes the memory side of the Issue-0
step-interface contract (§0.3): `Memory.step_mem_extract`/`trace_mem_extract` are the
concrete deliverables the `StepInterface.MemoryBridge` proposition anticipated.

### 1.1 States and the commitment invariant

**Full state** over the commitment's native types: `S = (pc, regs, mem)` with
`mem : Index → Value`. **Committed state** `Ŝ = (pc, regs, mem̂)` with `mem̂ ∈ Com`.
*Lean:* `FullVMState VC`, `CommittedVMState VC`.

**Commitment invariant** `CommitInv Ŝ S`: `Ŝ.pc = S.pc`, `Ŝ.regs = S.regs`, and
`Ŝ.mem = commit(S.mem)`. Ties a committed state to the full state it commits.
*Lean:* `CommitInv`.

**Commitment injectivity.** Completeness + position binding make `commit` injective on
memories: `commit m₁ = commit m₂ ⟹ m₁ = m₂`.
*Lean:* `mem_eq_of_commit_eq`.

### 1.2 The classified step predicates

A step carries an explicit descriptor `w ∈ MemStep = read(addr,v,π) | write(addr,v,vOld,π)
| other`, exposing the openings memory extraction consumes. `φ̂_step`/`φ_step` are the
committed/full step predicates, each a case split on `w`; the register/pc part is an
opaque `memFreePred` shared by both.

**Committed read** `φ̂_read`: register part holds, `Ŝ₁.mem = Ŝ₂.mem`, and `π` opens
`Ŝ₁.mem` at `addr` to `v`. **Committed write** `φ̂_write`: register part holds, `π`
opens the pre-root at `addr` to `vOld` and the post-root at `addr` to `v`.
*Lean:* `readC`, `writeC`, `stepC`.

**Full read** `φ_read`: register part holds, `S₁.mem addr = v`, `S₂.mem = S₁.mem`.
**Full write** `φ_write`: register part holds, `S₂.mem addr = v`, and `S₂.mem = S₁.mem`
off `addr`.
*Lean:* `readF`, `writeF`, `stepF`.

### 1.3 Memory extractability (`prop:memory-extractability`)

**One step.** Given completeness, position binding, update binding, `CommitInv` on both
endpoints, and a committed step `φ̂_step(Ŝ₁,Ŝ₂,w)`, the full step `φ_step(S₁,S₂,w)`
holds. (Reads/others: position binding + injectivity. Writes: update binding pins the
post-root, injectivity identifies the post-memory.)
*Lean:* `step_mem_extract`.

**Invariant across a write.** From `CommitInv` on the pre-state and a committed write,
the reconstructed post-state (memory point-updated at `addr`) satisfies `CommitInv` —
update binding is essential here.
*Lean:* `commit_update`, `commitInv_write`.

**Whole trace.** Reconstruct a full trace from `S₀` and per-step descriptors; the
invariant holds at every state and every committed step becomes a full step. Descriptors
for an existential `∃w. φ̂_step` step are chosen classically.
*Lean:* `trace_mem_extract` (with `stepReconstruct`, `reconstructTrace`, `chooseDescr`).

### 1.4 Two-step VM over full memory

The two-step toy is instantiated twice: `toZkVM` over committed states (binary step
`stepRel Ŝ₁ Ŝ₂ := ∃w. φ̂_step(Ŝ₁,Ŝ₂,w)`), and `toZkVMFull` over full states (step
`∃w. φ_step`), whose verifier commits the full boundary states and defers to the
committed final SNARK.

**Committed CTE.** Under knowledge soundness of both SNARKs and `0 < Nseg`,
`toZkVM` is CTE (two-layer extraction + `chain_flatten`).
*Lean:* `TwoStep.System.cte`.

**Full-memory CTE** (the Issue-1 headline). Additionally assuming completeness, position
binding, and update binding of `Com_mem`, `toZkVMFull` is CTE: the extractor commits the
boundaries, runs the committed extractor, and folds `trace_mem_extract`. The terminal
state matches because the invariant at the last state plus injectivity pin its memory.
*Lean:* `TwoStep.System.cte_full` (bridge lemma `traceValid_full`).

**Step-interface instance.** The two-step VM instantiates the Issue-0 contract:
`toZkVMFull` as the plain `ZkVM`, `CommitInv` as the representation, `stepRel` as the
committed step. `MemoryBridge` is discharged by `step_mem_extract` ∘ `commitInv_step`.
*Lean:* `TwoStep.System.stepInterface`, `TwoStep.System.memoryBridge`.
