# Math companion

The pen-and-paper statements matching the Lean, kept in lockstep with the code
(CONVENTIONS.md §7). For each frozen-kernel definition and headline theorem this
states it in ordinary mathematical notation with its paper citation, so a reviewer can
compare **paper ↔ companion ↔ Lean** without reading proof internals. The companion,
`docs/CORRESPONDENCE.md`, and the Lean must agree; a discrepancy is a review blocker.

Every later issue appends its layer to this file. This first section is **Issue 0**: the
frozen kernel (`docs/INVARIANTS.md` I4).

Paper: `zkvm-whitepaper/sampleVM/{ch01..ch05}.tex`. Anchors below cite chapters/labels.

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
`step ⊆ State × State`, `T ∈ ℕ` is a fixed step count (independent of any security
parameter), `initial, terminal : Stmt → State` are the boundary projections, and
`verify : Stmt × Proof → {0,1}` is the final verifier.
*Lean:* `ZkVM`.

**Trace validity.** A candidate trace `tr : ℕ → State` is valid for statement `x` iff

    tr(0) = initial(x)  ∧  tr(T) = terminal(x)  ∧  ∀ i < T. step(tr(i), tr(i+1)).

*Lean:* `ZkVM.TraceValid`.

**Correct-execution relation `R*`** (ch03). Statements are boundary claims `x`,
witnesses are traces `tr`, and `(x ; tr) ∈ R*` iff `tr` is valid for `x`.
*Lean:* `ZkVM.Rstar`. The final argument system viewed over `R*` is `ASstar`.

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

## Provisional (not frozen — commitment layer)

Stated here for completeness but **expected to change** (I4); see the note in
`docs/CORRESPONDENCE.md`. `PuncturedBinding` is known insufficient and is replaced by
`UpdateBinding` in Issue 1.

**Vector commitment** (ch02, `Com_mem`). `VC = (Value, Index, Com, OpenProof, commit,
openProof, verify)`; a vector is a total map `Index → Value`; `verify C i v π` checks
position `i` of the committed vector holds `v`.
*Lean:* `VectorCommitment`.

**Position binding** (`def:binding`, ch02). No commitment admits two accepted openings
of different values at the same position:

    verify C i v π  ∧  verify C i v' π'  ⟹  v = v'.

*Lean:* `PositionBinding`.

**Punctured binding** (provisional, *insufficient* — retired in Issue 1). If one
opening at `addr` is accepted under both `C` and `C'`, they agree at every other
position.
*Lean:* `PuncturedBinding`.

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
