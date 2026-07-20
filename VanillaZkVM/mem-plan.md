# Memory Extractability — Implementation Plan

A concrete, Lean-oriented plan for adding **memory extractability** — the step that turns `cte`'s committed-state conclusion into a statement about real full-memory execution. Grounded in Proposition (Memory extractability) and Step 6 of the whitepaper's `sampleVM/ch05-security.tex`.

> **Scope constraint:** keep the existing `VectorCommitment` (Crypto.lean) — do **not** introduce a new/specialized memory-commitment structure.

> **Status (integration branch `memory-integration`).**
> - **Stages 0–2 — DONE**, implemented verbatim in [`Memory.lean`](Memory.lean): `FullVMState`, `Complete`, `CommitInv`, `mem_eq_of_commit_eq`, `MemStep`, `readC`/`writeC`/`readF`/`writeF`, `stepC`/`stepF`, and the heart `step_mem_extract`. This is the first place `PositionBinding`/`PuncturedBinding` are consumed. `#print axioms VanillaZkVM.step_mem_extract` reports only `[Quot.sound]` — no `sorry`.
> - **Stage 3.1 — DONE**, in [`Twostep.lean`](Twostep.lean): `SegWitness` carries `steps : ℕ → MemStep VC`, the `System` field is now `regPart : RegPart` (not an opaque `stepC`), and `RSeg` uses the classified `stepC sys.regPart (w.states j) (w.states (j+1)) (w.steps j)`. The `cte` theorem still goes through.
> - **Stages 3.2–3.3 — REMAINING**: the memory-reconstruction fold and the strengthened `cte` conclusion (see the rewritten Stage 3 below).
>
> **Architecture note.** This plan predates b-wagn's restructure (`Restructure: abstract zkVM and CTE`). Since then: `Model.lean` is deleted — its VM-state definitions (`Word`, `Addr`, `Byte`, `VMStateWith`, `VMState`, `CommittedVMState`, `memUpdate`) now live in [`Zkvm.lean`](Zkvm.lean). `Twostep.lean` no longer stands alone; it instantiates the abstract `ZkVM` and its theorem is `cte` (formerly `toy_cte`). Traces are `ℕ`-indexed (with `j < Nseg` side conditions), not `Fin`-indexed. `ArgumentSystem` now carries only a verifier (no `prove`). References below have been updated to match; the original Fin-indexed sketch is retained in the Stage 3 discussion for context, then translated.

## Goal

Prove the analogue of the whitepaper's Proposition: **position-binding + punctured-binding of `Com_mem` ⟹ a committed-memory step lifts to a full-memory step**, then thread it through the trace to reconstruct `mem₀ … mem_T` and conclude `φ_step (S_k, S_{k+1})` for the *real* predicate. In the perfect/probability-free style of Crypto.lean, "except with probability `Adv`" collapses to "always", so the two binding hypotheses are consumed as plain implications and the `T`-fold union bound disappears.

*(Stages 0–2 of this goal — the single-step lemma — are now proved in `Memory.lean`. What remains is the trace-level fold of Stage 3.)*

## What's missing today (the gaps to close)

*(Gaps 1–4 below have all been closed by `Memory.lean`; kept here as the design record.)*

1. **~~No link between `CommittedVMState` and `VMState`.~~** ✅ `CommitInv Ŝ S := Ŝ.pc = S.pc ∧ Ŝ.regs = S.regs ∧ Ŝ.mem = VC.commit S.mem` (Memory.lean).
2. **~~`stepC` is fully opaque.~~** ✅ The classified `stepC regPart Ŝ₁ Ŝ₂ (w : MemStep VC)` exposes the operation kind and opening witnesses (`π` for read, `(π, vOld)` for write) as concrete `MemStep` fields — not existentials. Threaded into `SegWitness.steps` (Stage 3.1).
3. **~~No commitment completeness.~~** ✅ `Complete VC` added as a standalone predicate.
4. **~~Index/value typing.~~** ✅ Full memory is `VC.Index → VC.Value`; the descriptor carries the typed `addr`/`v`/`vOld`/`π`, so every `VC.verify` is well-typed with no casts.

> **How the scope constraint is honored.** We use the commitment's native index/value types as the memory address/value types — full memory becomes `VC.Index → VC.Value` — and the memory-step descriptor carries `addr : VC.Index`, values `: VC.Value`, and the opening `: VC.OpenProof`. Every `VC.verify` call is then well-typed with **no casts** and no new structure. The old `VMState = VMStateWith (Addr → Byte)` is recovered as the special case `VC.Index := ℕ`, `VC.Value := ℕ` (since `Addr = Byte = ℕ`).

---

## Stage 0 — Model plumbing  ✅ DONE (`Memory.lean`)

Implemented in `Memory.lean`, keeping the **existing** `VectorCommitment`. (The VM-state definitions it builds on — `VMStateWith`, `CommittedVMState`, `Word` — now come from `Zkvm.lean`, since `Model.lean` was deleted in the restructure; `Memory.lean` imports `VanillaZkVM.Zkvm`.)

- **Full-memory state over the commitment's native types** (no wrapper, no casts):
  ```lean
  abbrev FullVMState (VC : VectorCommitment) : Type := VMStateWith (VC.Index → VC.Value)
  ```
  `CommittedVMState VC = VMStateWith VC.Com` is unchanged; the two states again share `pc`/`regs`
  and differ only in memory. The original `VMState = VMStateWith (Addr → Byte)` is the instance
  `VC.Index := ℕ`, `VC.Value := ℕ`.
- **Commitment completeness** — the one genuinely new crypto assumption (added as a standalone predicate rather than a `VectorCommitment` field, to avoid touching `Crypto.lean`):
  ```lean
  def Complete (VC : VectorCommitment) : Prop :=
    ∀ (m : VC.Index → VC.Value) (i : VC.Index),
      VC.verify (VC.commit m) i (m i) (VC.openProof m i)
  ```
- **Commitment invariant** linking a full state to a committed one (typechecks directly — both sides live over `VC.Index → VC.Value`):
  ```lean
  def CommitInv (Ŝ : CommittedVMState VC) (S : FullVMState VC) : Prop :=
    Ŝ.pc = S.pc ∧ Ŝ.regs = S.regs ∧ Ŝ.mem = VC.commit S.mem
  ```

## Stage 1 — Concrete committed + full-memory predicates  ✅ DONE (`Memory.lean`)

Split each op predicate into its memory-free register part and its memory equation, exactly like eqs. (phi-read-decomp)/(phi-write-decomp) and (op-mem-comm-read)/(op-mem-comm-write). Because we keep the existing commitment, the address/value handed to `VC.verify` must be typed `VC.Index`/`VC.Value` — so the descriptor carries them explicitly (which is also exactly the "explicit witness field" the paper demands). Tying `addr`/`v` back to `regs 0`/`regs 1` is a memory-free side condition inside `regPart`, deferred to the concrete step model.

- The **memory-step descriptor** as a typed sum (read/write/other distinguished at the type level, carrying the opening *and* the typed address/value):
  ```lean
  inductive MemStep (VC : VectorCommitment) where
    | read  (addr : VC.Index) (v : VC.Value) (π : VC.OpenProof)
    | write (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof)
    | other
  ```
- **Committed** read/write (`φ̂_read`, `φ̂_write`), taking the opening explicitly — every `VC.verify` is well-typed, no casts:
  ```lean
  def readC  (regPart : RegPart) (Ŝ₁ Ŝ₂) (addr) (v) (π) : Prop :=
    regPart Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧ Ŝ₁.mem = Ŝ₂.mem ∧
    VC.verify Ŝ₁.mem addr v π
  def writeC (regPart) (Ŝ₁ Ŝ₂) (addr) (v vOld) (π) : Prop :=
    regPart Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧
    VC.verify Ŝ₁.mem addr vOld π ∧
    VC.verify Ŝ₂.mem addr v π
  ```
- **Full-memory** counterparts (`φ_read`, `φ_write`), over `FullVMState VC`. (`writeF` is stated point-wise — `S₂.mem addr = v` plus agreement off `addr` — to avoid a `DecidableEq VC.Index` requirement that `Function.update` would impose):
  ```lean
  def readF  (regPart) (addr) (v) (S₁ S₂ : FullVMState VC) : Prop :=
    regPart … ∧ S₁.mem addr = v ∧ S₂.mem = S₁.mem
  def writeF (regPart) (addr) (v) (S₁ S₂ : FullVMState VC) : Prop :=
    regPart … ∧ S₂.mem addr = v ∧ (∀ j, j ≠ addr → S₂.mem j = S₁.mem j)
  ```
- A **classified committed step** replacing opaque `stepC`, carrying the descriptor (this is where the bus-free, memory-only slice of `φ̂_step` lives; non-memory ops carry `.other` and a memory-free predicate):
  ```lean
  def stepC (regPart : RegPart) (Ŝ₁ Ŝ₂ : CommittedVMState VC) : MemStep VC → Prop
  def stepF (regPart : RegPart) (S₁ S₂ : FullVMState VC) : MemStep VC → Prop
  ```
  For the first increment we keep only three op classes — `read`, `write`, `other` (a memory-free black box covering ALU/precompiles) — enough to exercise both binding properties. The bus/range/precompile refinement is handled separately in `Bus.lean` (roadmap item 3).

## Stage 2 — The per-step memory-extractability lemma (the heart)  ✅ DONE (`Memory.lean`)

```lean
theorem step_mem_extract
    (hComplete : Complete VC) (hpos : PositionBinding VC) (hpunc : PuncturedBinding VC)
    (regPart : RegPart)
    (S₁ S₂ : FullVMState VC) (Ŝ₁ Ŝ₂ : CommittedVMState VC) (w : MemStep VC)
    (h1 : CommitInv Ŝ₁ S₁) (h2 : CommitInv Ŝ₂ S₂)
    (hstep : stepC regPart Ŝ₁ Ŝ₂ w) :
    stepF regPart S₁ S₂ w
```

Proof by case on `w` (mirrors the paper's Step A, minus probabilities). `addr`, `v`, `vOld`, `π` are the typed fields of the descriptor, so nothing casts:

- **Other (memory-free):** register part transfers directly; memory equality via `mem_eq_of_commit_eq`.
- **Read `(addr, v, π)`:**
  - `S₁.mem addr = v`: honest opening `hComplete S₁.mem addr` verifies `VC.commit S₁.mem` at `addr` to `S₁.mem addr`; the descriptor's `π` verifies the same commitment (rewrite `Ŝ₁.mem = VC.commit S₁.mem` via `CommitInv`) to `v`; `hpos` ⟹ `S₁.mem addr = v`.
  - `S₂.mem = S₁.mem`: from `Ŝ₁.mem = Ŝ₂.mem` ⟹ `commit S₁.mem = commit S₂.mem`; `mem_eq_of_commit_eq`.
- **Write `(addr, v, vOld, π)`:**
  - At `addr`: `hpos` on the descriptor's `VC.verify Ŝ₂.mem addr v π` vs the honest opening of `commit S₂.mem` ⟹ `S₂.mem addr = v`.
  - Off `addr` (`j ≠ addr`): `hpunc` with the *same* `π` at `addr` under `C = Ŝ₁.mem`, `C' = Ŝ₂.mem` gives the two commitments agree at `j`; with `hComplete` ⟹ `S₁.mem j = S₂.mem j`. (The `vOld` opening at `addr` under `Ŝ₁.mem` and the `v` opening under `Ŝ₂.mem` supply the two accepted openings punctured-binding needs.)

## Stage 3 — Trace-level reconstruction (Step 6): extend the system and CTE

The upgrade is done **in place** on the one `System` and the one `cte` theorem — no parallel `System'` or separate `cte_full_memory`. Because non-memory ops carry `.other`, every change is a *conservative extension*: the old opaque behaviour is the `.other` special case.

### 3.1 — Extend `System` and `SegWitness` (Twostep.lean)  ✅ DONE

- The opaque `stepC : Ŝ → Ŝ → Prop` field of `System` is replaced by `regPart : RegPart`; the full committed step is the classified `stepC sys.regPart` from `Memory.lean`.
- `SegWitness` gains `steps : ℕ → MemStep VC` (ℕ-indexed to match `states`; only the first `Nseg` matter).
- `RSeg.rel` now reads `stepC sys.regPart (w.states j) (w.states (j+1)) (w.steps j)` for `j < Nseg`.

**Interaction with the abstract `ZkVM` (new since this plan was written).** `Twostep` instantiates the abstract `ZkVM`, whose `step : State → State → Prop` is descriptor-free, but the classified `stepC` needs a `MemStep`. Resolved with an **existential projection** kept at the system level:
```lean
def stepRel (Ŝ₁ Ŝ₂ : CommittedVMState sys.VC) : Prop :=
  ∃ w : MemStep sys.VC, stepC sys.regPart Ŝ₁ Ŝ₂ w
```
`toZkVM.step := sys.stepRel`, so the flattened abstract trace stays descriptor-free while the concrete descriptors remain in `SegWitness.steps`. In `cte`, each flattening obligation `stepRel (seg i j) (seg i (j+1))` is discharged by `⟨(extracted witness).steps j, …⟩`. The two-layer extraction proof is otherwise unchanged.

> **Design point for review.** The existential projection means the *flattened* trace's step no longer names its descriptor — the concrete openings live only in the per-segment witnesses. The memory fold (3.2) therefore operates on the segment witnesses, before/around flattening. The alternative — generalizing `ZkVM.step` to carry a descriptor slot — is a larger change to `Zkvm.lean` and is deliberately deferred; worth a sync with the `Zkvm.lean` authors before adopting.

### 3.2 — Memory reconstruction fold  ⏳ REMAINING

From an extracted committed chain `Ŝ₀ … Ŝ_{Nseg}` (per segment) and its descriptors `w₀ … w_{Nseg-1}`, together with `CommitInv Ŝ₀ S₀` for the adversary's initial full state `S₀`, define `mem_{k+1}` by recursion on the descriptor (read/other: `mem_k`; write `(addr, v, …)`: point-wise update of `mem_k` at `addr` to `v`). Prove `CommitInv Ŝ_{k+1} S_{k+1}` is maintained — the inductive step, which consumes `hpos`/`hpunc`/`hComplete` through `step_mem_extract`.

Before implementing the fold, isolate the additional update/realizability property needed here: `step_mem_extract` **assumes** `CommitInv` for the post-state, while `Complete`, `PositionBinding`, and `PuncturedBinding` alone do not state that an arbitrary extracted post-commitment is `VC.commit` of a full memory. Formulate this as the smallest standalone predicate over the existing `VectorCommitment` (e.g. "every reachable committed memory is a commitment of some full memory, and a write's post-commitment is the commitment of the updated memory") and thread it through the fold.

### 3.3 — Strengthen `cte` in place  ⏳ REMAINING

Give the *existing* `cte` the extra memory hypotheses (`Complete`, `PositionBinding`, `PuncturedBinding`, the 3.2 realizability predicate, and `CommitInv st.S0 S₀`) and a stronger conclusion, so the single theorem yields both the committed trace *and* the reconstructed full-memory execution.

The original Fin-indexed sketch (for context) was:
```lean
-- (pre-restructure, Fin-indexed)
∃ d : Fin (sys.m + 1) → CommittedVMState sys.VC,
  d 0 = st.S0 ∧ d (Fin.last sys.m) = st.ST ∧
  (∀ i, ∃ ws, sys.RSeg.rel ⟨d i.castSucc, d i.succ⟩ ws) ∧          -- (a) committed content
  (∀ i, ∃ S : Fin (sys.Nseg + 1) → FullVMState sys.VC,             -- (b) full-memory
      CommitInv (d i.castSucc) (S 0) ∧ CommitInv (d i.succ) (S (Fin.last sys.Nseg)) ∧
      ∀ j, stepF sys.regPart (S j.castSucc) (S j.succ) ((ws i).steps j))
```

Translated to main's current shape:
- Conjunct **(a)** — the committed content — is now *already delivered* by the existing `cte`: `TraceValid` gives a flattened `ℕ`-indexed committed trace whose every step satisfies `stepRel` (i.e. `∃ w, stepC sys.regPart …`). The per-segment `RSeg` witnesses (with their `steps`) are the intermediate objects the extractor produces.
- Conjunct **(b)** — the full-memory upgrade — is the new content: for each segment `i < m`, a full-memory chain `S : ℕ → FullVMState sys.VC` with `CommitInv` at both boundaries and `stepF sys.regPart (S j) (S (j+1)) ((wᵢ).steps j)` for `j < Nseg`, obtained by running the 3.2 fold and applying `step_mem_extract` at every `j`.

Keep the per-segment shape (each segment reconstructed on its own `Nseg`-length chain and chained through the boundary `CommitInv`); flattening the `m·Nseg` full-memory steps into one trace is the separate combinatorial step (`concatTrace`/`chain_flatten` already do exactly this for the committed trace and can be reused for the full-memory one) and does not touch the memory argument.

## Ordering, risks, effort

- **Stages 0–2 — done and in isolation** (single-step lemma over the existing `VectorCommitment`); the highest-value result, and what makes the binding definitions non-vacuous.
- **Stage 3.1 — done**: witness/relation threading plus the `stepRel` bridge to the abstract `ZkVM`.
- **Remaining risk (3.2/3.3):** the reconstruction fold's realizability predicate (see 3.2) is the genuinely new mathematical content; getting it minimal but sufficient is the main design task. The per-step application of `step_mem_extract` is mechanical once the fold's invariant is stated.
- **New assumption already added:** `Complete VC` — uncontroversial (honest openings verify), added as an explicit predicate so it is visible.
- **Deliberately deferred:** the bus is handled separately in `Bus.lean` (so `stepC`'s `other` class stays a black box here), range checks, and flattening the full-memory `m·Nseg` chain — none interact with the per-step memory argument, matching the whitepaper's separation.

**Next step:** formulate the smallest commitment update/realizability property (3.2) that lets a valid classified step extend `CommitInv` to its post-state, then use it in the reconstruction fold and the strengthened `cte`. Keep it as a standalone predicate over the existing `VectorCommitment` rather than replacing the commitment structure.
