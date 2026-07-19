# Memory Extractability — Implementation Plan

A concrete, Lean-oriented plan for adding **memory extractability** — the step that turns `toy_cte`'s committed-state conclusion into a statement about real full-memory execution. Grounded in Proposition (Memory extractability) and Step 6 of the whitepaper's `sampleVM/ch05-security.tex`.

> **Scope constraint:** keep the existing `VectorCommitment` (Crypto.lean) — do **not** introduce a new/specialized memory-commitment structure.

## Goal

Prove the analogue of the whitepaper's Proposition: **position-binding + punctured-binding of `Com_mem` ⟹ a committed-memory step lifts to a full-memory step**, then thread it through the trace to reconstruct `mem₀ … mem_T` and conclude `φ_step (S_k, S_{k+1})` for the *real* predicate. In the perfect/probability-free style of Crypto.lean, "except with probability `Adv`" collapses to "always", so the two binding hypotheses are consumed as plain implications and the `T`-fold union bound disappears.

## What's missing today (the gaps to close)

1. **No link between `CommittedVMState` and `VMState`.** Nothing says `Ŝ.mem = VC.commit S.mem`. Need a *commitment invariant* predicate.
2. **`stepC` is fully opaque.** Memory extractability needs the step to *expose* its operation kind and the opening witnesses (`π` for read, `(π_write, v_old)` for write). The paper stresses these must be concrete witness fields, not existentials.
3. **No commitment completeness.** The derivation `mem₁[addr] = x` needs an *honest* opening to verify against the adversarial one under position-binding. `VectorCommitment` currently has no `verify (commit m) i (m i) (openProof m i)` guarantee.
4. **Index/value typing.** `VC.verify` expects `VC.Index`/`VC.Value`, but registers are `ℕ`. Rather than specialize the commitment (forbidden by the scope constraint), we work over the commitment's *own* `VC.Index`/`VC.Value` on the state side and let the op-descriptor carry the typed address/value it feeds to `verify`.

> **How the scope constraint is honored.** We use the commitment's native index/value types as the memory address/value types — full memory becomes `VC.Index → VC.Value` — and the memory-step descriptor carries `addr : VC.Index`, values `: VC.Value`, and the opening `: VC.OpenProof`. Every `VC.verify` call is then well-typed with **no casts** and no new structure. The old `VMState = VMStateWith (Addr → Byte)` is recovered as the special case `VC.Index := ℕ`, `VC.Value := ℕ` (since `Addr = Byte = ℕ`).

---

## Stage 0 — Model plumbing

In Model.lean / a new `Memory.lean`, keeping the **existing** `VectorCommitment`:

- **Full-memory state over the commitment's native types** (no wrapper, no casts):
  ```lean
  abbrev FullVMState (VC : VectorCommitment) : Type := VMStateWith (VC.Index → VC.Value)
  ```
  `CommittedVMState VC = VMStateWith VC.Com` is unchanged; the two states again share `pc`/`regs`
  and differ only in memory. The original `VMState = VMStateWith (Addr → Byte)` is the instance
  `VC.Index := ℕ`, `VC.Value := ℕ`.
- **Commitment completeness** — the one genuinely new crypto assumption (add to `VectorCommitment` in Crypto.lean as a field, or as a standalone predicate):
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

## Stage 1 — Concrete committed + full-memory predicates

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
  def readC  (regPart : …→Prop) (Ŝ₁ Ŝ₂) (addr) (v) (π) : Prop :=
    regPart Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧ Ŝ₁.mem = Ŝ₂.mem ∧
    VC.verify Ŝ₁.mem addr v π
  def writeC (regPart) (Ŝ₁ Ŝ₂) (addr) (v vOld) (π) : Prop :=
    regPart Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧
    VC.verify Ŝ₁.mem addr vOld π ∧
    VC.verify Ŝ₂.mem addr v π
  ```
- **Full-memory** counterparts (`φ_read`, `φ_write`), over `FullVMState VC`:
  ```lean
  def readF  (regPart) (addr) (v) (S₁ S₂ : FullVMState VC) : Prop :=
    regPart … ∧ S₁.mem addr = v ∧ S₂.mem = S₁.mem
  def writeF (regPart) (addr) (v) (S₁ S₂ : FullVMState VC) : Prop :=
    regPart … ∧ S₂.mem = Function.update S₁.mem addr v
  ```
  (`memUpdate` in Model.lean is `Function.update` specialized to `Addr → Byte`; over `VC.Index → VC.Value` we call `Function.update` directly, or generalize `memUpdate`.)
- A **classified committed step** replacing opaque `stepC`, carrying the descriptor (this is where the bus-free, memory-only slice of `φ̂_step` lives; non-memory ops carry `.other` and a memory-free predicate):
  ```lean
  def stepC (Ŝ₁ Ŝ₂ : CommittedVMState VC) (w : MemStep VC) : Prop := …
  def stepF (S₁ S₂ : FullVMState VC) : Prop := …   -- the real φ_step
  ```
  For the first increment keep only three op classes — `read`, `write`, `other` (a memory-free black box covering ALU/precompiles) — enough to exercise both binding properties. The bus/range/precompile refinement is deferred to roadmap step 3.

## Stage 2 — The per-step memory-extractability lemma (the heart)

```lean
theorem step_mem_extract
    (hComplete : Complete VC) (hpos : PositionBinding VC) (hpunc : PuncturedBinding VC)
    (S₁ S₂ : FullVMState VC) (Ŝ₁ Ŝ₂ : CommittedVMState VC) (w : MemStep VC)
    (h1 : CommitInv Ŝ₁ S₁) (h2 : CommitInv Ŝ₂ S₂)
    (hstep : stepC Ŝ₁ Ŝ₂ w) :
    stepF S₁ S₂
```

Proof by case on `w` (mirrors the paper's Step A, minus probabilities). `addr`, `v`, `vOld`, `π` are the typed fields of the descriptor, so nothing casts:

- **Other (memory-free):** register part transfers directly; memory irrelevant. Trivial.
- **Read `(addr, v, π)`:**
  - `S₁.mem addr = v`: honest opening `hComplete S₁.mem addr` verifies `VC.commit S₁.mem` at `addr` to `S₁.mem addr`; the descriptor's `π` verifies the same commitment (rewrite `Ŝ₁.mem = VC.commit S₁.mem` via `CommitInv`) to `v`; `hpos` ⟹ `S₁.mem addr = v`.
  - `S₂.mem = S₁.mem`: from `Ŝ₁.mem = Ŝ₂.mem` ⟹ `commit S₁.mem = commit S₂.mem`; `hpos` + `hComplete` at every `i`, then `funext`.
  - Conclude `readF`.
- **Write `(addr, v, vOld, π)`:**
  - `S₂.mem = Function.update S₁.mem addr v`, by `funext i`, `by_cases i = addr`:
    - `i = addr`: `hpos` on the descriptor's `VC.verify Ŝ₂.mem addr v π` vs the honest opening of `commit S₂.mem` ⟹ `S₂.mem addr = v`.
    - `i ≠ addr`: `hpunc` with the *same* `π` at `addr` under `C = Ŝ₁.mem`, `C' = Ŝ₂.mem` gives the two commitments agree at `i`; with `hComplete` ⟹ `S₁.mem i = S₂.mem i`. (The `vOld` opening at `addr` under `Ŝ₁.mem` and the `v` opening under `Ŝ₂.mem` supply the two accepted openings punctured-binding needs.)
  - Conclude `writeF`.

This is the first place `PositionBinding` and `PuncturedBinding` — declared but unused in Crypto.lean — actually get consumed. Expect the `funext` + `by_cases` write case to be the bulk of the work.

## Stage 3 — Trace-level reconstruction (Step 6): extend the existing system and CTE

Do the upgrade **in place** — enrich the one `System` and the one `toy_cte`, do
**not** introduce a parallel `System'` or a separate `toy_cte_full_memory`.
Because non-memory ops carry `.other`, every change below is a *conservative
extension*: the old opaque behaviour is recovered as the `.other` special case,
so anything already built on `System`/`toy_cte` keeps working.

1. **Extend `System` and `SegWitness` (Twostep.lean) — implemented in place.**
   - Replace the opaque field with the classified, descriptor-carrying predicate
     `stepC : CommittedVMState VC → CommittedVMState VC → MemStep VC → Prop`, and
     add a `regPart : RegPart` field. The previous `stepC Ŝ Ŝ'` is exactly
     `stepC Ŝ Ŝ' .other` (with a memory-free `regPart`), so the segment/final
     relations and their argument systems are otherwise untouched.
   - Add `steps : Fin Nseg → MemStep VC` to the **existing** `SegWitness`, and
     change `RSeg.rel` to `sys.stepC (w.states i.castSucc) (w.states i.succ) (w.steps i)`.
   The two-layer extraction in `toy_cte` still goes through with the same proof
   skeleton — the extractor now additionally returns the per-step descriptors and
   openings.
2. **Memory reconstruction fold.** From the extracted committed chain `Ŝ₀ … Ŝ_T`
   and its descriptors, together with `CommitInv Ŝ₀ S₀` for the adversary's
   initial full state `S₀`, define `mem_{k+1}` by recursion on the descriptor
   (read/other: `mem_k`; write `(addr, v, …)`: point-wise update of `mem_k` at
   `addr` to `v`). Prove `CommitInv Ŝ_{k+1} S_{k+1}` is maintained — the inductive
   step, which consumes `hpos`/`hpunc`/`hComplete` through `step_mem_extract`.
   Before implementing the fold, isolate the additional update/realizability
   property needed here: `step_mem_extract` assumes `CommitInv` for the post-state,
   while `Complete`, `PositionBinding`, and `PuncturedBinding` alone do not state
   that an arbitrary extracted post-commitment is `VC.commit` of a full memory.
3. **Strengthen `toy_cte` in place — no new theorem.** Give the *existing*
   `toy_cte` the extra memory hypotheses and a stronger conclusion, so the single
   theorem yields both the committed segmentation *and* the reconstructed
   full-memory execution:
   ```lean
   theorem toy_cte (sys : System)
       (hComplete : Complete sys.VC) (hpos : PositionBinding sys.VC)
       (hpunc : PuncturedBinding sys.VC)
       (hseg : KnowledgeSound sys.ASSeg) (hfinal : KnowledgeSound sys.ASFinal)
       (st : FinalStmt sys.VC) (pf : sys.FinalProof) (hpf : sys.finalVerify st pf)
       (S₀ : FullVMState sys.VC) (hInit : CommitInv st.S0 S₀) :
       ∃ d : Fin (sys.m + 1) → CommittedVMState sys.VC,
         d 0 = st.S0 ∧ d (Fin.last sys.m) = st.ST ∧
         -- (a) committed content: exactly the old conclusion, unchanged
         (∀ i, ∃ ws : SegWitness sys.VC sys.Nseg, sys.RSeg.rel ⟨d i.castSucc, d i.succ⟩ ws) ∧
         -- (b) new: a genuine full-memory execution, per segment, glued by CommitInv
         (∀ i, ∃ S : Fin (sys.Nseg + 1) → FullVMState sys.VC,
             CommitInv (d i.castSucc) (S 0) ∧ CommitInv (d i.succ) (S (Fin.last sys.Nseg)) ∧
             ∀ j : Fin sys.Nseg, stepF sys.regPart (S j.castSucc) (S j.succ) (ws i).steps j)
   ```
   Conjunct (a) is the original statement verbatim, so existing callers keep
   compiling; conjunct (b) is the memory upgrade, obtained by running the fold of
   step 2 and applying `step_mem_extract` at every `j`. Keep the per-segment shape
   (each segment reconstructed on its own `Fin (Nseg+1)` chain and chained through
   the boundary `CommitInv`); flattening `m·Nseg` into one `Fin (T+1)` stays the
   separate combinatorial step and does not touch the memory argument.

## Ordering, risks, effort

- **Do Stage 0–2 first and in isolation** (single-step lemma over the existing `VectorCommitment`); it's self-contained and gives the highest-value result — it's what makes the binding definitions non-vacuous. Stage 3 depends on it plus the strengthened witness.
- **Biggest proof risk:** the write case `funext`/`by_cases` and getting the `PuncturedBinding` argument order to line up (its signature already matches, so this is mechanical but fiddly). The `mem₂ = mem₁` read argument needs position-binding *at every address* — cheap here (no union bound) but requires `hComplete`.
- **New assumption to justify:** `Complete VC`. It's uncontroversial (honest openings verify) and the paper uses it implicitly; worth adding as an explicit field so it's visible.
- **Deliberately deferred:** the bus (so `stepC`'s `other` class stays a black box), range checks, and flattening `m·Nseg` into one `Fin (T+1)` — none of them interact with the memory argument, matching the whitepaper's separation.
- **Interaction with flattening:** the strengthened `toy_cte` keeps the
  per-segment shape — each segment is reconstructed on its own `Fin (Nseg+1)`
  chain and chained through the boundary `CommitInv` — so the memory upgrade
  lands entirely inside the existing theorem. Flattening the `m·Nseg` steps into
  one flat chain remains a separate, purely combinatorial follow-up that does not
  touch the memory argument.

Net: the memory-only slice (Stages 0–2) is a compact, high-value addition that finally exercises `PositionBinding`/`PuncturedBinding`; Stage 3 is the inductive glue that upgrades `toy_cte` from committed states to real memory.

**Next step:** formulate the smallest commitment update/realizability property that lets a valid classified step extend `CommitInv` to its post-state, then use it in the Stage 3.2 reconstruction fold. Keep this as a standalone predicate over the existing `VectorCommitment` rather than replacing the commitment structure.
