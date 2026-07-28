# Branch analysis vs `main-temp` (146e0f8)

All branches were inspected read-only (`git diff --stat`, `git diff -- <file>`, `git log`,
`git show`). No checkout was performed; the repo stayed on `main-temp` throughout.
`main-temp` = `VanillaZkVM/{Crypto,Zkvm,Twostep,Bus}.lean`, no `Cost.lean`/`Memory.lean`.
No branch contains an actual `sorry`/`admit` tactic — all are axiom-clean as far as grep shows.

## Summary table

| Branch | Purpose | Verdict | Note |
|---|---|---|---|
| `origin/extract-or-collision` | Refactor `Bus.segment_extract` into an unconditional extract-or-collision reduction + CR corollary | **REUSE — port to main-temp now** | Small (1 commit, ~120 net lines), self-contained improvement of existing theorem, same spirit as the merged assumption-safeguards PR #4. Needs manual re-apply (predates #4). |
| `cost-bus-reduction` | Cost model (`Cost.lean`) + toy exact-cost bus-unification reduction (`BusE.lean`) | REFERENCE-ONLY | Toy/standalone (1 step + 1 chip, not the real `Bus.System`). Stale (predates PR #4, diff shows spurious deletions). Superseded in spirit by `extract-or-collision`. |
| `origin/cr-algorithmic` | `cost-bus-reduction` + `CRAlg.lean`, an algorithmic (keyed, cost-bounded) redefinition of collision-resistance | REFERENCE-ONLY | Adds one extra isolated file on top of cost-bus-reduction; not wired into `Bus.lean`/`Crypto.lean`. Good idea, not integrated. |
| `cost-twostep` | Cost model + exact-cost, cost-friendly `Twostep.lean` (CTE reduction with explicit cost) | **REUSE — for a future "cost of reductions" task** | Complete, compiling-looking, no sorries. `Cost.lean` here is a superset (adds `seqRange`) of cost-bus-reduction's — use this version if unifying. Independent of memory/bus work. |
| `memory-integration` | Wire memory-extractability (`Memory.lean`) into the abstract zkVM + into `Twostep` (`cte_full`) | REFERENCE-ONLY / partial REUSE | Most "reviewed" of the memory branches (has math companion doc, addressed review comments, renamed `Complete`/`RegPart`). Targets **TwoStep**, not Bus. Redundant core (`Memory.lean`) with `memory-recon` and `pr5`. |
| `memory-recon` | Earlier/parallel memory-reconstruction exploration; also deletes `Bus.lean`/`Zkvm.lean` in favor of a new `Model.lean` | DROP | Least complete (`Memory.lean` stops at `step_mem_extract`, no trace-level theorem), has leftover `plan.md`/`mem-plan.md`, and destructively restructures away `Bus.lean`. Superseded by `memory-integration`/`pr5`. |
| `pr5` | Memory-reconstruction core + wire it into **Bus** (`BusMemory.lean`) + trace-level correctness (`MemoryTrace.lean`) + concrete sanity-check VCs (`MemorySanity.lean`) | **REUSE — best base for "memory reconstruction" task** | Most complete of the three memory branches: full trace-level theorem, concrete instantiations proving the binding notions non-vacuous, and an explicit counterexample showing `appendBitVC` breaks `UpdateBinding`. Identical Lean code to `origin/yl-memory-reconstruction`. |
| `origin/yl-memory-reconstruction` | Same as `pr5` | REFERENCE-ONLY (docs) | Byte-identical Lean diff to `pr5`; adds ~2800 lines of planning/review markdown (`docs/ADVERSARIAL_REVIEW.md`, `docs/SECURITY_ARCHITECTURE.md`, etc.). Keep as the write-up/rationale companion to `pr5`, not as a separate code branch. |

## `origin/extract-or-collision`

**Purpose:** replace `Bus.lean`'s existing `segment_extract` theorem with a version that never assumes collision-resistance — it extracts a genuine collision explicitly whenever the four bus copies disagree — plus a corollary `segment_knowledgeSound` that adds CR (cited externally, not baked into the reduction) to recover the original conclusion.

**Diff:** single commit `13ba151`, touches only `Bus.lean` (+143/−? net), `Cost.lean` not needed, `Crypto.lean`/`Cost.lean` diff noise is a rebase artifact (see below). Net vs `main-temp`: `Bus.lean` 143 changed lines, `Cost.lean` +46/−? (unused here, comes from a shared ancestor), `Crypto.lean` +44 (adds `CollisionResistant`-related helpers used by the corollary).

**New/changed Lean:**
- `Assumptions` (`Bus.System`) — drops the `busCR` field (CR is no longer part of the trust base for extraction).
- `theorem segment_extract_or_collision (h : sys.Assumptions) : ∃ E, ∀ x p, verify → rel x (E x p) ∨ ∃ b b', b ≠ b' ∧ H.hash b = H.hash b'` — the unconditional reduction.
- `theorem segment_knowledgeSound (h) (hcr : CollisionResistant sys.H) : KnowledgeSound sys.ASSegmentTrace` — corollary, one-line proof by discharging the collision branch via `hcr`.

**Complete/compiling:** yes, no `sorry`; single tight commit, well-commented.

**Caveat:** this branch was cut before PR #4 ("assumption-safeguards", which added `trivialAS`/`knowledgeSound_trivialAS` to `Crypto.lean`) was merged into `main-temp`. The `git diff --stat` against `main-temp` for `Crypto.lean`/`Cost.lean` mixes in that unrelated drift. **Action to reuse:** cherry-pick/re-apply just the `Bus.lean` hunk onto current `main-temp` rather than merging the branch wholesale.

**Recommendation:** REUSE — this is a genuine improvement of code that already exists on `main-temp` and directly continues the "make assumptions explicit/non-vacuous" theme from PR #4. Low effort, high value; do this first.

## `cost-bus-reduction`

**Purpose:** introduce a generic cost-annotated algorithm type `Alg` (`Cost.lean`) and use it to give an *exact* (not asymptotic) cost to a bus-unification reduction, illustrated on a minimal toy system (`BusE.lean`: one step + one delegated chip, not `Bus.lean`'s real 3-chip `System`).

**Diff:** adds `VanillaZkVM/BusE.lean` (158 lines, new file) and `VanillaZkVM/Cost.lean` (51 lines, new file); trims `Bus.lean` (−? , mostly doc tweaks) and `Twostep.lean`/`Crypto.lean` (removes `trivialAS`/`knowledgeSound_trivialAS` — see rebase-artifact note above, this is stale drift, not an intentional change).

**New Lean:**
- `Cost.Alg` (`structure`), `Alg.comp`, `Alg.pair`, `Alg.share` — sequential/parallel/shared-prefix combinators with additive cost.
- `BusE.Dstep`, `BusE.Dchip` — output-selection helpers.
- `BusE.reductionPair` / `BusE.reductionShare` — naive vs. shared-extraction reductions to `Domain ⊕ (Domain × Domain)` (unify or exhibit a collision).
- `reductionShare_correct`, `reductionPair_cost`, `reductionShare_cost`, `reductionPair_cost_gap` — exact cost equations, showing `share` saves exactly one extractor run vs. `pair`.

**Complete/compiling:** yes, no sorries; but it's a standalone toy model, not plugged into the real `Bus.System`.

**Recommendation:** REFERENCE-ONLY. The cost-combinator library (`Cost.lean`) is reusable infrastructure, but the applied result here is superseded by `extract-or-collision` (which does the real, un-costed version directly on `Bus.System`) and by `cost-twostep`'s superset `Cost.lean`. Keep as a worked example/reference if a future task is "add exact costs to the real Bus reduction."

## `origin/cr-algorithmic`

**Purpose:** `cost-bus-reduction` plus one extra file, `CRAlg.lean`, proposing an alternative, "algorithmic" definition of collision-resistance (keyed hash family, CR = "no cost-bounded finder wins") instead of the perfect-injectivity notion used everywhere else, with a bridge lemma from injectivity and a worked use-pattern lemma.

**Diff:** identical to `cost-bus-reduction` plus `VanillaZkVM/CRAlg.lean` (+82 new lines, confirmed via `git diff --stat cost-bus-reduction..origin/cr-algorithmic` → only `CRAlg.lean` differs).

**New Lean (`CRAlg.lean`):**
- `HashFamily` (structure, keyed hash).
- `Wins`, `CollisionResistant` (algorithmic, cost-bounded def over `Alg`).
- `theorem cr_of_injective` — old perfect notion implies the new one at every bound.
- `theorem eq_of_cr` — worked "valid-or-collision ⇒ valid" use pattern.

**Complete/compiling:** yes, no sorries. Entirely self-contained; not wired into `Bus.lean`/`Crypto.lean` — it's a design proposal, not an applied change.

**Recommendation:** REFERENCE-ONLY. Interesting conceptual alternative to `Crypto.CollisionResistant`, but doesn't touch/replace it and needs a deliberate decision (and follow-up work) before being adopted project-wide. Same staleness caveat as `cost-bus-reduction`.

## `cost-twostep`

**Purpose:** cost-annotate the two-step (segment + final) architecture in `Twostep.lean` — give the CTE (correct-trace-extraction) reduction an explicit reduction algorithm and an exact cost formula.

**Diff:** adds `Cost.lean` (59 lines — same as `cost-bus-reduction`'s plus `seqRange`), rewrites large parts of `Twostep.lean` (+166/− existing), trims `Bus.lean`/`Crypto.lean` (same stale-`trivialAS` rebase artifact as the other cost branches).

**New Lean (`Twostep.lean`):**
- `SegStmt`, `SegWitness`, `FinalStmt`, `FinalWitness` — cost-friendly restatement of the segment/final relations as explicit structures (part 1, "cost-friendly definitions").
- `System`, `RSeg`/`ASSeg`, `RFinal`/`ASFinal`, `toZkVM` — same architecture as `main-temp`'s `Twostep.System`, restated.
- `theorem cte` — the correct-trace-extraction theorem (same statement as `main-temp`).
- `def buildTrace`, `def cteReduction : Alg (FinalStmt × FinalProof) (ℕ → CommittedVMState)` — the CTE extractor reified as a cost-tracked `Alg`.
- `theorem cteReduction_cost` — the exact cost formula (sum over `Nseg` segments via `seqRange`).
- `theorem cteReduction_correct` — ties the `Alg` back to the `cte` correctness statement.

**Complete/compiling:** yes, no sorries; 3 commits ("part 1", "part 2", "more comment") reading as a finished, polished unit.

**Recommendation:** REUSE for a future "cost of the top-level CTE reduction" task. It is the most complete and self-contained of the cost-themed branches. If cost work resumes, prefer this branch's `Cost.lean` (superset with `seqRange`) as the shared base over `cost-bus-reduction`'s. Needs a rebase onto current `main-temp` (post PR #4) before use.

## `memory-integration`

**Purpose:** "Integrate memory extractability onto the abstract-zkVM architecture" — add a generic `Memory.lean` (committed vs. full VM state, read/write step predicates, per-step and per-trace memory-extraction theorems) and wire it specifically into `Twostep.lean`, producing a full-memory version of the CTE theorem.

**Diff:** new `VanillaZkVM/Memory.lean` (330 lines), substantial `Twostep.lean` changes (+166), `Crypto.lean` changes (+67/−, adds `Complete`/binding notions, per "Address review: move Complete to Crypto, rename RegPart"), plus two markdown docs (`math-companion.md` 380 lines, `update-binding.md` 129 lines — the latter documents replacing "punctured binding" with "update binding").

**New Lean (`Memory.lean`):**
- `FullVMState`, `CommitInv` — full state type and the commitment-consistency invariant.
- `MemFreePredicate`, `readC`/`writeC`/`readF`/`writeF`, `stepC`/`stepF` — committed vs. full step predicates parameterized by a memory-independent ("free") predicate on the rest of the step.
- `theorem step_mem_extract` — per-step: a valid committed step + `CommitInv` ⇒ a full step exists with the same memory-free part.
- `theorem commit_update`, `commitInv_write` — commitment update lemmas.
- `noncomputable def stepReconstruct`, `reconstructTrace` — build a full-state trace from a committed trace + per-step descriptors.
- `theorem commitInv_step`, `trace_mem_extract` — trace-level extraction: a valid committed trace lifts to a valid full-memory trace.
- `noncomputable def chooseDescr`, `theorem chooseDescr_spec` — existence/choice of the per-step descriptor.

**New Lean (`Twostep.lean` additions):** `FinalStmtFull`, `toCommitted`, `stepRel`, `toZkVMFull`, `theorem traceValid_full`, `theorem cte_full` — a full-memory-aware final theorem parallel to `cte`.

**Complete/compiling:** yes, no sorries; the doc explicitly notes `cte : [propext, Quot.sound]` (no `sorryAx`), i.e. axiom-clean. Most "reviewed" branch of the three memory branches (review comments visibly addressed across commits).

**Recommendation:** Partial REUSE / mostly REFERENCE-ONLY. This is a solid, independent memory-reconstruction core wired into **TwoStep**. It duplicates the same core problem `pr5` solves for **Bus**, using different naming (`RegPart`→ eventually renamed, `PuncturedBinding`) and no concrete sanity-check instances. If memory work resumes, decide once which `Memory.lean` core to keep (recommend `pr5`'s, since it has concrete non-vacuity checks) and reapply this branch's `Twostep` integration (`cte_full`) on top of it, rather than keeping both cores.

## `memory-recon`

**Purpose:** earliest/parallel memory-reconstruction exploration; diverges from `main-temp` far upstream (before "Restructure: abstract zkVM and CTE") and goes further — it deletes `Bus.lean` and `Zkvm.lean` entirely and introduces a new `Model.lean` for the VM-state primitives.

**Diff:** `Bus.lean` −268 (deleted), `Zkvm.lean` −189 (deleted), new `Memory.lean` (181 lines) and `Model.lean` (53 lines), `Crypto.lean` +120/−, `Twostep.lean` heavily rewritten (214 changed), plus leftover planning docs `mem-plan.md` (178 lines) and `plan.md` (68 lines), and a `lakefile.toml` tweak.

**New Lean:**
- `Model.lean`: `Word`, `Addr`, `Byte` (abbreviations), `VMStateWith`, `VMState`, `StatePred`, `memUpdate` — basic VM-state vocabulary factored out.
- `Memory.lean`: `FullVMState`, `Complete`, `CommitInv`, `theorem mem_eq_of_commit_eq`, `RegPart` (abbrev, later renamed `MemFreePredicate` on `memory-integration`), `readC`/`writeC`/`readF`/`writeF`, `stepC`/`stepF`, `theorem step_mem_extract` — same shape as `memory-integration`'s core but stops at the single-step theorem; no trace-level extraction, no `chooseDescr`.

**Complete/compiling:** likely compiles (no sorries found), but functionally the least developed of the three memory branches, and it removes `Bus.lean` — a large piece of already-landed functionality — which is a red flag for merging as-is.

**Recommendation:** DROP. Superseded by both `memory-integration` (same core, further along, plus TwoStep integration) and `pr5` (same core, further along, plus Bus integration and sanity checks). Its destructive removal of `Bus.lean`/`Zkvm.lean` makes it unsuitable to merge; only look at it if curious about the very first design iteration.

## `pr5`

**Purpose:** "Formalize Bus-to-full-memory reconstruction" — same core memory-reconstruction problem as the other two branches, but wires it into **Bus.lean** (the segment/leaf layer) rather than TwoStep, adds trace-level correctness, and adds concrete instantiated vector commitments to sanity-check that the binding notions used are non-vacuous.

**Diff:** new `Memory.lean` (426 lines), `BusMemory.lean` (118 lines), `MemorySanity.lean` (145 lines), `MemoryTrace.lean` (228 lines); `Crypto.lean` +95 (adds `Complete`, `UpdateBinding`, break-witness structures); `Bus.lean` +50; `Zkvm.lean` +11; doc `docs/MEMORY_RECONSTRUCTION.md` (198 lines). Single commit `99a2c61`.

**New Lean:**
- `Crypto.lean`: `Complete`, `UpdateBinding`, `PositionBindingBreak`/`IsPositionBindingBreak`, `UpdateBindingBreak`/`IsUpdateBindingBreak` (explicit "break" witnesses — a counterexample-carrying formulation of binding failure), `not_isPositionBindingBreak`/`not_isUpdateBindingBreak`, `mem_eq_of_commit_eq`.
- `Memory.lean`: `FullVMState`, `CommitInv`, `MemFreePredicate`, `readC`/`writeC`/`readF`/`writeF`, `stepC`/`stepF`, `def reconstructStepReduction` (+ `_correct`, `_success`), `theorem reconstructStep`, `step_mem_extract`, `commit_update`, `commitInv_write`.
- `BusMemory.lean`: `segmentDescriptor`, `segmentCoreStep`, `MemoryTraceValid`, `theorem segment_reconstruct_memory`, `theorem accepting_segment_reconstructs_memory` — the actual bridge from an accepting Bus segment proof to a reconstructed full-memory trace.
- `MemoryTrace.lean`: `def reconstructTrace` + `reconstructTrace_zero/_succ_of_success/_commitInv/_step/_from_initial/_terminal/_correct` — full trace-level reconstruction and its correctness, boundary-exact.
- `MemorySanity.lean`: concrete `exactVC`, `appendBitVC` vector commitments; proofs each does/doesn't satisfy `Complete`/`PositionBinding`/`PuncturedBinding`/`UpdateBinding`; notably `appendBitBreak`/`appendBitBreak_wins`/`appendBitVC_not_updateBinding` — an explicit counterexample proving `appendBitVC` **fails** update-binding, i.e. the definitions are demonstrably non-vacuous (mirrors the "assumption safeguards" theme).

**Complete/compiling:** yes, no sorries; the branch's own doc (`docs/MEMORY_RECONSTRUCTION.md`) explicitly scopes what's proven vs. not ("not yet connected to a concrete ISA/program or a computational probability bound").

**Recommendation:** REUSE — this is the strongest base for a future "memory reconstruction" task: most complete (trace-level, boundary-exact), only branch with concrete non-vacuity sanity checks, and it plugs into `Bus.lean` (the layer `main-temp` already has fully built out), unlike `memory-integration`/`memory-recon` which target/replace other layers. Needs a rebase check against current `main-temp` (diverges only at `Crypto.lean`/`Bus.lean`/`Zkvm.lean`, all additive, so should apply cleanly).

## `origin/yl-memory-reconstruction`

**Purpose:** identical Lean payload to `pr5` (confirmed: `git diff --stat pr5..origin/yl-memory-reconstruction` touches **zero** `.lean` files), plus ~2,800 lines of planning/review markdown under `docs/`: `ADVERSARIAL_REVIEW.md`, `ADVERSARIAL_REVIEW_RESPONSE.md`, `AXIOM_AUDIT.md`, `BUS_SECURITY_PLAN.md`, `COMPUTATIONAL_SECURITY_DESIGN.md`, `CONCRETE_SEMANTICS_PLAN.md`, `MEMORY_INVARIANT_REVIEW.md`, `PROOF_REVIEW_CHECKLIST.md`, `SECURITY_ARCHITECTURE.md`, `VANILLAVM_ROADMAP.md`, `docs/README.md`.

**Recommendation:** REFERENCE-ONLY (docs companion to `pr5`). Do not treat as a separate code branch — reuse `pr5` for the code and consult this branch's `docs/` only if the adversarial-review/roadmap write-ups are wanted for context. `AXIOM_AUDIT.md` in particular may be worth skimming before landing `pr5`, to double check the axiom-cleanliness claim independently.

## Cross-branch relationships

- **Identical-code pairs:** `pr5` ≡ `origin/yl-memory-reconstruction` (Lean); `cost-bus-reduction` ⊂ `origin/cr-algorithmic` (latter = former + `CRAlg.lean`).
- **Cost-model overlap:** `cost-bus-reduction` and `cost-twostep` each define their own `Cost.lean`; `cost-twostep`'s is a strict superset (adds `seqRange`). If cost work resumes, standardize on `cost-twostep`'s version.
- **Three independent takes on the same "memory reconstruction" core** (`Memory.lean`, `CommitInv`, `stepC`/`stepF`, `step_mem_extract`): `memory-recon` (earliest, least complete, deletes Bus/Zkvm), `memory-integration` (wires into TwoStep, best-reviewed docs), `pr5` (wires into Bus, most complete + sanity-checked). Recommend consolidating on `pr5`'s core and re-deriving `memory-integration`'s TwoStep integration on top of it if both integration points are eventually wanted.
- **Staleness:** all of `cost-bus-reduction`, `origin/cr-algorithmic`, `cost-twostep` were cut before PR #4 ("assumption-safeguards") merged into `main-temp`; their diffs show spurious removal of `trivialAS`/`knowledgeSound_trivialAS` from `Crypto.lean` that is really just missing-commit drift, not an intended change. Rebase before reusing.
- **Theme continuity:** `origin/extract-or-collision`'s split of `segment_extract` and `pr5`'s `MemorySanity.lean` counterexamples both continue the "make cryptographic assumptions explicit / non-vacuous" theme started by PR #4 (`trivialAS`) — these three fit together conceptually even though on different branches.
