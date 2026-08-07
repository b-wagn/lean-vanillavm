# PLAN — development issues for the Vanilla zkVM Lean formalization

This is the working plan: **10 dependency-ordered issues** taking us from the current two-step toy
to a formalized main security theorem for the full vanilla VM (`thm:main`). It supersedes the
free-form task list in `benedikt-plan.md` (whose relevant items it incorporates)
and is the authoritative scope (I2).

**How to read an issue.** Each has: *Goal · Depends on · Assigned · Reuse · New public surface ·
Deliverables · Math companion · Review requirement (where assigned; human, not delegatable) ·
Skills & conventions · Paper anchor.* Everything is written on a branch per issue and merged into `main-temp`
(`CONVENTIONS.md` §4).

**Collaborators & roles.**
- **Implementers:** Yavor (RovayL), Dmitry (khovratovich), Jessica (j-cqy).
- **Reviewers only (for now):** Benedikt (b-wagn) — on vacation.
- **George (asn-d6): reviewer now, likely to join as an implementer.** When he does, his natural
  slots (he is a paper co-author, so strongest on structure/topology) are: the redundant **human**
  second attempt at the tree-unrolling lemma in **Issue 4**, and co-lead of **Issue 6** (explicit
  reductions) and/or the **Issue 7** capstone. Until then he stays a reviewer. **Rule:** whoever
  implements an issue cannot be its reviewer — if George takes an issue, its reviewer shifts to
  Benedikt (or another non-author).

**Assignments follow the code people have already written** (git-verified):
Yavor owns memory reconstruction (`pr5`/`yl-memory-reconstruction`) and authored
the former `Bus.lean` prototype, now retained only in git history;
Dmitry owns the memory→abstract-VM integration (`memory-integration`, full-memory CTE) and the
cost/reduction experiments (`cost-twostep`, `cost-bus-reduction`); Jessica owns reductions
(`extract-or-collision`, `cr-algorithmic`).

**Redundancy (by design).** Issue **1** carries two independent memory integrations (Yavor's
Bus-wired core vs Dmitry's abstract-VM full-memory CTE) that must prove the same statement, and Issue
**9** re-derives the statements independently. This cross-validation is deliberate (Hicks).

---

## Dependency graph

```
        ┌─────────────────────────── Issue 0  (freeze KERNEL + scaffolding)  ← blocks all
        │
        ├── Issue 1  memory  → TwoStepWithMemory          (Yavor + Dmitry, redundant)
        ├── Issue 2  reduction vocabulary + extract-or-break  (Jessica)
        ├── Issue 3  ISA ops {read, write, arith, hash, bin} (Yavor)
        └── Issue 4  multi-layer recursion → MultiStepVM   (Dmitry)   [abstract leaf — no bus needed]

   Issue 5  bus per segment, wired into a VM   (Yavor)   depends 0,3     ← intentionally LATE
   Issue 6  explicit per-layer reductions      (Dmitry + Jessica)  depends 1,2,4,5
   Issue 7  full Vanilla VM + main theorem      (Dmitry + Yavor)   depends 1,3,4,5,6
   Issue 8  (parallel) concrete/asymptotic/runtime + reuse study (Jessica)  depends 0
   Issue 9  (rolling) independent re-derivation + audit matrix + vacuity (Yavor + Dmitry)  depends 0
```

Critical path: **0 → {1,4} → 6 → 7**. Recursion (4) is built over an **abstract** leaf relation, so
it does **not** wait for the bus (5) — that is why the bus is scheduled late.

**Every issue produces or extends a math companion** (`VanillaZkVM/math-companion.md`, following the
precedent Dmitry set on `memory-integration`): the pen-and-paper statements matching the Lean, kept
in lockstep. This is a hard deliverable, not optional.

---

## Issue 0 — Freeze the core *kernel* & stand up the review scaffolding
- **Goal.** Cleanly separate (0) crypto preliminaries, (1) abstract zkVM + security definition,
  (2) concrete VM, (3) proofs; and **freeze the kernel** (I4) — *not* all of `Crypto.lean`. The
  kernel is the stable heart Hicks says to polish; the commitment layer is explicitly left
  provisional (see below).
- **Depends on.** — (first).
- **Assigned.** Dmitry (kernel interfaces) + Yavor (scaffolding & docs).
- **Reuse.** Current `main-temp` `Crypto.lean`/`Zkvm.lean` (refactor, don't rewrite). No branch code.
- **Frozen kernel (I4).** `Relation`, `ArgumentSystem`, `Extractor`, `KnowledgeSound`; abstract
  `ZkVM`, `TraceValid`, `Rstar`, `CTE`, `cte_iff_knowledgeSound`; plus the Lean-only consistency
  signatures `StepInterface`, `StepInterface.MemoryBridge`, and `StepInterface.BusBridge`.
  **Provisional (NOT frozen — expected to change):** `VectorCommitment`'s binding predicates —
  `PuncturedBinding` is known to be **insufficient** and is **replaced by `UpdateBinding`**
  in Issue 1; `Complete` is made explicit there; and `CollisionResistant` is now keyed and
  finder-based (Issue 2; efficiency/probability deferred to Issue 6). These live in `Crypto.lean` but are
  marked provisional in their docstrings and are free to change without a constitutional amendment.
- **New public surface (3 source declarations).** `StepInterface` (whose three structure fields are
  its committed-step API), `StepInterface.MemoryBridge`, and `StepInterface.BusBridge`. These are
  the minimum coordination surface needed by Issues 1, 3, and 5; `ZkVM.step` is reused as the
  canonical plain predicate rather than duplicated. All other changes reorganize existing
  declarations or add private validation examples.
- **Deliverables.** (a) `Crypto.lean` = definitions only, kernel vs provisional clearly separated;
  proofs/instances moved out. (b) `docs/` scaffolding ratified: `INVARIANTS.md`, `CORRESPONDENCE.md`,
  `CONVENTIONS.md`, `docs/sessions/TEMPLATE.md`, `docs/LESSONS_LEARNED.md`,
  `SKILLS/adversarial-review.md` ported from finality. (c) CI: `lake build` + `#print axioms` +
  a `CORRESPONDENCE` row-elaboration check and repo-wide I7 hygiene check. (d) Freeze the step
  contract in `Step.lean` / `docs/STEP_INTERFACES.md`: `ZkVM.step` is the plain predicate,
  `stepCommitted` is the memory-layer predicate, and `stepWithBus` feeds it through the bus bridge;
  concrete bodies belong to Issues 1, 3, and 5.
- **Math companion.** Establish `VanillaZkVM/math-companion.md` with the kernel definitions written
  out on paper; every later issue appends to it.
- **Review requirement.** Ordinary collaborator PR review; there is no additional joint
  Benedikt/George ratification gate for Issue 0. Dmitry signed the paper-facing core rows on
  2026-07-29. Independent re-derivation and rolling audits remain Issue 9.
- **Skills & conventions.** `/simplify` on the refactor; `/security-review` on the definitions.
  `CONVENTIONS.md` §1–2. No existing declaration changes behavior; validation and interface
  scaffolding may be additive.
- **Paper anchor.** The revision pinned in `docs/PAPER_REVISION.md`: ch03 (`R*`), ch05
  (`def:extractable`, `def:cte`, `rem:cte-ks`).
- **Scope amendment (approved 2026-07-29, Dmitry).** Add exactly three public step-interface
  declarations, close the discovered I7 enumeration/string-literal gaps, record the corrected
  fixed-`T` CTE semantics (with the available paper commit pinned for PR confirmation), and drop the
  previously stated Benedikt/George joint-review requirement.

## Issue 1 — Committed memory → `TwoStepWithMemory` (CTE from memory-commitment properties)
- **Goal.** Make the two-step VM operate on *committed* memory and prove it CTE **assuming**
  properties of the memory commitment scheme — reconstruct the full `Addr→Byte` memory from a
  committed-state trace + per-step opening witnesses. **Introduce `UpdateBinding` to replace the
  insufficient `PuncturedBinding`** and formalize `prop:memory-extractability`.
- **Depends on.** Issue 0.
- **Assigned.** **Redundant:** Yavor (base: `pr5`'s Bus-wired reconstruction core — his code) **and**
  Dmitry (`memory-integration`'s abstract-VM full-memory CTE); reconcile to one `Memory.lean`
  core at the end. *Review: George (and/or Benedikt).*
- **Reuse.** **`pr5`** — best base (trace-level `trace_mem_extract`, boundary-exact, only branch with
  concrete non-vacuity checks incl. `appendBitVC_not_updateBinding`; already replaces punctured with
  update binding). **`memory-integration`** — its full-memory `Twostep` integration + its
  `math-companion.md` (incorporate into the project companion). **`yl-memory-reconstruction`** — docs
  reference (identical Lean to pr5; skim `AXIOM_AUDIT.md`). **DROP `memory-recon`** (destructive,
  least complete). Re-apply hunks onto post-#4 `main-temp` (§4).
- **New public surface (max ~5).** `UpdateBinding` (+ break witness), `FullVMState`/`CommitInv`,
  the concrete `committedStep` predicate underlying `StepInterface.stepCommitted`,
  `step_mem_extract`, and `trace_mem_extract`. `TwoStepWithMemory` is realized as
  `TwoStep.System.toZkVMFullMemory`, an *instance* of the abstract `ZkVM` (I5), rather than as a duplicate
  security definition. Deprecate/remove `PuncturedBinding` in the same PR.
- **Deliverables.** Reconciled `Memory.lean` core, the `TwoStepWithMemory` instance, `cte_fullMemory`
  (CTE over *full* memory), `MemorySanity`-style non-vacuity instances, and a concrete proof of
  `StepInterface.MemoryBridge`.
- **Math companion.** Write the memory-extractability proposition and the read/write commitment
  equations into `math-companion.md` (Dmitry already drafted much of this on `memory-integration`).
- **Review requirement (human — George).** Confirm `UpdateBinding` matches `def:binding` and is
  the update-realizability guarantee missing from the retired punctured condition (the paper treats
  position binding and update binding as independent); that `CommitInv` is the right invariant; and
  that Yavor's and Dmitry's two integrations prove *the same* statement. Approve the Issue-1
  `CORRESPONDENCE` rows; run the vacuity probe.
- **Skills & conventions.** `/security-review` (definitions), `/simplify`, adversarial-review at
  session end. Derive from `VectorCommitment`; do not re-declare frozen kernel notions.
- **Paper anchor.** ch02 (`Com_mem`, `def:binding`), ch03 (`φ̂_read`/`φ̂_write`),
  `prop:memory-extractability`.

## Issue 2 — Reduction vocabulary + extract-or-break refactor
- **Goal.** Establish the *lightweight* reduction discipline (I9) as reusable vocabulary and refactor
  proofs into **extract-or-break** form: a break of a guarantee yields either a valid witness or an
  explicit assumption break (e.g. a collision), with the assumption applied only in a thin corollary.
- **Depends on.** Issue 0.
- **Assigned.** Jessica (her `extract-or-collision`/`cr-algorithmic` code). *Review: Benedikt/George.*
- **Reuse.** **`extract-or-collision`** — Jessica's `segment_extract_or_collision` +
  `segment_knowledgeSound` corollary; generalize it into reusable vocabulary (it currently targets a
  bus segment, but the *shape* is what we standardize). **`cr-algorithmic`** — her keyed
  CR design; adopted in Issue 2 as the keyed, finder-based `CollisionResistant` (efficiency/probability
  deferred to Issue 6).
- **New public surface (max ~3).** A `Reduction`/break-witness shape (a `structure`; adversary as a
  plain function per VCVio), an `extract-or-break` combinator, and the generalized statement.
  Advantage *numbers* are **not** introduced here (that's Issue 6); stay perfect.
- **Deliverables.** The reduction vocabulary module; a `docs/reuse-notes.md` entry on how to phrase a
  reduction so all later layers share one shape.
- **Math companion.** Write the extract-or-break template (game/break-witness) into the companion.
- **Review requirement (human — Dmitry, as cryptographer).** Bless the extract-or-break *shape*:
  does it compose across layers? Is the "break" a genuine assumption break? Confirm designing so a
  later swap to VCVio's `SecurityGame`/`Negligible` is mechanical.
- **Skills & conventions.** `/security-review`, `/simplify`. Adversaries as plain functions;
  efficiency a separate future concern.
- **Paper anchor.** `lem:segment` (bad-event structure), ch05 §5.2 reduction structure.

## Issue 3 — ISA operations: a small representative op set `{read, write, arith, hash, bin}`
- **Goal.** Replace the fully-opaque step predicate with a **small, representative** op taxonomy —
  memory `read`/`write`, `arith` (arithmetic), `hash` (hash-call precompiles, collapsing
  keccak/poseidon), and `bin` (binary/bitwise ops) — and the disjunctive `φ_step := ⋁_op φ_op`.
  **Deliberately do not model the paper's full 20-opcode taxonomy**; op *semantics* stay opaque
  black-box predicates. We model the *structure* (memory-free split, which class defers to a chip).
- **Depends on.** Issue 0. (Soft-coordinates with Issue 1 for `read`/`write`, Issue 5 for chip routing.)
- **Assigned.** Yavor (his memory work already defines `readC`/`writeC`/`readF`/`writeF`).
  *Review: George.*
- **Reuse.** Yavor's own read/write predicates from `pr5`. Otherwise new.
- **New public surface (max ~4).** An `ISA` operation type (the 5-class op set + per-op predicate
  split `φ_op`/`φ'_op`), the memory-free/memory-equation decomposition, and the disjunctive
  `stepPred`.
- **Deliverables.** `ISA.lean`: the 5 op classes, `φ'_op`/`φ_op` split, `φ_read`/`φ_write` with their
  memory equations, and `φ_step` as the disjunction; a lemma that non-memory ops don't mutate
  memory. The resulting `ISA.stepPlain` is used as the concrete `ZkVM.step`, not a parallel relation.
- **Math companion.** Write the 5-class step predicate and the read/write memory equations.
- **Review requirement (human — George).** Confirm the 5-class set is a faithful *representative*
  simplification of ch03 (fetch conjunct `code[pc]=op` present; `φ_step` neither stronger nor weaker
  than the disjunction over these classes). Approve the op-predicate `CORRESPONDENCE` rows, noting
  the deliberate simplification from 20 ops.
- **Skills & conventions.** `/simplify` (factor the classes via a family — I10), `/code-review`.
  Paper-vocabulary names.
- **Paper anchor.** ch01 (step relation, memory ops), ch03 (op taxonomy, `φ_step`) — simplified.

## Issue 4 — Multi-layer recursion → `MultiStepVM` (convert / combine / embed)
- **Goal.** Replace the flat two-layer merge with the paper's recursion tower over an **abstract
  leaf** relation: `R_2` convert (1-to-1), `R_3` combine (binary 2-to-1, self-recursive, well-founded
  by strictly-decreasing step counts), `R_4` embed (final, `T ≥ 2·N_seg`). Provide the
  **tree-unrolling** extraction lemma generalizing `chain_flatten` from a list to a binary tree
  (yielding the `(m-1)` combine-node count).
- **Depends on.** Issue 0. (Uses an abstract leaf — does **not** depend on the bus, Issue 5.)
- **Assigned.** Dmitry (his `cost-twostep` shows he works on the merge/two-step structure).
  *Review: George + Benedikt. Redundant tree-lemma attempt via the Issue-9 autonomous re-derivation.*
- **Reuse.** None directly; `chain_flatten` is the pattern to generalize.
- **New public surface (max ~6).** `RConvert`/`RCombine`/`REmbed` (derived via `Relation`), the
  binary-tree topology as data, the `combine_tree` unrolling lemma, and `MultiStepVM` as a `ZkVM`
  instance. Well-foundedness side conditions live inside the relation, not as public lemmas.
- **Deliverables.** `MultiStep.lean` with the three relations, the tree type + unrolling lemma, the
  `MultiStepVM` instance, and its CTE (perfect model) via composed extraction over an abstract leaf.
- **Math companion.** Write the tree topology, the well-founded measure, and the unrolling lemma.
- **Review requirement (human — George).** Confirm the well-founded measure (child step counts
  strictly `< N`; `N=N_seg` base vacuous by arithmetic, per `rem:wellfounded`); that unbalanced trees
  are admitted (only `N_L+N_R=N` + divisibility); and that `embed`'s `T≥2N_seg` is enforced. Confirm
  the redundant re-derivation proves the same statement.
- **Skills & conventions.** `/security-review`, `/simplify`. Generalize — don't fork — `chain_flatten`.
  Heavy branch-point comments on the induction (finality style).
- **Paper anchor.** ch04 (`R_2`,`R_3`,`R_4`, `fig:topo`), `lem:convert`/`combine`/`embed`,
  `rem:wellfounded`.

## Issue 5 — Bus functionality per segment, wired into a VM  *(scheduled late)*
- **Goal.** Build the segment/bus layer **properly**. The former `Bus.lean`
  playground prototype was removed from the active tree because it was not
  ground truth; consult it only in git history. Then lift
  single-segment extraction across a whole execution: `m` segments each with their own
  internally-consistent bus `B̂_i`, concatenated by `concatTrace`/`chain_flatten` into one length-`T`
  trace carrying per-segment `StepAux`/bus data. Slotted **late** because the recursion tower (Issue
  4) is built over an abstract leaf and does not need it.
- **Depends on.** Issue 0, Issue 3 (chips consume the op taxonomy). Soft-dep on Issue 2 (extract-or-break).
- **Assigned.** Yavor (author of the prototype). *Review: Benedikt.*
- **Reuse.** The deleted prototype from git history as *reference only* — reimplement to the frozen kernel and the
  Issue-3 ISA; do not treat its `segment_extract` as done. `cost-bus-reduction` reference for the
  future cost combinators. Reuse `concatTrace`/`chain_flatten` from the kernel (do not duplicate).
- **New public surface (max ~3).** A bus-backed segment relation + a `Bus`-backed VM as an *instance*
  of the abstract `ZkVM`, plus the lifting lemma (segment extraction ∘ concatenation).
- **Deliverables.** The proper segment/bus layer, a proof of `StepInterface.BusBridge`, a
  `Bus`-backed VM instance, and the per-execution lifting theorem threading per-segment `StepAux`.
- **Math companion.** Write the bus, `φ̂_step` bus-deferral, and the per-execution lift.
- **Review requirement (human — Benedikt).** Confirm the redone layer faithfully realizes
  `lem:segment` (bus unification / extract-or-collision), that per-segment buses are **not** claimed
  equal across segments (only internally consistent), and that concatenation preserves the boundary
  chaining `thm:main` Steps 4–5 need. Confirm `chain_flatten` is reused, not reimplemented.
- **Skills & conventions.** `/simplify`, `/security-review`. Reuse the frozen concatenation lemma (I5).
- **Paper anchor.** ch02 (bus, segments), `lem:segment`, `thm:main` Steps 4–5.

## Issue 6 — Make all security proofs explicit reductions (per layer)
- **Goal.** Rephrase every layer's proof (memory, bus, convert, combine, embed) in the explicit
  extract-or-break form of Issue 2: a failure of the layer's guarantee ⇒ a named assumption break
  (KS extraction failure, collision, position/update-binding break). Introduce
  **advantage-placeholder bookkeeping** so the composition mirrors `thm:main`'s weighted sum
  (`1, m-1, m, m·(…+cr), Σ_{k=1}^T(pos+upd)`) while keeping running time deferred (I9).
- **Depends on.** Issues 1, 2, 4, 5.
- **Assigned.** Dmitry (cost/reduction author) + Jessica (bus/segment reductions — her extract-or-collision).
  *Review: Benedikt + George, one per half.*
- **Reuse.** Issue 2's vocabulary; `cost-twostep`/`cost-bus-reduction` reference for how an explicit
  reduction `Alg` + its cost were written (for when running time is added).
- **New public surface (max ~4).** Per-layer reduction statements sharing Issue 2's vocabulary; no new
  *definitions* beyond that vocabulary.
- **Deliverables.** Each layer lemma restated as "guarantee-break ⇒ ∃ explicit assumption-break",
  composed outermost→innermost, with `thm:main`'s coefficient structure represented (placeholder
  advantages, not real probabilities).
- **Math companion.** Write the per-layer reductions and the summed bound (with placeholders).
- **Review requirement (human — Dmitry/Benedikt).** Confirm each reduction targets the *correct*
  assumption and that the coefficient structure matches `thm:main` (Hicks: *what* you reduce to
  matters). Explicitly check no reduction is vacuous.
- **Skills & conventions.** `/security-review` mandatory. Reductions = plain `def`s + `≤`/⇒ statements;
  design for a mechanical VCVio swap later.
- **Paper anchor.** ch05 §5.2 (all layer lemmas, `prop:memory-extractability`), `thm:main` bound.

## Issue 7 — Assemble the full Vanilla VM & state the main theorem
- **Goal.** Compose Issues 1+3+4+5+6 into the full `zkVM = ({φ_op}, Com_bus, Com_mem, Π_0..Π_4)` and
  state + prove (perfect model) the top-level CTE theorem as a single sum of named assumption breaks
  — the Lean analogue of `thm:main`. Tie the outermost CTE statement to `VMState`/`CommittedVMState`
  via `Com_mem` (the `Commit(mem_0/T)` step the abstract statement currently omits).
- **Depends on.** Issues 1, 3, 4, 5, 6.
- **Assigned.** Dmitry + Yavor (capstone). *Review: Benedikt + George.*
- **Reuse.** Everything above.
- **New public surface (max ~2).** The full `VanillaVM` instance + `cte_main`. Nothing else public.
- **Deliverables.** The assembled VM, `cte_main`, and a `docs/` note recording the paper's own
  idealization caveat (`rem:idealized`: relativized SNARKs don't exist → validates reduction
  *structure*, not concrete security).
- **Math companion.** Write `thm:main` and its assembly from the layer lemmas.
- **Review requirement (human — Dmitry + Benedikt).** Confirm `cte_main` is the faithful Lean form of
  `thm:main`, the boundary-commitment step is present, and the idealization caveat is documented.
  Approve the `thm:main` row (fidelity + completeness). Full `#print axioms cte_main`.
- **Skills & conventions.** `/security-review`, `/simplify`, adversarial-review. Final public surface
  + `cte_main` must be readable and ≈ paper length (I10) — measure it.
- **Paper anchor.** ch05 (`thm:main`, zkVM system definition, `rem:idealized`).

## Issue 8 — (Parallel, exploratory) concrete/asymptotic security, runtime, and dependency reuse
- **Goal.** Scope how/whether to lift the perfect model to real security (advantages, `negligible`,
  running time of reductions) and report feasibility/size/dependencies — **do not merge into core**
  (I8). Also the "not reinventing the wheel" reuse study (mathlib/VCVio/arklib).
- **Depends on.** Issue 0 (otherwise independent).
- **Assigned.** Jessica (reductions/concrete-security fit; benedikt-plan's "concrete vs asymptotic"
  and "reuse" tasks). *Review: Dmitry + Benedikt.*
- **Reuse.** **VCVio**: the *pattern* from `CryptoFoundations/Asymptotics/Negligible.lean` (~90 lines,
  near-liftable) + `Security.lean` (advantage decoupled from game; reduction/game-hop/hybrid
  meta-theorems) + `HardnessAssumptions/DiffieHellman.lean` (reduction-as-function template). **Cost:**
  `cost-twostep`'s `Cost.lean` (superset with `seqRange`) as the exact-cost reference; note VCVio's
  `WorstCasePolyTime`/`ExpectedPolyTime` are *documented but not implemented* — expect to build PPT
  predicates from scratch.
- **New public surface.** None in core. Output = a `docs/` report + an isolated prototype branch.
- **Deliverables.** `docs/security-model-report.md` (perfect vs asymptotic vs concrete recommendation;
  cost of a `PMF` re-foundation; when/if to import VCVio; a map of our frozen kernel to VCVio
  equivalents so a later swap is mechanical) + a throwaway prototype lifting **one** lemma to
  advantages as a size probe.
- **Math companion.** N/A (a report, not core Lean) — but the VCVio-mapping table lives in the report.
- **Review requirement (human — Dmitry + Benedikt).** Review the *recommendation*: is perfect still
  the right default? Is our `KnowledgeSound` translatable to VCVio's? Decide go/no-go on a future
  concrete-security issue. (Hicks: keep the door open, don't walk through yet.)
- **Skills & conventions.** Strictly out of `main-temp`'s core build (isolated branch/dir). Cheaper
  models + subagents to read VCVio; store findings in files.
- **Paper anchor.** ch05 advantages/`negl`; `rem:idealized`.

## Issue 9 — (Rolling, redundant) independent re-derivation + audit matrix + vacuity sweep
- **Goal.** The independent-certificate track Hicks endorsed: in a **separate** repo/branch, have
  agents formalize the statements from *informal* requirements **without** the paper, then match
  against the paper as an independent correctness certificate. Simultaneously keep `CORRESPONDENCE.md`
  current and run periodic vacuity/axiom sweeps.
- **Depends on.** Issue 0; then rolls alongside 1–7 (audits each as it lands).
- **Assigned.** Yavor + Dmitry (benedikt-plan's documentation/communication task), redundant
  re-derivation driven by an autonomous agent under their oversight. *Review: George.*
- **Reuse.** finality's `AUDIT.md`, `SKILLS/adversarial-review.md`, `spec_index` idea, session ledger;
  VCVio's `docs/agents/*.md` per-topic guide format once layers stabilize.
- **New public surface.** None.
- **Deliverables.** A maintained `CORRESPONDENCE.md` with reviewer sign-offs; periodic
  `docs/sessions/` audit entries; the independent re-derivation write-up; a `docs/agents/` guide set.
- **Math companion.** The re-derivation's own companion is compared against the main one.
- **Review requirement (human — George; re-derivation judged by Dmitry).** For each audited issue, a
  reviewer other than its author performs the `CONVENTIONS.md` §6 definition audit and signs the row.
  For the re-derivation, Dmitry judges whether the independently-derived statements *mean the same
  thing* as the paper's — a human "these coincide" is precisely the payoff.
- **Skills & conventions.** adversarial-review skill; fan-out independent skeptics; CONFIRMED-only
  findings; revert all injected probes.
- **Paper anchor.** whole paper (matrix); `rem:cte-ks`/`thm:main` for the re-derivation target.

---

## Branch disposition summary (from `docs/branch-analysis.md`)

| Branch | Author | Disposition | Used by |
|---|---|---|---|
| `pr5` | Yavor | **REUSE — best memory base** (Bus-wired, sanity checks, already update-binding) | Issue 1 |
| `memory-integration` | Dmitry | REUSE (abstract-VM full-memory CTE + math-companion), cross-validate | Issue 1 |
| `yl-memory-reconstruction` | Yavor | REFERENCE (docs; identical Lean to pr5) | Issue 1 |
| `memory-recon` | Yavor/Dmitry | **DROP** (destructive, least complete) | — |
| `extract-or-collision` | Jessica | **REUSE — generalize** (extract-or-collision shape) | Issue 2 |
| `cr-algorithmic` | Jessica | REUSE as provisional CR variant (keyed/algorithmic) | Issue 2/8 |
| `cost-twostep` | Dmitry | REFERENCE (most complete cost/`Cost.lean` superset) | Issue 6/8 |
| `cost-bus-reduction` | Dmitry | REFERENCE (cost combinators, toy) | Issue 6/8 |
| former `main-temp` `Bus.lean` (git history) | Yavor | **NOT ground truth** — deleted playground prototype; redo in Issue 5 | Issue 5 (ref) |

All cost/CR branches predate PR #4 — **re-apply hunks, don't merge wholesale** (`CONVENTIONS.md` §4).
