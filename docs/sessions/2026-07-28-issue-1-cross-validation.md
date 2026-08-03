# Session 2026-07-28 — Issue 1 cross-validation

## Bootstrap

- **Issue:** `docs/PLAN.md` → Issue 1 (Committed memory →
  `TwoStepWithMemory`; GitHub #7).
- **Branch:** `yl-issue-1`, forked from `main-temp` and fast-forwarded to the
  completed Issue-0 implementation on `freeze-kernel`.
- **Read at start:** `INVARIANTS.md`, `CONVENTIONS.md`, `PLAN.md`,
  `CORRESPONDENCE.md`, every Lean file on `main-temp`, the paper digest and
  branch analyses, GitHub Issues #6/#7, the current whitepaper
  `origin/proof`, Dmitry's `memory-integration`/`memory-twostep`, and Yavor's
  `yl-memory-reconstruction`.
- **Build at start:** `lake build` and
  `python3 scripts/ci_checks.py --check-correspondence --check-axioms` green at
  `27487f1`.

## Cross-validation decision

- Dmitry's and Yavor's branches use the same `UpdateBinding`, `FullVMState`,
  `CommitInv`, and committed/full read-write predicates.
- Yavor's branch makes the one-step valid-or-binding-break reduction explicit
  and retains descriptors through its Bus witness. Those features belong to
  Issues 5–6 under the current dependency plan and are not ported here.
- Dmitry's branch supplies the missing Issue-1 target: a compact generic trace
  fold plus `TwoStep.System.toZkVMFull` and `cte_full`, without adding global
  decidable-equality requirements. This is the integration base.
- Yavor's `exactVC` and append-bit countermodel are retained. The documentation
  is corrected to say that position binding and update binding are independent:
  the append-bit construction shows that position binding and the retired
  punctured-binding condition do not suffice for update binding; it does not
  establish a logical implication from update binding to position binding.
- `main-temp`'s Bus prototype is not touched (Issue 5), and the frozen kernel is
  not changed (I4).

## What changed

- `Crypto.lean` now defines the provisional `Complete` and paper-faithful
  `UpdateBinding` predicates, removes `PuncturedBinding`, and includes the
  lightweight `UpdateBindingBreak` winning record. The frozen declarations are
  byte-for-byte unchanged.
- New `Memory.lean` provides `FullVMState`, `CommitInv`, the classified
  committed/full memory predicates, the one-step lift, write reconstruction,
  the inductive commitment-invariant fold, and descriptor selection for an
  existential committed-step relation.
- `Twostep.lean` retains one `MemStep` descriptor per extracted segment step,
  derives both committed and full-memory `ZkVM` instances, and proves
  `traceValid_full` and `cte_full`.
- New `MemorySanity.lean` contains:
  - `exactVC`, which jointly satisfies completeness, position binding, and
    update binding;
  - the append-bit scheme, which also satisfies the punctured
    non-equivocation formula but has a certified update-binding break.
- `math-companion.md` and `CORRESPONDENCE.md` now state the exact memory
  equations, reconstruction invariant, theorem scope, and remaining semantic
  dependencies. README, paper digest, and lessons learned were synchronized.
- CI now checks the memory fold, full-memory CTE, satisfiability model, and
  countermodel as headline declarations.

### Public surface (I5)

The intended interface groups are:

- commitment properties: `Complete`, `UpdateBinding` and its break record;
- memory model: `FullVMState`, `CommitInv`, `MemStep`, `stepC`/`stepF`;
- reconstruction: `step_mem_extract`, `trace_mem_extract`;
- abstract-VM instance: `TwoStep.System.toZkVMFull`,
  `TwoStep.System.cte_full`.

The read/write predicates and reconstruction functions are derived plumbing
used by the later ISA integration. No frozen relation, argument-system,
extractor, or CTE notion was redeclared.

## Axiom / `sorry` ledger diff

- `lake build`: 8,589 jobs, exit 0.
- `scripts/ci_checks.py --check-correspondence --check-axioms`: 30 audited
  declarations elaborate.
- `trace_mem_extract` and `TwoStep.System.cte_full` depend only on
  `[propext, Classical.choice, Quot.sound]`.
- `MemorySanity.exactVC_bindingAssumptions` depends only on `[Quot.sound]`;
  `appendBitVC_not_updateBinding` is axiom-free.
- Repository-wide Lean scan found no `sorry`, `admit`, `native_decide`, or new
  `axiom`.

## CORRESPONDENCE rows touched

- Core/provisional: added `Complete`, realized `UpdateBinding`, and removed the
  obsolete `PuncturedBinding` row.
- Added the memory invariant, committed/full read-write equations,
  `stepC`/`stepF`, `step_mem_extract`, `trace_mem_extract`, and both I6 models.
- Split the toy result into committed `cte` and full-memory `cte_full`.
- Removed the two realized Issue-1 entries from the planned table. All reviewer
  cells remain `_unreviewed_`.

## Adversarial review

- **Commitment-swap attack:** closed for writes. A verifier-accepted post-root
  outside the image of `commit` is exactly an `UpdateBindingBreak`; the
  append-bit scheme demonstrates why position/punctured non-equivocation alone
  was insufficient.
- **Unknown-memory attack:** the theorem does not claim to invert an arbitrary
  root. Reconstruction starts from the full initial memory supplied in the
  statement, then preserves or point-updates it while proving `CommitInv`
  inductively.
- **Boundary attack:** `traceValid_full` proves the final full state equals the
  claimed terminal state using the terminal commitment invariant plus
  commitment injectivity.
- **Vacuity:** a temporary, non-committed Lean probe instantiated a one-segment,
  one-step system over `exactVC`, proved both KS assumptions, exhibited an
  accepting final proof, proved all hypotheses jointly satisfiable, and applied
  `cte_full`. It compiled successfully.
- **Zero-length segments:** `cte` and `cte_full` require `0 < Nseg`. If `m = 0`,
  `RFinal` still forces the two boundary states to coincide.
- **Arbitrary verifier:** acceptance is useful only through the explicit
  `KnowledgeSound` assumptions for the segment and final relations.
- **Frozen-kernel integrity:** `Zkvm.lean`, `Trace.lean`, and
  `CryptoSanity.lean` are unchanged; the frozen declaration block in
  `Crypto.lean` is unchanged.
- **Confirmed limitation:** `MemFreePredicate` sees only PCs/register files, so
  it cannot bind a separate descriptor address/value to registers. This branch
  is therefore the memory-only slice, not the complete `φ_step`; Issue 3 must
  add those equations and Issue 5 must add the bus.
- **Deferred by the ratified plan:** `chooseDescr` uses permitted
  `Classical.choice`, and binding assumptions are applied directly. Executable
  extract-or-break reductions, advantages, and runtime inspection remain
  Issues 2, 6, and 8.
- **Documentation correction:** the current paper explicitly calls position
  binding and update binding independent. The countermodel proves the former
  (even with punctured non-equivocation) does not imply the latter; it does not
  prove update binding logically implies position binding.

## Build at end

- `lake build`: green (8,589 jobs).
- Correspondence/axiom CI: green.
- `git diff --check`: green.

## Handoff note

- Human review remains required from George:
  1. compare `UpdateBinding` directly with `def:binding`;
  2. approve `CommitInv` and the known-initial-memory reconstruction strategy;
  3. confirm the retained Dmitry trace/`cte_full` integration and Yavor sanity
     models represent the best reconciliation;
  4. classify the memory rows as faithful but intentionally partial until the
     descriptor/register and bus conjuncts land.
- The review wording now asks whether `UpdateBinding` supplies the realizability
  guarantee missing from punctured non-equivocation; it does not claim a logical
  implication between the paper's independent binding properties.

---

## Continuation — 2026-08-02 (after Issue 0 merged)

- Merged `origin/main-temp@584476e` into `yl-issue-1` with `--no-commit`, preserving
  the paper pin, frozen `StepInterface`, hardened I7 checks, and Dmitry's signed
  Issue-0 correspondence rows. No commit or push was made.
- Replaced the draft-only `TwoStep.System.stepRel` with the memory layer's single
  public binary `committedStep := ∃ w, stepC …`.
- Added `step_reconstruct`, which constructs the represented full post-state from
  only the pre-invariant and a committed step. This is stronger than the
  two-endpoint `step_mem_extract` in precisely the direction needed for induction.
- Its proof establishes the reconstructed write invariant once and proves the
  concrete post-state semantics directly, avoiding a second logical use of the
  binding hypotheses that would obscure later advantage accounting.
- Added `TwoStep.System.memoryStepInterface` and proved the concrete frozen
  `TwoStep.System.memoryBridge`; `toZkVMFull.step` remains the canonical plain
  predicate.
- Made the changed-write non-vacuity probe permanent in `MemorySanity.lean` and
  added private `TwostepSanity.lean`, where identity extractors, an accepting final
  proof, and `exactVC` jointly instantiate every hypothesis of `cte_full`.
- Added a bridge-level append-bit attack: an accepted committed write starts from
  a represented pre-state but its verifier-accepted post-root is outside the image
  of `commit`, so no represented post-state exists without update binding.
- Updated the math companion, step-interface ownership note, correspondence rows,
  CI headline list, paper digest, README, and lessons learned to distinguish the
  conditional paper proposition from constructive trace reconstruction.
- **Final verification:** `lake build` completed all 8,592 jobs; the combined CI
  self-test/correspondence/axiom/hygiene run built all 12 discovered project
  modules, elaborated 33 audited declarations, and inspected 611 project
  declarations. No forbidden proof holes or non-permitted axioms were found.
- Final headline footprints for `step_reconstruct`, `memoryBridge`,
  `trace_mem_extract`, and `cte_full` are subsets of
  `{propext, Classical.choice, Quot.sound}`. `git diff --check` is clean.

## PR preparation — 2026-08-04

- Rebuilt `yl-issue-1` as one clean Issue-1 commit directly on
  `origin/main-temp@584476e`. The resulting source tree is identical to the
  previously reviewed draft, but the old Bus prototype commit is no longer in
  the branch history.
- `VanillaZkVM/Bus.lean` remains exactly the version inherited from
  `main-temp`; it is absent from the Issue-1 diff and remains deferred to Issue
  5.
- Added [`../MEMORY_RECONSTRUCTION.md`](../MEMORY_RECONSTRUCTION.md), a
  human-readable review guide for the files, definitions, headline theorems,
  and explicit scope boundary of Issue 1.
- Re-ran `lake build` (8,592 jobs) and the combined CI
  self-test/correspondence/axiom/hygiene check (33 audited declarations and 611
  project declarations). All checks passed with no forbidden proof holes or
  non-permitted axioms.
