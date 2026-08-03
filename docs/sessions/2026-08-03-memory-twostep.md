# Session 2026-08-03 — memory-twostep (Issue 1 close-out)

Continuation of [`2026-07-28-memory-twostep.md`](2026-07-28-memory-twostep.md). No new mathematical
content: this session ran the two remaining mandated skills (CONVENTIONS §5), fixed the branch
topology, and closed the documentation gaps left by the Issue-1 implementation session.

## Bootstrap
- **Issue:** PLAN.md → Issue 1 (GitHub #7). Branch `memory-twostep`, 4 commits ahead of `main-temp`.
- **Read at start:** PLAN.md Issue 1, CONVENTIONS §4–§8, CORRESPONDENCE.md, the 07-28 ledger.
- **Build at start:** green (`lake build` 8591 jobs; GitHub CI green on the pushed tree).

## Branch topology fix (was wrong)
The Issue-1 commits (`ab5fccc`, `10edab5`, `59c9fb2`, merge `ddfe51d`) had been pushed **directly onto
`main-temp`**, bypassing CONVENTIONS §4 ("branch per issue, PR'd back into `main-temp`") and leaving
George's mandated review with nothing to review. Corrected:
- `origin/main-temp` force-rewound to **584476e** (the ratified PR #16 merge) — no other author's
  commits were in the discarded range, all four were Dmitry's Issue-1 work.
- `origin/memory-twostep` force-updated from the stale pre-rebase `7b4e1ad` to **ddfe51d**, so the
  Issue-1 work now lives on its own branch, 4 commits ahead of `main-temp`, ready for a PR.
- Local safety ref `backup/main-temp-ddfe51d` kept; `memory-twostep-pre-rebase` still holds `7b4e1ad`.
- Note `59c9fb2` and `10edab5` are the same change committed twice (identical trees at `59c9fb2` and
  `ddfe51d`); the history was kept verbatim rather than linearized, by request.

## Undocumented 2026-08-02 pass, recorded retroactively
Commit `10edab5`/`59c9fb2` ("some fixes") was a surface-minimization + terminology pass that the 07-28
ledger predates:
- `readC`/`writeC`/`readF`/`writeF`, `commit_update`, `commitInv_write` → `private` (I5). The public
  memory surface is now `FullVMState`, `CommitInv`, `MemFreePredicate`, `MemStep`, `stepC`/`stepF`,
  `step_mem_extract`, `commitInv_step`, `trace_mem_extract`, `stepReconstruct`, `reconstructTrace`,
  `chooseStepWitness`(+`_spec`), `mem_eq_of_commit_eq`.
- `chooseDescr` → `chooseStepWitness` (+`_spec`); "descriptor" → "step witness", "classified" →
  "multi-option" throughout the docstrings, `math-companion.md`, and the CORRESPONDENCE row text.

## `/simplify` (CONVENTIONS §5 — was outstanding)
Four blind cleanup agents (reuse / simplification / build-cost / altitude) over `584476e..HEAD`.

**Applied** (net −14 lines of Lean; no theorem statement changed, no public surface changed):
- `MemorySanity.lean`: deleted the dead private block `singleWriteMemory` +
  `exactVC_accepts_changed_write` (no consumer anywhere; `exactVC_updateBinding` already witnesses the
  positive model). Deleted the duplicate `/- DK: … -/` prologue comment (CONVENTIONS §1: imports →
  module docstring; the docstring below it said the same thing). `appendBitVC_complete` now delegates
  to `exactVC_complete` instead of re-proving it, matching its sibling `appendBitVC_positionBinding`.
- `Memory.lean`: `step_mem_extract` — hoisted the two moves every branch repeats (`hfree`, the
  memory-free transport, 3 verbatim copies; `hsame`, equal committed memories ⇒ equal memories, 2
  copies) above `cases w`; dropped the no-op `unfold CommitInv` (`obtain` unfolds plain `def`s).
  `commitInv_step` — the `.read` and `.other` branches were the same proof modulo destructuring arity;
  factored into one `hkeep` and dropped three unused binders.
- `Twostep.lean`: `cte_full`'s extractor no longer spells `E ⟨toCommitted x.S0, toCommitted x.ST⟩ p`
  twice (now a `let`); dropped the unused `set … with hST'` binder; `le_refl` → `Nat.le_refl`.

**Deferred, deliberately — these change the public surface or the layering and belong to George's
definition audit or a follow-up issue, not to a mechanical cleanup pass:**
- *Altitude, highest value and free only until Issue 3 lands:* `MemFreePredicate` is shared by all
  three `MemStep` branches, but the paper (and Issue 3's mandate) has a per-op `φ'_op`; and
  `MemStep.other` carries no payload, so Issue 3's `arith`/`hash`/`bin` and Issue 5's per-step
  chip/bus data have nowhere to go. Indexing the predicate by the op and parameterizing
  `MemStep`'s `other` are free today (no proof inspects either) and a re-signing of ~15 declarations
  plus four CORRESPONDENCE rows afterwards.
- `STEP_INTERFACES.md:83` assigns `MemoryBridge`'s proof to `Memory.lean`; it was discharged in
  `Twostep.lean` instead (`TwoStep.System.memoryBridge`), even though the proof uses nothing about the
  toy. Either generalize it into `Memory.lean` or amend the contract doc.
- `stepRel` (a public binary committed-step relation) sits in the toy, while `STEP_INTERFACES.md:32`
  calls that the memory layer's job; the committed/full existential projections are inlined in three
  places.
- `toCommitted` (in `Twostep`) and `CommitInv` (in `Memory`) are the same fact stated twice — a
  `commitInv_iff : CommitInv Ŝ S ↔ Ŝ = toCommitted S` bridge would collapse the terminal-state
  argument; the committed→full `ZkVM` lift (`toZkVMFull`/`traceValid_full`/`cte_full`) is generic in
  everything but its `System` parameterization, so Issue 7 currently has to redo it.
- `chooseStepWitness` recovers by `Classical.choice` a witness the two-layer extraction already had;
  threading it through would remove the choice round-trip and is what Issue 5/6 will need.
- The break scaffolding (`UpdateBindingBreak`/`IsUpdateBindingBreak`/`not_isUpdateBindingBreak`, ~50
  lines for one 3-line consequence) is documented forward scaffolding for Issue 6; kept as-is, but it
  is a "do we pay for it now?" question for the reviewer.
- Folding `MemorySanity.lean` into `CryptoSanity.lean` (it imports only `Crypto` and every declaration
  is about the commitment layer, which is `CryptoSanity`'s stated remit) — a rename cascade through
  `CORRESPONDENCE.md` and `Crypto.lean`'s docstring, so not done unilaterally.
- **Build cost, repo-wide (out of Issue-1 scope, worth its own PR):** the whole project depends on
  `import Mathlib` through `Crypto.lean` for exactly three uses — `Function.update` in the dead
  `Zkvm.memUpdate`, one `ring` in `Trace.lean` (`Nat.succ_mul`), and one `le_refl` (removed above).
  Dropping those would take `lake build` off Mathlib entirely (~750 s cold today).

## `/security-review` (CONVENTIONS §5 — was outstanding)
Run over the branch diff. **No finding at the reporting bar.** The `.lean` files are inert (no
`#eval`/`macro`/`elab`/`run_cmd`/`IO`/`native_decide`/`unsafe` anywhere); `ci_checks.py` builds its
generated Lean only from identifiers matching `^[A-Za-z_][A-Za-z0-9_.']*$`, so a crafted
`CORRESPONDENCE.md` cell cannot inject Lean or shell (verified against the real parser), and both
`subprocess` calls are argument lists with no `shell=True`. One sub-bar MEDIUM, **pre-existing from
Issue 0 and not Issue 1's to fix**: `ci.yml` pipes `elan-init.sh` from a mutable `master` ref into
`sh` and declares no `permissions:` block, so an upstream compromise would run in a push-triggered job
with a possibly write-capable `GITHUB_TOKEN` and persist via the toolchain cache. Suggested follow-up:
pin the installer to a commit SHA + checksum, and add `permissions: contents: read`.
Note the *definitional* security review Issue 1 actually cares about (is `UpdateBinding` the right
notion, is the assumption bundle non-vacuous) is the adversarial-review dimension (a) already recorded
in the 07-28 entry plus George's non-delegatable audit — not something this skill covers.

## Documentation consistency (retired `PuncturedBinding`, naming, trackers)
- `INVARIANTS.md` I4, `CONVENTIONS.md` §4, `README.md`: "`PuncturedBinding` is *being* retired" →
  retired (the declaration no longer exists); `Complete`'s migration into `Crypto.lean` recorded as done.
- `paper-digest.md`: the pre-Issue-1 baseline paragraph and gap (a) now carry an explicit update note —
  the live pair is `PositionBinding` + `UpdateBinding` (+ `Complete`), `prop:memory-extractability` is
  formalized, and what remains open there is Issue 3 (per-op predicates) and Issue 6 (probabilities).
- **Naming gap recorded:** no Lean declaration is called `TwoStepWithMemory`; PLAN.md Issue 1 now states
  that the deliverable is the triple `TwoStep.System.toZkVMFull` / `toCommitted` / `cte_full`.
- `README.md` checkpoints: C3 (Issue 0) ticked; C4 marked `[~]` — code complete and green, pending
  George's definition audit and the CORRESPONDENCE sign-offs.

## Axiom / `sorry` ledger diff
- No change. `sorry`/`admit`/`axiom` added: none. Headline axiom footprints unchanged
  ({`propext`, `Classical.choice`, `Quot.sound`}); the `/simplify` edits removed no `Classical` use
  (all remaining uses are load-bearing — `VC.Index` has no `DecidableEq`).

## CORRESPONDENCE rows touched
- None. All 9 Issue-1 rows (2 Core: `Complete`, `UpdateBinding`; 6 memory-extractability;
  `cte_full`) remain `_unreviewed_` with empty Fidelity/Complete — that is George's per-row act.

## Build at end
- `lake build`: green (8591 jobs; `Memory`, `MemorySanity`, `Twostep` rebuilt after the `/simplify`
  edits). `python scripts/ci_checks.py --self-test --check-correspondence --check-axioms
  --check-hygiene`: green. Not committed (CONVENTIONS §4 — human commits).

## Handoff note — what is left to close #7
1. **Open the PR** `memory-twostep` → `main-temp` (the branch is now correctly positioned for it) and
   request George's review; CI will re-run on the PR.
2. **George's non-delegatable audit** (unchanged from the 07-28 entry): `UpdateBinding` ⇔ `def:binding`;
   position binding does not imply it, so it is a genuinely additional requirement; `CommitInv` is the
   right invariant; the `memory-integration` and `pr5` integrations prove the same statement; run the
   vacuity probe. Then **sign the 9 CORRESPONDENCE rows** (fidelity *and* completeness — the section
   carries a deliberate "faithful but partial" scope note).
3. **Decide the deferred `/simplify` items above**, in particular the two that are cheap now and
   expensive after Issue 3 lands (per-op `MemFreePredicate`, `MemStep.other` payload).
4. **Housekeeping** per PLAN's branch-disposition table: PR #1 (`memory-integration`) is still open
   though absorbed; PR #5 is reference-only; `memory-recon` is marked DROP but still exists locally and
   on `origin`. Issue #6 (Issue 0) is also still open although PR #16 merged.
