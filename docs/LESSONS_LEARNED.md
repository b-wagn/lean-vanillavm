# LESSONS LEARNED

Recurring footguns, clustered by theme. **Every lesson carries a guard** — a CI check,
an invariant, or a checklist item — because "a finding without a guard will recur"
(CONVENTIONS.md §8). When a session hits a new recurring problem, add it here with its
guard; when a guard becomes a CI check, note that.

## Lean / build

- **Imports come before the module docstring.** `/-! # … -/` before any `import` is a
  real compile error. Order is: `import …`, blank line, then the module docstring.
  Logged twice in `finality`.
  **Guard:** CONVENTIONS.md §1 (file prologue, fixed order); caught by `lake build` in CI.

- **`autoImplicit` off means every variable is explicit.** A "mysterious" universe or
  type error is often a variable Lean would have auto-bound elsewhere. Declare it.
  **Guard:** `autoImplicit = false` in `lakefile.toml`; do not silence the linter locally.

## Git / branches

- **Stale branches predate PR #4 and carry drift.** Merging a cost/CR/memory branch
  wholesale spuriously deletes `trivialAS` (and other post-#4 declarations). Always
  cherry-pick / re-apply the relevant hunks onto current `main`, never merge the
  stale branch.
  **Guard:** CONVENTIONS.md §4; branch dispositions in `docs/branch-analysis.md`.

- **The deleted `Bus.lean` prototype was not ground truth.** Its declarations
  were Yavor's playground and are redone in Issue 5. Do not restore or build on
  them as if they were an audited checkpoint.
  **Guard:** CONVENTIONS.md §4; the planned Issue-5 rows in CORRESPONDENCE.md.

## Definitions / abstraction (the load-bearing 80%, I3)

- **Do not over-freeze.** The commitment/binding layer is deliberately *provisional*:
  `PuncturedBinding` is insufficient and is replaced by `UpdateBinding` (Issue 1).
  Freezing it now would force a constitutional amendment to fix a known-wrong def.
  Only the I4 kernel list is frozen.
  **Guard:** INVARIANTS.md I4; provisional docstrings in `Preliminaries/VectorCommitment.lean`.

- **"Faithful but partial" is a distinct failure mode.** A Lean statement can mean the
  paper statement yet cover only a fragment of it. Fidelity and completeness are
  separate reviewer columns for a reason.
  **Guard:** CORRESPONDENCE.md `Fidelity` **and** `Complete` columns; CONVENTIONS.md §6.1.

- **"Needed for this reduction" does not mean logical implication.** The paper
  defines position binding and update binding as independent properties.
  `appendBitVC` proves that the punctured non-equivocation condition plus position
  binding does not imply update binding; it does not prove that update binding
  implies position binding.
  **Guard:** the `def:binding` companion text and the append-bit countermodel;
  reject "strictly stronger" wording unless both implication directions have
  actually been checked.

- **An opaque predicate cannot constrain values absent from its type.**
  `MemFreePredicate` sees only PCs and register files, so it cannot by itself tie a
  separate `MemStep.addr`/`value` field to particular registers. The current
  theorem is therefore a memory-only slice; the ISA layer must add those equations.
  In prose, name this formal type as `MemStep` or a “`MemStep` witness”; the
  generic term “descriptor” is neither a Lean declaration nor paper vocabulary.
  **Guard:** explicit limitation in `VMs/Memory.lean` and `CORRESPONDENCE.md`; Issue 3
  owns the concrete `MemStep`/register wiring, and review rejects generic
  synonyms for formal witness types.

- **A two-endpoint refinement is not an inductive reconstruction theorem.**
  `step_mem_extract` faithfully proves the paper's conditional proposition when
  `CommitInv` is supplied for both endpoint states. A trace extractor additionally
  needs to construct the next full memory and prove `CommitInv` for it from the
  current represented state; assuming that conclusion would hide the
  commitment-swap gap.
  **Guard:** frozen `StepInterface.MemoryBridge`; Issue 1's `step_reconstruct` and
  `TwoStep.System.memoryBridge` existentially produce the represented next state.

- **Agents anchor on training-data analogues for novel-but-familiar notions.** A
  definition that "looks like" a standard one may be silently bent toward the textbook
  version. Novel material (I3) is written interactively or with heavy up-front docs.
  **Guard:** INVARIANTS.md I11; human definition audit (CONVENTIONS.md §6.1).

## Naming / documentation

- **Parallel predicate families get namespaces, not letter suffixes.** `stepC`/`stepF`
  made every reader carry a decoder ring; `CommittedMemory.step` / `FullMemory.step`
  names the state type at each use site, and the type checker already enforces the
  split. Corollary: never `open` such a namespace — opening erases exactly the
  distinction it encodes.
  **Guard:** "use qualified names, do not `open`" notes in `VMs/Memory.lean`; review
  rejects new one-letter variant suffixes on paired declarations (CONVENTIONS.md §1).

- **Comments must survive without the conversation that produced them.** Session-local
  metaphors ("the two worlds") and undefined adjectives ("classified", 12 occurrences)
  read as jargon to a fresh reader — the target reader had to ask what "classified"
  meant. Use paper vocabulary (citable in the `Paper:` line) or describe the mechanism
  ("a case split over the `MemStep` witness"). Same family as the "descriptor" rule
  above.
  **Guard:** docstring review checks vocabulary against the paper and Lean identifiers
  (CONVENTIONS.md §6).

- **A rename's risk lives in the docs, not the Lean.** `lake build` fully verifies the
  code side of a pure rename; drift lands in prose. Update living docs
  (CORRESPONDENCE.md, MEMORY_RECONSTRUCTION.md, math-companion.md); leave historical
  records (docs/sessions/, branch-analysis.md) describing old states. Footgun: in a
  CORRESPONDENCE.md name cell, a bare name inherits the namespace of the *previous*
  dotted name, so rows mixing namespaces must fully qualify every name.
  **Guard:** `ci_checks.py --check-correspondence` elaborates every audited row
  (caught the `committedStep` mis-prefix live); repo-wide grep for the old name
  before declaring a rename done.

## Vacuity / axioms

- **A theorem with unsatisfiable hypotheses is a bug (I6).** Every headline theorem
  needs a model / instance / counterexample witness (cf. `knowledgeSound_trivialAS`,
  pr5's `appendBitVC_not_updateBinding`).
  **Guard:** vacuity probe in the adversarial-review skill; INVARIANTS.md I6.

- **Axiom set is fixed at `{propext, Classical.choice, Quot.sound}`.** No `native_decide`,
  no new `axiom`, no untracked `sorry`.
  **Guard:** headline `#print axioms` plus the repo-wide source/module hygiene gate in CI
  (INVARIANTS.md I7).

- **The default Lake target is not the whole source tree.** A new `.lean` file that is not
  imported by `VanillaZkVM.lean` is ignored by bare `lake build`; the umbrella file itself is
  also missed by a `VanillaZkVM/**/*.lean`-only source glob. Either gap can hide an anonymous
  `sorry` or direct `sorryAx`.
  **Guard:** `scripts/ci_checks.py` inventories the umbrella plus every submodule, explicitly
  builds/imports each discovered module, and self-tests the enumeration.

- **A hygiene scanner must lex non-code, not merely delete comments.** Deleting comments
  shifts diagnostic line numbers, and scanning string literals makes harmless prose such as
  `"sorry"` fail CI.
  **Guard:** the CI lexer blanks nested comments and strings while preserving newlines;
  `--self-test` exercises both behavior and direct-`sorryAx` detection.
