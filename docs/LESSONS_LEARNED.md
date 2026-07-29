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
  cherry-pick / re-apply the relevant hunks onto current `main-temp`, never merge the
  stale branch.
  **Guard:** CONVENTIONS.md §4; branch dispositions in `docs/branch-analysis.md`.

- **`main-temp`'s `Bus.lean` is a prototype, not ground truth.** Its `segment_extract`
  etc. are Yavor's playground and are redone in Issue 5. Do not build on them or treat
  their CORRESPONDENCE rows as audited.
  **Guard:** CONVENTIONS.md §4; the "⚠ PROTOTYPE" banner in CORRESPONDENCE.md.

## Definitions / abstraction (the load-bearing 80%, I3)

- **Do not over-freeze.** The commitment/binding layer is deliberately *provisional*:
  `PuncturedBinding` is insufficient and is replaced by `UpdateBinding` (Issue 1).
  Freezing it now would force a constitutional amendment to fix a known-wrong def.
  Only the I4 kernel list is frozen.
  **Guard:** INVARIANTS.md I4; provisional docstrings in `Crypto.lean`.

- **"Faithful but partial" is a distinct failure mode.** A Lean statement can mean the
  paper statement yet cover only a fragment of it. Fidelity and completeness are
  separate reviewer columns for a reason.
  **Guard:** CORRESPONDENCE.md `Fidelity` **and** `Complete` columns; CONVENTIONS.md §6.1.

- **Agents anchor on training-data analogues for novel-but-familiar notions.** A
  definition that "looks like" a standard one may be silently bent toward the textbook
  version. Novel material (I3) is written interactively or with heavy up-front docs.
  **Guard:** INVARIANTS.md I11; human definition audit (CONVENTIONS.md §6.1).

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
