# SKILL — adversarial review (session-end audit)

Ported from `finality/SKILLS/adversarial-review.md` and adapted to this project
(`docs/CONVENTIONS.md` §6, `docs/INVARIANTS.md` I6/I7/I11). Run this at the **end**
of every substantial session, after the build is green, before requesting human review.

The point is not to re-run the normal review checklist. It is to **actively try to
break your own work** from several independent angles, each blind to the others, and
report only what actually reproduces.

## Method

1. **Fan out independent skeptics along named dimensions.** Spawn one agent per
   dimension below. Each starts cold (a fresh read of `INVARIANTS.md` +
   `CONVENTIONS.md` and the diff) and is *not* told what the others found. Diversity
   of angle is the point — redundancy along one angle catches less than one probe per
   failure mode.

2. **Triage every claim to CONFIRMED vs SUSPECTED.** A finding is real only once it is
   *reproduced* (the build fails, the probe elaborates, `#print axioms` shows the
   extra axiom). Report CONFIRMED findings with the exact reproduction; keep SUSPECTED
   ones separate and clearly labelled as unreproduced.

3. **Revert every injected probe.** Any weakened assertion, `sorry`, or `False`-probe
   an agent introduces to test vacuity MUST be reverted, and `git status` re-checked
   clean, before the session closes. A left-behind probe is a worse defect than the
   bug it was hunting.

## Dimensions

- **(a) Soundness / vacuity (I6).** Attempt to derive `False` from the headline
  theorem's assumption bundle. Are the hypotheses jointly satisfiable? Is there a
  model / instance / counterexample witness for each new definition (as
  `knowledgeSound_trivialAS` is for `KnowledgeSound`)? A theorem whose assumptions
  imply `False` is a bug, not a result.

- **(b) Kernel-truth re-verification (I4/I7).** Rebuild from clean
  (`lake build` from a fresh checkout of the branch). Run `#print axioms` on every
  headline theorem and confirm only `{propext, Classical.choice, Quot.sound}` appear.
  Confirm no frozen-kernel signature (the I4 list) changed without a corresponding
  `INVARIANTS.md` edit and CORRESPONDENCE re-approval.

- **(c) Gate / CI integrity.** Confirm the CI checks actually run and actually fail
  when they should. Temporarily break a CORRESPONDENCE row (rename a declaration) and
  confirm the row-elaboration check catches it; add a throwaway `axiom` and confirm the
  axiom gate catches it. Revert both.

- **(d) Docs / overclaim.** Does every `CORRESPONDENCE.md` row's status match reality
  (`stated` vs `proved`, `sorry` ledger)? Does the math companion agree with the Lean?
  Are there docstrings claiming more than the proof delivers ("faithful but partial")?

## Output

Append the result to the session ledger (`docs/sessions/<date>-<issue>.md`), using
`docs/sessions/TEMPLATE.md`: the dimensions run, CONFIRMED findings with reproductions,
SUSPECTED findings, and confirmation that all probes were reverted (`git status` clean).
