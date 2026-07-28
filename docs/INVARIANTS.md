# INVARIANTS — the project constitution

These are the non-negotiable rules for the lean-vanillavm formalization. They hold at **all**
times; changing any of them requires explicit human sign-off (a PR that edits this file, approved
by at least one of Benedikt/Dmitry). Both humans and agents check work against this list, and cite
the invariant number (I1, I2, …) when a decision depends on it. Modeled on the `finality` repo's
`INVARIANTS.md`, adapted per the Hicks meeting (see `docs/hicks-digest.md`).

- **I1 — Ground truth is the paper.** The whitepaper `zkvm-whitepaper/sampleVM/{ch01..ch05}.tex`
  (the "Vanilla zkVM") is the specification. Any Lean definition or theorem that formalizes a paper
  notion must cite the exact paper label/section in its docstring and appear as a row in
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md). Where the Lean deliberately differs from or generalizes
  the paper, the difference is stated in the docstring, not left implicit.

- **I2 — Scope is fixed and only widened deliberately.** The active scope is exactly the issues in
  [`PLAN.md`](PLAN.md). New scope is added only by editing `PLAN.md` with an approval date and a
  bounded item count. Everything else is out of scope until re-scoped the same way. The scope test
  for any piece of work is: *does this serve the target CTE theorem for the full vanilla VM?*

- **I3 — Definitions are load-bearing; polish them, not the proofs.** ~80% of review effort goes
  into a small set of **core definitions** (`KnowledgeSound`, `CTE`, the abstract `ZkVM`,
  commitment binding notions, and the reduction/advantage vocabulary). These are frozen interfaces
  (I4). Helper lemmas and proof internals matter only insofar as they type-check and are
  non-vacuous (I6); they may be produced/refactored freely.

- **I4 — Frozen *kernel* (not all of `Crypto.lean`).** Only the stable heart is frozen: the
  structures `Relation`, `ArgumentSystem`, `Extractor` and the predicate `KnowledgeSound` (from
  `Crypto.lean`), plus the abstract `ZkVM`, `TraceValid`, `Rstar`, `CTE`, and
  `cte_iff_knowledgeSound` (from `Zkvm.lean`). Downstream work extends or instantiates these; it does
  not fork or duplicate them. Changing a frozen kernel signature requires a PR touching this file and
  re-approval of every dependent `CORRESPONDENCE.md` row.

  **Explicitly NOT frozen — the commitment layer is provisional and expected to change:**
  `VectorCommitment`'s binding predicates in particular. `PuncturedBinding` is **known to be
  insufficient** (the paper replaced it) and **will be replaced by `UpdateBinding`** in Issue 1; a
  `Complete` invariant may migrate into `Crypto.lean`; and `CollisionResistant` may gain a
  keyed/algorithmic variant (Jessica's `cr-algorithmic`). These declarations live in `Crypto.lean`
  but carry a "provisional" note in their docstrings and may change without a constitutional
  amendment. Freezing the commitment layer now would be premature (do not over-freeze —
  over-restriction was flagged as a risk).

- **I5 — Minimal public surface; everything derives from the abstract.** Each new module exposes
  the **smallest possible** set of new public definitions (state the count in the PR). Every VM
  variant is an *instance* of the abstract `ZkVM`; every concrete relation/argument-system is
  *derived* from `Relation`/`ArgumentSystem`; every security property is stated via the frozen
  predicates. Anything not needed by another module is `private` or `local`. A new public
  definition that merely re-states an abstract one is a review blocker.

- **I6 — Non-vacuity is mandatory.** Every headline theorem must be accompanied by evidence its
  hypotheses are satisfiable — a model, an instance, or a concrete counterexample witness (as in
  `knowledgeSound_trivialAS` and pr5's `appendBitVC_not_updateBinding`). A theorem whose
  assumptions jointly imply `False` is treated as a bug. Every PR runs the vacuity check
  (see `CONVENTIONS.md`).

- **I7 — Axiom hygiene, CI-checked.** The permitted axiom set is `{propext, Classical.choice,
  Quot.sound}`. No `sorry`/`admit` outside an explicitly tracked allowlist in the PR description,
  no `native_decide`, no new `axiom`. `#print axioms <headline theorem>` is part of every PR.

- **I8 — Crypto is idealized "perfect/probability-free" until deliberately lifted.** Following the
  Hicks meeting: we stay self-contained. `KnowledgeSound`/binding/CR are perfect predicates; we do
  **not** import VCVio and do **not** build PPT/`negl`/running-time machinery yet. Reductions are
  modeled *lightweight* (see I9). The probabilistic re-foundation is its own scoped exploration
  (Issue 8) and is not merged into the core until reviewed.

- **I9 — Reductions are explicit and structural; running time is deferred.** Security proofs are
  phrased as explicit reductions: "if the VM's guarantee fails, then one names a concrete break of
  a hardness assumption (a collision, a position-binding or update-binding break, or a KS
  extraction failure)". *What* we reduce to/from is fixed now and reviewed carefully; the reduction
  *mechanics* and *running-time bookkeeping* may be placeholders, subbed in later. Every reduction
  must be efficient in the intended sense (a finite composition of a finite number of
  sub-adversaries), even if the cost is not yet counted.

- **I10 — Legible and compact.** The final set of public definitions plus the main theorems must be
  human-readable and not materially longer than the paper's statements. Redundancy introduced by
  agents is a defect (see the anti-duplication rule in `CONVENTIONS.md`). Target: the whole
  development stays on the order of a couple thousand lines.

- **I11 — Autonomy contract.** An agent session may run unsupervised only if: it starts from a
  named bootstrap (an issue in `PLAN.md`) and a fresh read of this file + `CONVENTIONS.md`; the
  build is green (`lake build`) at start and end; and it closes with an audit (`CONVENTIONS.md`
  review checklist), an axiom/`sorry` ledger diff, and updated `CORRESPONDENCE.md` rows. Novel
  material (I3) is done interactively or with extensive up-front documentation, because agents
  anchor on training-data analogues for novel-but-familiar-looking notions.
