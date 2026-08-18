# Analysis of `finality-master` (Lean 4 finality-gadget formalization)

## Purpose & scope

`finality` formalizes a consensus **finality gadget** ("Fresh Simplex with
Height Filter and Timeouts") from a LaTeX spec (`paper_spec/full/`) into Lean 4,
proving **accountable safety**: *unless ≥ n/3 validators are slashable, no two
conflicting blocks can be finalized* (`thm:safety`). It is a paper-first
formalization project: the LaTeX is unquestionable ground truth, and the whole
harness exists to keep the Lean statements provably faithful to it while
multiple sessions/agents work over months.

Two parallel tracks:
- **Native** (`lean/Finality/`): executable spec + hand-written safety proof,
  mathlib `v4.28.0`, axiom-clean.
- **Veil** (`lean/veil_model/`): the same transition system re-modeled in the
  Veil DSL (Ivy-style, model checking + limited verification) as an
  *independent* cross-validation — deliberately unshared definitions from the
  native track, so agreement is meaningful evidence, not circular.

Currently mid-scope-extension: safety core (§1–§2, 20 items) is fully proved;
work has extended to R1 (§3 fork-choice store, 18 items), where statements are
written and proofs are `sorry`'d pending R1.2 — a live example of the
"statements-first" discipline below.

## Directory map

```
finality/
├── README.md, AGENTS.md (+CLAUDE.md stub), HANDOVER.md   — entry points
├── INVARIANTS.md         — non-negotiable project axioms (I1–I8)
├── PLAN.md                — roadmap, phases, open questions
├── AUDIT.md (+ per-phase) — adversarial-review checklist template
├── LESSONS_LEARNED.md    — clustered issue→resolution log
├── CORRESPONDENCE.md     — paper-label ↔ Lean-declaration table (curated)
├── PAPER_FINDINGS.md, R1_REVIEWER_PACKET.md, CORRESPONDENCE.md
├── SKILLS/                — project-specific agent workflows (4 files)
├── docs/
│   ├── design/BLUEPRINT.md, MODEL_ARCHITECTURE.md(_STORE.md)  — design decisions
│   ├── research/          — deep-research + review-triage notes
│   ├── sessions/          — one dated file per work session (ledger)
│   ├── REVIEW_GUIDE.md, MODEL_BOUNDARIES.md, VALIDATION_PARITY.md, VEIL_TRACK.md
│   └── dependency-matrix.md — pinned toolchain/dep revisions
├── spec_index/             — machine-generated JSON index of the paper
├── paper_spec/full/*.tex   — the LaTeX specs (ground truth)
├── blueprint/              — generated LaTeX "blueprint" cross-linking paper↔Lean
├── scripts/                — validate.sh (local CI), build_*.py generators, checks
├── lean/Finality/
│   ├── Spec/   (Basic, Tree, Vote, Quorum, State, Machine, Global, Store, Examples)
│   ├── Safety/ (Statements, MachineLemmas, Bridge)
│   └── Store/  (Statements, Invariants, Evolution)  — R1, in progress
└── lean/veil_model/        — separate Lake package, Veil DSL
```

## Reusable components / patterns

Directly transferable ideas/shapes for a zkVM security proof:

- **Abstract "Protocol" context structure** (`Spec/Tree.lean`): a single
  bundled structure (`Protocol`) carrying the abstract state space (block
  type, validator type, genesis, parent function, well-foundedness proof) that
  every other file threads as an explicit argument `(M : Protocol)`. Mirrors
  well onto a zkVM's abstract machine-config structure (ISA params, memory
  model, trace shape) threaded through step-relation/soundness files.
- **Traced fold with erasure-by-construction** (`Spec/Machine.lean`): the
  state-transition fold `sigmaT` computes `(finalState, eventLog)` and the
  "plain" fold `sigma := (sigmaT ·).1` is *definitionally* the erasure — no
  erasure lemma needed. Directly reusable for zkVM execution traces where you
  want both the bare post-state and a witness/event log (e.g. memory
  read/write events, opcode-fired events) without duplicating the step
  function or proving a separate erasure theorem.
  - Concrete lesson embedded here: they originally captured only *post-state*
    finality witnesses and found (logged in LESSONS_LEARNED) that this loses
    information needed by the safety proof — the fix was recording the
    *pre-guard-check* state in the event. Directly relevant to zkVM
    soundness/extraction proofs: witness events must carry the state at the
    moment a guard/check fired, not just the post-step state.
- **Fuel-bounded loop realizing an unbounded paper `while`**
  (`advanceSlotsT`, fuel = `target - σ.s`): a clean pattern for turning
  paper pseudocode with an unbounded loop into a structurally terminating
  Lean function without extra well-founded-recursion machinery — reusable for
  any zkVM "run until N steps"/fetch-decode-execute loop formalization.
- **Polymorphic selector/oracle contract instead of inventing tie-break
  semantics** (`Selector` structure in `Spec/State.lean`): the paper's
  `argmax` is captured as a structure of *properties* (returns none iff all
  none; a non-none choice is actually held; it's maximal) rather than a
  concrete deterministic function — safety statements are proved polymorphic
  over any implementation satisfying the contract. Good pattern for a zkVM
  proof needing an abstract "prover strategy"/scheduler without overspecifying it.
- **Reusable arithmetic layer separated from protocol semantics**
  (`Spec/Quorum.lean`): quorum-threshold arithmetic and the *proved* (not
  assumed) intersection property live in a file that "mentions neither blocks
  nor E1" — generic and reusable across any BFT-style quorum system. Good
  model for hiving off e.g. commitment-scheme / Merkle-arithmetic lemmas from
  protocol-specific soundness code.
- **Global vs per-chain split, made an explicit, justified design choice**
  (`Spec/Global.lean`): quorum-counting is per-chain but slashability is
  global over *all* signed votes ever included anywhere — modeled with a
  `Set`+`Classical`/`noncomputable` existential rather than forcing
  decidability. Relevant where a zkVM soundness proof needs a global
  adversary/attacker action space (e.g. "exists some accepting transcript
  anywhere") distinct from a per-execution local view.
- **Contrapositive statement of the "unless X, then Y" theorem**
  (`safety_contrapositive` vs `safety`): the primary proved statement is the
  contrapositive (conflicting facts ⇒ quantified adversary corruption bound),
  with the paper's natural-language "unless" form derived as a corollary.
  This is exactly the shape of typical extraction/soundness theorems
  ("if the verifier accepts, the extractor produces X, unless the adversary
  broke assumption Y") — worth adopting directly.
- **Statements-first, proofs-`sorry`'d-and-tracked workflow**: R1 store layer
  (`Store/Statements.lean`) has all 8 theorems fully stated (types, hypotheses,
  paper citations) with bare `sorry` bodies, explicitly gated by a tracked
  burndown (CI-checked sorry inventory) rather than skipped. Useful for
  staging a large zkVM soundness proof: get the full statement surface
  reviewed/frozen before spending proof effort.
- **Independent, definitionally-unshared cross-validation** (Veil track):
  rather than re-deriving trust in the same proof, they build a *second*,
  independently-defined model of the same system checked by different means
  (model checking small instances) — explicitly designed so agreement is
  non-circular evidence. Applicable to zkVM circuits: an independent
  arithmetization vs an independent Lean spec, cross-checked on small instances.

## Writing style & conventions

- **Module docstrings always cite the paper.** Every file's `/-! # Title -/`
  header names the paper section/label and line range, and states what is and
  isn't in that file, e.g. `Spec/Quorum.lean`'s docstring: *"This layer
  mentions neither blocks nor E1 — it is reusable across quorum systems."*
  Declaration-level docstrings cite the exact spec label and line range too
  (`/-- ... (`lem:mainsafety`, lines 415–417) ... -/`).
- **Imports strictly before any docstring/other syntax** — logged explicitly
  as a Lean-mechanics gotcha in `LESSONS_LEARNED.md` (a module docstring
  before `import` fails to compile); called out because it recurred twice.
- **Naming mirrors the paper's vocabulary exactly**, never invented jargon:
  `processVote`, `voteFresh`, `isSlashable`, `IsJustified`, `TimeoutFires`.
  Enforced as an audit checklist item ("Names match the paper's vocabulary…
  no invented jargon").
- **Namespacing**: `Finality.Spec` / `Finality.Spec.Protocol` /
  `Finality.Safety`, mirroring paper section structure (§1 spec / §2 safety),
  again an explicit audit item ("File/section structure mirrors the paper's").
- **`structure` for data/records (State, Protocol, FinalityEvent, Selector);**
  properties as plain `def ... : Prop` / theorems, not bundled into classes —
  no typeclass-heavy style. `Selector` is the one "interface" and it's a plain
  structure of proof-carrying fields, not a type class.
- **Every proved theorem gets a one/two-line English restatement in the
  docstring plus the exact paper citation**, e.g.:
  ```
  /-- **Accountable safety, contrapositive form** (`thm:safety`, lines 444–446;
  primary statement per Q2): two conflicting finalized blocks force at least
  `⌈n/3⌉` distinct slashable validators. Proved from `lem:finchain`. -/
  ```
- **Proofs are heavily commented at branch points**, explaining *why* a
  `by_cases`/`split` collapses the way it does, not just what tactic runs:
  ```
  by_cases hP : quorumThreshold M.n ≤ σ.P.card <;> simp only [hP, if_true, if_false] <;>
  · split
    · -- `sel.choose σ.targets = some T`
  ```
- **Open design questions are numbered (Q1, Q2, Q7, Q8...) and require
  explicit human approval before being resolved**, then cited by number
  forever after in docstrings/CORRESPONDENCE ("Open question Q2 (approved
  2026-06-16): the primary statement is the contrapositive…"). Nothing is
  silently decided by whoever is coding.
- **Comment markers for non-obvious Lean workarounds**, e.g. a recurring
  one-liner before functions using `decreasing_by`:
  `-- \`h\` is used in \`decreasing_by\` but the unused-variable linter misses that.`
  `set_option linter.unusedVariables false in`
- **Every spec-formalizing declaration must have both** a paper-citing
  docstring *and* a row in `CORRESPONDENCE.md` — a hard CI-checked rule
  (`AGENTS.md` Rules; `check_correspondence.py` actually elaborates the name
  via `#check`, not just greps for it — closing a real false-pass they hit).
- **Assumption/trust-base handling**: fault-model constants (`n`, `f`,
  `n ≥ 3f+1`) are deliberately *not* baked into the core `Protocol` structure;
  instead the safety theorems are phrased directly in terms of a bound on
  `|SlashableValidators|`, with the classical `f`-based reading kept as an
  explicitly-labeled "off the main proof path" bridge lemma
  (`f_lt_slashThreshold`), and the modeling choice is justified in a docstring
  under a "Modeling note" heading rather than left implicit.
- **Target axiom set is fixed and CI-checked**: `{propext, Classical.choice,
  Quot.sound}` — no `sorry` outside an explicit tracked allowlist, no
  `native_decide`, no new `axiom`. This is treated as load-bearing, not
  aspirational (`scripts/check_axioms.sh`, `#print axioms` in CI).

## Collaboration / review / skills worth adopting

- **`INVARIANTS.md`**: a short, numbered list (I1–I8) of things that hold at
  *all* times and require explicit human sign-off to change — ground truth
  source, scope boundary ("does this serve the target theorem?"), fault-model
  fixed assumptions, axiom/sorry hygiene, toolchain pins, and an explicit
  "autonomy contract" (I8) stating exactly when an agent is allowed to work
  unsupervised (session starts from a bootstrap file + fresh audit; CI green
  at start/end; closing audit + doc updates). This is the single most portable
  artifact — a project-specific constitution that both humans and agents
  check against, cited by number everywhere else.
- **`AUDIT.md` — a fresh, context-free-reviewer adversarial-review template**,
  run at minimum at session start/end. Five lettered sections: (A) statement
  fidelity incl. a *completeness* pass distinct from faithfulness ("faithful
  but partial" statements are a named failure mode, discovered the hard way —
  see LESSONS_LEARNED's `lem:slotmono` case), (B) coverage/scope, (C) proof
  hygiene/kernel truth, (D) legibility, (E) harness/docs freshness, (F)
  dependency drift. Explicitly separates "faithful" from "complete."
- **`SKILLS/adversarial-review.md`**: operationalizes AUDIT.md as a skill —
  key idea is **fan out independent skeptics along named dimensions**
  (soundness/vacuity, kernel-truth re-verification, CI/gate integrity,
  docs/overclaim), each blind to the others' findings, then triage to
  `CONFIRMED` vs `SUSPECTED` (a finding is only real once reproduced), fix,
  re-verify. Also has a "hygiene for reviewer agents" rule: any probe an agent
  injects (a weakened assertion, a false claim) must be reverted and `git
  status` re-checked clean afterward.
- **`LESSONS_LEARNED.md`**: not a changelog — a clustered issue log (cluster
  by theme, not by date), each entry recording issue → resolution → **guard
  added** (a CI check, an invariant, or an audit checklist item). The explicit
  rule "a finding without a guard will recur" and "merge into existing
  clusters rather than appending" keeps it from becoming noise.
- **`docs/sessions/TEMPLATE.md`**: a fixed per-session ledger format
  (bootstrap ref, autonomy modality, opening/closing audit verdicts, work
  done referencing PLAN/CORRESPONDENCE rows, an axiom/sorry ledger diff,
  a docs-updated checklist, and an explicit handoff note for the next
  session). This is the concrete mechanism that makes multi-session,
  multi-agent collaboration work without shared memory.
- **`CORRESPONDENCE.md`**: one row per formalized paper item with a
  mechanically-checked status vocabulary (`pending(N)` / `stated` / `proved` /
  `n/a`), used as the literal side-by-side validation surface a human reviewer
  reads with the paper open next to it. CI enforces every "safety-core" label
  has a row and that named Lean declarations actually elaborate.
- **`spec_index/spec_index.json` + generator scripts**: the paper is
  mechanically parsed into a labeled, line-ranged JSON index with a curated
  "semantic overlay" for dependencies the LaTeX `\ref` graph misses (prose
  references by name). A `--check` CI mode enforces the index stays in sync
  with the paper and flags "ground truth went stale" (they hit a real 8-commit
  drift incident, documented in LESSONS_LEARNED).
- **Scope-extension discipline**: `INVARIANTS.md` I2 requires any new scope
  (e.g. the R1 store track) to be logged with an explicit human-approval date
  and a bounded item count, with everything else remaining "out of scope"
  until re-scoped the same way — prevents silent scope creep in a long-running
  proof effort with rotating contributors/agents.
- **`scripts/validate.sh`** as a single local command mirroring CI exactly
  (with a documented single intentional difference), plus a `--fast` mode
  that skips the Lean build for quick iteration — and multiple logged
  incidents of the gate itself being wrong (string-match version-coupling,
  scans recursing into vendored `.lake/` deps, non-blocking jobs guarding
  blocking invariants) treated as first-class bugs, not curiosities.

## Recommended adoptions (ranked)

1. **Adopt an `INVARIANTS.md`-style constitution** for the zkVM proof: fix
   ground-truth source, scope boundary question ("does this serve the target
   soundness theorem?"), fault/adversary-model assumptions, axiom/`sorry`
   policy, and an explicit autonomy contract for agent-driven sessions.
2. **Adopt the CORRESPONDENCE.md pattern**: one row per spec item (ISA
   instruction, constraint, security claim) ↔ Lean declaration, with a
   checked status vocabulary and CI verification that names actually resolve.
3. **Adopt the audit template + adversarial-review skill**, especially the
   faithful-vs-complete distinction and the "fan out independent skeptics,
   only count CONFIRMED findings" workflow — cheap and has already paid off
   for them multiple times per the lessons log.
4. **Adopt the session-ledger template** (`docs/sessions/`) if multiple
   people/agents will touch the zkVM proof over time — the axiom/sorry ledger
   diff and explicit handoff note are the parts most worth copying verbatim.
5. **Adopt the traced-fold-with-definitional-erasure pattern** for the zkVM
   execution trace / witness log, and the "record pre-guard-check state, not
   just post-state" lesson if any proof step needs to reconstruct why a check
   fired.
6. **Adopt the contrapositive-statement-first convention** for soundness/
   extraction theorems phrased as "unless assumption A is broken, property P
   holds."
7. **Adopt LESSONS_LEARNED.md's cluster-by-theme + guard-required discipline**
   — lower cost than the full audit machinery but keeps recurring Lean/CI
   footguns (e.g. import-before-docstring, vendored-dep scan pollution) from
   resurfacing.
8. Lower priority / project-specific, likely not worth porting as-is: the
   dual native+Veil cross-validation track (only worth it if a second,
   independently-defined formal model of the zkVM is actually planned) and
   the LaTeX blueprint-generation tooling (useful mainly because their ground
   truth *is* LaTeX; a zkVM spec may live elsewhere).
