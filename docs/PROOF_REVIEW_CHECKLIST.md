# Security Proof Review Checklist

> **Document status on `yl-memory-reconstruction`: shared review guidance.**
> This checklist is intended for reviewing all AI-generated or substantially
> modified security theorems, independent of which experimental branch
> eventually supplies the chosen implementation.

Use this checklist for every AI-generated or substantially modified security
theorem before merging it.

## Statement

- What exact relation does the conclusion mention?
- Is that relation defined independently of the extractor being proved correct?
- Does it eventually imply `ZkVM.Rstar`, or is the missing bridge named?
- Is the state representation committed or full memory?
- Are all quantifiers, bounds, and step counts explicit?
- Is `Nseg > 0` enforced, and are recursion counts/divisibility constraints
  explicit?
- Is the conclusion stronger than the corresponding LaTeX claim, weaker, or
  incomparable?

## Assumptions

- List every semantic assumption.
- List every cryptographic assumption.
- List every structural/arithmetic assumption.
- Does any assumption already contain the desired conclusion?
- Are the assumptions jointly satisfiable in at least a small model?
- If a verifier is arbitrary, is its required knowledge-soundness stated for
  the exact source relation?
- Would an always-accepting or always-rejecting verifier make the theorem
  misleading? Explain why or why not.

## Reduction

- Is the extractor/reduction a named definition outside the proof body?
- What are its exact inputs and outputs?
- Does it call the adversary or outer extractor more than once?
- Are shared intermediate results actually reused?
- Is every failure branch converted into an explicit game-winning witness?
- Is correctness proved before assuming the security property that rules the
  bad branch out?
- Can a human inspect the algorithm and plausibly assess efficiency?

## Cryptographic modeling

- Is collision resistance modeled as injectivity, an explicit collision game,
  or a computational advantage?
- Are binding failures represented by concrete accepted openings?
- Are opening completeness and commitment realizability stated separately?
- For a write, does the assumption force the candidate post-root to equal the
  honest commitment of the point-updated pre-memory (`UpdateBinding` or a
  scheme-specific equivalent)?
- Would appending a verifier-ignored bit to every commitment defeat the stated
  assumptions while preserving verification? If so, image membership is still
  missing.
- Are success probabilities, security parameters, and running times present?
  If not, is the theorem clearly labeled qualitative/idealized?
- Does a cost annotation have a justified machine-model interpretation, or is
  it only manual accounting?

## Semantic integration

- Is there exactly one canonical step relation for this system instance?
- Is that relation derived from a concrete/fixed program and instruction
  semantics, or is it still an arbitrary field?
- Does every step fetch exactly `program.code[pre.pc]` and apply the matching
  PC/register/memory semantics?
- Does `stepBus` refine it?
- Does the memory relation refine it?
- Does the primary memory theorem construct the post full state from the
  pre-state invariant, or does it circularly assume `CommitInv` at both
  endpoints?
- Are opcode selection and all operation cases exhaustive?
- Is the bus a tagged, multiplicity-preserving structure?
- Does every deferred call require its exact bus entry (no missing entries)?
- Does each chip validate every entry of its tag under the documented
  extra-entry policy?
- Are per-step auxiliary witnesses preserved until all consumers use them?
- Are segment boundaries and memory commitments consistent?

## Lean trust

- Does `lake build` pass?
- Are there any `sorry`, `admit`, `axiom`, or unexpected `unsafe` declarations?
- What does `#print axioms` report for the main theorem?
- Was `docs/AXIOM_AUDIT.md` updated when the report changed?
- Is the toolchain and dependency lock pinned?
- Is the pinned Lean/Mathlib toolchain a stable release for public milestones?
- Did the change introduce a theorem statement, import, or definition not
  required by the proof contract?

## Adversarial tests

Try deliberately weakening or corrupting the model:

- remove one knowledge-soundness assumption;
- make a verifier always accept;
- make an operation predicate `True`;
- set the canonical step to `True` in an allegedly concrete instance;
- fetch an instruction from a different program/program counter;
- omit a required deferred bus entry or collapse duplicate entries;
- allow distinct buses with one digest;
- omit one operation or chip case;
- swap pre- and post-state memory;
- replace an honest post commitment with an off-image value that has the same
  accepted openings (for example, an ignored appended bit);
- assume the post commitment invariant instead of constructing it;
- remove a boundary condition;
- replace a full-memory conclusion with a committed-memory one;
- add a hidden axiom or `sorry`.

The theorem or its audit should fail, or the weakened assumption should be
immediately visible in the final statement. If neither happens, the result is
not ready to merge.

Prefer a Lean theorem exhibiting a concrete countermodel to a fragile test that
edits source code and expects compilation to fail.

## Human explanation

The PR must answer, in a few sentences:

1. What does the theorem prove intuitively?
2. Which exact part of the VanillaVM security proof does it formalize?
3. What does it deliberately not prove?
4. Where is the explicit reduction?
5. What remains before the result reaches full-memory `Rstar`/CTE?
6. Is the claim perfect/qualitative or computational, and what exact model and
   advantage bound does it use?
7. What human expert reviewed the semantic and cryptographic modeling choices?
