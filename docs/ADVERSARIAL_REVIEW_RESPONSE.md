# Response to the Adversarial Review

> **Document status on `yl-memory-reconstruction`: historical response.**
> Statements about what the “current branch” implements refer to the earlier
> Bus experiment and may have been superseded by the memory reconstruction and
> Bus composition documented in `MEMORY_RECONSTRUCTION.md`.

## Bottom line

The review is substantially correct about the **current branch**. The strongest
honest description of the current result is:

> an idealized, conditional proof of the bus-unification reduction and
> committed-segment extraction skeleton.

It is not a proof of VanillaVM security. In particular, the current branch does
not yet bind execution to a concrete program/ISA, reconstruct full memory,
unroll the recursive proof hierarchy, or state computational success bounds.

The review overstates one point: if every phase of the roadmap were genuinely
completed—including concrete program semantics, the memory lift, recursion,
and the computational theorem—then the three headline gaps would no longer be
“entirely unaddressed.” The valid process criticism is that the earlier roadmap
made those phases easy to defer and did not give them testable completion gates.
The revised roadmap corrects that.

Even the completed project would remain a **conditional reduction theorem**. It
would assume security of the component SNARKs and commitments, and it would
verify a Lean model rather than a production verifier binary. Those boundaries
must remain in every public claim.

## July 23 memory-invariant follow-up

Benedikt's append-bit counterexample sharpens—and validates—the review's memory
criticism. The earlier response said the experimental memory branch consumed
position and punctured binding, but that did not close trace reconstruction:
those properties constrain accepted openings without forcing an arbitrary
post-root to be an honest output of `Commit`.

The latest `memory-integration` branch replaces punctured binding with
`UpdateBinding` and proves `commit_update`/`commitInv_write`. This blocks the
counterexample and establishes the critical one-write invariant. It still does
not prove full-memory trace extraction. The required next theorem must
construct the post full state from the pre-state invariant alone and return
both `CommitInv` and a valid full step; only then can it be folded over the
trace. The full assessment is in `MEMORY_INVARIANT_REVIEW.md`.

## Classification

The findings below are classified as:

- **Accepted:** the review identifies a real gap or misleading presentation;
- **Qualified:** the core concern is useful, but part of the technical claim is
  inaccurate or too broad;
- **Deferred:** a precision improvement, not a present soundness blocker;
- **Rejected:** no change is warranted for the stated reason.

## Semantic and architectural findings

| Finding | Decision | Assessment and action |
|---|---|---|
| `canonicalStep` is unconstrained | **Accepted, critical** | The generic Bus theorem may target `True`. This is acceptable only as an intermediate parametric theorem. A final instance must derive its step relation from a public program and an inductive instruction semantics; an arbitrary field is a release blocker. |
| `BusRefinesStep` is assumed | **Accepted, critical** | It is the missing bus-elimination theorem and must be proved for the concrete instance. It is not, by itself, the full memory-extractability proposition: bus refinement and committed-to-full-memory lifting are separate obligations and will remain separate in Lean. |
| No full-memory reconstruction on this branch | **Accepted, critical** | Memory binding remains unused on this Bus branch. The latest `memory-integration` branch consumes completeness, position binding, and update binding in `step_mem_extract`, `commit_update`, and `commitInv_write`, so “zero Lean counterpart” is too broad across all branches. Its endpoint-transfer theorem assumes both endpoint invariants, and it has no trace fold, so it still does not close the gap. |
| No convert/combine/embed recursion | **Accepted, high** | `Twostep.lean` is explicitly a flat toy. No final security claim is permitted before the recursive relations, step-count decrease, base case, and boundary equality are formalized. |
| No program/opcode model | **Accepted, high** | The paper binds an operation predicate to `code[pc]`. The final statement must carry or fix the program, and the canonical step must perform opcode fetch/selection. Treating individual instruction semantics as black-box predicates does not justify omitting fetch and program binding. |
| Opaque bus and arbitrary chip predicates | **Accepted, high** | A concrete bus must be a collection of tagged entries. Deferred steps must prove membership, chip predicates must quantify over all entries of their tag, and coverage/multiplicity invariants must be explicit. |

## Cryptographic findings

| Finding | Decision | Assessment and action |
|---|---|---|
| Perfect collision resistance changes the theorem | **Accepted with qualification** | Injectivity is impossible for a real compressing finite-output hash, but not for every abstract `HashCommitment` allowed by the Lean type. The current theorem is a perfect/idealized theorem and must never be presented as Keccak/Poseidon collision resistance. |
| A probabilistic reduction must itself return a distribution | **Qualified** | A reduction can remain a deterministic function of sampled adversary/extractor outputs. Randomness belongs in the adversary, extractor, oracle, and game semantics. The theorem must nevertheless lift deterministic valid-or-break inclusion to probability bounds and union bounds. |
| Extractors have no efficiency bound | **Accepted** | `Extractor` is currently an arbitrary function. The computational layer must specify an algorithm/cost interface and the model in which straight-line extraction is assumed (for example ROM/AGM/CRS with trapdoor). |
| Vector-commitment binding is unused | **Accepted for this branch** | The memory branch now consumes position and update binding and proves the load-bearing write invariant, but it still needs a pre-invariant-only reconstruction theorem, integration, a trace fold, and computational binding games. |
| Perfect results can simply be upgraded later | **Rejected as an assumption** | The deterministic proof skeleton may be reusable, but probability bookkeeping, bad-event definitions, extractor scheduling, and cost bounds require separate theorems. The computational design is now an early parallel workstream, not a final cosmetic phase. |

## Logical and structural findings

| Finding | Decision | Assessment and action |
|---|---|---|
| `cte_iff_knowledgeSound` is tautological | **Accepted** | It is useful packaging, not a substantive security result. Comments now call it a “packaging equivalence,” not a keystone. |
| `Nseg = 0` | **Accepted** | `Bus.System` now contains `NsegPos : 0 < Nseg`, so no Bus instance can choose zero without proving `False`. |
| Traces should use `Fin` | **Deferred** | `ℕ → State` with guarded indices is sound and convenient for concatenation. A bounded-vector representation may improve APIs later, but it is not a security fix. Off-range values are deliberately irrelevant to `TraceValid`. |
| Constant fallback in `traceOfReductionOutput` | **Accepted only as a migration warning** | Totalization is legitimate in the perfect theorem because collision resistance proves the branch unreachable on accepting proofs. A computational theorem must keep success/failure as an event or result and must not claim the fallback trace is valid. |
| Collision pairs should involve `busCom` | **Rejected** | `busCom` is a digest, not a hash preimage. A collision is correctly a pair of distinct buses whose hashes both equal that digest. Comparing every extracted bus to the step bus is the intended reduction. |
| Hash equalities are assumptions of `unifyBuses_correct` | **No issue** | They are local lemma premises derived from the five extractor-correctness statements in `segment_valid_or_collision`. The public constructive theorem does not assume them independently. |

## Process and assurance findings

| Finding | Decision | Assessment and action |
|---|---|---|
| No satisfiability models | **Accepted** | `trivialAS` and `knowledgeSound_trivialAS` now give a witness-as-proof model. This proves only that generic `KnowledgeSound` is satisfiable, not that all Bus assumptions are jointly satisfiable. Joint concrete models remain a gate. |
| No negative tests | **Accepted with a method change** | Deleting a hypothesis and expecting compilation to fail is brittle. `Sanity.lean` now gives formal countermodels: an always-accepting system for an empty relation is not knowledge-sound; a constant hash is not collision-resistant; an accept-all vector commitment is not position-binding. Concrete Bus countermodels remain to be added. |
| No axiom audit | **Accepted with correction** | A reproducible `#print axioms` audit is recorded separately and must be rerun in CI. Standard classical axioms are not automatically introduced merely because Mathlib is imported; dependencies are declaration-specific. `Classical.choice` also does not make every type inhabited—it selects from a supplied `Nonempty` witness. The audited Bus theorems use no axioms; `TwoStep.cte` reports `propext` and `Quot.sound`. |
| AI-generated modeling needs human review | **Accepted, critical process gate** | Kernel checking validates implication, not adequacy. Concrete ISA, bus coverage, memory invariants, and cryptographic game statements require named human reviewers. |
| No CI | **Accepted** | A clean local build is insufficient for a public artifact. CI is a pre-merge requirement; it must run `lake build`, placeholder scans, and the axiom audit on the pinned toolchain. |
| Release-candidate toolchain | **Accepted as release risk** | It is not evidence of a current proof flaw. Before a public milestone, migrate to a stable Lean/Mathlib release and rerun all audits. |

## The bus footnote

The review usefully flags the footnote but describes its direction
inconsistently. The whitepaper says the expanded predicate is **stronger** when
it validates extra bus entries not referenced by the segment. Extra, valid
entries do not create an invalid executed step; missing or unchecked entries
can.

The concrete model must state three separate properties:

1. **No missing entries:** every deferred operation or range check executed by a
   segment contributes the required tagged bus entry.
2. **Validation coverage:** each chip validates every bus entry bearing its tag
   (or the exact explicitly specified subset, if the optimized protocol uses a
   different rule).
3. **Multiplicity policy:** use a list/multiset or indexed entries if repeated
   calls matter; plain set membership can silently collapse duplicates.

Whether extra entries are allowed is a protocol choice. If allowed, validating
them makes the circuit stronger than the bus-free step predicate but does not
harm soundness. The Lean relation and LaTeX statement must choose the same
policy.

## Attack-scenario disposition

| Attack | Current branch | Required blocking invariant |
|---|---|---|
| Trivial/empty bus | Not ruled out for a concrete ISA | Tagged bus, required membership from each deferred step, universal chip validation |
| Commitment swap / off-image post-root | Not ruled out by this branch | Explicit openings, commitment invariant, completeness, position binding, update binding, and a trace reconstruction fold |
| Phantom/zero segment | Zero segment now ruled out locally; recursion absent | Positive `Nseg`, divisibility, decreasing combine counts, exact base case |
| Wrong program | Not ruled out | Public/fixed program in statements and `fetch P S.pc` in every step constructor |
| Inconsistent recursive boundary | Flat toy checks it; recursion absent | Combine relation shares and checks the exact left-terminal/right-initial state |

## Changes made in response

- Added `Bus.System.NsegPos`.
- Added `trivialAS` and proved `knowledgeSound_trivialAS`.
- Added `Sanity.lean` with three formal adversarial countermodels.
- Reworded `cte_iff_knowledgeSound` as a structural packaging equivalence.
- Added a concrete minimal-ISA/bus work plan.
- Added a computational-security design with explicit games, bad events,
  probability composition, and cost gates.
- Revised the roadmap so semantic, memory, recursion, and computational work
  have blocking milestones and dependency order.
- Added a reproducible axiom audit and strengthened the review checklist.
- Added a dedicated review of the off-image commitment counterexample and
  changed the memory plan from punctured binding to a pre-invariant-only
  reconstruction theorem using update binding.

## Permitted project claims

Until the full-memory and concrete-semantics gates pass, use:

> “We formalized and kernel-checked an idealized conditional reduction for
> bus unification and committed-segment extraction.”

Do not use:

> “Lean verified the security of VanillaVM.”

After all planned layers are complete, the strongest expected claim is still
conditional:

> “Under the stated extraction and cryptographic assumptions, the Lean model of
> VanillaVM satisfies the stated computational correct-trace-extractability
> bound.”

That claim would not establish security of concrete primitives, correctness of
the ISA specification against an external reference, or equivalence of a
production verifier implementation to the Lean model.
