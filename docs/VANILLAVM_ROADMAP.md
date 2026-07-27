# Roadmap to an End-to-End VanillaVM Security Theorem

> **Document status on `yl-memory-reconstruction`: forward-looking working
> roadmap.** Its dependency gates remain useful, but the progress descriptions
> predate this branch's completed one-step reduction, trace fold, and
> Bus-to-memory segment composition. The team should reconcile and assign this
> roadmap in the next planning meeting.

## Target

The final theorem should say that the **Lean model** of the final VanillaVM
verifier is correct-trace extractable for its reviewed full-memory VanillaVM
semantics, under explicitly stated computational assumptions. Its trace must
begin and end at states consistent with the public committed boundaries and
every adjacent pair must execute the instruction fetched from the claimed
program.

The current repository contains valuable pieces, but they are intermediate
models:

- `Zkvm.lean` defines the abstract goal and proves `CTE` equivalent to
  knowledge soundness for `Rstar`;
- `Twostep.lean` demonstrates extractor composition and trace flattening;
- `Bus.lean` models inner/segment extraction and bus unification;
- the memory branch proves endpoint step transfer plus the critical
  one-write commitment-invariant lemma using update binding.

The main engineering task is to connect these pieces without allowing each
file to choose an unrelated step predicate.

## Current maturity and claim

Today the repository proves an idealized conditional bus-unification and
committed-segment result. It does **not** prove VanillaVM security. Concrete
program semantics, structured bus coverage, trace-level memory reconstruction,
recursion, and probability/cost bounds are release blockers, not optional
extensions.

## Dependency graph and stop-the-line gates

```text
proof hygiene/non-vacuity
          |
          v
program + thin-slice ISA + structured bus -----> probability/game prototype
          |                                           |
          v                                           v
one-step memory integration                  quantitative Bus theorem
          |                                           |
          +-------------> full segment <--------------+
                               |
                               v
                    convert/combine/embed
                               |
                               v
                 full-memory computational CTE
```

Work may proceed in parallel across the two columns, but neither column may be
deferred until after a large abstract framework is built.

- **Gate S (semantics):** a public program, fetched instruction, thin-slice ISA,
  tagged bus, and concrete bus-refinement theorem.
- **Gate M (memory):** a one-step theorem constructs the post full state from
  the pre-state invariant, and a trace reconstruction fold maintains
  `CommitInv` through every operation and proves the final boundary.
- **Gate R (recursion):** exact R2/R3/R4 relations, decreasing step counts,
  divisibility/base cases, and shared boundaries.
- **Gate Q (quantitative):** named games, event containment, union bounds, and
  explicit extractor/reduction costs.
- **Gate H (human review):** cryptographer approval of the model and an
  independent Lean/modeling review.

No end-to-end security wording is allowed until S, M, R, Q, and H all pass.

## Proposed module boundaries

The eventual layout should separate reusable foundations, toy models, and the
real VanillaVM instance:

```text
VanillaZkVM/
  Core/
    Crypto.lean          relations, verifiers, extractors, games
    Reduction.lean       named algorithms and optional cost accounting
    Zkvm.lean             Rstar, CTE, generic trace lemmas
  Toy/
    Twostep.lean          minimal extraction-composition example
  Vanilla/
    ISA.lean              operations and canonical full step
    Memory.lean           committed/full predicates and reconstruction
    Bus.lean              bus relations and valid-or-collision reduction
    Segment.lean          R0/R1 integration
    Recursion.lean        convert/combine/embed proof tree
    Security.lean         final theorem and assumption ledger
```

This reorganization should happen only after active feature branches settle,
to avoid unnecessary merge conflicts. The semantic interfaces below matter
more than directory names.

## Phase 0: proof discipline and assumption hygiene

- Ban `sorry` and audit transitive axioms.
- Add a trivial witness-as-proof argument system to demonstrate that the
  abstract `KnowledgeSound` proposition is satisfiable.
- Collect each main theorem's semantic, cryptographic, and structural
  assumptions in an auditable ledger.
- Require named extractor/reduction definitions for security-critical results.
- Keep valid-or-break theorems separate from cryptographic corollaries.

Current status: `trivialAS`, three sanity countermodels, positive Bus segment
size, and the initial axiom audit are implemented. Joint satisfiability of a
concrete Bus instance and CI remain open.

## Phase 1: canonical operation semantics

Define one classified operation type and one canonical binary step relation.
The first useful subset can be:

- read;
- write;
- ordinary memory-free operation;
- Keccak;
- Poseidon;
- range-checked operation;
- padding/no-op.

The classified relation carries auxiliary witnesses. Its existential
projection is the binary relation installed as `ZkVM.step`. Later ISA detail
can refine the memory-free operations without changing the security
architecture.

Required theorem:

```text
classified step witness -> canonical binary step
```

This phase follows `CONCRETE_SEMANTICS_PLAN.md`. Completion additionally
requires program fetch, tagged bus entries with multiplicity, no-missing-entry
coverage, universal chip validation, and a concrete proof discharging
`BusRefinesStep` by exhaustive instruction cases.

## Phase 2: memory correctness

- Retain explicit memory openings in extracted witnesses.
- Prove honest-opening completeness.
- Prove the one-step reconstruction result using position and update binding.
- Define the reconstruction fold from an initial full memory.
- Prove or explicitly assume the concrete commitment scheme's update-binding
  reduction; do not derive commitment realizability from point
  non-equivocation.
- Lift an entire committed segment to a full-memory segment.

Required result:

```text
valid committed classified segment + initial full state
  -> valid full-memory canonical segment
  OR explicit memory-binding break
```

The `memory-integration` branch supplies a qualitative one-step lemma consuming
completeness, position binding, and update binding, plus a constructive
one-write invariant lemma. Its current transfer lemma assumes `CommitInv` at
both endpoints, so it is input to this phase—not completion of it. The primary
missing interface is:

```text
CommitInv Ŝ₁ S₁ + committed step Ŝ₁ -> Ŝ₂
  -> exists S₂, CommitInv Ŝ₂ S₂ and valid full step S₁ -> S₂.
```

The missing trace fold, final-memory boundary proof, and explicit
binding-break outputs remain mandatory. See `MEMORY_INVARIANT_REVIEW.md`.

## Phase 3: bus correctness

- Implement the plan in `BUS_SECURITY_PLAN.md`.
- Connect `stepBus` and chip predicates to the canonical classified step.
- Output explicit bus collisions instead of hiding the reduction behind
  injectivity.
- Conclude committed-segment CTE, then compose with memory reconstruction.

Required result:

```text
accepting segment proof
  -> valid full-memory canonical segment
  OR explicit inner-SNARK/bus/memory security break
```

## Phase 4: segment and trace composition

- Reuse `chain_flatten` for fixed-size segment traces.
- Preserve per-step auxiliary witnesses long enough for memory extraction.
- Prove boundary consistency, including memory commitments, at every segment
  seam.
- Ensure `T = m * Nseg` and positivity/divisibility assumptions are explicit.

## Phase 5: actual recursion

Replace the flat final merger with the whitepaper hierarchy:

1. `R2` / convert: one segment proof becomes one recursive proof;
2. `R3` / combine: two child proofs with adjacent boundary states and valid
   step counts become one parent proof;
3. `R4` / embed: the final proof verifies the root combine proof.

Use an inductive proof-tree type carrying step counts. Prove unrolling by
well-founded induction. The theorem should return the list of segment proofs
and boundaries or an explicit knowledge-soundness break.

## Phase 6: final full-memory `Rstar`

Instantiate `ZkVM` with:

- full-memory states;
- the canonical bus-free ISA step;
- the fixed total step count;
- public statements containing the committed boundary claims;
- the actual final proof type and verifier.

The boundary relation must explicitly say that the full initial/final memories
commit to the public committed states. The current abstract `TraceValid`
equality boundary is not by itself the paper's committed-boundary relation, so
the final statement/state interface may need a generalized boundary predicate.

Prove `CTE` for this instance by composing recursion unrolling, segment
extraction, bus unification, memory reconstruction, and trace flattening.

## Phase 7: computational security layer

The qualitative development should already expose all reductions. Then add,
incrementally:

- adversary and reduction algorithms;
- randomized execution and success events;
- a security parameter;
- exact or upper-bounded running costs;
- polynomial-time predicates;
- advantage functions and negligibility;
- the final union/hybrid bound.

Follow `COMPUTATIONAL_SECURITY_DESIGN.md`. Begin the probability substrate and
one-chip Bus prototype in parallel with Phase 1. Only migrate the full
VanillaVM after the interface is stable, but do not postpone validating the
proof architecture against probability and cost composition.

## Phase 8: LaTeX/Lean consistency (continuous)

For every major theorem, maintain a proof contract recording:

- the LaTeX label;
- the Lean declaration;
- whether the mapping is exact, idealized, a specialization, or only a
  component;
- assumptions and omitted features;
- the exact source commits.

Generate the human proof and Lean proof from a frozen shared contract, then
audit them independently. Lean validates logical implication; a separate
review verifies that the formal statement matches the intended cryptographic
claim.

This work begins with Phase 1 and is updated in every PR; it is numbered last
only because the final end-to-end contract cannot be frozen earlier.

## Integration order

To minimize rework, merge concepts in this order:

1. assumption/non-vacuity safeguards;
2. explicit reduction interface and valid-or-break pattern;
3. concrete program/ISA and structured-bus thin slice;
4. probability/game spike on the toy Bus, in parallel with step 3;
5. memory integration with the same classified step;
6. concrete Bus refinement and full-segment reconstruction;
7. recursive proof tree;
8. full-memory computational CTE and exact advantage equation.

Parallel experimental branches are useful, but each should publish a small
interface and theorem-strength comparison before integration. More code is not
automatically a stronger security statement.

## Progress matrix

| Layer | Current qualitative status | Missing bridge |
|---|---|---|
| Abstract `Rstar` / CTE | Implemented | Final full-memory instance |
| Trace flattening | Implemented | Preserve auxiliary witnesses as needed |
| Two-layer toy | Implemented for abstract committed step | Concrete semantics and memory |
| One-step memory lifting | Endpoint transfer and write-invariant core implemented on memory branch | Constructive all-operation `reconstructStep`, trace fold, final boundary, and final instance |
| Bus unification | Explicit valid-or-collision reduction and committed CTE | Concrete `BusRefinesStep` proof and full-memory lift |
| Concrete ISA | Not implemented | Classified operations and opcode selection |
| Program binding | Not implemented | Program statement, fetch, PC semantics |
| Structured bus coverage | Not implemented | Tagged entries, multiplicity, no-missing/validation proofs |
| Convert/combine/embed | Not implemented | Inductive recursive proof tree |
| Quantitative security | Bus reduction algorithm exposed; no quantitative theorem | Probabilities, cost, polynomial time, negligibility |

This table should be kept current. It is the quickest defense against claiming
that an intermediate theorem proves the entire VanillaVM security statement.
