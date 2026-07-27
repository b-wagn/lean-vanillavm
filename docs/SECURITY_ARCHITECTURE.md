# Security Architecture and Proof Discipline

> **Document status on `yl-memory-reconstruction`: shared architecture with
> partially outdated implementation terminology.** The implication chain and
> proof-discipline rules are still relevant. References to
> `canonicalStep`/`BusRefinesStep` describe the alternative Bus experiment;
> consult `MEMORY_RECONSTRUCTION.md` for this branch's current interfaces.

## Purpose

This document states what the Lean development is meant to establish and how
each intermediate theorem must connect to that goal. It is also a guardrail for
AI-generated code: a theorem compiling in Lean proves that its proposition
follows from its assumptions, but it does not by itself show that the
proposition models the intended zkVM or that the assumptions are achievable by
efficient cryptographic constructions.

The final goal is correct-trace extractability (CTE): an accepting final proof
must yield a full-memory execution trace satisfying the one canonical VanillaVM
step relation. In the abstract framework this is `ZkVM.CTE`, equivalently
knowledge soundness for `ZkVM.Rstar`.

## Current assurance level

The current Bus result is an **idealized conditional committed-segment
theorem**. It kernel-checks the extractor composition and bus-collision
reduction, assuming perfect component knowledge soundness, perfect hash
injectivity, and `BusRefinesStep` for an abstract system. It does not establish
semantic adequacy of a VanillaVM ISA or program, full-memory correctness,
recursion, or computational security.

Accordingly, this repository is presently a formal specification and checked
proof skeleton—not a formal verification of VanillaVM security. See
`ADVERSARIAL_REVIEW_RESPONSE.md` for the detailed claim boundary.

## Three separate assurance questions

Every result must answer three questions separately.

1. **Logical validity.** Does the Lean kernel accept the proof, without
   `sorry`, unexpected axioms, or an inconsistent imported theory?
2. **Model adequacy.** Is the theorem's target the intended semantic relation,
   rather than a fresh relation defined to contain exactly what the extractor
   happens to return?
3. **Cryptographic validity.** Are failures reduced by an explicit efficient
   algorithm to a stated security game, with the correct success probability
   and cost?

The current repository handles (1), partially handles (2), and deliberately
idealizes most of (3). These levels must never be described as if they were the
same guarantee.

## The canonical implication chain

The completed proof should have the following shape:

```text
accepting final proof
  -> valid R4 witness                         (embed knowledge soundness)
  -> valid recursive R3 tree                 (combine knowledge soundness)
  -> valid R2 proofs                         (convert knowledge soundness)
  -> valid R1 segment proofs                 (segment knowledge soundness)
  -> valid R0 witnesses on one common bus    (inner knowledge soundness
                                               + bus collision reduction)
  -> canonical committed steps               (bus-refinement theorem)
  -> canonical full-memory steps             (memory reconstruction
                                               + commitment reductions)
  -> one flattened full execution trace      (trace concatenation)
  -> membership in Rstar
  -> CTE
```

Every arrow is a named proof obligation. No file should introduce a private
notion of “valid execution” without proving how it implies the next relation in
this chain.

## One canonical step relation

The repository currently approaches the step relation from several directions:

- `ZkVM.step` is the abstract binary relation used by `Rstar`;
- the memory development classifies a step as read, write, or other;
- the bus development has `stepBus` plus delegated chip predicates;
- a future ISA development will define concrete opcode semantics.

These must converge on relations derived from one public/fixed program, not
remain independent predicates with similar names. The intended layering is:

1. `FullStep P`: the bus-free full-memory relation derived from fetching
   `P.code[S.pc]` and applying the selected instruction semantics;
2. `CommittedStep P`: a witness-carrying committed-memory relation with explicit
   memory openings;
3. `CommittedStepBus P`: an implementation relation that checks inline work and
   requires exact tagged entries for deferred work;
4. a proved bus-elimination theorem from `CommittedStepBus` plus universal chip
   validity to `CommittedStep`;
5. a separate binding-based memory theorem from `CommittedStep` plus commitment
   invariants to `FullStep`.

The generic `Bus.System.canonicalStep` field is only an intermediate interface.
The final VanillaVM instance must derive it from these definitions; choosing it
independently, including choosing `True`, fails the model-adequacy gate.

For the memory slice, the witness contains a read/write descriptor and opening.
For the full VanillaVM it should be extended with explicit constructors for the
supported operation classes (at least read, write, Keccak, Poseidon,
range-checked arithmetic, ordinary arithmetic, and padding/other).

## Constructive reductions before security assumptions

A security-critical theorem should be split in two.

### 1. Valid-or-break theorem

This theorem does not assume collision resistance or binding. It defines a
named reduction algorithm and proves that, on an accepting proof, the algorithm
returns either:

- the desired semantic witness; or
- an explicit witness that wins a precisely defined cryptographic game.

For bus unification, the output is either a canonical segment trace or two
distinct buses with the same digest. For memory, the bad output is a pair of
inconsistent accepted openings witnessing a position-binding failure, or an
honest pre-memory, shared write path, and malformed post-root witnessing an
update-binding failure.

The primary memory theorem must construct the post full-memory state from the
pre-state invariant. A theorem that assumes `CommitInv` for both endpoints is a
valid transfer lemma, but it cannot maintain the invariant inductively and is
not by itself a reconstruction algorithm. See
`MEMORY_INVARIANT_REVIEW.md`.

### 2. Security corollary

Only the corollary assumes collision resistance, binding, or knowledge
soundness and rules out the bad branch. This separation makes the reduction
visible to a human reviewer and gives a stable place to add probability and
running-time accounting later.

The current perfect assumptions may remain as a separately labeled theorem,
but proofs should already have this reduction-shaped structure. The
computational migration is specified in `COMPUTATIONAL_SECURITY_DESIGN.md` and
runs in parallel with concrete semantic work.

## Explicit algorithms and the middle ground

There is a useful intermediate point between pure injectivity and a complete
probabilistic cryptographic framework:

- reductions are named Lean functions;
- each reduction consumes exactly the adversary/proof output it needs;
- extractor calls and sharing are visible in its definition;
- correctness is proved as a valid-or-break theorem;
- running time is manually auditable, or recorded by an explicit cost model;
- probabilities and negligibility are deferred.

Without a security parameter or running-time restriction, “no algorithm finds
a collision” is logically equivalent to “no collision exists”, because an
algorithm can hard-code a collision. Its value is therefore structural rather
than logical: it forces the proof to expose the reduction that a later
computational theorem will analyze.

Cost annotations are useful only if their interpretation is explicit. A field
`cost : Input -> Nat` is an accounting interface, not by itself a proof that the
compiled function runs in that many steps. Exact cost equations can still make
sharing and repeated extractor calls visible, but they must be described as a
manual-audit layer until connected to a machine model.

## Assumption ledger

Every main theorem must classify its hypotheses.

### Semantic assumptions

- the operation predicates describe the intended ISA;
- bus-checked execution refines the canonical step relation;
- committed and full-memory relations correspond as claimed.

### Cryptographic assumptions

- knowledge soundness of each argument system;
- collision resistance of the bus commitment;
- completeness, position binding, and update binding of the memory
  commitment;
- any model-specific extraction assumption used for recursive SNARKs.

### Structural assumptions

- positive segment size;
- trace-length and divisibility constraints;
- well-founded recursive proof trees;
- decidable equality where an executable reduction compares buses.

The theorem must not assume its own target, a proposition definitionally equal
to its target, or an opaque “soundness” field that already contains the desired
conclusion.

## Vacuity and satisfiability

Implication theorems can be vacuously true when their assumptions are
inconsistent. Two safeguards are required:

1. provide small concrete models showing that generic assumptions such as
   `KnowledgeSound` are satisfiable (implemented by `trivialAS`), plus formal
   countermodels for omitted assumptions (`Sanity.lean`);
2. separately document that this is only a consistency floor, not evidence that
   a real succinct SNARK satisfies the assumptions.

An always-accepting verifier is not a counterexample to a theorem assuming its
knowledge soundness: if the target relation lacks a valid extractable witness,
that verifier simply cannot satisfy the assumption. This should be made
explicit whenever one verifier is viewed as an argument system for two
different relations.

## Proof and review artifacts

Each security theorem should have:

- an intuitive statement in a doc comment;
- an exact list of assumptions and their category;
- a link to the whitepaper relation or proof step it formalizes;
- a named extractor/reduction definition outside the theorem body;
- a valid-or-break theorem;
- the security corollary;
- an `Rstar`/CTE connection or an explicit statement that it is only an
  intermediate relation;
- a non-goals paragraph listing omitted probability, efficiency, memory, bus,
  or recursion features.

## Acceptance standard for the final VanillaVM result

The project may claim a conditional formalization of the VanillaVM reduction
only when:

- the final theorem concludes `CTE` for a full-memory `ZkVM` instance;
- its `step` is derived from a program, opcode fetch, and reviewed ISA
  semantics—not an unconstrained field;
- its structured bus proves no-missing-entry and chip-coverage invariants;
- all recursive layers terminate in segment extraction;
- segment extraction terminates in canonical committed steps;
- memory reconstruction constructs full states from the initial full state,
  maintains the commitment invariant without assuming it at post-states, and
  proves the final full-memory boundary;
- all cryptographic assumptions are collected and displayed;
- every bad-event implication has an explicit reduction function;
- the computational theorem defines games, probabilities, extractor scheduling,
  union bounds, and cost claims in a named model;
- the build is free of `sorry` and unapproved axioms.

Even then, the theorem does not prove the assumed SNARK/hash/commitment security,
the correctness of the ISA specification against an external reference, or
equivalence to a production verifier implementation. Those are separate claims.

Until then, results should be labeled by the exact layer they establish, such
as “bus unification”, “committed-segment CTE”, or “one-step memory lifting”.
