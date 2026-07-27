# Computational Security Design

> **Document status on `yl-memory-reconstruction`: forward-looking proposal.**
> The qualitative reductions were designed with this migration in mind, but
> the probability, game, and running-time layer described here is not yet
> implemented or approved as the final model.

## Purpose

The perfect development is not a theorem about real compressing hashes or
real SNARKs. This document specifies the quantitative layer early enough that
the qualitative interfaces can be tested against it rather than retrofitted at
the end.

The target is the whitepaper-style statement:

```text
Adv_CTE(A, λ)
  <= sum of knowledge-soundness advantages
   + bus-collision advantage
   + per-step memory-binding advantages,
```

with the exact multiplicities from the recursion tree and all reductions having
an explicit running-cost bound.

This remains conditional security: Lean will prove the reduction and bound,
while security of concrete SNARKs/hashes/commitments remains an assumption in a
named model such as ROM, AGM, or a trapdoor CRS model.

## What remains deterministic

The core bus comparison does not need to become a distribution. Given sampled
extractor outputs, `unifyBuses` deterministically returns a trace or a collision
candidate. Likewise, trace concatenation and memory reconstruction are
deterministic functions.

Randomness enters through:

- the CTE adversary;
- randomized extractors, if the chosen extraction model uses them;
- oracle/CRS setup and queries;
- cryptographic game challengers.

The computational theorem lifts deterministic event implications into
probability inequalities.

## Probability substrate

The first executable prototype should use discrete distributions over finite or
countable bitstring types. A suitable initial representation is `PMF`; aborting
algorithms can return `Option α` inside the distribution. Before choosing it for
the full development, prove the following library spike:

1. sequencing/`bind` for adversary and extractor calls;
2. probability of a decidable bad event;
3. event monotonicity (`E ⊆ F -> Pr[E] <= Pr[F]`);
4. finite union bound;
5. mapping a deterministic reduction over a sampled output;
6. conditioning or an equivalent experiment formulation that avoids informal
   conditional probabilities.

If `PMF` cannot express the intended oracle/setup experiments cleanly, stop and
select an alternative before formalizing full games. Do not build a custom
probability theory as part of the VanillaVM proof.

## Algorithm interface

Use a common wrapper for named randomized algorithms:

```lean
structure Alg (Input Output : Type) where
  run  : Input → PMF Output
  cost : Input → Nat
```

Initially, `cost` is an auditable annotation. The theorem must say so. A later
machine-model relation may validate it. Deterministic functions are lifted with
`PMF.pure`.

Security-critical composition must use named combinators whose cost equations
are proved:

- sequential composition;
- mapping a deterministic postprocessor;
- sharing one sampled/extracted result among several consumers;
- bounded iteration over segments and steps.

The `share` combinator is important: the outer adversary and segment extractor
must not be rerun independently for each chip, or the probability and running
time claims will be wrong.

## Game interfaces

### Computational knowledge soundness

For an argument system, record:

- a named straight-line extractor algorithm;
- the model/setup/oracle parameters available to it;
- the failure event
  `verify x p ∧ ¬R.rel x extractedWitness`;
- a bound for every allowed PPT adversary;
- extractor and reduction cost overhead.

The quantifier order must match the intended model. In particular, document
whether one universal extractor works for all adversaries and what trapdoor or
oracle access it receives.

### Bus collision resistance

The game samples/runs an adversary producing `HashCollisionCandidate H` and
wins exactly on `IsHashCollision H candidate`. The real hash interface must also
specify:

- security parameter and domain/digest lengths;
- serialization of the structured bus;
- whether the hash is keyed or unkeyed;
- oracle access, if modeled in ROM.

### Vector-commitment games

Define algorithmic output records for:

- two inconsistent openings at one commitment/index (position binding);
- an honest pre-memory, address/new value, candidate post-root, and shared
  write proof that verify correctly while the candidate root differs from the
  honest point-update commitment (update binding).

The memory reduction must return these concrete records. Perfect implications
using `PositionBinding`/`UpdateBinding` then become corollaries of the same
valid-or-break structure.

### Correct-trace extractability game

The adversary outputs the program, public committed boundaries, step count, and
final proof as prescribed by the selected VanillaVM statement. The extractor
outputs a full-memory trace. The bad event is:

```text
finalVerify statement proof
AND NOT FullTraceValid program statement trace.
```

Program binding, initial/final memory commitment relations, and the fixed or
bounded step-count policy belong inside this game—not in prose.

## Required event decomposition

For one segment, prove a deterministic containment lemma:

```text
AcceptingSegment AND InvalidCanonicalSegment
  implies
    SegmentKSFailure
    OR InnerStepKSFailure
    OR KeccakKSFailure
    OR PoseidonKSFailure
    OR RangeKSFailure
    OR BusCollision
    OR SemanticRefinementFailure.
```

For the concrete system, `SemanticRefinementFailure` is impossible by the
proved program/ISA/bus theorem. It must not be hidden in a cryptographic
advantage.

Memory reconstruction adds, per step:

```text
PositionBindingFailure OR UpdateBindingFailure.
```

The operation split should sharpen this bound: reads need only the position
event, writes need position or update, and memory-free operations need neither.
The same bad event must be shared between establishing the post commitment
invariant and proving the full-step semantics; these are not two independent
cryptographic failures.

Recursion adds the embed, combine, and convert knowledge-soundness failure
events with their exact invocation counts.

## Probability theorem

Apply event monotonicity and a finite union bound to the containment theorem.
The final coefficients must be derived from the recursion structure, not typed
as unexplained constants. For `m = T / Nseg`, the target shape is the paper's:

```text
Adv_CTE
  <= Adv_KS(embed)
   + (m - 1) * Adv_KS(combine)
   + m * Adv_KS(convert)
   + m * (Adv_KS(segment)
          + sum_j Adv_KS(inner_j)
          + Adv_CR(busHash))
   + sum_{k < T} (Adv_position(k) + Adv_update(k)).
```

Any change in recursion arity, chip set, or memory protocol must update this
derived equation and its LaTeX contract.

## No fallback-trace argument

The perfect theorem may totalize its extractor on the impossible collision
branch. The computational theorem must instead reason about events:

- on the good event, the result contains a valid trace;
- on a bad branch, the corresponding reduction wins its game;
- the probability of all bad branches is bounded.

It must never assert that the constant fallback from
`traceOfReductionOutput` is valid with high probability.

## Running-time obligations

For each named reduction, record and prove an exact symbolic call count:

- outer adversary calls;
- extractor calls by proof-system layer;
- bus comparisons;
- segment/step iterations;
- memory-opening operations.

The initial theorem may conclude “cost according to the declared accounting
interface.” Promotion to a PPT theorem requires either:

1. a trusted manual lemma for each primitive algorithm plus verified
   composition; or
2. an executable machine/circuit cost semantics connected to `Alg.run`.

The distinction must appear in theorem names and documentation.

## Development sequence and gates

### Q0: probability spike

Implement the six substrate lemmas above in a toy module. Gate: a one-page
example proves a union bound for a deterministic valid-or-collision reduction.

### Q1: one-chip bus game

Use one step extractor and one chip extractor. Gate: Lean proves that invalid
output probability is bounded by two KS failures plus collision advantage, with
one adversary run and explicit call counts.

### Q2: current four-inner Bus

Lift `segmentReduction` to the algorithm interface. Gate: reproduce the five KS
terms plus one collision term and show the outer extraction result is shared.

### Q3: memory one-step games

Make the pre-invariant-only `reconstructStep` theorem
valid-or-binding-break. Gate: read produces a position break or a reconstructed
full step; write produces a position/update break or a reconstructed full step;
other operations reconstruct without a memory bad event. Then fold the same
interface over a segment and prove the final full-memory boundary.

### Q4: recursion and full equation

Compose the concrete semantic proof, segment extraction, memory reconstruction,
and recursion. Gate: derive the exact final advantage equation and cost bound.

### Q5: model instantiation review

State which concrete components plausibly satisfy each assumption and in which
model. Gate: approval by a human cryptographer; no claim that Lean proved the
primitive assumptions themselves.

## Migration rule

Qualitative theorems remain useful only if their reduction functions and bad
outputs map directly into these games. If a perfect proof uses contradiction or
classical choice in place of a named reduction, it must be refactored before it
can be cited by the computational theorem.
