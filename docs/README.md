# AI-Assisted Documentation Index

## Purpose

This directory collects the plans, reviews, threat analyses, proof contracts,
and review checklists produced during the AI-assisted VanillaVM Lean
experiments. They are included on `yl-memory-reconstruction` so that the team
can review not only the Lean code, but also the reasoning and proposed project
structure that guided it.

These documents do not all describe the same code snapshot. Some are current
proof contracts, some are forward-looking proposals, and some are historical
or branch-specific reviews. The Lean declarations and successful build are the
source of truth about what is currently implemented.

## Suggested reading order

1. [`SECURITY_ARCHITECTURE.md`](SECURITY_ARCHITECTURE.md) — intended proof
   discipline and end-to-end implication chain.
2. [`MEMORY_RECONSTRUCTION.md`](MEMORY_RECONSTRUCTION.md) — current proof
   contract for the implementation on this branch.
3. [`PROOF_REVIEW_CHECKLIST.md`](PROOF_REVIEW_CHECKLIST.md) — questions for
   reviewing AI-generated security statements.
4. [`VANILLAVM_ROADMAP.md`](VANILLAVM_ROADMAP.md) — proposed route to a full
   VanillaVM theorem.
5. [`CONCRETE_SEMANTICS_PLAN.md`](CONCRETE_SEMANTICS_PLAN.md) and
   [`COMPUTATIONAL_SECURITY_DESIGN.md`](COMPUTATIONAL_SECURITY_DESIGN.md) —
   proposed semantic and quantitative layers.
6. The adversarial and invariant reviews for the history behind the current
   design.

## Status ledger

| Document | Status on `yl-memory-reconstruction` |
|---|---|
| `MEMORY_RECONSTRUCTION.md` | Current branch proof contract and axiom audit |
| `PROOF_REVIEW_CHECKLIST.md` | Shared review guidance |
| `SECURITY_ARCHITECTURE.md` | Shared architecture; some older Bus terminology remains |
| `VANILLAVM_ROADMAP.md` | Forward-looking; its progress table predates the latest implementation |
| `CONCRETE_SEMANTICS_PLAN.md` | Forward-looking proposal; interfaces still require team agreement |
| `COMPUTATIONAL_SECURITY_DESIGN.md` | Forward-looking proposal; not implemented |
| `BUS_SECURITY_PLAN.md` | Alternative design from `yl-bus-modifications-draft` |
| `MEMORY_INVARIANT_REVIEW.md` | Historical analysis that motivated the implemented reconstruction |
| `ADVERSARIAL_REVIEW.md` | Historical adversarial review of an earlier code snapshot |
| `ADVERSARIAL_REVIEW_RESPONSE.md` | Response to that historical review |
| `AXIOM_AUDIT.md` | Historical/branch-specific audit; use the current audit in `MEMORY_RECONSTRUCTION.md` for this branch |

## Provenance and interpretation

The documents other than `MEMORY_RECONSTRUCTION.md` were copied on 2026-07-27
from the AI-assisted working-document set in the
`yl-bus-modifications-draft` worktree. They are preserved for comparison and
human review rather than silently rewritten to make the alternative branches
appear identical.

When documents disagree:

1. distinguish a desired end-state from an implemented result;
2. prefer the current Lean theorem signature when assessing present behavior;
3. treat explicit non-claims and unresolved review questions as open work;
4. record the team decision before updating both the code and its proof
   contract.
