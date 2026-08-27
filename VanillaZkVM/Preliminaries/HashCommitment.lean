import Mathlib

/-!
# The collision-resistant (bus) commitment (definitions only)

The hash-style commitment used for the bus, kept separate from the vector
commitment in `VectorCommitment.lean` because the two layers are independent:
memory reconstruction consumes only the vector-commitment binding notions, while
the bus consumes only collision-resistance.

## Provisional (`docs/INVARIANTS.md` I4) — expected to change
`HashCommitment` with `CollisionResistant`. Not frozen: `CollisionResistant` may
gain a keyed/algorithmic variant, so it may change without a constitutional
amendment.

As everywhere in `Preliminaries/`, the notion is the **perfect**,
probability-free specialization required by I8 — here, plain injectivity of the
commitment map. The rationale is documented once in `ArgumentSystem.lean`.

`VMs/Bus.lean` consumes these declarations to identify the four buses extracted
inside one segment. A concrete VM can then use the resulting committed-step
theorem to prove its `StepInterface.BusBridge`; the two-layer VM does so in
`VMs/TwoStep/Bus.lean`. No theorem compares buses from different segments.
-/

namespace VanillaZkVM

/-- A hash-style commitment `hash : Domain → Digest`.

Paper: `def:bus-cr`.

**Provisional** (I4): may gain a keyed/algorithmic variant. -/
structure HashCommitment where
  Domain : Type
  Digest : Type
  hash : Domain → Digest

/-- **Collision-resistance** (perfect): the commitment map is injective.

Paper: `def:bus-cr`. Lean deliberately uses the probability-free
specialization required by I8.

**Provisional** (I4): may gain a keyed/algorithmic variant. -/
def CollisionResistant (H : HashCommitment) : Prop :=
  ∀ b b' : H.Domain, H.hash b = H.hash b' → b = b'

end VanillaZkVM
