import Mathlib

/-!
# Generic cryptographic notions (definitions only)

Scheme-independent definitions the whole development rests on. This file is
**definitions only**; the consistency-floor models that witness their
satisfiability (I6) live in `CryptoSanity.lean`.

The file is split into two tiers (`docs/INVARIANTS.md` I4):

## Frozen kernel — the stable heart, not to be forked or re-shaped
* `Relation` — a statement/witness relation.
* `ArgumentSystem` — a non-interactive argument (verifier only; see below).
* `Extractor` + `KnowledgeSound` — straight-line knowledge soundness.

## Provisional — the commitment layer, expected to change
* `VectorCommitment` with `Complete`, `PositionBinding`, and `UpdateBinding`.
* `HashCommitment` (for the bus commitment; its collision assumption is
  `Reduction.crAssumption`, not a predicate here).

These binding/CR notions are **not** frozen. `UpdateBinding` is the
commitment-realizability property used by memory reconstruction; the earlier
condition on openings away from an updated address did not rule out
commitments that pass `verify` but are not equal to `commit m` for any memory
`m`. This branch defines **no** standalone `CollisionResistant` predicate: the bus
commitment's collision assumption is packaged directly as a `HardnessAssumption`
(`Reduction.crAssumption`), discharged via its `.Holds`. These declarations may
change without a constitutional amendment; see the `provisional` note on each.

## Soundness is modeled as *perfect straight-line extraction* (no probabilities)

Every security notion below is phrased in a **perfect**, probability-free style:
the relevant "bad event" simply never happens. For knowledge soundness this
reads "whenever a proof verifies, the extractor returns a valid witness"; for the
commitments, "no two accepted openings disagree" and "the commitment map is
injective".

We model an adversary as the already-sampled output of a single run, so its
advantage is a `{0,1}` indicator; a negligibility predicate then collapses to
"the bad event is eventually false". Since every reduction here is pointwise and
the one non-trivial base case fails by an arithmetic contradiction, neither the
security parameter nor a real-analysis layer does any work, so we drop them.
Recovering quantitative security later means reintroducing, jointly, real-valued
advantages, randomized adversaries (e.g. via `PMF`), and negligibility; only the
soundness/binding predicates would change, not the structures.

`ArgumentSystem` carries only a verifier: the document's `Π = (Prove, Verify)`
has a prover too, but it plays no role in soundness, so we omit it.
-/

namespace VanillaZkVM

/-! ## Frozen kernel (I4) — relations and argument systems:

      Relation              -- statements, witnesses, membership
         ▲  R
      ArgumentSystem R      -- proof type + verifier for `R`
         ▲  AS
      Extractor R AS        -- From R.Stmt and AS.Proof, we get R.Wit
         ▲  ∃ E
      KnowledgeSound AS     -- every accepting proof for AS extracts
-/

/-- A relation `R ⊆ Stmt × Wit`, given by its statement and witness types and a
membership predicate. We write `R.rel x w` for "`(x; w) ∈ R`". -/
structure Relation where
  Stmt : Type
  Wit : Type
  rel : Stmt → Wit → Prop

/-- A non-interactive argument system for a relation `R`, given by its proof type
and verifier. `verify` is morally a Boolean polynomial-time algorithm; we phrase
acceptance as a `Prop`, reading `verify x p` as "`Verify(x, p) = 1`".

Paper: `def:zkvm` writes each system as `Π = (Prove, Verify)`. Lean deliberately
omits `Prove`, which plays no role in the soundness statements formalized here. -/
structure ArgumentSystem (R : Relation) where
  Proof : Type
  verify : R.Stmt → Proof → Prop

/-- A straight-line extractor for `AS`: it maps a statement and a proof to a
candidate witness, without rewinding or reading the adversary's code. -/
structure Extractor (R : Relation) (AS : ArgumentSystem R) where
  extract : R.Stmt → AS.Proof → R.Wit

/-- `AS` is **knowledge-sound** (perfect straight-line extraction) if there is a
single universal extractor `E` such that whenever a proof verifies for a
statement, `E` recovers a valid witness.

Paper: `def:extractable` / `eq:extractable`. Lean deliberately takes the
perfect, probability-free specialization required by I8. -/
def KnowledgeSound {R : Relation} (AS : ArgumentSystem R) : Prop :=
  ∃ E : Extractor R AS, ∀ (x : R.Stmt) (p : AS.Proof),
    AS.verify x p → R.rel x (E.extract x p)

/-! ## Provisional — vector commitments and their binding notions

The whole commitment/binding layer is **provisional** (I4): not frozen, expected
to change. Do not depend on the exact current shape. -/

/-- A vector commitment scheme `Com = (Commit, Open, Verify)`. A vector is a
total map `Index → Value`. `verify C i v p` checks that position `i` of the
committed vector holds value `v` under commitment `C`.

Paper: `def:binding` (commit/open/verify interface).

**Provisional** (I4): the binding notions below are expected to change. -/
structure VectorCommitment where
  Value : Type
  Index : Type
  Com : Type
  OpenProof : Type
  commit : (Index → Value) → Com
  openProof : (Index → Value) → Index → OpenProof
  verify : Com → Index → Value → OpenProof → Prop

namespace VectorCommitment

/-- **Commitment completeness** (perfect): an honest opening always verifies.
This makes explicit the correctness property used by the binding reductions,
as requested by the instruction preceding `def:binding` in ch05.

**Provisional** (I4). -/
def Complete (VC : VectorCommitment) : Prop :=
  ∀ (m : VC.Index → VC.Value) (i : VC.Index),
    VC.verify (VC.commit m) i (m i) (VC.openProof m i)

/-- **Position-binding** (perfect): no commitment admits two accepted openings of
different values at the same position.

Paper: `def:binding`.

**Provisional** (I4). -/
def PositionBinding (VC : VectorCommitment) : Prop :=
  ∀ (C : VC.Com) (i : VC.Index) (v v' : VC.Value) (pi pi' : VC.OpenProof),
    VC.verify C i v pi → VC.verify C i v' pi' → v = v'

/-- **Update-binding** (perfect, `def:binding`, ch05): suppose `m'` is obtained
from `m` by changing only `addr`, whose new value is `x`. If the same opening
`pi` verifies the old value against `VC.commit m` and the new value against a
candidate commitment `C'`, then `C'` must equal `VC.commit m'`.

In plain terms, merely passing verification at the changed address is not
enough. The commitment after the write must be the value computed by
`VC.commit` from exactly the updated full memory.

The first two premises describe "`m'` is `m` updated at `addr`" directly:
`m' addr = x`, and `m'` agrees with `m` at every other address. This avoids a
global `DecidableEq VC.Index` requirement.
As in the paper, this property is assumed independently of `PositionBinding`;
neither implication is built into the definitions.

**Provisional** (I4). -/
def UpdateBinding (VC : VectorCommitment) : Prop :=
  ∀ (m m' : VC.Index → VC.Value) (addr : VC.Index) (x : VC.Value)
    (C' : VC.Com) (pi : VC.OpenProof),
    m' addr = x → (∀ j, j ≠ addr → m' j = m j) →
    VC.verify (VC.commit m) addr (m addr) pi →
    VC.verify C' addr x pi →
    C' = VC.commit m'

end VectorCommitment

/-! ## Provisional — update-binding break witness -/

/-- The data needed to describe a possible update-binding failure: the memory
before and after one write, the changed address and value, and the candidate
commitment and opening proof accepted for that write.

`IsUpdateBindingBreak` below states that the memories differ only by the stated
write and that the proof verifies against both commitments, even though the
candidate commitment is not `VC.commit` of the updated memory. An explicit
extract-or-break reduction can return this record when reconstruction fails. -/
structure UpdateBindingBreak (VC : VectorCommitment) where
  preMemory : VC.Index → VC.Value
  postMemory : VC.Index → VC.Value
  index : VC.Index
  newValue : VC.Value
  postCommitment : VC.Com
  proof : VC.OpenProof

/-- `IsUpdateBindingBreak VC b` holds when `b` describes a valid one-address
update whose proof is accepted, but whose candidate commitment is not the
commitment of the resulting memory. -/
def IsUpdateBindingBreak (VC : VectorCommitment)
    (b : UpdateBindingBreak VC) : Prop :=
  b.postMemory b.index = b.newValue ∧
  (∀ j, j ≠ b.index → b.postMemory j = b.preMemory j) ∧
  VC.verify (VC.commit b.preMemory) b.index (b.preMemory b.index) b.proof ∧
  VC.verify b.postCommitment b.index b.newValue b.proof ∧
  b.postCommitment ≠ VC.commit b.postMemory

/-! ## Provisional — collision-resistant (bus) commitment -/

/-- A **keyed** hash-style commitment: a family `hash : Key → Domain → Digest`,
one hash function per key.

Paper: `def:bus-cr`.

**Provisional** (I4): the bus commitment's collision assumption is packaged as
`Reduction.crAssumption`, not a standalone predicate here. -/
structure HashCommitment where
  Key : Type
  Domain : Type
  Digest : Type
  hash : Key → Domain → Digest

end VanillaZkVM
