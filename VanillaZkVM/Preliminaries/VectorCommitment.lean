import Mathlib

/-!
# Vector commitments and their binding notions (definitions only)

The memory-commitment layer. This file is **definitions only**; the models that
witness satisfiability of the binding notions and the countermodel separating
them (I6) live in `VanillaZkVM/VMs/MemorySanity.lean`, beside the memory
reconstruction that consumes them.

## Provisional (`docs/INVARIANTS.md` I4) — expected to change
`VectorCommitment` with `Complete`, `PositionBinding`, and `UpdateBinding`, plus
the `UpdateBindingBreak` break witness.

These binding notions are **not** frozen; do not depend on their exact current
shape. `UpdateBinding` is the commitment-realizability property used by memory
reconstruction; the earlier condition on openings away from an updated address
did not rule out commitments that pass `verify` but are not equal to `commit m`
for any memory `m`. These declarations may change without a constitutional
amendment; see the `provisional` note on each.

Like every security notion in `Preliminaries/`, binding is stated in the
**perfect**, probability-free style: "no two accepted openings disagree" and "the
commitment map is injective", with no security parameter and no negligibility.
The rationale for that choice, and what recovering quantitative security would
require, is documented once in `ArgumentSystem.lean`.
-/

namespace VanillaZkVM

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

end VanillaZkVM
