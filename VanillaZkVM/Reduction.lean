import VanillaZkVM.Crypto

/-!
# Reduction vocabulary (extract-or-break)

The reusable, *lightweight* reduction discipline (`docs/INVARIANTS.md` I9) shared by
every security layer: a break of a guarantee yields **either** a valid witness
**or** an explicit break of a named hardness assumption, with the assumption
applied only in a thin corollary. This is the shape the paper's layer lemmas take
(`lem:segment` bus unification, ch05 §5.2 reductions); it is standardized here so
memory (position/update binding), the bus (collision resistance), and the later
recursion layers all reduce through one interface.

## Main definitions
* `Assumption` — a hardness assumption, given by its *break-witness* type and the
  predicate recognizing a genuine break.
* `Assumption.Holds` — the assumption is true: no genuine break exists (perfect,
  probability-free, I8).
* `ExtractOrBreak` — the reduction shape: an extractor `E` and a reduction `B`
  such that every accepting proof either extracts a valid witness or produces
  a genuine break.
* `ReducesTo` — the reusable existential (`∃ E B, ExtractOrBreak …`) a layer
  states as its guarantee.

## Main results
* `knowledgeSound_of_extractOrBreak` — the thin corollary: if the assumption
  holds, extract-or-break gives knowledge soundness.
* `crAssumption` — collision resistance (at a fixed key) packaged as an
  `Assumption`; the canonical worked instance. A segment/bus layer applies it
  end-to-end in Issue 5 (at the execution's bus key).

Both `E` and `B` are **plain functions** (`docs/CONVENTIONS.md`: adversaries and
reductions are plain functions, efficiency a separate future concern). No
advantages/`negl`/running time appear here — those are Issue 6.
-/

namespace VanillaZkVM
namespace Reduction

/-- A hardness assumption, presented by its **break-witness** type `Break` and the
predicate `IsBreak` recognizing a genuine break. The assumption is a black box;
`Break`/`IsBreak` are the only interface a reduction sees.

Paper: ch05 §5.2 — the assumptions the security reductions break (`Adv^cr`,
`Adv^pos`, `Adv^upd`), each here in its perfect (probability-free) form. -/
structure Assumption where
  Break : Type
  IsBreak : Break → Prop

/-- The assumption **holds**: no genuine break exists. This is the perfect,
probability-free (I8) reading of "the advantage is zero". -/
def Assumption.Holds (A : Assumption) : Prop := ∀ w, ¬ A.IsBreak w

/-- **Extract-or-break** for an argument system `AS` against assumption `A`: an
extractor `E` and a reduction `B` such that on every accepting proof
`(x, p)`, either `E` returns a valid `R`-witness, or `B` produces a genuine break
of `A`. The reduction `B` never assumes `A`; it *exhibits* a break when extraction
fails (`lem:segment` bad-event structure). -/
def ExtractOrBreak {R : Relation} (AS : ArgumentSystem R) (A : Assumption)
    (E : R.Stmt → AS.Proof → R.Wit) (B : R.Stmt → AS.Proof → A.Break) : Prop :=
  ∀ x p, AS.verify x p → R.rel x (E x p) ∨ A.IsBreak (B x p)

/-- `AS` reduces to assumption `A` -/
def ReducesTo {R : Relation} (AS : ArgumentSystem R) (A : Assumption) : Prop :=
  ∃ (E : R.Stmt → AS.Proof → R.Wit) (B : R.Stmt → AS.Proof → A.Break),
    ExtractOrBreak AS A E B

/-- If `E`, `B` satisfy extract-or-break for `AS`, and the assumption `A`
actually holds, then `AS` is knowledge-sound. -/
theorem knowledgeSound_of_extractOrBreak {R : Relation} {AS : ArgumentSystem R}
    {A : Assumption} {E : R.Stmt → AS.Proof → R.Wit} {B : R.Stmt → AS.Proof → A.Break}
    (h : ExtractOrBreak AS A E B) (hA : A.Holds) : KnowledgeSound AS :=
  ⟨⟨E⟩, fun x p hp => (h x p hp).resolve_right (hA _)⟩

/-! ## Worked instance: collision resistance -/

/-- Collision resistance of a keyed bus commitment `H` **at a fixed key `k`**,
packaged as an `Assumption`: a break is a colliding pair under `k` (distinct
preimages with equal digest). A reduction to this `Assumption` returns such a pair
as its break — e.g. the segment/bus layer built in Issue 5, instantiated at the
execution's bus key. A consumer discharges the break branch from
`(crAssumption H k).Holds` ("no pair collides under `k`"), which
`CollisionResistant H` supplies at every key.

Paper: `def:bus-cr` / `Adv^cr`. -/
def crAssumption (H : HashCommitment) (k : H.Key) : Assumption where
  Break := H.Domain × H.Domain
  IsBreak := fun bb => bb.1 ≠ bb.2 ∧ H.hash k bb.1 = H.hash k bb.2

/-- Update binding of the memory commitment `VC`, packaged as an `Assumption`:
a break is an `UpdateBindingBreak` record that is genuine in the sense of
`IsUpdateBindingBreak`.

Paper: `def:binding` / `Adv^upd`. -/
def updAssumption (VC : VectorCommitment) : Assumption where
  Break := UpdateBindingBreak VC
  IsBreak := IsUpdateBindingBreak VC

/-- Position binding of the memory commitment `VC`, packaged as an
`Assumption`.

Paper: `def:binding` / `Adv^pos`. -/
def posAssumption (VC : VectorCommitment) : Assumption where
  Break := PositionBindingBreak VC
  IsBreak := IsPositionBindingBreak VC

end Reduction
end VanillaZkVM
