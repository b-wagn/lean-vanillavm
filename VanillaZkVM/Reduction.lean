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
* `ExtractOrBreak` — the reduction shape: a witness-extractor `E` and a
  break-extractor `B` such that every accepting proof either extracts a valid
  witness or produces a genuine break.
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

/-- **Extract-or-break** for an argument system `AS` against assumption `A`: a
witness-extractor `E` and a break-extractor `B` such that on every accepting proof
`(x, p)`, either `E` returns a valid `R`-witness, or `B` produces a genuine break
of `A`. The reduction never assumes `A`; it *exhibits* a break when extraction
fails (`lem:segment` bad-event structure). -/
def ExtractOrBreak {R : Relation} (AS : ArgumentSystem R) (A : Assumption)
    (E : R.Stmt → AS.Proof → R.Wit) (B : R.Stmt → AS.Proof → A.Break) : Prop :=
  ∀ x p, AS.verify x p → R.rel x (E x p) ∨ A.IsBreak (B x p)

/-- The reusable existential form: `AS` **reduces to** `A` when some
witness-extractor and break-extractor form an extract-or-break reduction. A layer
states its guarantee as `ReducesTo AS A` rather than re-spelling the
two-extractor existential each time. -/
def ReducesTo {R : Relation} (AS : ArgumentSystem R) (A : Assumption) : Prop :=
  ∃ (E : R.Stmt → AS.Proof → R.Wit) (B : R.Stmt → AS.Proof → A.Break),
    ExtractOrBreak AS A E B

/-- **Thin corollary.** If the assumption holds, an extract-or-break reduction is
knowledge-sound: the break branch is impossible, so `E` always succeeds. This is
the one place the assumption is consumed — cf. `lem:segment`, where collision
resistance is applied only after the reduction is built. -/
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

end Reduction
end VanillaZkVM
