import VanillaZkVM.Reduction
import VanillaZkVM.CryptoSanity

/-!
# A test use case for our reduction vocabulary

The protocol: a value is committed as `d = hash k w`, and a proof is a *pair* of
openings of `d`, checked independently by two "inspectors":
- inspector 1 checks its opening against a property `P`
- inspector 2 checks its own against `Q`.

The verifier never compares the two openings; only the digest ties them together. If they agree,
the common value is a valid witness; if they disagree, they are a collision under `k`.

## Main results
* `twoInspectors_extract_or_collision` — the two-inspector system `ReducesTo`
  collision resistance at `k`, so `ReducesTo` is satisfiable (not `False`).
* `twoInspectors_knowledgeSound` — the thin corollary applied end-to-end; at
  `CryptoSanity`'s injective model it discharges with nothing left to assume.
* `constHashCommitment` examples — under the constant hash a cheating proof is
  accepted, extraction fails, and the reduction's output is a genuine break:
  the break branch of `ExtractOrBreak` is reachable (not vacuous).
-/

namespace VanillaZkVM

variable (H : HashCommitment) (k : H.Key) (P Q : H.Domain → Prop)

/-- "The value committed in `d` satisfies both `P` and `Q`."
(`@[reducible]` only so the examples below can write numerals.) -/
@[reducible] def twoInspectorsRel : Relation where
  Stmt := H.Digest
  Wit := H.Domain
  rel := fun d w => H.hash k w = d ∧ P w ∧ Q w

/-- A proof is a pair of openings: inspector 1 checks `P`, inspector 2 checks
`Q`. Nothing forces the two openings to be equal. -/
@[reducible] def twoInspectorsAS : ArgumentSystem (twoInspectorsRel H k P Q) where
  Proof := H.Domain × H.Domain
  verify := fun d ab =>
    (H.hash k ab.1 = d ∧ P ab.1) ∧
    (H.hash k ab.2 = d ∧ Q ab.2)

/-- The two-inspector system reduces to collision resistance at `k`: the
extractor returns opening 1, the reduction returns the pair. -/
theorem twoInspectors_extract_or_collision :
    Reduction.ReducesTo (twoInspectorsAS H k P Q) (Reduction.crAssumption H k) := by
  refine ⟨fun _ ab => ab.1, fun _ ab => ab, ?_⟩
  rintro d ⟨a, b⟩ ⟨⟨ha, hP⟩, hb, hQ⟩
  by_cases hEq : a = b
  · exact Or.inl ⟨ha, hP, hEq ▸ hQ⟩
  · exact Or.inr ⟨hEq, ha.trans hb.symm⟩

/-- Assuming the collision assumption holds, the two-inspector system is
knowledge-sound. -/
theorem twoInspectors_knowledgeSound (hHolds : (Reduction.crAssumption H k).Holds) :
    KnowledgeSound (twoInspectorsAS H k P Q) := by
  obtain ⟨E, B, hEB⟩ := twoInspectors_extract_or_collision H k P Q
  exact Reduction.knowledgeSound_of_extractOrBreak hEB hHolds

-- Non-vacuity: at the injective model, knowledge soundness discharges completely.
example (P Q : idHashCommitment.Domain → Prop) :
    KnowledgeSound (twoInspectorsAS idHashCommitment () P Q) :=
  twoInspectors_knowledgeSound idHashCommitment () P Q
    (fun _ hbb => hbb.1 hbb.2)

/-- Countermodel hash: everything collides. -/
@[reducible] def constHashCommitment : HashCommitment where
  Key := Unit
  Domain := ℕ
  Digest := ℕ
  hash := fun _ _ => 0

-- Break-branch reachability: the cheating proof `(2, 11)` is accepted for
-- statement `0` …
example :
    (twoInspectorsAS constHashCommitment () Even (fun n => 10 ≤ n)).verify 0 (2, 11) :=
  ⟨⟨rfl, 1, rfl⟩, rfl, by decide⟩

-- … the extractor's candidate `2` is not a valid witness …
example :
    ¬ (twoInspectorsRel constHashCommitment () Even (fun n => 10 ≤ n)).rel 0 2 := by
  rintro ⟨-, -, h10⟩
  exact absurd h10 (by decide)

-- … and the reduction's candidate `(2, 11)` is a genuine break.
example : (Reduction.crAssumption constHashCommitment ()).IsBreak (2, 11) :=
  ⟨by decide, rfl⟩

end VanillaZkVM
