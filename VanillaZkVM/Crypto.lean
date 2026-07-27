import Mathlib

/-!
# Generic cryptographic notions (stage 1)

Scheme-independent definitions the whole development rests on:

* `Relation` — a statement/witness relation.
* `ArgumentSystem` — a non-interactive argument (verifier only; see below).
* `Extractor` + `KnowledgeSound` — straight-line knowledge soundness.
* `VectorCommitment` with completeness, position binding, and update binding.
* `HashCommitment` with `CollisionResistant` (for the bus commitment).

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

/-! ## Relations and argument systems -/

/-- A relation `R ⊆ Stmt × Wit`, given by its statement and witness types and a
membership predicate. We write `R.rel x w` for "`(x; w) ∈ R`". -/
structure Relation where
  Stmt : Type
  Wit : Type
  rel : Stmt → Wit → Prop

/-- A non-interactive argument system for a relation `R`, given by its proof type
and verifier. `verify` is morally a Boolean polynomial-time algorithm; we phrase
acceptance as a `Prop`, reading `verify x p` as "`Verify(x, p) = 1`". Note that
we don't specify a prover, as we just care about soundness and not completeness. -/
structure ArgumentSystem (R : Relation) where
  Proof : Type
  verify : R.Stmt → Proof → Prop

/-- A straight-line extractor for `AS`: it maps a statement and a proof to a
candidate witness, without rewinding or reading the adversary's code. -/
structure Extractor (R : Relation) (AS : ArgumentSystem R) where
  extract : R.Stmt → AS.Proof → R.Wit

/-- `AS` is **knowledge-sound** (perfect straight-line extraction) if there is a
single universal extractor `E` such that whenever a proof verifies for a
statement, `E` recovers a valid witness. -/
def KnowledgeSound {R : Relation} (AS : ArgumentSystem R) : Prop :=
  ∃ E : Extractor R AS, ∀ (x : R.Stmt) (p : AS.Proof),
    AS.verify x p → R.rel x (E.extract x p)

/-- The **trivial argument system** for `R`: a "proof" is literally a witness, and
`verify x w` just checks membership `(x; w) ∈ R`. This is the honest degenerate
argument — no succinctness, no hiding. This is used only to guarantee satisfiability of
`KnowledgeSound` below. -/
def trivialAS (R : Relation) : ArgumentSystem R where
  Proof := R.Wit
  verify := fun x w => R.rel x w

/-- **Non-vacuity of `KnowledgeSound`.** `KnowledgeSound` is the an idealized
assumption. Here we discharge the  worry — that it might be unsatisfiable,
making every `KnowledgeSound … → …` theorem vacuously true — by exhibiting a model:
`trivialAS` is knowledge-sound, with the identity extractor.
This is a consistency floor, not a security guarantee: it
shows the assumption is not `False`, not that any real (succinct) SNARK meets it. -/
theorem knowledgeSound_trivialAS (R : Relation) : KnowledgeSound (trivialAS R) :=
  ⟨⟨fun _ w => w⟩, fun _ _ h => h⟩

/-! ## Vector commitments and their binding notions -/

/-- A vector commitment scheme `Com = (Commit, Open, Verify)`. A vector is a
total map `Index → Value`. `verify C i v p` checks that position `i` of the
committed vector holds value `v` under commitment `C`. -/
structure VectorCommitment where
  Value : Type
  Index : Type
  Com : Type
  OpenProof : Type
  commit : (Index → Value) → Com
  openProof : (Index → Value) → Index → OpenProof
  verify : Com → Index → Value → OpenProof → Prop

/-- **Commitment completeness** (perfect): every honest opening verifies. -/
def Complete (VC : VectorCommitment) : Prop :=
  ∀ (m : VC.Index → VC.Value) (i : VC.Index),
    VC.verify (VC.commit m) i (m i) (VC.openProof m i)

/-- **Position-binding** (perfect): no commitment admits two accepted openings of
different values at the same position. -/
def PositionBinding (VC : VectorCommitment) : Prop :=
  ∀ (C : VC.Com) (i : VC.Index) (v v' : VC.Value) (pi pi' : VC.OpenProof),
    VC.verify C i v pi → VC.verify C i v' pi' → v = v'

/-- **Punctured-binding** (perfect): if a single opening `pi` is accepted at
`addr` under both `C` and `C'`, then `C` and `C'` agree at every other position.

This historical non-equivocation property does not force `C'` to lie in the
image of `commit`, so it is insufficient for reconstructing post-write memory.
It remains here only to state the append-bit countermodel precisely. -/
def PuncturedBinding (VC : VectorCommitment) : Prop :=
  ∀ (C C' : VC.Com) (addr : VC.Index) (v v' : VC.Value) (pi : VC.OpenProof)
    (i : VC.Index) (u u' : VC.Value) (rho rho' : VC.OpenProof),
    VC.verify C addr v pi → VC.verify C' addr v' pi →
    VC.verify C i u rho → VC.verify C' i u' rho' →
    i ≠ addr → u = u'

/-- **Update-binding** (perfect): a shared opening path that opens an honest
pre-commitment at `addr` and a candidate post-commitment to `x` forces the
candidate to be the honest commitment of the point-updated memory.

The post-memory is supplied pointwise, avoiding a global
`DecidableEq VC.Index` requirement in the property itself. -/
def UpdateBinding (VC : VectorCommitment) : Prop :=
  ∀ (m m' : VC.Index → VC.Value) (addr : VC.Index) (x : VC.Value)
    (C' : VC.Com) (pi : VC.OpenProof),
    m' addr = x →
    (∀ j, j ≠ addr → m' j = m j) →
    VC.verify (VC.commit m) addr (m addr) pi →
    VC.verify C' addr x pi →
    C' = VC.commit m'

/-! ## Explicit vector-commitment failure records -/

/-- Data returned by a reduction attempting to break position binding. -/
structure PositionBindingBreak (VC : VectorCommitment) where
  commitment : VC.Com
  index : VC.Index
  leftValue : VC.Value
  rightValue : VC.Value
  leftProof : VC.OpenProof
  rightProof : VC.OpenProof

/-- The exact winning predicate for a position-binding failure record. -/
def IsPositionBindingBreak (VC : VectorCommitment)
    (b : PositionBindingBreak VC) : Prop :=
  VC.verify b.commitment b.index b.leftValue b.leftProof ∧
  VC.verify b.commitment b.index b.rightValue b.rightProof ∧
  b.leftValue ≠ b.rightValue

/-- Data returned by a reduction attempting to break update binding. The
point-updated post-memory is included explicitly so this record does not require
decidable equality on the abstract index type. -/
structure UpdateBindingBreak (VC : VectorCommitment) where
  preMemory : VC.Index → VC.Value
  postMemory : VC.Index → VC.Value
  index : VC.Index
  newValue : VC.Value
  postCommitment : VC.Com
  proof : VC.OpenProof

/-- The exact winning predicate for an update-binding failure record. -/
def IsUpdateBindingBreak (VC : VectorCommitment)
    (b : UpdateBindingBreak VC) : Prop :=
  b.postMemory b.index = b.newValue ∧
  (∀ j, j ≠ b.index → b.postMemory j = b.preMemory j) ∧
  VC.verify (VC.commit b.preMemory) b.index (b.preMemory b.index) b.proof ∧
  VC.verify b.postCommitment b.index b.newValue b.proof ∧
  b.postCommitment ≠ VC.commit b.postMemory

/-- Position binding rules out every certified position-binding break. -/
theorem PositionBinding.not_isPositionBindingBreak {VC : VectorCommitment}
    (hpos : PositionBinding VC) (b : PositionBindingBreak VC) :
    ¬IsPositionBindingBreak VC b := by
  rintro ⟨hleft, hright, hne⟩
  exact hne (hpos b.commitment b.index b.leftValue b.rightValue
    b.leftProof b.rightProof hleft hright)

/-- Update binding rules out every certified update-binding break. -/
theorem UpdateBinding.not_isUpdateBindingBreak {VC : VectorCommitment}
    (hupd : UpdateBinding VC) (b : UpdateBindingBreak VC) :
    ¬IsUpdateBindingBreak VC b := by
  rintro ⟨hat, hoff, hpre, hpost, hne⟩
  exact hne (hupd b.preMemory b.postMemory b.index b.newValue
    b.postCommitment b.proof hat hoff hpre hpost)

/-- Completeness and position binding make `commit` injective on memories. -/
theorem mem_eq_of_commit_eq {VC : VectorCommitment}
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    {m₁ m₂ : VC.Index → VC.Value} (h : VC.commit m₁ = VC.commit m₂) :
    m₂ = m₁ := by
  funext i
  have h₂ : VC.verify (VC.commit m₁) i (m₂ i) (VC.openProof m₂ i) := by
    rw [h]
    exact hComplete m₂ i
  exact (hpos (VC.commit m₁) i (m₁ i) (m₂ i)
    (VC.openProof m₁ i) (VC.openProof m₂ i)
    (hComplete m₁ i) h₂).symm

/-! ## Collision-resistant (bus) commitment -/

/-- A hash-style commitment `hash : Domain → Digest`. -/
structure HashCommitment where
  Domain : Type
  Digest : Type
  hash : Domain → Digest

/-- **Collision-resistance** (perfect): the commitment map is injective. -/
def CollisionResistant (H : HashCommitment) : Prop :=
  ∀ b b' : H.Domain, H.hash b = H.hash b' → b = b'

end VanillaZkVM
