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
* `HashCommitment` with `CollisionResistant` (for the bus commitment).

These binding/CR notions are **not** frozen: `UpdateBinding` supersedes the earlier
punctured-binding notion (which was insufficient — it could not pin a reconstructed
post-write root into the image of `commit`; see `Memory.lean`), and
`CollisionResistant` may gain a keyed/algorithmic variant. They may change without a
constitutional amendment; see the `provisional` note on each.

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

/-- **Commitment completeness** (perfect): an *honest* opening always verifies.
Provides the honest opening that position binding compares an adversarial opening
against, and that update binding uses to identify the honest pre-root.

Paper: `def:binding` (correctness of `open`/`verify`).

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

/-- **Update-binding** (perfect): a single opening `π` that opens an *honest*
commitment `commit m` at `addr` (necessarily to `m addr`) and also opens some `C'`
at `addr` to `x` forces `C'` to be the honest commitment of `m` point-updated at
`addr` to `x`. The updated vector `m'` is described pointwise (`m' addr = x`, and
`m' j = m j` off `addr`), so no `DecidableEq VC.Index` is required; classically
`m'` is unique.

This is the property that pins a *reconstructed* post-write root to an actual
output of `commit`. Position binding only bounds what a root can be *opened to*
(non-equivocation); it does **not** force a committed root to lie in the image of
`commit`, which is exactly what full-memory reconstruction needs (`Memory.lean`).

Paper: `def:binding`.

**Provisional** (I4): supersedes the earlier, insufficient punctured-binding
notion. The `MemorySanity.appendBitVC` model satisfies position binding yet fails
this, witnessing that position binding does **not** imply update binding — it is a
genuinely additional requirement, not derivable from position binding. -/
def UpdateBinding (VC : VectorCommitment) : Prop :=
  ∀ (m m' : VC.Index → VC.Value) (addr : VC.Index) (x : VC.Value)
    (C' : VC.Com) (π : VC.OpenProof),
    m' addr = x → (∀ j, j ≠ addr → m' j = m j) →
    VC.verify (VC.commit m) addr (m addr) π → VC.verify C' addr x π →
    C' = VC.commit m'

/-! ## Provisional — collision-resistant (bus) commitment -/

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
