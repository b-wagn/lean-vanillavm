import Mathlib

/-!
# Relations and argument systems — the frozen kernel (definitions only)

The scheme-independent heart the whole development rests on: relations,
non-interactive arguments, and straight-line knowledge soundness. This file is
**definitions only**; the consistency-floor model that witnesses their
satisfiability (I6) lives in `ArgumentSystemSanity.lean`.

## Frozen kernel (`docs/INVARIANTS.md` I4) — the stable heart, not to be forked
* `Relation` — a statement/witness relation.
* `ArgumentSystem` — a non-interactive argument (verifier only; see below).
* `Extractor` + `KnowledgeSound` — straight-line knowledge soundness.

The rest of `Preliminaries/` is the **provisional** commitment layer, which is
*not* frozen and is expected to change: `VectorCommitment.lean` (with `Complete`,
`PositionBinding`, and `UpdateBinding`) and `HashCommitment.lean` (with
`CollisionResistant`, for the bus commitment). Do not depend on the exact current
shape of either; each declaration there carries a `provisional` note.

## Soundness is modeled as *perfect straight-line extraction* (no probabilities)

Every security notion in `Preliminaries/` — here and in the commitment layer — is
phrased in a **perfect**, probability-free style: the relevant "bad event" simply
never happens. For knowledge soundness this reads "whenever a proof verifies, the
extractor returns a valid witness"; for the commitments, "no two accepted openings
disagree" and "the commitment map is injective".

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

end VanillaZkVM
