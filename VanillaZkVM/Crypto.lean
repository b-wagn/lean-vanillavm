-- This file goes at `VanillaZkVM/VanillaZkVM/Crypto.lean`.

import VanillaZkVM.Model

/-!
# Generic cryptographic notions (stage 1)

Scheme-independent definitions the whole development rests on:

* `Relation` — a statement/witness relation.
* `ArgumentSystem` — a non-interactive argument `Π = (Prove, Verify)`.
* `Extractor` + `KnowledgeSound` — straight-line knowledge soundness.
* `VectorCommitment` with `PositionBinding` and `PuncturedBinding`.
* `HashCommitment` with `CollisionResistant` (for the bus commitment).

## Soundness is modeled as *perfect straight-line extraction* (no probabilities)

Every security notion below — knowledge soundness of the argument systems,
position- and punctured-binding of the memory commitment, and
collision-resistance of the bus commitment — is phrased in a **perfect**,
probability-free style: the relevant "bad event" simply never happens. For
knowledge soundness this reads "whenever a proof verifies, the extractor returns
a valid witness"; for the commitments, "no two accepted openings disagree" and
"the commitment map is injective".

### Why not negligibility?

We model an adversary as (the already-sampled output of) a single run, so its
advantage in any game is a `{0,1}`-valued indicator. For such an indicator, a
negligibility predicate collapses to "the bad event is eventually false" — and
since

  * every reduction in the security proof is *pointwise* (a bad event on some
    input implies a bad event of a sub-component on the same input), and
  * the one non-trivial base case (a `combine` proof at `N = N_seg`) fails by an
    outright arithmetic contradiction, `N_L + N_R ≥ 2·N_seg > N_seg`, not a
    probability bound,

the security parameter `λ` and the whole real-analysis layer (inverse
polynomials, closure of a negligibility predicate under sums and constant
multiples) do no discriminating work. They would earn their keep only with
genuinely *randomized* adversaries whose advantages lie strictly inside
`(0, 1)`, so we drop them.

### What this costs, and how to upgrade

We give up the paper's theorem-as-a-numeric-bound
(`ε ≤ Adv₄ + (m-1)·Adv₃ + …`). The source document itself notes those numbers are
not meaningful under its idealization, so structurally nothing is lost: we prove
the qualitative statement — "an accepting final proof yields a valid execution
trace" — as a clean logical/inductive fact.

"A perfectly sound argument system" is a strong object no real construction
meets. That is fine here: it is an *assumption we never discharge* — precisely
the heuristic the document flags — so the main theorem stays a meaningful
conditional. Recovering quantitative security later means reintroducing, jointly:
real-valued advantages, randomized adversaries (e.g. via `PMF`), and a
negligibility predicate. Only the soundness/binding predicates would change; the
structures below would not.
-/

namespace VanillaZkVM

/-! ## Relations and argument systems -/

/-- A relation `R ⊆ Stmt × Wit`, given by its statement and witness types and a
membership predicate. We write `R.rel x w` for "`(x; w) ∈ R`". -/
structure Relation where
  Stmt : Type
  Wit : Type
  rel : Stmt → Wit → Prop

/-- A non-interactive argument system `Π = (Prove, Verify)` for a relation `R`.
`verify` is morally a Boolean polynomial-time algorithm; we phrase acceptance as
a `Prop`, reading `verify x p` as "`Verify(x, p) = 1`". `prove` is kept to match
the tuple `Π = (Prove, Verify)` but plays no role in the soundness development. -/
structure ArgumentSystem (R : Relation) where
  Proof : Type
  prove : R.Stmt → R.Wit → Proof
  verify : R.Stmt → Proof → Prop

/-- A straight-line extractor for `AS`: it maps a statement and a proof to a
candidate witness, without rewinding or reading the adversary's code. -/
structure Extractor (R : Relation) (AS : ArgumentSystem R) where
  extract : R.Stmt → AS.Proof → R.Wit

/-- `AS` is **knowledge-sound** (perfect straight-line extraction) if there is a
single universal extractor `E` such that whenever a proof verifies for a
statement, `E` recovers a valid witness. Compare Definition
(Knowledge-soundness): the negligible error is idealized to zero (see this
file's header). -/
def KnowledgeSound {R : Relation} (AS : ArgumentSystem R) : Prop :=
  ∃ E : Extractor R AS, ∀ (x : R.Stmt) (p : AS.Proof),
    AS.verify x p → R.rel x (E.extract x p)

/-! ## Vector commitments and their binding notions -/

/-- A vector commitment scheme `Com = (Commit, Open, Verify)`. A vector is a
total map `Index → Value`. `commit` returns a commitment; `openProof` produces an
opening for a position; `verify C i v p` checks that position `i` of the
committed vector holds value `v` under commitment `C`. -/
structure VectorCommitment where
  Value : Type
  Index : Type
  Com : Type
  OpenProof : Type
  commit : (Index → Value) → Com
  openProof : (Index → Value) → Index → OpenProof
  verify : Com → Index → Value → OpenProof → Prop

/-- Committed VM state `Ŝ = (pc, regs, mem̂)`: a VM state whose memory component
is a commitment value from `VC`. -/
abbrev CommittedVMState (VC : VectorCommitment) : Type := VMStateWith VC.Com

/-- **Position-binding** (perfect): no commitment admits two accepted openings of
different values at the same position. -/
def PositionBinding (VC : VectorCommitment) : Prop :=
  ∀ (C : VC.Com) (i : VC.Index) (v v' : VC.Value) (pi pi' : VC.OpenProof),
    VC.verify C i v pi → VC.verify C i v' pi' → v = v'

/-- **Punctured-binding** (perfect): if a single opening `pi` is accepted at
position `addr` under both `C` and `C'`, then `C` and `C'` agree at every other
position — any pair of accepted openings at `i ≠ addr` yields the same value. -/
def PuncturedBinding (VC : VectorCommitment) : Prop :=
  ∀ (C C' : VC.Com) (addr : VC.Index) (v v' : VC.Value) (pi : VC.OpenProof)
    (i : VC.Index) (u u' : VC.Value) (rho rho' : VC.OpenProof),
    VC.verify C addr v pi → VC.verify C' addr v' pi →
    VC.verify C i u rho → VC.verify C' i u' rho' →
    i ≠ addr → u = u'

/-! ## Collision-resistant (bus) commitment -/

/-- A hash-style commitment `hash : Domain → Digest`. The bus commitment
`Com_bus` is an instance whose `Domain` is the bus type (defined in stage 2). -/
structure HashCommitment where
  Domain : Type
  Digest : Type
  hash : Domain → Digest

/-- **Collision-resistance** (perfect): the commitment map is injective. Used to
unify the four inner-circuit buses in the segment layer of the security proof. -/
def CollisionResistant (H : HashCommitment) : Prop :=
  ∀ b b' : H.Domain, H.hash b = H.hash b' → b = b'

/-!
## Not yet defined (stage 2)

The **zkVM system** bundle (step predicates `φ_op`, the bus commitment `Com_bus`,
the memory commitment `Com_mem`, and the SNARK hierarchy `Π₀ … Π₄`) is assembled
in stage 2, once the concrete relations `R₀ … R₄` and operation predicates exist.
The pieces above are exactly the generic ingredients that bundle will refer to.
-/

end VanillaZkVM
