import VanillaZkVM.Crypto

/-!
# Consistency-floor models for the crypto kernel

Non-vacuity witnesses (`docs/INVARIANTS.md` I6) for the definitions in
`Crypto.lean`, kept out of the definitions file so the kernel is definitions only.

## Main definitions
* `trivialAS` — the honest degenerate argument system for any relation.
* `idHashCommitment` — an injective hash model.

## Main results
* `knowledgeSound_trivialAS` — it is knowledge-sound, so `KnowledgeSound` is
  satisfiable (not `False`).
* `collisionResistant_iff_injective` — the keyed `CollisionResistant` is
  equivalent to per-key injectivity of `hash`.
* `collisionResistant_idHashCommitment` — an injective hash is collision-resistant,
  so `CollisionResistant` is satisfiable (not `False`).
-/

namespace VanillaZkVM

/-- The **trivial argument system** for `R`: a "proof" is literally a witness, and
`verify x w` just checks membership `(x; w) ∈ R`. This is the honest degenerate
argument — no succinctness, no hiding. Used only to witness satisfiability of
`KnowledgeSound`. -/
def trivialAS (R : Relation) : ArgumentSystem R where
  Proof := R.Wit
  verify := fun x w => R.rel x w

/-- **Non-vacuity of `KnowledgeSound`.** `KnowledgeSound` is an idealized
assumption. Here we discharge the worry — that it might be unsatisfiable, making
every `KnowledgeSound … → …` theorem vacuously true — by exhibiting a model:
`trivialAS` is knowledge-sound, with the identity extractor. This is a consistency
floor, not a security guarantee: it shows the assumption is not `False`, not that
any real (succinct) SNARK meets it. -/
theorem knowledgeSound_trivialAS (R : Relation) : KnowledgeSound (trivialAS R) :=
  ⟨⟨fun _ w => w⟩, fun _ _ h => h⟩

/-- The keyed `CollisionResistant` is equivalent to per-key injectivity of `hash`:
"no finder outputs a collision for its key" ⟺ "each keyed hash has no collision".
The forward direction packages any collision into the constant finder that returns
it. This documents the honest fact that, in the perfect (probability-free) model,
keying fixes only the *structure* — the notion is still injectivity per key;
efficiency/probability (Issue 6) is what would separate it from injectivity. -/
theorem collisionResistant_iff_injective (H : HashCommitment) :
    CollisionResistant H ↔
      ∀ (k : H.Key) (b b' : H.Domain), H.hash k b = H.hash k b' → b = b' := by
  constructor
  · intro hCR k b b' hbb
    by_contra hne
    exact hCR (fun _ => (b, b')) k ⟨hne, hbb⟩
  · intro hinj finder k hbreak
    exact hbreak.1 (hinj k _ _ hbreak.2)

/-- An injective keyed hash-commitment model (single key; `hash` ignores it and is
the identity on the domain). -/
def idHashCommitment : HashCommitment where
  Key := Unit
  Domain := ℕ
  Digest := ℕ
  hash := fun _ d => d

/-- **Non-vacuity of `CollisionResistant`.** `idHashCommitment` is
collision-resistant, so `CollisionResistant` is satisfiable (not `False`) — no
finder can output a collision of the identity map at any key. -/
theorem collisionResistant_idHashCommitment : CollisionResistant idHashCommitment :=
  (collisionResistant_iff_injective idHashCommitment).mpr (fun _ _ _ h => h)

end VanillaZkVM
