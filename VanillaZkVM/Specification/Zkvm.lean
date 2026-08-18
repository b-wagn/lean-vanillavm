import Mathlib

/-!
# What a zkVM system is

The abstract packaging every concrete VM instantiates: a state type with a step
predicate, a fixed step count, boundary projections, and a final verifier — plus
the trace-validity predicate over it.

This file deliberately depends on nothing but Mathlib. What the system is meant
to *prove* — the correct-execution relation `R*`, correct-trace extractability,
and the keystone equivalence with knowledge soundness — is the specification
proper and lives in `Cte.lean`, which is the only file in `Specification/` that
needs the argument-system kernel.

## Main definitions
* an abstract `ZkVM` system (compare the zkVM of the vanilla document, stripped
  to what the security statement needs);
* `ZkVM.TraceValid`, the validity of a candidate execution trace for a statement.

Concrete systems (the two-step toy in `VMs/TwoStep/`, later the full vanilla VM)
instantiate `ZkVM` and prove `CTE` from `Cte.lean`.
-/

namespace VanillaZkVM

/-! ## Abstract zkVM systems -/

/-- An abstract zkVM system: a state type with a step predicate, a fixed step
count `T`, a statement type with `initial`/`terminal` boundary projections, and
the final proof type with its verifier.

This is Lean-only abstract packaging, motivated by `def:zkvm` and corrected
`def:cte` at the revision pinned in `docs/PAPER_REVISION.md`; the full
formalization of `def:zkvm` is the Issue-7 concrete instance. At the pinned
revision, program code and `T` are fixed system parameters rather than adversary
outputs. Lean omits code here because the abstract step predicate already closes
over it. -/
structure ZkVM where
  State : Type
  step : State → State → Prop
  T : ℕ
  Stmt : Type
  initial : Stmt → State
  terminal : Stmt → State
  Proof : Type
  verify : Stmt → Proof → Prop

namespace ZkVM

variable (V : ZkVM)

/-- A candidate trace `tr` is **valid** for statement `x` when it starts at the
claimed initial state, ends after `T` steps at the claimed final state, and every
step satisfies `step`.

Paper: the winning condition of `def:cte` and the step conjunct of
`eq:relation-star`. -/
def TraceValid (x : V.Stmt) (tr : ℕ → V.State) : Prop :=
  tr 0 = V.initial x ∧ tr V.T = V.terminal x ∧
  ∀ i, i < V.T → V.step (tr i) (tr (i + 1))

end ZkVM

end VanillaZkVM
