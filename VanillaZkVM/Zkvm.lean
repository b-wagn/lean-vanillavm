import VanillaZkVM.Crypto
import VanillaZkVM.Reduction

/-!
# What a zkVM system is, and correct-trace extractability (the abstract heart)

This is the central file. It defines, abstractly:

## Main definitions
* the VM state (absorbed from the old `Model` file);
* an abstract `ZkVM` system (compare the zkVM of the vanilla document, stripped
  to what the security statement needs);
* the correct-execution relation `Rstar` the system is meant to prove, and the
  final argument system `ASstar` viewed as an argument system for it;
* correct-trace extractability `CTE`, stated in VM-native terms.

## Main results
* The keystone theorem `cte_iff_knowledgeSound`:
  `CTE V ↔ KnowledgeSound V.ASstar`.
* `cte_of_reducesTo`: an extract-or-break reduction to an assumption family,
  plus the family holding, gives `CTE`.

Concrete systems (the two-step toy, later the full vanilla VM) instantiate
`ZkVM` and prove `CTE` — typically by proving `KnowledgeSound ASstar` and
invoking the equivalence.
-/

namespace VanillaZkVM

/-! ## VM states (Execution Model — Chapter 1) -/

/-- A 32-bit machine word (abstracted as `ℕ` for now). -/
abbrev Word : Type := ℕ
/-- A byte-addressed memory address. -/
abbrev Addr : Type := ℕ
/-- A byte stored in memory. -/
abbrev Byte : Type := ℕ

/-- A VM state parameterized by its memory representation `Mem`. The `k`
registers are abstracted as a total function `index ↦ value`.

Paper: ch01, section “Program, Execution, and VM State.” -/
structure VMStateWith (Mem : Type) where
  pc : Word
  regs : ℕ → Word
  mem : Mem

/-- Full VM state `S = (pc, regs, mem)` with explicit byte-addressed memory.

Paper: ch01, section “Program, Execution, and VM State.” -/
abbrev VMState : Type := VMStateWith (Addr → Byte)

/-- Committed VM state `Ŝ = (pc, regs, mem̂)`: memory replaced by a commitment.

Paper: ch02, section “Execution Segments,” and ch03 `eq:step-bus2`. -/
abbrev CommittedVMState (VC : VectorCommitment) : Type := VMStateWith VC.Com

/-- Memory update `mem[addr ↦ v]`. -/
def memUpdate (m : Addr → Byte) (addr : Addr) (v : Byte) : Addr → Byte :=
  Function.update m addr v

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

/-- The correct-execution relation `R*`: statements are boundary claims,
witnesses are traces, membership is trace validity.

Paper: `eq:relation-star`. This is deliberately the abstract trace-validity
skeleton: requiring statements to carry full-memory boundary states and the
verifier to commit them is left to the full Vanilla VM instance in Issue 7. -/
def Rstar : Relation where
  Stmt := V.Stmt
  Wit := ℕ → V.State
  rel := fun x tr => V.TraceValid x tr

/-- The system's final argument system, viewed as an argument system for `R*`. -/
def ASstar : ArgumentSystem V.Rstar where
  Proof := V.Proof
  verify := V.verify

/-- **Correct-trace extractability** (VM-native form): a single trace-extractor
turns every accepting proof into a valid `T`-step execution of the claim.

Paper: `def:cte` at the revision pinned in `docs/PAPER_REVISION.md`. This is its
perfect, probability-free core; PPT/probability bookkeeping is deferred by I8,
and the full-memory boundary commitment equations belong to the concrete
Issue-7 instance. -/
def CTE : Prop :=
  ∃ E : V.Stmt → V.Proof → (ℕ → V.State),
    ∀ (x : V.Stmt) (p : V.Proof), V.verify x p → V.TraceValid x (E x p)

/-- **Keystone.** Correct-trace extractability is exactly knowledge soundness of
the final argument system for the correct-execution relation `R*`. The proof is
structural: both sides are "∃ extractor, ∀ accepting (x, p), the output is a
valid trace", differing only in packaging the extractor as a bare function versus
an `Extractor` record.

Paper: `rem:cte-ks`. -/
theorem cte_iff_knowledgeSound : V.CTE ↔ KnowledgeSound V.ASstar := by
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨⟨E⟩, ?_⟩
    intro x p hp
    exact hE x p hp
  · rintro ⟨E, hE⟩
    refine ⟨E.extract, ?_⟩
    intro x p hp
    exact hE x p hp

end ZkVM

/-! ## CTE from extract-or-break -/

/-- Generic bridge, once for all systems: if the system's final argument system
reduces to a family of assumptions (`Reduction.ReducesToFamily`), and the
family holds, the frozen `CTE` follows — via the keystone and
`Reduction.knowledgeSound_of_extractOrBreak`. -/
theorem ZkVM.cte_of_reducesTo {V : ZkVM} {F : Reduction.AssumptionFamily}
    (h : Reduction.ReducesToFamily V.ASstar F) (hA : F.Holds) : V.CTE := by
  obtain ⟨E, B, hEB⟩ := h
  exact (V.cte_iff_knowledgeSound).mpr
    (Reduction.knowledgeSound_of_extractOrBreak hEB
      (Reduction.AssumptionFamily.toAssumption_holds.mpr hA))

end VanillaZkVM
