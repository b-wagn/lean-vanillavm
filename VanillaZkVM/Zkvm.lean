import VanillaZkVM.Crypto

/-!
# What a zkVM system is, and correct-trace extractability (the abstract heart)

This is the central file. It defines, abstractly:

* the VM state (absorbed from the old `Model` file);
* an abstract `ZkVM` system (compare the zkVM of the vanilla document, stripped
  to what the security statement needs);
* the correct-execution relation `Rstar` the system is meant to prove, and the
  final argument system `ASstar` viewed as an argument system for it;
* correct-trace extractability `CTE`, stated in VM-native terms; and
* the keystone theorem `cte_iff_knowledgeSound`:
  `CTE V ↔ KnowledgeSound V.ASstar`.

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
registers are abstracted as a total function `index ↦ value`. -/
structure VMStateWith (Mem : Type) where
  pc : Word
  regs : ℕ → Word
  mem : Mem

/-- Full VM state `S = (pc, regs, mem)` with explicit byte-addressed memory. -/
abbrev VMState : Type := VMStateWith (Addr → Byte)

/-- Committed VM state `Ŝ = (pc, regs, mem̂)`: memory replaced by a commitment. -/
abbrev CommittedVMState (VC : VectorCommitment) : Type := VMStateWith VC.Com

/-- Memory update `mem[addr ↦ v]`. -/
def memUpdate (m : Addr → Byte) (addr : Addr) (v : Byte) : Addr → Byte :=
  Function.update m addr v

/-! ## Abstract zkVM systems -/

/-- An abstract zkVM system: a state type with a step predicate, a fixed step
count `T` (the document fixes `T` independent of the security parameter), a
statement type with `initial`/`terminal` boundary projections, and the final
proof type with its verifier. -/
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
step satisfies `step`. -/
def TraceValid (x : V.Stmt) (tr : ℕ → V.State) : Prop :=
  tr 0 = V.initial x ∧ tr V.T = V.terminal x ∧
  ∀ i, i < V.T → V.step (tr i) (tr (i + 1))

/-- The correct-execution relation `R*`: statements are boundary claims,
witnesses are traces, membership is trace validity. -/
def Rstar : Relation where
  Stmt := V.Stmt
  Wit := ℕ → V.State
  rel := fun x tr => V.TraceValid x tr

/-- The system's final argument system, viewed as an argument system for `R*`. -/
def ASstar : ArgumentSystem V.Rstar where
  Proof := V.Proof
  verify := V.verify

/-- **Correct-trace extractability** (VM-native form): a single trace-extractor
turns every accepting proof into a valid `T`-step execution of the claim. -/
def CTE : Prop :=
  ∃ E : V.Stmt → V.Proof → (ℕ → V.State),
    ∀ (x : V.Stmt) (p : V.Proof), V.verify x p → V.TraceValid x (E x p)

/-- **Keystone.** Correct-trace extractability is exactly knowledge soundness of
the final argument system for the correct-execution relation `R*`. The proof is
structural: both sides are "∃ extractor, ∀ accepting (x, p), the output is a
valid trace", differing only in packaging the extractor as a bare function versus
an `Extractor` record. -/
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

end VanillaZkVM
