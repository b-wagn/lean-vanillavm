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

/-! ## A reusable trace-concatenation lemma

`concatTrace` glues `m` sub-traces of length `Nseg` (with matching boundary
states `d 0, d 1, …, d m`) into one trace of length `m * Nseg`. `chain_flatten`
states its correctness. This is the "concatenation" step shared by the two-step
toy and the full VM. -/

/-- Flatten `m` length-`Nseg` sub-chains into one length-`m * Nseg` trace: at
global position `k`, look up segment `k / Nseg` at local position `k % Nseg`; past
the end, return the final boundary state `d m`. -/
def concatTrace {State : Type} (Nseg : ℕ) (d : ℕ → State) (seg : ℕ → ℕ → State)
    (m : ℕ) : ℕ → State :=
  fun k => if k < m * Nseg then seg (k / Nseg) (k % Nseg) else d m

/-- Correctness of `concatTrace`: if each segment `i < m` is a valid `Nseg`-step
`step`-chain from `d i` to `d (i + 1)`, then `concatTrace` is a valid
`m * Nseg`-step chain from `d 0` to `d m`.

PROOF SKETCH (deferred). Endpoints are immediate from the definition. For the
step at global `k < m * Nseg`, write `k = Nseg * (k / Nseg) + k % Nseg` with
`k % Nseg < Nseg`, and case on whether `k % Nseg + 1 < Nseg` (stay inside segment
`k / Nseg`, use `hstep`) or `k % Nseg + 1 = Nseg` (cross into the next segment,
where `seg (k / Nseg) Nseg = d (k / Nseg + 1) = seg (k / Nseg + 1) 0`, using
`hlast` and `h0`). Cleanest via induction on `m` with a two-chain concatenation
helper, which avoids explicit div/mod juggling. -/
theorem chain_flatten {State : Type} (step : State → State → Prop)
    (Nseg m : ℕ) (hN : 0 < Nseg) (d : ℕ → State) (seg : ℕ → ℕ → State)
    (h0 : ∀ i, i < m → seg i 0 = d i)
    (hlast : ∀ i, i < m → seg i Nseg = d (i + 1))
    (hstep : ∀ i, i < m → ∀ j, j < Nseg → step (seg i j) (seg i (j + 1))) :
    concatTrace Nseg d seg m 0 = d 0 ∧
    concatTrace Nseg d seg m (m * Nseg) = d m ∧
    ∀ k, k < m * Nseg →
      step (concatTrace Nseg d seg m k) (concatTrace Nseg d seg m (k + 1)) := by
  sorry

end VanillaZkVM
