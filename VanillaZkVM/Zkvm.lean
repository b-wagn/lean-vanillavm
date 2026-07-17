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

/-- Flatten `m` length-`Nseg` sub-chains into one length-`m * Nseg` trace. -/
def concatTrace {State : Type} (Nseg : ℕ) (d : ℕ → State) (seg : ℕ → ℕ → State) :
    ℕ → ℕ → State
  | 0 => fun _ => d 0
  | (m + 1) => fun k =>
      if k ≤ m * Nseg then concatTrace Nseg d seg m k else seg m (k - m * Nseg)

/-- Correctness of `concatTrace`: if each segment `i < m` is a valid `Nseg`-step
`step`-chain from `d i` to `d (i + 1)`, then `concatTrace` is a valid
`m * Nseg`-step chain from `d 0` to `d m`. Proved by induction on `m`; treating
`n * Nseg` as an opaque atom keeps every arithmetic side-condition linear, so
`omega` discharges them. -/
theorem chain_flatten {State : Type} (step : State → State → Prop)
    (Nseg m : ℕ) (hN : 0 < Nseg) (d : ℕ → State) (seg : ℕ → ℕ → State)
    (h0 : ∀ i, i < m → seg i 0 = d i)
    (hlast : ∀ i, i < m → seg i Nseg = d (i + 1))
    (hstep : ∀ i, i < m → ∀ j, j < Nseg → step (seg i j) (seg i (j + 1))) :
    concatTrace Nseg d seg m 0 = d 0 ∧
    concatTrace Nseg d seg m (m * Nseg) = d m ∧
    ∀ k, k < m * Nseg →
      step (concatTrace Nseg d seg m k) (concatTrace Nseg d seg m (k + 1)) := by
  revert h0 hlast hstep
  induction m with
  | zero =>
    intro _ _ _
    refine ⟨rfl, rfl, ?_⟩
    intro k hk
    simp at hk
  | succ n ih =>
    intro h0 hlast hstep
    obtain ⟨ih0, ihN, ihstep⟩ :=
      ih (fun i hi => h0 i (by omega)) (fun i hi => hlast i (by omega))
         (fun i hi => hstep i (by omega))
    have hstepC : ∀ k, concatTrace Nseg d seg (n + 1) k
        = if k ≤ n * Nseg then concatTrace Nseg d seg n k
          else seg n (k - n * Nseg) := fun k => rfl
    have he : (n + 1) * Nseg = n * Nseg + Nseg := by ring
    refine ⟨?_, ?_, ?_⟩
    · -- start: concatTrace … (n+1) 0 = d 0
      rw [hstepC, if_pos (Nat.zero_le _)]
      exact ih0
    · -- end: concatTrace … (n+1) ((n+1)*Nseg) = d (n+1)
      rw [hstepC, he, if_neg (by omega)]
      have h1 : n * Nseg + Nseg - n * Nseg = Nseg := by omega
      rw [h1]
      exact hlast n (by omega)
    · -- steps
      intro k hk
      rw [he] at hk
      rw [hstepC, hstepC]
      by_cases hk1 : k + 1 ≤ n * Nseg
      · -- both endpoints inside the first n segments
        rw [if_pos (show k ≤ n * Nseg by omega), if_pos hk1]
        exact ihstep k (by omega)
      · rw [if_neg hk1]
        by_cases hk2 : k ≤ n * Nseg
        · -- the seam: k = n * Nseg, crossing from segment n-1's end into segment n
          have hkeq : k = n * Nseg := by omega
          rw [if_pos hk2, hkeq, ihN]
          have h1 : n * Nseg + 1 - n * Nseg = 1 := by omega
          rw [h1, ← h0 n (by omega)]
          exact hstep n (by omega) 0 hN
        · -- strictly inside the last segment
          rw [if_neg hk2]
          have h2 : k + 1 - n * Nseg = (k - n * Nseg) + 1 := by omega
          rw [h2]
          exact hstep n (by omega) (k - n * Nseg) (by omega)


end VanillaZkVM
