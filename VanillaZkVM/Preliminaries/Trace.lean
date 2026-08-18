import Mathlib

/-!
# Trace concatenation

A reusable trace-concatenation lemma, shared by every multi-segment layer (the
two-step toy, later the full VM). It is a generic helper over an abstract `step`
predicate — **not** part of the frozen kernel (`docs/INVARIANTS.md` I4).

## Main definitions / results
* `concatTrace` — glue `m` length-`Nseg` sub-traces into one length-`m * Nseg` trace.
* `chain_flatten` — its correctness: gluing valid sub-traces yields a valid trace.
-/

namespace VanillaZkVM

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
