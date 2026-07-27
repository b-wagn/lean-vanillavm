import VanillaZkVM.Memory

/-!
# Trace-level full-memory reconstruction

`reconstructTrace` iterates the explicit one-step reduction from an initial
full state. Under completeness, position binding, and update binding, every
iteration takes the success branch. The main theorems prove:

* `CommitInv` at every reconstructed index;
* the full-memory step predicate at every transition;
* exact initial and, when a claimed terminal opening is supplied, final
  full-state boundaries.

This is the qualitative trace fold needed before composing memory with the Bus
and recursive proof layers.
-/

namespace VanillaZkVM

variable {VC : VectorCommitment}

/-- Deterministically iterate the one-step reconstruction algorithm. The
failure fallback makes the function total; the correctness theorems below prove
that binding excludes those branches for every valid committed trace. -/
def reconstructTrace
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (initial : FullVMState VC)
    (committed : ℕ → CommittedVMState VC)
    (descriptors : ℕ → MemStep VC) : ℕ → FullVMState VC
  | 0 => initial
  | n + 1 =>
      let pre := reconstructTrace initial committed descriptors n
      match reconstructStepReduction pre (committed (n + 1)) (descriptors n) with
      | .success post => post
      | .positionBreak _ => pre
      | .updateBreak _ => pre

theorem reconstructTrace_zero
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (initial : FullVMState VC)
    (committed : ℕ → CommittedVMState VC)
    (descriptors : ℕ → MemStep VC) :
    reconstructTrace initial committed descriptors 0 = initial :=
  rfl

/-- If the one-step reduction succeeds at index `n`, its post-state is
definitionally the next reconstructed trace state. -/
theorem reconstructTrace_succ_of_success
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (initial : FullVMState VC)
    (committed : ℕ → CommittedVMState VC)
    (descriptors : ℕ → MemStep VC) (n : ℕ)
    (post : FullVMState VC)
    (hsuccess :
      reconstructStepReduction
        (reconstructTrace initial committed descriptors n)
        (committed (n + 1)) (descriptors n) = .success post) :
    reconstructTrace initial committed descriptors (n + 1) = post := by
  simp only [reconstructTrace, hsuccess]

/-- The commitment invariant is maintained at every reconstructed state up to
the declared trace length. -/
theorem reconstructTrace_commitInv
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC) (memFreePred : ℕ → MemFreePredicate)
    (T : ℕ) (initial : FullVMState VC)
    (committed : ℕ → CommittedVMState VC)
    (descriptors : ℕ → MemStep VC)
    (hInitial : CommitInv (committed 0) initial)
    (hSteps : ∀ k, k < T →
      stepC (memFreePred k) (committed k) (committed (k + 1))
        (descriptors k)) :
    ∀ k, k ≤ T →
      CommitInv (committed k)
        (reconstructTrace initial committed descriptors k) := by
  intro k
  induction k with
  | zero =>
      intro _
      simpa only [reconstructTrace] using hInitial
  | succ k ih =>
      intro hk
      have hklt : k < T := Nat.lt_of_succ_le hk
      have hpre := ih (Nat.le_of_lt hklt)
      have hstep := hSteps k hklt
      obtain ⟨post, hsuccess, hpostInv, _⟩ :=
        reconstructStepReduction_success hComplete hpos hupd (memFreePred k)
          (reconstructTrace initial committed descriptors k)
          (committed k) (committed (k + 1)) (descriptors k)
          hpre hstep
      have hnext :
          reconstructTrace initial committed descriptors (k + 1) = post :=
        reconstructTrace_succ_of_success
          initial committed descriptors k post hsuccess
      rw [hnext]
      exact hpostInv

/-- Every adjacent pair of reconstructed full states satisfies the full-memory
step predicate with the descriptor extracted for that transition. -/
theorem reconstructTrace_step
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC) (memFreePred : ℕ → MemFreePredicate)
    (T : ℕ) (initial : FullVMState VC)
    (committed : ℕ → CommittedVMState VC)
    (descriptors : ℕ → MemStep VC)
    (hInitial : CommitInv (committed 0) initial)
    (hSteps : ∀ k, k < T →
      stepC (memFreePred k) (committed k) (committed (k + 1))
        (descriptors k)) :
    ∀ k, k < T →
      stepF (memFreePred k)
        (reconstructTrace initial committed descriptors k)
        (reconstructTrace initial committed descriptors (k + 1))
        (descriptors k) := by
  intro k hk
  have hpre :=
    reconstructTrace_commitInv hComplete hpos hupd memFreePred
      T initial committed descriptors hInitial hSteps
      k (Nat.le_of_lt hk)
  obtain ⟨post, hsuccess, _, hfullStep⟩ :=
    reconstructStepReduction_success hComplete hpos hupd (memFreePred k)
      (reconstructTrace initial committed descriptors k)
      (committed k) (committed (k + 1)) (descriptors k)
      hpre (hSteps k hk)
  have hnext :
      reconstructTrace initial committed descriptors (k + 1) = post :=
    reconstructTrace_succ_of_success
      initial committed descriptors k post hsuccess
  rw [hnext]
  exact hfullStep

/-- **Primary trace reconstruction theorem.** Starting from only the initial
commitment invariant, construct a full trace, maintain `CommitInv` at every
index, and prove every full-memory step. No post-state invariant is assumed. -/
theorem reconstructTrace_from_initial
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC) (memFreePred : ℕ → MemFreePredicate)
    (T : ℕ) (initial : FullVMState VC)
    (committed : ℕ → CommittedVMState VC)
    (descriptors : ℕ → MemStep VC)
    (hInitial : CommitInv (committed 0) initial)
    (hSteps : ∀ k, k < T →
      stepC (memFreePred k) (committed k) (committed (k + 1))
        (descriptors k)) :
    reconstructTrace initial committed descriptors 0 = initial ∧
    (∀ k, k ≤ T →
      CommitInv (committed k)
        (reconstructTrace initial committed descriptors k)) ∧
    ∀ k, k < T →
      stepF (memFreePred k)
        (reconstructTrace initial committed descriptors k)
        (reconstructTrace initial committed descriptors (k + 1))
        (descriptors k) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact reconstructTrace_commitInv hComplete hpos hupd memFreePred
      T initial committed descriptors hInitial hSteps
  · exact reconstructTrace_step hComplete hpos hupd memFreePred
      T initial committed descriptors hInitial hSteps

/-- If a claimed terminal full state satisfies the same terminal commitment
invariant, then it equals the reconstructed terminal state. Completeness and
position binding turn equal honest commitments into equality of full memories.
-/
theorem reconstructTrace_terminal
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC) (memFreePred : ℕ → MemFreePredicate)
    (T : ℕ) (initial terminal : FullVMState VC)
    (committed : ℕ → CommittedVMState VC)
    (descriptors : ℕ → MemStep VC)
    (hInitial : CommitInv (committed 0) initial)
    (hTerminal : CommitInv (committed T) terminal)
    (hSteps : ∀ k, k < T →
      stepC (memFreePred k) (committed k) (committed (k + 1))
        (descriptors k)) :
    reconstructTrace initial committed descriptors T = terminal := by
  have hReconstructed :=
    reconstructTrace_commitInv hComplete hpos hupd memFreePred
      T initial committed descriptors hInitial hSteps T (Nat.le_refl T)
  obtain ⟨hpcReconstructed, hregsReconstructed, hmemReconstructed⟩ :=
    hReconstructed
  obtain ⟨hpcTerminal, hregsTerminal, hmemTerminal⟩ := hTerminal
  have hpc :
      (reconstructTrace initial committed descriptors T).pc = terminal.pc :=
    hpcReconstructed.symm.trans hpcTerminal
  have hregs :
      (reconstructTrace initial committed descriptors T).regs = terminal.regs :=
    hregsReconstructed.symm.trans hregsTerminal
  have hmem :
      (reconstructTrace initial committed descriptors T).mem = terminal.mem := by
    exact (mem_eq_of_commit_eq hComplete hpos
      (hmemReconstructed.symm.trans hmemTerminal)).symm
  exact VMStateWith.ext hpc hregs hmem

/-- Exact-terminal corollary of trace reconstruction. Unlike
`reconstructTrace_from_initial`, this additionally assumes that a claimed
terminal full state honestly opens the extracted terminal commitment. -/
theorem reconstructTrace_correct
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC) (memFreePred : ℕ → MemFreePredicate)
    (T : ℕ) (initial terminal : FullVMState VC)
    (committed : ℕ → CommittedVMState VC)
    (descriptors : ℕ → MemStep VC)
    (hInitial : CommitInv (committed 0) initial)
    (hTerminal : CommitInv (committed T) terminal)
    (hSteps : ∀ k, k < T →
      stepC (memFreePred k) (committed k) (committed (k + 1))
        (descriptors k)) :
    reconstructTrace initial committed descriptors 0 = initial ∧
    reconstructTrace initial committed descriptors T = terminal ∧
    ∀ k, k < T →
      stepF (memFreePred k)
        (reconstructTrace initial committed descriptors k)
        (reconstructTrace initial committed descriptors (k + 1))
        (descriptors k) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact reconstructTrace_terminal hComplete hpos hupd memFreePred
      T initial terminal committed descriptors
      hInitial hTerminal hSteps
  · exact reconstructTrace_step hComplete hpos hupd memFreePred
      T initial committed descriptors hInitial hSteps

end VanillaZkVM
