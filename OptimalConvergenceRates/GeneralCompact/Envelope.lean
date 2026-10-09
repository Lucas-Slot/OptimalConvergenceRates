/-
  Degree-tracked coefficient envelopes from a fixed preordering ball certificate.
-/
import OptimalConvergenceRates.GeneralCompact.Schmudgen
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanEnvelopeDegree
import OptimalConvergenceRates.KrivineStengle.TruncatedPreordering
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralCompact

variable {n m : ℕ}

/-- Finite sums preserve a common preordering truncation. -/
theorem genPreordering_sum
    {ι : Type*} {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι) (p : ι → MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hp : ∀ i ∈ s, p i ∈ GenPreordering g r) :
    ∑ i ∈ s, p i ∈ GenPreordering g r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact GenPreordering_mono (Nat.zero_le r)
        (KrivineStengle.genPreordering_zero g)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      simpa using KrivineStengle.genPreordering_add
        (hp a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ hp i (Finset.mem_insert_of_mem hi))

/-- Replace the singleton quadratic-module ball generator by its fixed
certificate in the original preordering. -/
theorem singletonModule_to_preordering
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    {ball q : MvPolynomial (Fin n) ℝ} {rBall r : ℕ}
    (hball0 : ball ≠ 0)
    (hball : ball ∈ GenPreordering g rBall)
    (hq : q ∈ GenQuadraticModule (fun _ : Fin 1 ↦ ball) r) :
    q ∈ GenPreordering g (r + rBall) := by
  obtain ⟨sigmaZero, sigma, hsigmaZero, hsigma,
    hdegreeZero, hdegree, hid⟩ := hq
  have hzero0 : sigmaZero ∈ GenQuadraticModule g r :=
    genQuadraticModule_sos g hsigmaZero hdegreeZero
  have hzero : sigmaZero ∈ GenPreordering g (r + rBall) :=
    GenPreordering_mono (Nat.le_add_right r rBall)
      (GenQuadraticModule_subset_GenPreordering hzero0)
  have hterm : ∀ i : Fin 1,
      sigma i * ball ∈ GenPreordering g (r + rBall) := by
    intro i
    by_cases hs0 : sigma i = 0
    · rw [hs0, zero_mul]
      exact GenPreordering_mono (Nat.zero_le _)
        (KrivineStengle.genPreordering_zero g)
    have hsigmadeg : (sigma i).totalDegree ≤ r := by
      have hi := hdegree i
      rw [totalDegree_mul_of_isDomain hs0 hball0] at hi
      omega
    have hsigmaPre : sigma i ∈ GenPreordering g (sigma i).totalDegree :=
      GenQuadraticModule_subset_GenPreordering
        (genQuadraticModule_sos g (hsigma i) le_rfl)
    have hmul := KrivineStengle.genPreordering_mul hsigmaPre hball
    exact GenPreordering_mono (Nat.add_le_add_right hsigmadeg rBall) hmul
  have hsum : (∑ i : Fin 1, sigma i * ball) ∈
      GenPreordering g (r + rBall) :=
    genPreordering_sum Finset.univ _ (fun i _ ↦ hterm i)
  rw [hid]
  simpa using KrivineStengle.genPreordering_add hzero hsum

/-- A fixed preordering ball certificate supplies the same linear-degree
coefficient envelope used in the Archimedean quadratic-module proof. -/
theorem IsPreorderingArchimedean.exists_truncated_coefficient_envelope
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsPreorderingArchimedean g) :
    ∃ B t, 1 ≤ B ∧ ∀ q : MvPolynomial (Fin n) ℝ,
      C (GeneralArchimedean.weightedCoeffEnvelope B q) + q ∈
          GenPreordering g (t + 2 * q.totalDegree) ∧
        C (GeneralArchimedean.weightedCoeffEnvelope B q) - q ∈
          GenPreordering g (t + 2 * q.totalDegree) := by
  obtain ⟨R, rBall, hR, hball⟩ := harch
  let ball : MvPolynomial (Fin n) ℝ := C R - ∑ i : Fin n, X i ^ 2
  have hball' : ball ∈ GenPreordering g rBall := by simpa [ball] using hball
  have hball0 : ball ≠ 0 := by
    intro hzero
    have heval := congrArg (MvPolynomial.eval fun _ : Fin n ↦ (0 : ℝ)) hzero
    simp [ball, hR.ne'] at heval
  let g₀ : Fin 1 → MvPolynomial (Fin n) ℝ := fun _ ↦ ball
  have harch₀ : GeneralArchimedean.IsArchimedean g₀ := by
    refine ⟨R, ball.totalDegree, hR, ?_⟩
    simpa [g₀, ball] using genQuadraticModule_generator g₀ (0 : Fin 1)
  obtain ⟨B, t₀, hB, henvelope⟩ :=
    harch₀.exists_truncated_coefficient_envelope
  refine ⟨B, t₀ + rBall, hB, ?_⟩
  intro q
  obtain ⟨hplus, hminus⟩ := henvelope q
  constructor
  · have := singletonModule_to_preordering g hball0 hball' hplus
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  · have := singletonModule_to_preordering g hball0 hball' hminus
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

end OptimalConvergenceRates.GeneralCompact

end
