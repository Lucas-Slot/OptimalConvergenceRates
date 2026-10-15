/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/Common/VectorPolynomialEstimates.lean

  Dimension-independent estimates for finite vectors of univariate polynomials.
-/
import OptimalConvergenceRates.BasicNotions.SOSVector
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityClassical
import OptimalConvergenceRates.MarkovInequality.BernsteinInequality
import Mathlib.Topology.Algebra.Polynomial

open Finset

noncomputable section

namespace OptimalConvergenceRates

theorem continuous_interiorVecNorm_polynomial {N : ℕ} (P : Fin N → Polynomial ℝ) :
    Continuous (fun t : ℝ ↦ interiorVecNorm (fun i : Fin N ↦ (P i).eval t)) := by
  unfold interiorVecNorm interiorVecSqNorm
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i _
  fun_prop

private lemma polynomial_derivative_eval_sum {N : ℕ} (P : Fin N → Polynomial ℝ)
    (a : Fin N → ℝ) :
    (Polynomial.derivative (∑ i : Fin N, Polynomial.C (a i) * P i)).eval 0 =
      ∑ i : Fin N, a i * (Polynomial.derivative (P i)).eval 0 := by
  rw [Polynomial.derivative_sum]
  simp_rw [← Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Polynomial.derivative_mul]

private lemma polynomial_weighted_sum_natDegree_le {N k : ℕ}
    (P : Fin N → Polynomial ℝ) (a : Fin N → ℝ)
    (hdeg : ∀ i, (P i).natDegree ≤ k) :
    (∑ i : Fin N, Polynomial.C (a i) * P i).natDegree ≤ k := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  calc
    (Polynomial.C (a i) * P i).natDegree ≤
        (Polynomial.C (a i)).natDegree + (P i).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + k := by
      rw [Polynomial.natDegree_C]
      exact Nat.add_le_add_left (hdeg i) 0
    _ = k := by omega

private lemma polynomial_weighted_sum_eval {N : ℕ}
    (P : Fin N → Polynomial ℝ) (a : Fin N → ℝ) (t : ℝ) :
    (∑ i : Fin N, Polynomial.C (a i) * P i).eval t =
      vecDot a (fun i : Fin N ↦ (P i).eval t) := by
  unfold vecDot
  simp_rw [← Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Uniform vector-valued Markov estimate on `[-1,1]` for first derivatives. -/
theorem interior_markov_vector_first_derivative_unit
    {N k : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ 1 →
      interiorVecNorm (fun i : Fin N ↦ (P i).eval t) ≤ M) :
    interiorVecNorm (fun i : Fin N ↦ (Polynomial.derivative (P i)).eval 0) ≤
      (k : ℝ) ^ 2 * M := by
  let D : Fin N → ℝ := fun i ↦ (Polynomial.derivative (P i)).eval 0
  by_cases hD0 : interiorVecNorm D = 0
  · simpa [D, hD0] using mul_nonneg (sq_nonneg (k : ℝ)) hM
  · let u : Fin N → ℝ := fun i ↦ D i / interiorVecNorm D
    let R : Polynomial ℝ := ∑ i : Fin N, Polynomial.C (u i) * P i
    have hRdeg : R.natDegree ≤ k := by
      dsimp [R]
      exact polynomial_weighted_sum_natDegree_le P u hdeg
    have hRsup : polySupNormUni R ≤ M := by
      apply polySupNormUni_le_of_bound
      intro t ht1 ht2
      have ht : |t| ≤ 1 := abs_le.mpr ⟨ht1, ht2⟩
      dsimp [R]
      rw [polynomial_weighted_sum_eval]
      have hdot := abs_vecDot_unit_le (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
        (fun i : Fin N ↦ (P i).eval t)
      have hnorm : vecNorm (fun i : Fin N ↦ (P i).eval t) ≤ M := by
        simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hbound t ht
      exact hdot.trans hnorm
    have hmark := univariate_markov_first_derivative_inside R k hRdeg 0
      (by norm_num : |(0 : ℝ)| ≤ 1)
    have hderiv : (Polynomial.derivative R).eval 0 = interiorVecNorm D := by
      dsimp [R]
      rw [polynomial_derivative_eval_sum]
      change vecDot (fun i : Fin N ↦ D i / interiorVecNorm D) D = interiorVecNorm D
      exact vecDot_unit_self (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
    calc
      interiorVecNorm D = |(Polynomial.derivative R).eval 0| := by
        rw [hderiv]
        exact (abs_of_nonneg (interiorVecNorm_nonneg D)).symm
      _ ≤ (k : ℝ) ^ 2 * polySupNormUni R := hmark
      _ ≤ (k : ℝ) ^ 2 * M := mul_le_mul_of_nonneg_left hRsup (sq_nonneg (k : ℝ))

/-- Uniform vector-valued Bernstein estimate on `[-1,1]` at the center. -/
theorem interior_bernstein_vector_first_derivative_unit
    {N k : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ 1 →
      interiorVecNorm (fun i : Fin N ↦ (P i).eval t) ≤ M) :
    interiorVecNorm (fun i : Fin N ↦ (Polynomial.derivative (P i)).eval 0) ≤
      2 * (k : ℝ) * M := by
  let D : Fin N → ℝ := fun i ↦ (Polynomial.derivative (P i)).eval 0
  by_cases hD0 : interiorVecNorm D = 0
  · simpa [D, hD0] using
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg k)) hM
  · let u : Fin N → ℝ := fun i ↦ D i / interiorVecNorm D
    let R : Polynomial ℝ := ∑ i : Fin N, Polynomial.C (u i) * P i
    have hRdeg : R.natDegree ≤ k := by
      dsimp [R]
      exact polynomial_weighted_sum_natDegree_le P u hdeg
    have hRbound : ∀ t : ℝ, -1 ≤ t → t ≤ 1 → |R.eval t| ≤ M := by
      intro t ht1 ht2
      have ht : |t| ≤ 1 := abs_le.mpr ⟨ht1, ht2⟩
      dsimp [R]
      rw [polynomial_weighted_sum_eval]
      have hdot := abs_vecDot_unit_le (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
        (fun i : Fin N ↦ (P i).eval t)
      have hnorm : vecNorm (fun i : Fin N ↦ (P i).eval t) ≤ M := by
        simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hbound t ht
      exact hdot.trans hnorm
    have hbern := univariate_bernstein_first_derivative_zero_bound R k hRdeg M hM hRbound
    have hderiv : (Polynomial.derivative R).eval 0 = interiorVecNorm D := by
      dsimp [R]
      rw [polynomial_derivative_eval_sum]
      change vecDot (fun i : Fin N ↦ D i / interiorVecNorm D) D = interiorVecNorm D
      exact vecDot_unit_self (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
    calc
      interiorVecNorm D = |(Polynomial.derivative R).eval 0| := by
        rw [hderiv]
        exact (abs_of_nonneg (interiorVecNorm_nonneg D)).symm
      _ ≤ 2 * (k : ℝ) * M := hbern

/-- Bernstein's first-derivative estimate on a symmetric interval of positive radius. -/
theorem interior_bernstein_vector_first_derivative_radius
    {N k : ℕ} {M s : ℝ} (P : Fin N → Polynomial ℝ)
    (hs : 0 < s) (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ s →
      interiorVecNorm (fun i : Fin N ↦ (P i).eval t) ≤ M) :
    interiorVecNorm (fun i : Fin N ↦ (Polynomial.derivative (P i)).eval 0) ≤
      (2 / s) * (k : ℝ) * M := by
  let Ps : Fin N → Polynomial ℝ := fun i ↦
    (P i).comp (Polynomial.C s * Polynomial.X)
  have hdegPs : ∀ i, (Ps i).natDegree ≤ k := by
    intro i
    dsimp [Ps]
    calc
      ((P i).comp (Polynomial.C s * Polynomial.X)).natDegree ≤
          (P i).natDegree * (Polynomial.C s * Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ (P i).natDegree * 1 := by
        apply Nat.mul_le_mul_left
        exact (Polynomial.natDegree_mul_le.trans (by simp [Polynomial.natDegree_C]))
      _ = (P i).natDegree := by omega
      _ ≤ k := hdeg i
  have hboundPs : ∀ u : ℝ, |u| ≤ 1 →
      interiorVecNorm (fun i : Fin N ↦ (Ps i).eval u) ≤ M := by
    intro u hu
    have hsu : |s * u| ≤ s := by
      rw [abs_mul, abs_of_pos hs]
      exact mul_le_of_le_one_right hs.le hu
    simpa [Ps, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] using hbound (s * u) hsu
  have hunit := interior_bernstein_vector_first_derivative_unit Ps hM hdegPs hboundPs
  have hderiv : (fun i : Fin N ↦ (Polynomial.derivative (Ps i)).eval 0) =
      fun i : Fin N ↦ s * (Polynomial.derivative (P i)).eval 0 := by
    funext i
    dsimp [Ps]
    rw [Polynomial.derivative_comp]
    simp [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.eval_mul, Polynomial.eval_comp]
  have hscale : interiorVecNorm
      (fun i : Fin N ↦ s * (Polynomial.derivative (P i)).eval 0) =
        s * interiorVecNorm (fun i : Fin N ↦ (Polynomial.derivative (P i)).eval 0) := by
    rw [interiorVecNorm_smul_abs, abs_of_pos hs]
  have hsbound : s *
      interiorVecNorm (fun i : Fin N ↦ (Polynomial.derivative (P i)).eval 0) ≤
        2 * (k : ℝ) * M := by
    simpa [hderiv, hscale] using hunit
  calc
    interiorVecNorm (fun i : Fin N ↦ (Polynomial.derivative (P i)).eval 0) ≤
        (2 * (k : ℝ) * M) / s := by
      apply (le_div_iff₀ hs).2
      simpa [mul_comm] using hsbound
    _ = (2 / s) * (k : ℝ) * M := by field_simp

end OptimalConvergenceRates

end
