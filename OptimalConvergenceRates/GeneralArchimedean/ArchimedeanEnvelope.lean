/-
  OptimalConvergenceRates/GeneralArchimedean/ArchimedeanEnvelope.lean

  Algebraic coefficient envelopes supplied by an Archimedean ball
  certificate.
-/
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanGeometry
import OptimalConvergenceRates.BasicNotions.CoefficientNorm

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- A finite sum of untruncated quadratic-module elements is again in the module. -/
theorem QuadraticModuleMem.sum
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i ∈ s, QuadraticModuleMem g (p i)) :
    QuadraticModuleMem g (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using QuadraticModuleMem.of_isSOS g IsSOS_zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hp a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ hp i (Finset.mem_insert_of_mem hi))

/-- Combine two square bounds inside a quadratic module. -/
theorem QuadraticModuleMem.mul_square_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {A B : ℝ} {a b : MvPolynomial (Fin n) ℝ}
    (hB : 0 ≤ B)
    (ha : QuadraticModuleMem g (C A - a ^ 2))
    (hb : QuadraticModuleMem g (C B - b ^ 2)) :
    QuadraticModuleMem g (C (A * B) - (a * b) ^ 2) := by
  have hleft : QuadraticModuleMem g (C B * (C A - a ^ 2)) :=
    ha.sos_mul (IsSOS_C_nonneg B hB)
  have hright : QuadraticModuleMem g (a ^ 2 * (C B - b ^ 2)) :=
    hb.sos_mul (IsSOS_sq a)
  convert hleft.add hright using 1
  simp only [map_mul]
  ring

/-- An Archimedean ball certificate yields a common coordinate-square bound. -/
theorem IsArchimedean.exists_coordinate_square_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) :
    ∃ B, 1 ≤ B ∧ ∀ i : Fin n,
      QuadraticModuleMem g (C B - X i ^ 2) := by
  obtain ⟨R, r, hR, hball⟩ := harch
  let B := max 1 R
  refine ⟨B, le_max_left _ _, fun i ↦ ?_⟩
  have hotherSOS : IsSOS (∑ j ∈ Finset.univ.erase i,
      (X j : MvPolynomial (Fin n) ℝ) ^ 2) :=
    IsSOS_sum_finset fun j _ ↦ IsSOS_sq (X j)
  have hother : QuadraticModuleMem g
      (∑ j ∈ Finset.univ.erase i, (X j : MvPolynomial (Fin n) ℝ) ^ 2) :=
    QuadraticModuleMem.of_isSOS g hotherSOS
  have hRi : QuadraticModuleMem g (C R - X i ^ 2) := by
    have hsum := (show QuadraticModuleMem g
        (C R - ∑ j : Fin n, X j ^ 2) from ⟨r, hball⟩).add hother
    convert hsum using 1
    rw [show ∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2 =
        X i ^ 2 + ∑ j ∈ Finset.univ.erase i, X j ^ 2 from
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm]
    ring
  have hconstant : QuadraticModuleMem g (C (B - R)) :=
    ⟨0, genQuadraticModule_C_nonneg g (sub_nonneg.mpr (le_max_right 1 R))⟩
  convert hRi.add hconstant using 1
  simp only [map_sub]
  ring

/-- A coordinate square bound propagates to every power of that coordinate. -/
theorem coordinate_power_square_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, QuadraticModuleMem g (C B - X i ^ 2))
    (i : Fin n) : ∀ k : ℕ,
      QuadraticModuleMem g (C (B ^ k) - (X i ^ k) ^ 2) := by
  intro k
  induction k with
  | zero =>
      simpa using QuadraticModuleMem.of_isSOS g IsSOS_zero
  | succ k ih =>
      have hmul := QuadraticModuleMem.mul_square_bound hB ih (hcoord i)
      simpa [pow_succ] using hmul

/-- The common coordinate bound propagates to every monomial. -/
theorem monomial_square_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, QuadraticModuleMem g (C B - X i ^ 2))
    (α : Fin n →₀ ℕ) :
    QuadraticModuleMem g
      (C (B ^ α.degree) - (monomial α (1 : ℝ)) ^ 2) := by
  induction α using Finsupp.induction with
  | zero =>
      simpa using QuadraticModuleMem.of_isSOS g IsSOS_zero
  | single_add i k α _ _ ih =>
      have hk := coordinate_power_square_bound hB hcoord i k
      have hmul := QuadraticModuleMem.mul_square_bound
        (pow_nonneg hB α.degree) hk ih
      simpa [map_add, Finsupp.degree_single, pow_add,
        MvPolynomial.monomial_single_add] using hmul


/-- A square bound gives the positive linear bound by adding the square of x + 1. -/
theorem monomial_linear_plus_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, QuadraticModuleMem g (C B - X i ^ 2))
    (α : Fin n →₀ ℕ) :
    QuadraticModuleMem g
      (C (B ^ α.degree + 1) + 2 * monomial α (1 : ℝ)) := by
  let M : MvPolynomial (Fin n) ℝ := monomial α 1
  have hsq := monomial_square_bound hB hcoord α
  have hfree : QuadraticModuleMem g ((M + 1) ^ 2) :=
    QuadraticModuleMem.of_isSOS g (IsSOS_sq (M + 1))
  convert hsq.add hfree using 1
  simp only [M, map_add, map_one]
  ring

/-- A square bound gives the negative linear bound by adding the square of x - 1. -/
theorem monomial_linear_minus_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, QuadraticModuleMem g (C B - X i ^ 2))
    (α : Fin n →₀ ℕ) :
    QuadraticModuleMem g
      (C (B ^ α.degree + 1) - 2 * monomial α (1 : ℝ)) := by
  let M : MvPolynomial (Fin n) ℝ := monomial α 1
  have hsq := monomial_square_bound hB hcoord α
  have hfree : QuadraticModuleMem g ((M - 1) ^ 2) :=
    QuadraticModuleMem.of_isSOS g (IsSOS_sq (M - 1))
  convert hsq.add hfree using 1
  simp only [M, map_add, map_one]
  ring

/-- The radius-weighted contribution of one polynomial coefficient. -/
def weightedMonomialBound (B : ℝ) (α : Fin n →₀ ℕ) (c : ℝ) : ℝ :=
  (c / 2) ^ 2 * B ^ α.degree + 1
theorem weightedMonomialBound_nonneg
    {B : ℝ} (hB : 0 ≤ B) (α : Fin n →₀ ℕ) (c : ℝ) :
    0 ≤ weightedMonomialBound B α c := by
  dsimp [weightedMonomialBound]
  positivity


/-- A coefficient-weighted monomial has a one-sided module envelope. -/
theorem weighted_monomial_plus_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, QuadraticModuleMem g (C B - X i ^ 2))
    (α : Fin n →₀ ℕ) (c : ℝ) :
    QuadraticModuleMem g
      (C (weightedMonomialBound B α c) + monomial α c) := by
  let M : MvPolynomial (Fin n) ℝ := monomial α 1
  have hsq := monomial_square_bound hB hcoord α
  have hscaled := hsq.sos_mul (IsSOS_sq (C (c / 2)))
  have hfree : QuadraticModuleMem g ((C (c / 2) * M + 1) ^ 2) :=
    QuadraticModuleMem.of_isSOS g (IsSOS_sq (C (c / 2) * M + 1))
  have hmon : monomial α c = C c * M := by
    dsimp [M]
    rw [MvPolynomial.C_mul_monomial]
    simp
  have hc_two : (C (c / 2) : MvPolynomial (Fin n) ℝ) * 2 = C c := by
    change C (c / 2) * C 2 = C c
    rw [← map_mul]
    congr 1
    ring
  have hlinear : C (c / 2) * M * 2 = C c * M := by
    calc
      C (c / 2) * M * 2 = (C (c / 2) * 2) * M := by ring
      _ = C c * M := by rw [hc_two]
  rw [hmon]
  convert hscaled.add hfree using 1
  simp only [weightedMonomialBound, M, map_add, map_mul, map_pow, map_one]
  have hlinear' : C (c / 2) * monomial α (1 : ℝ) * 2 = C c * monomial α (1 : ℝ) := by
    simpa [M] using hlinear
  rw [← hlinear']
  ring

/-- Radius-weighted coefficient envelope of a polynomial. -/
def weightedCoeffEnvelope (B : ℝ) (q : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∑ α ∈ q.support, weightedMonomialBound B α (coeff α q)
theorem weightedCoeffEnvelope_nonneg
    {B : ℝ} (hB : 0 ≤ B) (q : MvPolynomial (Fin n) ℝ) :
    0 ≤ weightedCoeffEnvelope B q := by
  classical
  dsimp [weightedCoeffEnvelope]
  exact Finset.sum_nonneg fun α _ =>
    weightedMonomialBound_nonneg hB α (coeff α q)


/-- The positive coefficient envelope belongs to the Archimedean module. -/
theorem weightedCoeffEnvelope_plus_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, QuadraticModuleMem g (C B - X i ^ 2))
    (q : MvPolynomial (Fin n) ℝ) :
    QuadraticModuleMem g (C (weightedCoeffEnvelope B q) + q) := by
  classical
  have hsum := QuadraticModuleMem.sum q.support
    (fun α ↦ C (weightedMonomialBound B α (coeff α q)) + monomial α (coeff α q))
    (fun α _ ↦ weighted_monomial_plus_mem hB hcoord α (coeff α q))
  convert hsum using 1
  simp only [weightedCoeffEnvelope, map_sum, Finset.sum_add_distrib,
    MvPolynomial.support_sum_monomial_coeff]

/-- The negative coefficient envelope belongs to the Archimedean module. -/
theorem weightedCoeffEnvelope_minus_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, QuadraticModuleMem g (C B - X i ^ 2))
    (q : MvPolynomial (Fin n) ℝ) :
    QuadraticModuleMem g (C (weightedCoeffEnvelope B q) - q) := by
  classical
  have hterm (α : Fin n →₀ ℕ) : QuadraticModuleMem g
      (C (weightedMonomialBound B α (coeff α q)) - monomial α (coeff α q)) := by
    have h := weighted_monomial_plus_mem hB hcoord α (-coeff α q)
    have hsquare : (-coeff α q / 2) ^ 2 = (coeff α q / 2) ^ 2 := by ring
    simpa [weightedMonomialBound, sub_eq_add_neg, hsquare] using h
  have hsum := QuadraticModuleMem.sum q.support
    (fun α ↦ C (weightedMonomialBound B α (coeff α q)) - monomial α (coeff α q))
    (fun α _ ↦ hterm α)
  convert hsum using 1
  simp only [weightedCoeffEnvelope, map_sum, Finset.sum_sub_distrib,
    MvPolynomial.support_sum_monomial_coeff]

/-- Every Archimedean module admits a two-sided finite coefficient envelope. -/
theorem IsArchimedean.exists_coefficient_envelope
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) (q : MvPolynomial (Fin n) ℝ) :
    ∃ B, 1 ≤ B ∧
      QuadraticModuleMem g (C (weightedCoeffEnvelope B q) + q) ∧
      QuadraticModuleMem g (C (weightedCoeffEnvelope B q) - q) := by
  obtain ⟨B, hB, hcoord⟩ := harch.exists_coordinate_square_bound
  exact ⟨B, hB, weightedCoeffEnvelope_plus_mem (le_trans (by norm_num) hB) hcoord q,
    weightedCoeffEnvelope_minus_mem (le_trans (by norm_num) hB) hcoord q⟩

end OptimalConvergenceRates.GeneralArchimedean

end

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

/-- A single summand of the coefficient envelope is controlled uniformly by the
coefficient `ℓ¹` norm and the total degree. -/
theorem weightedMonomialBound_le_coeffL1Norm
    {B : ℝ} (hB : 1 ≤ B) (q : MvPolynomial (Fin n) ℝ)
    {α : Fin n →₀ ℕ} (hα : α ∈ q.support) :
    weightedMonomialBound B α (coeff α q) ≤
      (coeffL1Norm q / 2) ^ 2 * B ^ q.totalDegree + 1 := by
  have hc : |coeff α q| ≤ coeffL1Norm q := abs_coeff_le_coeffL1Norm q α
  have hcsq : (coeff α q / 2) ^ 2 ≤ (coeffL1Norm q / 2) ^ 2 := by
    have hnorm : 0 ≤ coeffL1Norm q := coeffL1Norm_nonneg q
    have hc_upper : coeff α q ≤ coeffL1Norm q := (le_abs_self _).trans hc
    have hc_lower : -coeffL1Norm q ≤ coeff α q := by
      exact (neg_le_neg hc).trans (neg_abs_le _)
    have hprod : 0 ≤ (coeffL1Norm q - coeff α q) *
        (coeffL1Norm q + coeff α q) :=
      mul_nonneg (sub_nonneg.mpr hc_upper) (by linarith)
    nlinarith
  have hdegree : α.degree ≤ q.totalDegree := by
    have heq : α.degree = α.sum fun _ e ↦ e := by rfl
    rw [heq]
    exact MvPolynomial.le_totalDegree hα
  have hpow : B ^ α.degree ≤ B ^ q.totalDegree := by
    exact pow_le_pow_right₀ hB hdegree
  dsimp [weightedMonomialBound]
  gcongr

/-- The weighted envelope is bounded by a simple expression involving only the
support size, coefficient norm, radius, and total degree. -/
theorem weightedCoeffEnvelope_le
    {B : ℝ} (hB : 1 ≤ B) (q : MvPolynomial (Fin n) ℝ) :
    weightedCoeffEnvelope B q ≤
      q.support.card * ((coeffL1Norm q / 2) ^ 2 * B ^ q.totalDegree + 1) := by
  classical
  rw [weightedCoeffEnvelope]
  calc
    ∑ α ∈ q.support, weightedMonomialBound B α (coeff α q)
        ≤ ∑ _α ∈ q.support,
            ((coeffL1Norm q / 2) ^ 2 * B ^ q.totalDegree + 1) := by
          exact Finset.sum_le_sum fun α hα ↦
            weightedMonomialBound_le_coeffL1Norm hB q hα
    _ = q.support.card *
        ((coeffL1Norm q / 2) ^ 2 * B ^ q.totalDegree + 1) := by
          simp only [Finset.sum_const, nsmul_eq_mul]

end OptimalConvergenceRates.GeneralArchimedean

end
