/-
  Degree-tracked form of the Archimedean coefficient envelope.
-/
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanEnvelope

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- An Archimedean certificate yields coordinate square bounds at one common order. -/
theorem IsArchimedean.exists_truncated_coordinate_square_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) :
    ∃ B t, 1 ≤ B ∧ ∀ i : Fin n,
      C B - X i ^ 2 ∈ GenQuadraticModule g t := by
  obtain ⟨R, r, hR, hball⟩ := harch
  let B := max 1 R
  let t := max r 2
  refine ⟨B, t, le_max_left _ _, fun i ↦ ?_⟩
  have hotherSOS : IsSOS (∑ j ∈ Finset.univ.erase i,
      (X j : MvPolynomial (Fin n) ℝ) ^ 2) :=
    IsSOS_sum_finset fun j _ ↦ IsSOS_sq (X j)
  have hotherDegree : (∑ j ∈ Finset.univ.erase i,
      (X j : MvPolynomial (Fin n) ℝ) ^ 2).totalDegree ≤ 2 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    simp
  have hother : (∑ j ∈ Finset.univ.erase i,
      (X j : MvPolynomial (Fin n) ℝ) ^ 2) ∈ GenQuadraticModule g 2 :=
    genQuadraticModule_sos g hotherSOS hotherDegree
  have hRi0 := genQuadraticModule_add hball hother
  have hRi : C R - X i ^ 2 ∈ GenQuadraticModule g t := by
    convert hRi0 using 1
    rw [show ∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2 =
        X i ^ 2 + ∑ j ∈ Finset.univ.erase i, X j ^ 2 from
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm]
    ring
  have hconstant : C (B - R) ∈ GenQuadraticModule g 0 :=
    genQuadraticModule_C_nonneg g (sub_nonneg.mpr (le_max_right 1 R))
  have hsum := genQuadraticModule_add hRi hconstant
  convert hsum using 1
  · simp [t]
  · simp only [map_sub]
    ring

/-- A common truncated coordinate bound propagates to coordinate powers. -/
theorem coordinate_power_square_bound_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} {t : ℕ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, C B - X i ^ 2 ∈ GenQuadraticModule g t)
    (i : Fin n) : ∀ k : ℕ,
      C (B ^ k) - (X i ^ k) ^ 2 ∈ GenQuadraticModule g (t + 2 * k) := by
  intro k
  induction k with
  | zero =>
      simpa using GenQuadraticModule_mono (Nat.zero_le t) (genQuadraticModule_zero g)
  | succ k ih =>
      have hmul := genQuadraticModule_mul_square_bound hB ih (hcoord i)
      have hdegree : (((X i : MvPolynomial (Fin n) ℝ) ^ k) ^ 2).totalDegree ≤ 2 * k := by
        calc
          (((X i : MvPolynomial (Fin n) ℝ) ^ k) ^ 2).totalDegree
              ≤ 2 * ((X i : MvPolynomial (Fin n) ℝ) ^ k).totalDegree :=
                MvPolynomial.totalDegree_pow ((X i : MvPolynomial (Fin n) ℝ) ^ k) 2
          _ = 2 * k := by simp
      have horder : max (t + 2 * k)
          (t + (((X i : MvPolynomial (Fin n) ℝ) ^ k) ^ 2).totalDegree) ≤
          t + 2 * (k + 1) := by
        apply max_le
        · omega
        · omega
      have hmono := GenQuadraticModule_mono horder hmul
      simpa [pow_succ] using hmono

/-- A common truncated coordinate bound propagates to arbitrary monomials. -/
theorem monomial_square_bound_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} {t : ℕ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, C B - X i ^ 2 ∈ GenQuadraticModule g t)
    (α : Fin n →₀ ℕ) :
    C (B ^ α.degree) - (monomial α (1 : ℝ)) ^ 2 ∈
      GenQuadraticModule g (t + 2 * α.degree) := by
  induction α using Finsupp.induction with
  | zero =>
      simpa using GenQuadraticModule_mono (Nat.zero_le t) (genQuadraticModule_zero g)
  | single_add i k α _ _ ih =>
      have hk := coordinate_power_square_bound_at hB hcoord i k
      have hmul := genQuadraticModule_mul_square_bound (pow_nonneg hB k) ih hk
      have hmonDegree : (monomial α (1 : ℝ)).totalDegree = α.degree := by
        rw [MvPolynomial.totalDegree_monomial α one_ne_zero]
        rfl
      have hdegree : ((monomial α (1 : ℝ)) ^ 2).totalDegree ≤ 2 * α.degree := by
        calc
          ((monomial α (1 : ℝ)) ^ 2).totalDegree
              ≤ 2 * (monomial α (1 : ℝ)).totalDegree :=
                MvPolynomial.totalDegree_pow _ _
          _ = 2 * α.degree := by rw [hmonDegree]
      have horder : max (t + 2 * α.degree)
          (t + 2 * k + ((monomial α (1 : ℝ)) ^ 2).totalDegree) ≤
          t + 2 * (Finsupp.single i k + α).degree := by
        simp only [map_add, Finsupp.degree_single]
        apply max_le
        · omega
        · omega
      have hmono := GenQuadraticModule_mono horder hmul
      simpa [map_add, Finsupp.degree_single, pow_add,
        MvPolynomial.monomial_single_add, mul_comm] using hmono


/-- The total degree of a real monomial with coefficient one is its exponent degree. -/
theorem totalDegree_monomial_one_eq_degree (α : Fin n →₀ ℕ) :
    (monomial α (1 : ℝ)).totalDegree = α.degree := by
  rw [MvPolynomial.totalDegree_monomial α one_ne_zero]
  rfl

/-- Degree-tracked positive linear monomial bound. -/
theorem monomial_linear_plus_bound_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} {t : ℕ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, C B - X i ^ 2 ∈ GenQuadraticModule g t)
    (α : Fin n →₀ ℕ) :
    C (B ^ α.degree + 1) + 2 * monomial α (1 : ℝ) ∈
      GenQuadraticModule g (t + 2 * α.degree) := by
  let M : MvPolynomial (Fin n) ℝ := monomial α 1
  have hsq := monomial_square_bound_at hB hcoord α
  have hM : M.totalDegree = α.degree := by
    simpa [M] using totalDegree_monomial_one_eq_degree α
  have hbase : (M + 1).totalDegree ≤ α.degree := by
    calc
      (M + 1).totalDegree ≤ max M.totalDegree (1 : MvPolynomial (Fin n) ℝ).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ α.degree := by simp [hM]
  have hfree : (M + 1) ^ 2 ∈ GenQuadraticModule g (t + 2 * α.degree) :=
    genQuadraticModule_sos g (IsSOS_sq (M + 1)) <| by
      calc
        ((M + 1) ^ 2).totalDegree ≤ 2 * (M + 1).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ ≤ t + 2 * α.degree := by omega
  convert GenQuadraticModule_add hsq hfree using 1
  simp only [M, map_add, map_one]
  ring

/-- Degree-tracked negative linear monomial bound. -/
theorem monomial_linear_minus_bound_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} {t : ℕ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, C B - X i ^ 2 ∈ GenQuadraticModule g t)
    (α : Fin n →₀ ℕ) :
    C (B ^ α.degree + 1) - 2 * monomial α (1 : ℝ) ∈
      GenQuadraticModule g (t + 2 * α.degree) := by
  let M : MvPolynomial (Fin n) ℝ := monomial α 1
  have hsq := monomial_square_bound_at hB hcoord α
  have hM : M.totalDegree = α.degree := by
    simpa [M] using totalDegree_monomial_one_eq_degree α
  have hbase : (M - 1).totalDegree ≤ α.degree := by
    calc
      (M - 1).totalDegree ≤ max M.totalDegree (1 : MvPolynomial (Fin n) ℝ).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
      _ ≤ α.degree := by simp [hM]
  have hfree : (M - 1) ^ 2 ∈ GenQuadraticModule g (t + 2 * α.degree) :=
    genQuadraticModule_sos g (IsSOS_sq (M - 1)) <| by
      calc
        ((M - 1) ^ 2).totalDegree ≤ 2 * (M - 1).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ ≤ t + 2 * α.degree := by omega
  convert GenQuadraticModule_add hsq hfree using 1
  simp only [M, map_add, map_one]
  ring

/-- Degree-tracked one-sided envelope for a coefficient-weighted monomial. -/
theorem weighted_monomial_plus_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} {t : ℕ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, C B - X i ^ 2 ∈ GenQuadraticModule g t)
    (α : Fin n →₀ ℕ) (c : ℝ) :
    C (weightedMonomialBound B α c) + monomial α c ∈
      GenQuadraticModule g (t + 2 * α.degree) := by
  let M : MvPolynomial (Fin n) ℝ := monomial α 1
  have hsq := monomial_square_bound_at hB hcoord α
  have hscaled : C (c / 2) ^ 2 *
      (C (B ^ α.degree) - M ^ 2) ∈
      GenQuadraticModule g (t + 2 * α.degree) := by
    have hraw := genQuadraticModule_sos_mul (IsSOS_sq (C (c / 2))) hsq
    have hdegree : (C (c / 2) ^ 2 : MvPolynomial (Fin n) ℝ).totalDegree = 0 := by
      rw [← MvPolynomial.C_pow]
      exact MvPolynomial.totalDegree_C _
    rw [hdegree, Nat.add_zero] at hraw
    simpa [M] using hraw
  have hM : M.totalDegree = α.degree := by
    simpa [M] using totalDegree_monomial_one_eq_degree α
  have hbase : (C (c / 2) * M + 1).totalDegree ≤ α.degree := by
    calc
      (C (c / 2) * M + 1).totalDegree ≤
          max (C (c / 2) * M).totalDegree
            (1 : MvPolynomial (Fin n) ℝ).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ α.degree := by
        apply max_le
        · calc
            (C (c / 2) * M).totalDegree ≤ (C (c / 2)).totalDegree + M.totalDegree :=
              MvPolynomial.totalDegree_mul _ _
            _ ≤ α.degree := by simp [hM]
        · simp
  have hfree : (C (c / 2) * M + 1) ^ 2 ∈
      GenQuadraticModule g (t + 2 * α.degree) :=
    genQuadraticModule_sos g (IsSOS_sq (C (c / 2) * M + 1)) <| by
      calc
        ((C (c / 2) * M + 1) ^ 2).totalDegree ≤
            2 * (C (c / 2) * M + 1).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ ≤ t + 2 * α.degree := by omega
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
  convert GenQuadraticModule_add hscaled hfree using 1
  simp only [weightedMonomialBound, M, map_add, map_mul, map_pow, map_one]
  have hlinear' : C (c / 2) * monomial α (1 : ℝ) * 2 =
      C c * monomial α (1 : ℝ) := by
    simpa [M] using hlinear
  rw [← hlinear']
  ring

/-- Degree-tracked positive polynomial coefficient envelope. -/
theorem weightedCoeffEnvelope_plus_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} {t : ℕ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, C B - X i ^ 2 ∈ GenQuadraticModule g t)
    (q : MvPolynomial (Fin n) ℝ) :
    C (weightedCoeffEnvelope B q) + q ∈
      GenQuadraticModule g (t + 2 * q.totalDegree) := by
  classical
  have hterm : ∀ α ∈ q.support,
      C (weightedMonomialBound B α (q.coeff α)) + monomial α (q.coeff α) ∈
        GenQuadraticModule g (t + 2 * q.totalDegree) := by
    intro α hα
    apply GenQuadraticModule_mono
      (show t + 2 * α.degree ≤ t + 2 * q.totalDegree by
        have hdegree : α.degree ≤ q.totalDegree := by
          have heq : α.degree = α.sum fun _ e ↦ e := by rfl
          rw [heq]
          exact MvPolynomial.le_totalDegree hα
        omega)
    exact weighted_monomial_plus_mem_at hB hcoord α (q.coeff α)
  have hsum := genQuadraticModule_sum q.support
    (fun α ↦ C (weightedMonomialBound B α (q.coeff α)) + monomial α (q.coeff α))
    hterm
  convert hsum using 1
  simp only [weightedCoeffEnvelope, map_sum, Finset.sum_add_distrib,
    MvPolynomial.support_sum_monomial_coeff]

/-- Degree-tracked negative polynomial coefficient envelope. -/
theorem weightedCoeffEnvelope_minus_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} {t : ℕ} (hB : 0 ≤ B)
    (hcoord : ∀ i : Fin n, C B - X i ^ 2 ∈ GenQuadraticModule g t)
    (q : MvPolynomial (Fin n) ℝ) :
    C (weightedCoeffEnvelope B q) - q ∈
      GenQuadraticModule g (t + 2 * q.totalDegree) := by
  classical
  have hterm : ∀ α ∈ q.support,
      C (weightedMonomialBound B α (q.coeff α)) - monomial α (q.coeff α) ∈
        GenQuadraticModule g (t + 2 * q.totalDegree) := by
    intro α hα
    have h := weighted_monomial_plus_mem_at hB hcoord α (-q.coeff α)
    have hsquare : (-q.coeff α / 2) ^ 2 = (q.coeff α / 2) ^ 2 := by ring
    have hneg : C (weightedMonomialBound B α (q.coeff α)) -
          monomial α (q.coeff α) ∈
        GenQuadraticModule g (t + 2 * α.degree) := by
      simpa [weightedMonomialBound, sub_eq_add_neg, hsquare] using h
    apply GenQuadraticModule_mono
      (show t + 2 * α.degree ≤ t + 2 * q.totalDegree by
        have hdegree : α.degree ≤ q.totalDegree := by
          have heq : α.degree = α.sum fun _ e ↦ e := by rfl
          rw [heq]
          exact MvPolynomial.le_totalDegree hα
        omega)
    exact hneg
  have hsum := genQuadraticModule_sum q.support
    (fun α ↦ C (weightedMonomialBound B α (q.coeff α)) - monomial α (q.coeff α))
    hterm
  convert hsum using 1
  simp only [weightedCoeffEnvelope, map_sum, Finset.sum_sub_distrib,
    MvPolynomial.support_sum_monomial_coeff]

/-- Uniform degree-tracked two-sided coefficient envelope for an Archimedean module. -/
theorem IsArchimedean.exists_truncated_coefficient_envelope
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) :
    ∃ B t, 1 ≤ B ∧ ∀ q : MvPolynomial (Fin n) ℝ,
      C (weightedCoeffEnvelope B q) + q ∈
          GenQuadraticModule g (t + 2 * q.totalDegree) ∧
        C (weightedCoeffEnvelope B q) - q ∈
          GenQuadraticModule g (t + 2 * q.totalDegree) := by
  obtain ⟨B, t, hB, hcoord⟩ := harch.exists_truncated_coordinate_square_bound
  refine ⟨B, t, hB, fun q ↦ ?_⟩
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  exact ⟨weightedCoeffEnvelope_plus_mem_at hB0 hcoord q,
    weightedCoeffEnvelope_minus_mem_at hB0 hcoord q⟩

end OptimalConvergenceRates.GeneralArchimedean

end
