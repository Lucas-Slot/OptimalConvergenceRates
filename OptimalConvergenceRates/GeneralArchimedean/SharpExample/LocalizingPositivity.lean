/-
  Positivity of the sharp moment functional on polynomial squares.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.GaussianKernel

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- The moment matrix is positive semidefinite on every finite,
injectively indexed family of bivariate monomials. -/
theorem sharpMoment_quadraticForm_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : ℝ} (hη : 0 < η)
    (e : ι → Fin 2 →₀ ℕ) (he : Function.Injective e)
    (c : ι → ℝ) :
    0 ≤ ∑ i : ι, ∑ j : ι,
      c i * sharpMoment η (e i + e j) * c j := by
  let coords : ι → ℕ × ℕ := fun i ↦ (e i 0, e i 1)
  have hcoords : Function.Injective coords := by
    intro i j hij
    apply he
    rw [← bivarExponent_of_exponents (e i),
      ← bivarExponent_of_exponents (e j)]
    exact congrArg (fun z : ℕ × ℕ ↦ bivarExponent z.1 z.2) hij
  let scale : ι → ℝ := fun i ↦
    sharpMomentScale η (coords i).1 (coords i).2
  have hscale (i : ι) : 0 < scale i :=
    sharpMomentScale_pos hη _ _
  let K : ι → ι → ℝ := fun i j ↦
    sharpMoment η (e i + e j) / (scale i * scale j)
  have hdiag (i : ι) : K i i = 1 := by
    have heq : e i = bivarExponent (coords i).1 (coords i).2 := by
      exact (bivarExponent_of_exponents (e i)).symm
    rw [show K i i = sharpMoment η (e i + e i) /
        (scale i * scale i) by rfl,
      heq, sharpMoment_add_self_eq_scale_sq hη]
    rw [pow_two]
    exact div_self (mul_ne_zero (ne_of_gt (hscale i)) (ne_of_gt (hscale i)))
  have hsymm (i j : ι) : K i j = K j i := by
    unfold K
    rw [add_comm]
    ring
  have habs (i j : ι) : |K i j| = bivarGaussianKernel (coords i) (coords j) := by
    have hei : e i = bivarExponent (coords i).1 (coords i).2 :=
      (bivarExponent_of_exponents (e i)).symm
    have hej : e j = bivarExponent (coords j).1 (coords j).2 :=
      (bivarExponent_of_exponents (e j)).symm
    rw [show K i j = sharpMoment η (e i + e j) /
        (scale i * scale j) by rfl, abs_div, hei, hej,
      abs_sharpMoment_add_eq_scale_mul_gaussian hη]
    rw [abs_mul, abs_of_pos (hscale i), abs_of_pos (hscale j)]
    change scale i * scale j * bivarGaussianKernel (coords i) (coords j) /
        (scale i * scale j) = bivarGaussianKernel (coords i) (coords j)
    exact mul_div_cancel_left₀ _
      (mul_ne_zero (ne_of_gt (hscale i)) (ne_of_gt (hscale j)))
  have hrow (i : ι) :
      (∑ j : ι, if i = j then 0 else |K i j|) ≤ 1 := by
    have hlt := bivarGaussianKernel_offDiagonal_sum_lt_one coords hcoords i
    simpa only [habs] using hlt.le
  have hq := quadraticForm_nonneg_of_normalized_diagonal_dominance
    K hdiag hsymm hrow (fun i ↦ c i * scale i)
  convert hq using 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  have hsi : scale i ≠ 0 := ne_of_gt (hscale i)
  have hsj : scale j ≠ 0 := ne_of_gt (hscale j)
  dsimp [K]
  field_simp

/-- Quantitative lower and upper comparisons for every monomial-shifted
moment matrix.  The parity correction is positive on its diagonal. -/
theorem sharpShiftedMoment_quadraticForm_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : ℝ} (hη : 0 < η) (u v : ℕ)
    (e : ι → Fin 2 →₀ ℕ) (he : Function.Injective e)
    (c : ι → ℝ) :
    let D := ∑ i : ι,
      (c i * sharpShiftedMomentScale η u v (e i 0) (e i 1)) ^ 2
    let Q := ∑ i : ι, ∑ j : ι,
      c i * (((-1 : ℝ) ^ (u * v)) *
        sharpMoment η (e i + e j + bivarExponent u v)) * c j
    (1 / 2 : ℝ) * D ≤ Q ∧ Q ≤ (3 / 2 : ℝ) * D := by
  dsimp only
  let coords : ι → ℕ × ℕ := fun i ↦ (e i 0, e i 1)
  have hcoords : Function.Injective coords := by
    intro i j hij
    apply he
    rw [← bivarExponent_of_exponents (e i),
      ← bivarExponent_of_exponents (e j)]
    exact congrArg (fun z : ℕ × ℕ ↦ bivarExponent z.1 z.2) hij
  let scale : ι → ℝ := fun i ↦
    sharpShiftedMomentScale η u v (coords i).1 (coords i).2
  have hscale (i : ι) : 0 < scale i :=
    sharpShiftedMomentScale_pos hη _ _ _ _
  let K : ι → ι → ℝ := fun i j ↦
    (((-1 : ℝ) ^ (u * v)) *
      sharpMoment η (e i + e j + bivarExponent u v)) /
        (scale i * scale j)
  have hdiag (i : ι) : K i i = 1 := by
    have heq : e i = bivarExponent (coords i).1 (coords i).2 :=
      (bivarExponent_of_exponents (e i)).symm
    rw [show K i i = (((-1 : ℝ) ^ (u * v)) *
        sharpMoment η (e i + e i + bivarExponent u v)) /
          (scale i * scale i) by rfl,
      heq, signed_sharpMoment_shift_self_eq_scale_sq hη]
    rw [pow_two]
    exact div_self (mul_ne_zero (ne_of_gt (hscale i)) (ne_of_gt (hscale i)))
  have hsymm (i j : ι) : K i j = K j i := by
    unfold K
    rw [show e i + e j = e j + e i by exact add_comm _ _]
    ring
  have habs (i j : ι) : |K i j| = bivarGaussianKernel (coords i) (coords j) := by
    have hei : e i = bivarExponent (coords i).1 (coords i).2 :=
      (bivarExponent_of_exponents (e i)).symm
    have hej : e j = bivarExponent (coords j).1 (coords j).2 :=
      (bivarExponent_of_exponents (e j)).symm
    rw [show K i j = (((-1 : ℝ) ^ (u * v)) *
        sharpMoment η (e i + e j + bivarExponent u v)) /
          (scale i * scale j) by rfl,
      abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      hei, hej, abs_sharpMoment_shift_eq_scale_mul_gaussian hη]
    rw [abs_mul, abs_of_pos (hscale i), abs_of_pos (hscale j)]
    change scale i * scale j * bivarGaussianKernel (coords i) (coords j) /
        (scale i * scale j) = bivarGaussianKernel (coords i) (coords j)
    exact mul_div_cancel_left₀ _
      (mul_ne_zero (ne_of_gt (hscale i)) (ne_of_gt (hscale j)))
  have hrow (i : ι) :
      (∑ j : ι, if i = j then 0 else |K i j|) ≤ (1 : ℝ) / 2 := by
    have hlt := bivarGaussianKernel_offDiagonal_sum_lt_half coords hcoords i
    simpa only [habs] using hlt.le
  let x : ι → ℝ := fun i ↦ c i * scale i
  have hlower := quadraticForm_lower_of_normalized_diagonal_dominance
    K hdiag hsymm (1 / 2 : ℝ) hrow x
  have hupper := quadraticForm_upper_of_normalized_diagonal_dominance
    K hdiag hsymm (1 / 2 : ℝ) hrow x
  have hnormalize :
      (∑ i : ι, ∑ j : ι, x i * K i j * x j) =
        ∑ i : ι, ∑ j : ι,
          c i * (((-1 : ℝ) ^ (u * v)) *
            sharpMoment η (e i + e j + bivarExponent u v)) * c j := by
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    have hsi : scale i ≠ 0 := ne_of_gt (hscale i)
    have hsj : scale j ≠ 0 := ne_of_gt (hscale j)
    dsimp [x, K]
    field_simp
  rw [hnormalize] at hlower hupper
  dsimp only [x] at hlower hupper
  norm_num at hlower hupper
  simpa only [scale, coords] using And.intro hlower hupper
/-- The sharp moment functional is nonnegative on every polynomial
square. -/
theorem sharpMomentFunctional_sq_nonneg {η : ℝ} (hη : 0 < η)
    (q : MvPolynomial (Fin 2) ℝ) :
    0 ≤ sharpMomentFunctional η (q ^ 2) := by
  let I := {α : Fin 2 →₀ ℕ // α ∈ q.support}
  let e : I → Fin 2 →₀ ℕ := fun α ↦ α.1
  let c : I → ℝ := fun α ↦ q.coeff α.1
  have he : Function.Injective e := by
    intro α β h
    exact Subtype.ext (by simpa [e] using h)
  have hq := sharpMoment_quadraticForm_nonneg hη e he c
  rw [show q = ∑ α : I, monomial (e α) (c α) by
    calc
      q = ∑ α ∈ q.support, monomial α (q.coeff α) := as_sum q
      _ = ∑ α : I, monomial (e α) (c α) := by
        symm
        simpa [I, e, c] using
          (Finset.sum_attach q.support (fun α ↦ monomial α (q.coeff α)))]
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum, map_sum,
    monomial_mul, sharpMomentFunctional_monomial]
  simpa only [e, c, mul_assoc, mul_left_comm, mul_comm] using hq

/-- Expansion of a monomial-shifted square under the moment functional. -/
theorem signed_sharpMomentFunctional_monomial_mul_sq
    (η : ℝ) (u v : ℕ) (q : MvPolynomial (Fin 2) ℝ) :
    ((-1 : ℝ) ^ (u * v)) * sharpMomentFunctional η
        (monomial (bivarExponent u v) 1 * q ^ 2) =
      ∑ α ∈ q.support, ∑ β ∈ q.support,
        q.coeff α * (((-1 : ℝ) ^ (u * v)) *
          sharpMoment η (α + β + bivarExponent u v)) * q.coeff β := by
  conv_lhs =>
    rw [as_sum q]
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum, map_sum,
    monomial_mul, sharpMomentFunctional_monomial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _hα
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _hβ
  rw [show bivarExponent u v + (α + β) = α + β + bivarExponent u v by
    simp only [add_assoc, add_comm]]
  ring

/-- Polynomial form of the quantitative shifted-localizer comparison. -/
theorem sharpShiftedMomentFunctional_sq_bounds
    {η : ℝ} (hη : 0 < η) (u v : ℕ)
    (q : MvPolynomial (Fin 2) ℝ) :
    let D := ∑ α ∈ q.support,
      (q.coeff α * sharpShiftedMomentScale η u v (α 0) (α 1)) ^ 2
    (1 / 2 : ℝ) * D ≤
        ((-1 : ℝ) ^ (u * v)) * sharpMomentFunctional η
          (monomial (bivarExponent u v) 1 * q ^ 2) ∧
      ((-1 : ℝ) ^ (u * v)) * sharpMomentFunctional η
          (monomial (bivarExponent u v) 1 * q ^ 2) ≤
        (3 / 2 : ℝ) * D := by
  dsimp only
  let I := {α : Fin 2 →₀ ℕ // α ∈ q.support}
  let e : I → Fin 2 →₀ ℕ := fun α ↦ α.1
  let c : I → ℝ := fun α ↦ q.coeff α.1
  have he : Function.Injective e := by
    intro α β h
    exact Subtype.ext (by simpa [e] using h)
  have hbounds := sharpShiftedMoment_quadraticForm_bounds hη u v e he c
  have hD :
      (∑ α : I,
          (c α * sharpShiftedMomentScale η u v (e α 0) (e α 1)) ^ 2) =
        ∑ α ∈ q.support,
          (q.coeff α * sharpShiftedMomentScale η u v (α 0) (α 1)) ^ 2 := by
    simpa [I, e, c] using
      (Finset.sum_attach q.support (fun α ↦
        (q.coeff α * sharpShiftedMomentScale η u v (α 0) (α 1)) ^ 2))
  have hfun := (signed_sharpMomentFunctional_monomial_mul_sq η u v q).symm
  have hQ :
      (∑ α : I, ∑ β : I,
          c α * (((-1 : ℝ) ^ (u * v)) *
            sharpMoment η (e α + e β + bivarExponent u v)) * c β) =
        ((-1 : ℝ) ^ (u * v)) * sharpMomentFunctional η
          (monomial (bivarExponent u v) 1 * q ^ 2) := by
    calc
      _ = ∑ α ∈ q.support, ∑ β : I,
          q.coeff α * (((-1 : ℝ) ^ (u * v)) *
            sharpMoment η (α + β.1 + bivarExponent u v)) * q.coeff β.1 := by
              simpa [I, e, c] using (Finset.sum_attach q.support (fun α ↦
                ∑ β : I, q.coeff α * (((-1 : ℝ) ^ (u * v)) *
                  sharpMoment η (α + β.1 + bivarExponent u v)) * q.coeff β.1))
      _ = ∑ α ∈ q.support, ∑ β ∈ q.support,
          q.coeff α * (((-1 : ℝ) ^ (u * v)) *
            sharpMoment η (α + β + bivarExponent u v)) * q.coeff β := by
              apply Finset.sum_congr rfl
              intro α _hα
              simpa [I] using (Finset.sum_attach q.support (fun β ↦
                q.coeff α * (((-1 : ℝ) ^ (u * v)) *
                  sharpMoment η (α + β + bivarExponent u v)) * q.coeff β))
      _ = _ := hfun
  rw [hD, hQ] at hbounds
  exact hbounds

/-- Exact diagonal ratio between the `-ab` and unshifted moment
matrices. -/
theorem sharpShiftedMomentScale_one_one_sq
    {η : ℝ} (hη : 0 < η) (i j : ℕ) :
    sharpShiftedMomentScale η 1 1 i j ^ 2 =
      η ^ 2 * Real.exp (16 * ((i : ℝ) + j) + 8) *
        sharpShiftedMomentScale η 0 0 i j ^ 2 := by
  have hsqrt : Real.sqrt η ^ (1 + 1) = η := by
    norm_num [Real.sq_sqrt hη.le]
  have hscale : sharpShiftedMomentScale η 1 1 i j =
      η * Real.exp (8 * ((i : ℝ) + j) + 4) *
        sharpShiftedMomentScale η 0 0 i j := by
    unfold sharpShiftedMomentScale
    rw [hsqrt]
    simp only [Nat.zero_add, pow_zero, mul_one]
    have hexp :
        Real.exp (2 * ((((2 * i + 1 : ℕ) : ℝ) ^ 2) +
            (((2 * j + 1 : ℕ) : ℝ) ^ 2))) =
          Real.exp (8 * ((i : ℝ) + j) + 4) *
            Real.exp (2 * ((((2 * i : ℕ) : ℝ) ^ 2) +
              (((2 * j : ℕ) : ℝ) ^ 2))) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  rw [hscale]
  have hexp : Real.exp (8 * ((i : ℝ) + j) + 4) ^ 2 =
      Real.exp (16 * ((i : ℝ) + j) + 8) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    (η * Real.exp (8 * ((i : ℝ) + j) + 4) *
        sharpShiftedMomentScale η 0 0 i j) ^ 2 =
      η ^ 2 * Real.exp (8 * ((i : ℝ) + j) + 4) ^ 2 *
        sharpShiftedMomentScale η 0 0 i j ^ 2 := by ring
    _ = _ := by rw [hexp]

theorem three_mul_eta_sq_scale_zero_le_scale_one_one
    {η : ℝ} (hη : 0 < η) (i j : ℕ) :
    3 * η ^ 2 * sharpShiftedMomentScale η 0 0 i j ^ 2 ≤
      sharpShiftedMomentScale η 1 1 i j ^ 2 := by
  rw [sharpShiftedMomentScale_one_one_sq hη]
  have hij : (0 : ℝ) ≤ (i : ℝ) + j := by positivity
  have harg : (8 : ℝ) ≤ 16 * ((i : ℝ) + j) + 8 := by
    nlinarith
  have he8 : (3 : ℝ) < Real.exp 8 := by
    linarith [Real.add_one_lt_exp (by norm_num : (8 : ℝ) ≠ 0)]
  have he : (3 : ℝ) ≤ Real.exp (16 * ((i : ℝ) + j) + 8) :=
    he8.le.trans (Real.exp_le_exp.mpr harg)
  have hnon : 0 ≤ η ^ 2 * sharpShiftedMomentScale η 0 0 i j ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left he hnon]

/-- The `a` localizer is positive on every square. -/
theorem sharpMomentFunctional_a_sq_nonneg {η : ℝ} (hη : 0 < η)
    (q : MvPolynomial (Fin 2) ℝ) :
    0 ≤ sharpMomentFunctional η (obstructionA * q ^ 2) := by
  have h := (sharpShiftedMomentFunctional_sq_bounds hη 1 0 q).1
  have hD : 0 ≤ ∑ α ∈ q.support,
      (q.coeff α * sharpShiftedMomentScale η 1 0 (α 0) (α 1)) ^ 2 := by
    positivity
  have hnon : 0 ≤ sharpMomentFunctional η
      (monomial (bivarExponent 1 0) 1 * q ^ 2) := by
    simp only [pow_zero, one_mul] at h
    exact (mul_nonneg (by norm_num) hD).trans h
  simpa [obstructionA, bivarExponent] using hnon

/-- The `b` localizer is positive on every square. -/
theorem sharpMomentFunctional_b_sq_nonneg {η : ℝ} (hη : 0 < η)
    (q : MvPolynomial (Fin 2) ℝ) :
    0 ≤ sharpMomentFunctional η (obstructionB * q ^ 2) := by
  have h := (sharpShiftedMomentFunctional_sq_bounds hη 0 1 q).1
  have hD : 0 ≤ ∑ α ∈ q.support,
      (q.coeff α * sharpShiftedMomentScale η 0 1 (α 0) (α 1)) ^ 2 := by
    positivity
  have hnon : 0 ≤ sharpMomentFunctional η
      (monomial (bivarExponent 0 1) 1 * q ^ 2) := by
    simp only [Nat.zero_mul, pow_zero, one_mul] at h
    exact (mul_nonneg (by norm_num) hD).trans h
  simpa [obstructionB, bivarExponent] using hnon

/-- The crucial shifted localizer `-(ab+η²)` is positive. -/
theorem sharpMomentFunctional_neg_ab_etaSq_sq_nonneg
    {η : ℝ} (hη : 0 < η) (q : MvPolynomial (Fin 2) ℝ) :
    0 ≤ sharpMomentFunctional η
      (-(obstructionA * obstructionB + C (η ^ 2)) * q ^ 2) := by
  let D0 := ∑ α ∈ q.support,
    (q.coeff α * sharpShiftedMomentScale η 0 0 (α 0) (α 1)) ^ 2
  let D11 := ∑ α ∈ q.support,
    (q.coeff α * sharpShiftedMomentScale η 1 1 (α 0) (α 1)) ^ 2
  have hD : 3 * η ^ 2 * D0 ≤ D11 := by
    dsimp [D0, D11]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α _hα
    have hs := three_mul_eta_sq_scale_zero_le_scale_one_one hη (α 0) (α 1)
    have hc : 0 ≤ q.coeff α ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hs hc]
  have h0 := (sharpShiftedMomentFunctional_sq_bounds hη 0 0 q).2
  have h11 := (sharpShiftedMomentFunctional_sq_bounds hη 1 1 q).1
  simp only [Nat.zero_mul, pow_zero, one_mul] at h0
  change sharpMomentFunctional η
      (monomial (bivarExponent 0 0) 1 * q ^ 2) ≤ (3 / 2 : ℝ) * D0 at h0
  simp only [Nat.one_mul, pow_one, neg_one_mul] at h11
  change (1 / 2 : ℝ) * D11 ≤
      -sharpMomentFunctional η
        (monomial (bivarExponent 1 1) 1 * q ^ 2) at h11
  have hη2 : 0 ≤ η ^ 2 := sq_nonneg η
  have hcompare :
      η ^ 2 * sharpMomentFunctional η
          (monomial (bivarExponent 0 0) 1 * q ^ 2) ≤
        -sharpMomentFunctional η
          (monomial (bivarExponent 1 1) 1 * q ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left h0 hη2
    nlinarith
  have hzero : monomial (bivarExponent 0 0) (1 : ℝ) =
      (1 : MvPolynomial (Fin 2) ℝ) := by simp [bivarExponent]
  have hab : monomial (bivarExponent 1 1) (1 : ℝ) =
      obstructionA * obstructionB := by
    change monomial (Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) 1) 1 =
      monomial (Finsupp.single (0 : Fin 2) 1) 1 *
        monomial (Finsupp.single (1 : Fin 2) 1) 1
    rw [monomial_mul]
    simp
  rw [hzero, one_mul, hab] at hcompare
  have hc : sharpMomentFunctional η (C (η ^ 2) * q ^ 2) =
      η ^ 2 * sharpMomentFunctional η (q ^ 2) := by
    rw [← MvPolynomial.smul_eq_C_mul, map_smul]
    rfl
  rw [show -(obstructionA * obstructionB + C (η ^ 2)) * q ^ 2 =
      -(obstructionA * obstructionB * q ^ 2) - C (η ^ 2) * q ^ 2 by ring,
    map_sub, map_neg, hc]
  linarith

end OptimalConvergenceRates.GeneralArchimedean

end
