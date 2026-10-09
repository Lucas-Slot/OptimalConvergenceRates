/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/Dirichlet.lean

  The scalar Chebyshev--Dirichlet polynomial used to construct positive zonal kernels.
-/
import OptimalConvergenceRates.Chebyshev.Chebyshev

open Polynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The polynomial (D_k(t)=1+2sum_{j=1}^k T_j(t)). -/
noncomputable def sphereDirichletPolynomial (k : ℕ) : Polynomial ℝ :=
  1 + 2 * ∑ j ∈ Finset.range k, chebyshevT (j + 1)

/-- Evaluation commutes with the defining finite Chebyshev sum. -/
theorem sphereDirichletPolynomial_eval (k : ℕ) (t : ℝ) :
    (sphereDirichletPolynomial k).eval t =
      1 + 2 * ∑ j ∈ Finset.range k, (chebyshevT (j + 1)).eval t := by
  simp [sphereDirichletPolynomial, Polynomial.eval_finset_sum]

/-- Trigonometric form of the Dirichlet polynomial on the cosine coordinate. -/
theorem sphereDirichletPolynomial_eval_cos (k : ℕ) (theta : ℝ) :
    (sphereDirichletPolynomial k).eval (Real.cos theta) =
      1 + 2 * ∑ j ∈ Finset.range k, Real.cos ((j + 1) * theta) := by
  rw [sphereDirichletPolynomial_eval]
  apply congrArg (1 + 2 * ·)
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Nat.cast_add, Nat.cast_one] using
    chebyshevT_cos (j + 1) theta

/-- The finite cosine sum telescopes after multiplication by the half-angle sine. -/
theorem two_mul_sin_half_mul_sum_cos (k : ℕ) (theta : ℝ) :
    2 * Real.sin (theta / 2) *
        (∑ j ∈ Finset.range k, Real.cos ((j + 1) * theta)) =
      Real.sin (((k : ℝ) + 1 / 2) * theta) -
        Real.sin (theta / 2) := by
  induction k with
  | zero =>
      norm_num only [Finset.sum_range_zero, sum_empty, mul_zero,
        Nat.cast_zero, zero_add]
      rw [show (1 / 2 : ℝ) * theta = theta / 2 by ring]
      ring
  | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih,
        Real.two_mul_sin_mul_cos]
      have hminus :
          theta / 2 - ((k : ℝ) + 1) * theta =
            -(((k : ℝ) + 1 / 2) * theta) := by
        ring
      have hplus :
          theta / 2 + ((k : ℝ) + 1) * theta =
            ((k : ℝ) + 3 / 2) * theta := by
        ring
      have hsucc :
          (((k + 1 : ℕ) : ℝ) + 1 / 2) * theta =
            ((k : ℝ) + 3 / 2) * theta := by
        push_cast
        ring
      rw [hminus, Real.sin_neg, hplus, hsucc]
      ring

/-- Exact product form of the scalar Dirichlet kernel, valid also at zero. -/
theorem sin_half_mul_sphereDirichletPolynomial_eval_cos
    (k : ℕ) (theta : ℝ) :
    Real.sin (theta / 2) *
        (sphereDirichletPolynomial k).eval (Real.cos theta) =
      Real.sin (((k : ℝ) + 1 / 2) * theta) := by
  rw [sphereDirichletPolynomial_eval_cos]
  calc
    Real.sin (theta / 2) *
        (1 + 2 * ∑ j ∈ Finset.range k,
          Real.cos ((j + 1) * theta)) =
      Real.sin (theta / 2) +
        2 * Real.sin (theta / 2) *
          (∑ j ∈ Finset.range k,
            Real.cos ((j + 1) * theta)) := by ring
    _ = Real.sin (((k : ℝ) + 1 / 2) * theta) := by
      rw [two_mul_sin_half_mul_sum_cos]
      ring

/-- Away from the peak, the scalar Dirichlet kernel has reciprocal-angle decay. -/
theorem abs_sphereDirichletPolynomial_eval_cos_le_pi_div
    (k : ℕ) {theta : ℝ} (htheta : 0 < theta)
    (hthetaPi : theta ≤ Real.pi) :
    |(sphereDirichletPolynomial k).eval (Real.cos theta)| ≤
      Real.pi / theta := by
  have hhalf :
      theta / Real.pi ≤ Real.sin (theta / 2) := by
    have hJordan := Real.mul_le_sin
      (x := theta / 2) (by positivity) (by linarith)
    have hrearrange :
        2 / Real.pi * (theta / 2) = theta / Real.pi := by
      ring
    exact hrearrange ▸ hJordan
  have hhalfNonneg : 0 ≤ Real.sin (theta / 2) :=
    (div_nonneg htheta.le Real.pi_pos.le).trans hhalf
  have hproduct :
      Real.sin (theta / 2) *
          |(sphereDirichletPolynomial k).eval (Real.cos theta)| ≤
        1 := by
    calc
      Real.sin (theta / 2) *
          |(sphereDirichletPolynomial k).eval (Real.cos theta)| =
          |Real.sin (theta / 2) *
            (sphereDirichletPolynomial k).eval (Real.cos theta)| := by
        rw [abs_mul, abs_of_nonneg hhalfNonneg]
      _ = |Real.sin (((k : ℝ) + 1 / 2) * theta)| := by
        rw [sin_half_mul_sphereDirichletPolynomial_eval_cos]
      _ ≤ 1 := Real.abs_sin_le_one _
  have hscaled :
      (theta / Real.pi) *
          |(sphereDirichletPolynomial k).eval (Real.cos theta)| ≤
        1 :=
    (mul_le_mul_of_nonneg_right hhalf (abs_nonneg _)).trans hproduct
  have hquot :
      theta *
          |(sphereDirichletPolynomial k).eval (Real.cos theta)| /
          Real.pi ≤ 1 := by
    calc
      theta *
          |(sphereDirichletPolynomial k).eval (Real.cos theta)| /
          Real.pi =
          (theta / Real.pi) *
            |(sphereDirichletPolynomial k).eval (Real.cos theta)| := by ring
      _ ≤ 1 := hscaled
  have hmul :
      theta *
          |(sphereDirichletPolynomial k).eval (Real.cos theta)| ≤
        Real.pi := by
    simpa using (div_le_iff₀ Real.pi_pos).1 hquot
  apply (le_div_iff₀ htheta).2
  simpa [mul_comm] using hmul

/-- The Dirichlet polynomial never exceeds its value at the peak on cosine
coordinates. This coarse bound is the near-cap input for the moment estimates. -/
theorem abs_sphereDirichletPolynomial_eval_cos_le (k : ℕ) (theta : ℝ) :
    |(sphereDirichletPolynomial k).eval (Real.cos theta)| ≤
      2 * (k : ℝ) + 1 := by
  rw [sphereDirichletPolynomial_eval_cos]
  have hsum :
      |∑ j ∈ Finset.range k, Real.cos ((j + 1) * theta)| ≤ (k : ℝ) := by
    calc
      |∑ j ∈ Finset.range k, Real.cos ((j + 1) * theta)| ≤
          ∑ j ∈ Finset.range k, |Real.cos ((j + 1) * theta)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact Real.abs_cos_le_one _
      _ = (k : ℝ) := by simp
  calc
    |1 + 2 * ∑ j ∈ Finset.range k, Real.cos ((j + 1) * theta)| ≤
        |(1 : ℝ)| + |2 * ∑ j ∈ Finset.range k,
          Real.cos ((j + 1) * theta)| := abs_add_le _ _
    _ = 1 + 2 * |∑ j ∈ Finset.range k,
        Real.cos ((j + 1) * theta)| := by
      rw [abs_one, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 1 + 2 * (k : ℝ) := by gcongr
    _ = 2 * (k : ℝ) + 1 := by ring

/-- The scalar estimate in `min(peak, reciprocal angle)` form. -/
theorem abs_sphereDirichletPolynomial_eval_cos_le_min
    (k : ℕ) {theta : ℝ} (htheta : 0 < theta)
    (hthetaPi : theta ≤ Real.pi) :
    |(sphereDirichletPolynomial k).eval (Real.cos theta)| ≤
      min (2 * (k : ℝ) + 1) (Real.pi / theta) := by
  exact le_min
    (abs_sphereDirichletPolynomial_eval_cos_le k theta)
    (abs_sphereDirichletPolynomial_eval_cos_le_pi_div
      k htheta hthetaPi)

/-- Algebraic interval form of the global Dirichlet bound. -/
theorem abs_sphereDirichletPolynomial_eval_le (k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |(sphereDirichletPolynomial k).eval t| ≤ 2 * (k : ℝ) + 1 := by
  rw [← Real.cos_arccos ht.1 ht.2]
  exact abs_sphereDirichletPolynomial_eval_cos_le k (Real.arccos t)

/-- On the natural `1/k` scale, every cosine term stays above one half, so
the Dirichlet polynomial is bounded below by its bandwidth. -/
theorem natCast_le_sphereDirichletPolynomial_eval_cos
    (k : ℕ) (hk : 1 ≤ k) {theta : ℝ}
    (htheta : |theta| ≤ 1 / (k : ℝ)) :
    (k : ℝ) ≤ (sphereDirichletPolynomial k).eval (Real.cos theta) := by
  rw [sphereDirichletPolynomial_eval_cos]
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hterm : ∀ j ∈ Finset.range k,
      (1 / 2 : ℝ) ≤ Real.cos ((j + 1) * theta) := by
    intro j hj
    have hjleNat : j + 1 ≤ k := by
      simpa only [Finset.mem_range] using hj
    have hjle : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjleNat
    have hjnonneg : 0 ≤ ((j + 1 : ℕ) : ℝ) := by positivity
    have harg : |((j + 1 : ℕ) * theta)| ≤ (1 : ℝ) := by
      rw [abs_mul, abs_of_nonneg hjnonneg]
      calc
        ((j + 1 : ℕ) : ℝ) * |theta| ≤ (k : ℝ) * (1 / (k : ℝ)) :=
          mul_le_mul hjle htheta (abs_nonneg theta) (Nat.cast_nonneg k)
        _ = 1 := by field_simp
    have hargsq : (((j + 1 : ℕ) : ℝ) * theta) ^ 2 ≤ 1 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg _) harg 2
      simpa [sq_abs] using hpow
    have hcos := Real.one_sub_sq_div_two_le_cos
      (x := ((j + 1 : ℕ) : ℝ) * theta)
    norm_num only [Nat.cast_add, Nat.cast_one] at hargsq hcos
    nlinarith
  have hsum : (k : ℝ) / 2 ≤
      ∑ j ∈ Finset.range k, Real.cos ((j + 1) * theta) := by
    calc
      (k : ℝ) / 2 = ∑ _j ∈ Finset.range k, (1 / 2 : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ j ∈ Finset.range k, Real.cos ((j + 1) * theta) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hterm j hj
  nlinarith

/-- The peak value is (D_k(1)=2k+1). -/
theorem sphereDirichletPolynomial_eval_one (k : ℕ) :
    (sphereDirichletPolynomial k).eval 1 = 2 * k + 1 := by
  rw [sphereDirichletPolynomial_eval]
  simp [chebyshevT_eval_one]
  ring

/-- The scalar kernel polynomial has degree at most its bandwidth. -/
theorem sphereDirichletPolynomial_natDegree_le (k : ℕ) :
    (sphereDirichletPolynomial k).natDegree ≤ k := by
  have hsum :
      (∑ j ∈ Finset.range k, chebyshevT (j + 1)).natDegree ≤ k := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    rw [natDegree_chebyshevT]
    simp only [Finset.mem_range] at hj
    omega
  unfold sphereDirichletPolynomial
  calc
    (1 + 2 * ∑ j ∈ Finset.range k, chebyshevT (j + 1) : Polynomial ℝ).natDegree ≤
        max (1 : Polynomial ℝ).natDegree
          (2 * ∑ j ∈ Finset.range k, chebyshevT (j + 1) : Polynomial ℝ).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ k := by
      apply max_le
      · simp
      · have hmul :
            (2 * ∑ j ∈ Finset.range k, chebyshevT (j + 1) : Polynomial ℝ).natDegree ≤
              (2 : Polynomial ℝ).natDegree +
                (∑ j ∈ Finset.range k, chebyshevT (j + 1)).natDegree :=
            Polynomial.natDegree_mul_le
        exact hmul.trans (by simpa using hsum)

/-- The even power used in the positive zonal kernel is pointwise nonnegative. -/
theorem sphereDirichletPolynomial_evenPow_nonneg (p k : ℕ) (t : ℝ) :
    0 ≤ ((sphereDirichletPolynomial k).eval t) ^ (2 * p) := by
  rw [show 2 * p = p * 2 by omega, pow_mul]
  exact sq_nonneg _

end QuarticConvergence
end OptimalConvergenceRates

end
