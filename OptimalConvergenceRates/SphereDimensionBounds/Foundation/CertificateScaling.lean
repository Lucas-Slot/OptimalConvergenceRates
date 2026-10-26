import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Hierarchy

/-!
# Scaling certificates without changing the sphere or the relaxation order

The square roots in a certificate are multiplied by `sqrt alpha`; the equality
multiplier is multiplied by `alpha`. The degree bounds are preserved even when
`alpha = 0`.
-/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

/-- Multiplication by a nonnegative real constant preserves feasibility at the
same order, with the same number of squares. -/
theorem Feasible.scale {n r : ℕ} {p : Polynomial n} {lam α : ℝ}
    (hfeas : Feasible r p lam) (hα : 0 ≤ α) :
    Feasible r (MvPolynomial.C α * p) (α * lam) := by
  classical
  rcases hfeas with ⟨m, h, g, hh, hg, hid⟩
  have hsqrt : (MvPolynomial.C (Real.sqrt α) : Polynomial n) ^ 2 =
      MvPolynomial.C α := by
    rw [← MvPolynomial.C_pow, Real.sq_sqrt hα]
  refine ⟨m, fun j => MvPolynomial.C (Real.sqrt α) * h j,
    MvPolynomial.C α * g, ?_, ?_, ?_⟩
  · intro j
    calc
      (MvPolynomial.C (Real.sqrt α) * h j).totalDegree ≤
          (MvPolynomial.C (Real.sqrt α) : Polynomial n).totalDegree +
            (h j).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = (h j).totalDegree := by simp
      _ ≤ r := hh j
  · calc
      (MvPolynomial.C α * g).totalDegree ≤
          (MvPolynomial.C α : Polynomial n).totalDegree + g.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = g.totalDegree := by simp
      _ ≤ 2 * r - 2 := hg
  · have hsum :
        (∑ j : Fin m, (MvPolynomial.C (Real.sqrt α) * h j) ^ 2) =
          MvPolynomial.C α * (∑ j : Fin m, h j ^ 2) := by
      simp_rw [mul_pow, hsqrt]
      rw [Finset.mul_sum]
    calc
      MvPolynomial.C α * p - MvPolynomial.C (α * lam) =
          MvPolynomial.C α * (p - MvPolynomial.C lam) := by
        rw [MvPolynomial.C_mul]
        ring
      _ = MvPolynomial.C α *
          ((∑ j : Fin m, h j ^ 2) + (1 - radiusPolynomial n) * g) := by rw [hid]
      _ = (∑ j : Fin m, (MvPolynomial.C (Real.sqrt α) * h j) ^ 2) +
          (1 - radiusPolynomial n) * (MvPolynomial.C α * g) := by
        rw [hsum]
        ring

/-- Positive scalar multiplication can be undone at the same order. -/
theorem feasible_scale_iff {n r : ℕ} {p : Polynomial n} {lam α : ℝ}
    (hα : 0 < α) :
    Feasible r (MvPolynomial.C α * p) (α * lam) ↔ Feasible r p lam := by
  constructor
  · intro hfeas
    have hscaled := hfeas.scale (le_of_lt (inv_pos.mpr hα))
    simpa only [← mul_assoc, ← MvPolynomial.C_mul,
      inv_mul_cancel₀ hα.ne', MvPolynomial.C_1, one_mul] using hscaled
  · intro hfeas
    exact hfeas.scale hα.le

/-- A certificate for the normalized objective `p / beta` gives a certificate
for `p` after multiplying its feasible value by the positive normalizer.

Scalar division of a multivariate polynomial is represented explicitly as
`C beta⁻¹ * p`.
-/
theorem Feasible.of_normalized {n r : ℕ} {p : Polynomial n} {lam β : ℝ}
    (hfeas : Feasible r (MvPolynomial.C β⁻¹ * p) lam) (hβ : 0 < β) :
    Feasible r p (β * lam) := by
  have hscaled := hfeas.scale hβ.le
  simpa only [← mul_assoc, ← MvPolynomial.C_mul,
    mul_inv_cancel₀ hβ.ne', MvPolynomial.C_1, one_mul] using hscaled

/-- The reverse normalization map, including its exact feasible value. -/
theorem Feasible.normalize {n r : ℕ} {p : Polynomial n} {lam β : ℝ}
    (hfeas : Feasible r p lam) (hβ : 0 < β) :
    Feasible r (MvPolynomial.C β⁻¹ * p) (lam / β) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (hfeas.scale (le_of_lt (inv_pos.mpr hβ)))

/-- Transporting a certificate obstruction through positive normalization does
not require SDP attainment or a supremum argument. -/
theorem normalized_certificate_obstruction {n r : ℕ} {p : Polynomial n}
    {β η : ℝ} (hβ : 0 < β)
    (hcert : ∀ lam, Feasible r p lam → lam ≤ -η) :
    ∀ lam, Feasible r (MvPolynomial.C β⁻¹ * p) lam → lam ≤ -η / β := by
  intro lam hfeas
  have hbound : β * lam ≤ -η := hcert (β * lam) (hfeas.of_normalized hβ)
  apply (le_div_iff₀ hβ).2
  simpa [mul_comm] using hbound

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
