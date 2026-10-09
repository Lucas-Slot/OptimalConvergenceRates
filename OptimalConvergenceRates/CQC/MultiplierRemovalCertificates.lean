import OptimalConvergenceRates.CQC.MultiplierRemovalBounds

/-!
# Interval certificates for multiplier removal

The pointwise inverse-series bounds are converted here into certificates in
the original quadratic module, with orders linear in the series length.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

open GeneralArchimedean

variable {n m : ℕ}

/-- The inverse approximant after substituting the shifted multiplier. -/
def inverseApproxAt (α β : ℝ) (ell : ℕ)
    (a : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  polynomialSubst (a - C α) (inverseSeriesApprox α β ell)

/-- The multiplicative residual after substituting the shifted multiplier. -/
def inverseResidualAt (α β : ℝ) (ell : ℕ)
    (a : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  polynomialSubst (a - C α) (inverseSeriesResidual α β ell)

/-- The inverse approximant has a certified square upper bound. -/
theorem inverseApproxAt_sq_upper_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ} {α β : ℝ} (ell : ℕ)
    (hα : 0 < α) (hαβ : α < β) {r s : ℕ}
    (hlower : a - C α ∈ GenQuadraticModule g r)
    (hupper : C β - a ∈ GenQuadraticModule g s) :
    C (α⁻¹ ^ 2) - inverseApproxAt α β ell a ^ 2 ∈
      GenQuadraticModule g
        (max r s + (2 * ell + 3) * (a - C α).totalDegree) := by
  obtain ⟨cert⟩ := intervalCertificate_nonempty (sub_pos.mpr hαβ)
    (inverseSeriesApproxGap α β ell)
    (inverseSeriesApproxGap_nonnegOn hα hαβ ell)
  have hright : C (β - α) - (a - C α) ∈ GenQuadraticModule g s := by
    convert hupper using 1
    simp only [map_sub]
    ring
  have hmem := cert.subst_mem_at (a - C α) hlower hright
  have horder :
      max r s + ((inverseSeriesApproxGap α β ell).natDegree + 3) *
          (a - C α).totalDegree ≤
        max r s + (2 * ell + 3) * (a - C α).totalDegree :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_right (a - C α).totalDegree
        (Nat.add_le_add_right (inverseSeriesApproxGap_natDegree_le α β ell) 3)) _
  apply GenQuadraticModule_mono horder
  simpa [inverseSeriesApproxGap, inverseApproxAt, polynomialSubst,
    map_sub, map_pow] using hmem

/-- The residual has a certified exponentially small square upper bound. -/
theorem inverseResidualAt_sq_upper_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ} {α β : ℝ} (ell : ℕ)
    (hα : 0 < α) (hαβ : α < β) {r s : ℕ}
    (hlower : a - C α ∈ GenQuadraticModule g r)
    (hupper : C β - a ∈ GenQuadraticModule g s) :
    C ((2 * (1 - α / β) ^ (ell + 1)) ^ 2) -
        inverseResidualAt α β ell a ^ 2 ∈
      GenQuadraticModule g
        (max r s + (4 * (ell + 1) + 3) *
          (a - C α).totalDegree) := by
  obtain ⟨cert⟩ := intervalCertificate_nonempty (sub_pos.mpr hαβ)
    (inverseSeriesResidualGap α β ell)
    (inverseSeriesResidualGap_nonnegOn hα hαβ ell)
  have hright : C (β - α) - (a - C α) ∈ GenQuadraticModule g s := by
    convert hupper using 1
    simp only [map_sub]
    ring
  have hmem := cert.subst_mem_at (a - C α) hlower hright
  have horder :
      max r s + ((inverseSeriesResidualGap α β ell).natDegree + 3) *
          (a - C α).totalDegree ≤
        max r s + (4 * (ell + 1) + 3) * (a - C α).totalDegree :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_right (a - C α).totalDegree
        (Nat.add_le_add_right (inverseSeriesResidualGap_natDegree_le α β ell) 3)) _
  apply GenQuadraticModule_mono horder
  simpa [inverseSeriesResidualGap, inverseResidualAt, polynomialSubst,
    map_sub, map_pow] using hmem

/-- The substituted residual satisfies the exact identity
`a² q² + v = 1`. -/
theorem inverseApproxAt_residual_identity
    (a : MvPolynomial (Fin n) ℝ) (α β : ℝ) (ell : ℕ) :
    a ^ 2 * inverseApproxAt α β ell a ^ 2 +
        inverseResidualAt α β ell a = 1 := by
  simp only [inverseApproxAt, inverseResidualAt, inverseSeriesResidual,
    polynomialSubst, map_sub, map_add, map_mul, map_pow, map_one,
    Polynomial.aeval_X, Polynomial.aeval_C, MvPolynomial.algebraMap_eq]
  ring

end CQCInternal
end OptimalConvergenceRates

end
