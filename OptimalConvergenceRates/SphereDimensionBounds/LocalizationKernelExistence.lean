import OptimalConvergenceRates.SphereDimensionBounds.GegenbauerLocalization
import OptimalConvergenceRates.SphereDimensionBounds.LocalizationKernelParameters

/-! Unconditional existence of the actual original-sphere localization
kernel at the exact physical order r, including its positive normalization,
fourth-moment rate and Taylor-inversion smallness. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.LocalizationKernelExistence

open Polynomial TaylorKernelData LocalizationKernelParameters

/-- The concentrated polynomial and all analytic moment inputs of the
Taylor transfer are supplied, for every n≥3,d≥4,r≥8nd. The integrals are
over the original n-dimensional sphere. -/
theorem exists_kernel {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) :
    ∃ chi : Polynomial ℝ,chi ≠ 0 ∧ chi.natDegree ≤ residualOrder n r-2 ∧
      0 < normalizingMass (by omega : 0 < n) (multiplier n) chi ∧
      fourthMoment (by omega : 0 < n) (multiplier n) chi ≤ (12*(n:ℝ)/(r:ℝ))^4 ∧
      (d.choose 4:ℝ)*fourthMoment (by omega : 0 < n) (multiplier n) chi ≤ 27/128 := by
  obtain ⟨chi,hchi,hdeg,hquotient⟩ := GegenbauerLocalization.exists_concentrated_polynomial
    (dimension_lower hn) (order_ge_dimension hn hd hr)
  exact ⟨chi,hchi,hdeg,AngularWeightShift.normalizingMass_pos (by omega) _ chi hchi,
    actual_moment_bound hn hd hr chi hchi hquotient,
    actual_moment_smallness hn hd hr chi hchi hquotient⟩

theorem exists_kernel_quarter {n d r : ℕ} (hn : 3 ≤ n) (hd : 4 ≤ d) (hr : 8 * n * d ≤ r) :
    ∃ chi : Polynomial ℝ,chi.natDegree ≤ residualOrder n r-2 ∧
      0 < normalizingMass (by omega : 0 < n) (multiplier n) chi ∧
      fourthMoment (by omega : 0 < n) (multiplier n) chi ≤ (12*(n:ℝ)/(r:ℝ))^4 ∧
      (d.choose 4:ℝ)*fourthMoment (by omega : 0 < n) (multiplier n) chi ≤ 1/4 := by
  obtain ⟨chi,_,hdeg,hZ,hmu,hsmall⟩ := exists_kernel hn hd hr
  exact ⟨chi,hdeg,hZ,hmu,hsmall.trans (by norm_num)⟩

end OptimalConvergenceRates.SphereDimensionBounds.LocalizationKernelExistence
