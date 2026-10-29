import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.DegreeAmplificationFeasibility
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.DegreeAmplificationTransfer
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.DegreeAmplificationRate
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.GeneralDegreeNormalization
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.UniformConstants

/-! One actual degree-d sparse-XOR amplification, fixed before every order. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace DegreeAmplification

open scoped BigOperators
open MvPolynomial Foundation
open DegreeAmplificationRate GeneralDegreeNormalization

namespace HardInput

variable {N K : ℕ} (D : HardQuarticData N K)

theorem homogeneous (k j : ℕ) :
    (finiteAmplified D k j).IsHomogeneous (4*(k+1)+2*j) :=
  (amplified_homogeneous D.polynomial D.polynomial_isHomogeneous k j).rename_isHomogeneous

theorem nonneg (k j : ℕ) (x : Fin (N + 2) → ℝ) :
    0≤eval x (finiteAmplified D k j) := by
  rw [finiteAmplified,eval_rename]
  exact amplified_nonneg D.polynomial D.polynomial_nonneg k j _

theorem minimum_zero (k j : ℕ) : IsSphereMinimum (finiteAmplified D k j) 0 := by
  apply isSphereMinimum_reindex D.coordinateEquiv
  · intro x hx
    exact amplified_nonneg D.polynomial D.polynomial_nonneg k j x
  · exact ⟨paddingPole,paddingPole_sphere,
      amplified_pole_eval D.polynomial D.polynomial_isHomogeneous k j⟩

theorem norm_positive (k j : ℕ) : 0<sphereSupNorm (finiteAmplified D k j) := by
  obtain ⟨x,hx,hpos⟩ := amplified_positive_value D.polynomial D.polynomial_isHomogeneous k j
    paddingPole paddingPole_sphere D.polynomial_positive_last_axis
  apply sphereSupNorm_pos_of_nonzero_value
    (x := reindexedPoint D.coordinateEquiv x)
  · change (∑ i,reindexedPoint D.coordinateEquiv x i^2)=1
    rw [reindexedPoint_sum_sq,hx]
  · rw [finiteAmplified,eval_reindexedPoint]
    exact ne_of_gt hpos

theorem norm_le_one (k j : ℕ) : sphereSupNorm (finiteAmplified D k j)≤1 := by
  obtain ⟨x,hx,hvalue⟩ := sphereSupNorm_attained (by omega : 0<N+2) (finiteAmplified D k j)
  change Foundation.sphereSupNorm (finiteAmplified D k j) ≤ 1
  rw [← hvalue,abs_of_nonneg (nonneg D k j x),finiteAmplified,eval_rename]
  apply amplified_sphere_upper D.polynomial D.polynomial_isHomogeneous
    (fun y hy ↦ D.polynomial_le_one_on_ball y hy.le)
  exact (D.coordinateEquiv.sum_comp (fun i ↦ x i^2)).trans hx

theorem certificate_high {k j r : ℕ} {lam ρ : ℝ}
    (hcert : Feasible r (finiteAmplified D k j) lam)
    (hr : 2 * (k + 1) + j ≤ r) (hrK : (k + 1) * K ≤ r) (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hscale : 1 ≤ ρ * (K : ℝ))
    (hA : 6 * (2 : ℝ) ^ N * angularTruncationFactor K ρ ≤ 1)
    (hAdelta : 6 * (2 : ℝ) ^ N * angularTruncationFactor K ρ ≤ (1 / (8712 * (N : ℝ))) / 32) :
    lam≤-((1/(8712*(N:ℝ)))*((k+1:ℕ)*ρ*(K:ℝ)/(r:ℝ))^4/64) := by
  have hgeneric := (finiteSphereCertificate_fin_iff (by omega)
    ((homogeneous D k j).totalDegree_le.trans (by omega))).mpr hcert
  have hback := hgeneric.rename_equiv D.coordinateEquiv.symm
  have hback' : FiniteSphereCertificate r (amplified D.polynomial k j) lam := by
    simpa only [finiteAmplified,rename_rename,D.coordinateEquiv.symm_comp_self,
      rename_id_apply] using hback
  rcases hback' with ⟨m,h,g,hdegree,hgdegree,hid⟩
  have hcertificate : amplified D.polynomial k j+C (-lam)=
      (∑ b,h b^2)+(1-genericRadius)*g := by
    simpa only [C_neg,sub_eq_add_neg] using hid
  have hAcube : 6*cubeSize (Fin N)*angularTruncationFactor K ρ≤1 := by
    simpa [cubeSize] using hA
  have hAdeltacube : 6*cubeSize (Fin N)*angularTruncationFactor K ρ≤
      (1/(8712*(N:ℝ)))/32 := by simpa [cubeSize] using hAdelta
  have hshift := amplified_certificate_high_order_shift D.pseudoexpectation D.polynomial
    D.polynomial_isHomogeneous D.polynomial_degree_truncated
    (fun y hy ↦ D.polynomial_le_one_on_ball y hy.le)
    (fun i z ↦ D.point z i) D.point_coordinate_degree D.point_unit
    D.polynomial_eval_negative k j (-lam) h g hcertificate hdegree
    (by have hK := D.level_ge_two; omega : 0<K) hrK hρ0 hρhalf hscale hAcube hAdeltacube
  linarith

theorem gap_high {k j r : ℕ} {ρ : ℝ} (hr : 2 * (k + 1) + j ≤ r)
    (hrK : (k + 1) * K ≤ r) (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hscale : 1 ≤ ρ * (K : ℝ))
    (hA : 6 * (2 : ℝ) ^ N * angularTruncationFactor K ρ ≤ 1)
    (hAdelta : 6 * (2 : ℝ) ^ N * angularTruncationFactor K ρ ≤ (1 / (8712 * (N : ℝ))) / 32) :
    (1/(8712*(N:ℝ)))*((k+1:ℕ)*ρ*(K:ℝ)/(r:ℝ))^4/64≤
      gap r (finiteAmplified D k j) := by
  apply gap_lower_of_certificates (minimum_zero D k j)
    ⟨_,finiteAmplified_feasible D k j r hr⟩
  exact fun _ hcert ↦ certificate_high D hcert hr hrK hρ0 hρhalf hscale hA hAdelta

theorem gap_low {k j r : ℕ} {ρ : ℝ} (hr : 2 * (k + 1) + j ≤ r)
    (hrK : r ≤ (k + 1) * K) (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hscale : 1 ≤ ρ * (K : ℝ))
    (hA : 6 * (2 : ℝ) ^ N * angularTruncationFactor K ρ ≤ 1)
    (hAdelta : 6 * (2 : ℝ) ^ N * angularTruncationFactor K ρ ≤ (1 / (8712 * (N : ℝ))) / 32) :
    (1/(8712*(N:ℝ)))*ρ^4/64≤gap r (finiteAmplified D k j) := by
  apply gap_lower_of_certificates (minimum_zero D k j)
    ⟨_,finiteAmplified_feasible D k j r hr⟩
  intro lam hcert
  have h := certificate_high D (feasible_mono hrK hcert) (hr.trans hrK) (le_refl ((k+1)*K))
    hρ0 hρhalf hscale hA hAdelta
  have hKpos : (0:ℝ)<K := by exact_mod_cast (by have hK := D.level_ge_two; omega : 0<K)
  have hellpos : (0:ℝ)<(k+1:ℕ) := by positivity
  have hratio : ((k+1:ℕ):ℝ)*ρ*(K:ℝ)/(((k+1)*K:ℕ):ℝ)=ρ := by
    push_cast
    field_simp <;> ring
  rwa [hratio] at h

end HardInput

/-- Every even degree is obtained by genuine angular amplification and at
most one radial factor. -/
theorem even_degree_parameters (d : ℕ) (hd : 4 ≤ d) (heven : Even d) :
    ∃ k j : ℕ, j≤1 ∧ d=4*(k+1)+2*j ∧ d/2=2*(k+1)+j ∧ d≤6*(k+1) := by
  obtain ⟨a,ha⟩ := heven
  refine ⟨d/4-1,(d-4*(d/4))/2,?_,?_,?_,?_⟩ <;> omega

/-- The new lower bound: one normalized nonnegative degree-d form, chosen
before the order r, with the original full sphere Feasible predicate. -/
theorem uniform_degree_lower_bound : UniformDegreeLowerBound := by
  obtain ⟨ρ,N₀,hρ,hρhalf,hparameters⟩ :=
    exists_uniform_dyadic_parameters (2^51) (by norm_num)
  have hdivisor : 0<(2:ℕ)^51 := by positivity
  have hc : 0<degreeRateConstant ρ (2^51) := degreeRateConstant_pos ρ (2^51) hρ hdivisor
  refine ⟨degreeRateConstant ρ (2^51),hc,max N₀ (2^53)+2,?_⟩
  intro n hn
  let N : ℕ := n-2
  have hN₀ : N₀≤N := by dsimp [N]; omega
  have hNbig : 2^53≤N := by dsimp [N]; omega
  have hNtwo : 2≤N := by norm_num at hNbig; omega
  have hdivN : 2^51≤N := by norm_num at hNbig ⊢; omega
  have hdimension : N+2=n := by dsimp [N]; omega
  obtain ⟨D⟩ := exists_hardQuarticData N hNbig
  obtain ⟨hKupper,hscale,herror⟩ := hparameters N hN₀
  have hNreal : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hden : (1:ℝ)≤32*(8712*(N:ℝ)) := by nlinarith
  have hfrac : 1/(32*(8712*(N:ℝ)))≤(1:ℝ) := by
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hden
  have hA : 6*(2:ℝ)^N*angularTruncationFactor (N/2^51) ρ≤1 := herror.trans hfrac
  have hAdelta : 6*(2:ℝ)^N*angularTruncationFactor (N/2^51) ρ≤
      (1/(8712*(N:ℝ)))/32 := by
    simpa only [div_div,mul_comm] using herror
  intro d hd heven
  obtain ⟨k,j,hj,hdform,hdhalf,hdell⟩ := even_degree_parameters d hd heven
  rw [← hdimension]
  refine ⟨normalizeObjective (finiteAmplified D k j),?_,?_⟩
  · apply normalizedObjective_form (by omega) _
      (by simpa only [← hdform] using HardInput.homogeneous D k j)
      (HardInput.nonneg D k j) (HardInput.minimum_zero D k j) (HardInput.norm_positive D k j)
  · intro r hr
    have horder : 2*(k+1)+j≤r := by omega
    have hne : (feasibleValues r (finiteAmplified D k j)).Nonempty :=
      ⟨_,finiteAmplified_feasible D k j r horder⟩
    refine ⟨normalizeObjective_feasible_nonempty (HardInput.norm_positive D k j) hne,?_⟩
    apply GeneralDegreeNormalization.normalizeObjective_gap_of_gap (by omega)
      (HardInput.homogeneous D k j) (HardInput.nonneg D k j)
      (HardInput.minimum_zero D k j) (HardInput.norm_positive D k j)
      (HardInput.norm_le_one D k j) hne
    · apply mul_nonneg hc.le
      apply le_min <;> positivity
    · apply degree_rate_of_two_regimes N (2^51) (k+1) d r hdivisor hdivN hNtwo
        (by omega) hdell ρ hρ
      · intro hrK
        exact HardInput.gap_low D horder hrK hρ.le hρhalf hscale hA hAdelta
      · intro hrK
        exact HardInput.gap_high D horder hrK hρ.le hρhalf hscale hA hAdelta

end DegreeAmplification
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
