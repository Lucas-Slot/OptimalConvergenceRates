import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.ComplexPolynomialSplit
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.WeightedTaylor
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.ScalarAlgebra
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.SphereCurve
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.PseudoexpectationBound
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.HardQuartic
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.FiniteReindex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Uniform transfer from a Boolean functional

This module separates the finite functional absorption from the analytic
Taylor estimate. Every application to the functional carries its actual
Boolean degree bound.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators

/-- An absolute evaluation bound on precisely the functional's domain. -/
def TruncatedEvaluationBound {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
    (E : TruncatedBooleanPseudoexpectation V K) (L : ℝ) : Prop :=
  ∀ (f : booleanDegreeSpace (I := V) (2 * K)) (B : ℝ),
    (∀ z, |(f : (V → Bool) → ℝ) z| ≤ B) → |E.functional f| ≤ L * B

/-- The evaluation bound follows from normalization and positivity alone. -/
theorem truncatedEvaluationBound_of_positive
    {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
    (E : TruncatedBooleanPseudoexpectation V K) :
    TruncatedEvaluationBound E (cubeSize V) := by
  intro f B hB
  exact pseudoexpectation_abs_le K E f B hB

theorem half_le_sin_of_le_half {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    t / 2 ≤ Real.sin t := by
  have hcoef : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_lt_four]
  have htpi : t ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
  calc
    t / 2 = (1 / 2) * t := by ring
    _ ≤ (2 / Real.pi) * t := mul_le_mul_of_nonneg_right hcoef ht0
    _ ≤ Real.sin t := Real.mul_le_sin ht0 htpi

section FunctionalAbsorption

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] {K : ℕ}

/-- Apply the truncated functional to the actual squared-norm approximation.
The vector may have an empty coordinate family. -/
theorem functional_transfer_inequality
    (E : TruncatedBooleanPseudoexpectation V K) {L D eps delta t : ℝ}
    (hbound : TruncatedEvaluationBound E L)
    (q : (V → Bool) → ℝ) (hq : HasBooleanDegree (2 * K) q)
    (hqeval : E.functional ⟨q, hq⟩ = -delta)
    (G : (V → Bool) → EuclideanSpace ℂ J)
    (hre : ∀ j, HasBooleanDegree K (fun z ↦ (G z j).re))
    (him : ∀ j, HasBooleanDegree K (fun z ↦ (G z j).im))
    (herror : ∀ z, |eps + Real.sin t ^ 4 * q z - ‖G z‖ ^ 2| ≤
      6 * D * (eps + t ^ 4)) :
    delta * Real.sin t ^ 4 - (6 * L * D) * t ^ 4 ≤
      (1 + 6 * L * D) * eps := by
  let oneE : booleanDegreeSpace (I := V) (2 * K) :=
    ⟨fun _ ↦ 1, hasBooleanDegree_one (2 * K)⟩
  let qE : booleanDegreeSpace (I := V) (2 * K) := ⟨q, hq⟩
  let gE : booleanDegreeSpace (I := V) (2 * K) :=
    ⟨fun z ↦ ‖G z‖ ^ 2, hasBooleanDegree_norm_sq G K hre him⟩
  let errorE := eps • oneE + Real.sin t ^ 4 • qE - gE
  have habs := hbound errorE (6 * D * (eps + t ^ 4)) (by
    intro z
    change |eps * 1 + Real.sin t ^ 4 * q z - ‖G z‖ ^ 2| ≤ _
    simpa only [mul_one] using herror z)
  have hpos : 0 ≤ E.functional gE :=
    truncatedPseudoexpectation_norm_sq_nonneg E G hre him
  have hone : E.functional oneE = 1 := E.normalized
  have hqE : E.functional qE = -delta := hqeval
  have heval : E.functional errorE =
      eps - delta * Real.sin t ^ 4 - E.functional gE := by
    simp only [errorE, map_sub, map_add, map_smul, hone, hqE, smul_eq_mul]
    ring
  rw [heval] at habs
  have hlow := (abs_le.mp habs).1
  nlinarith

/-- The final absorption, using only the quantitative evaluation bound and
positivity on degree-`K` real squares. -/
theorem functional_transfer_lower_bound
    (E : TruncatedBooleanPseudoexpectation V K) {L D eps delta t : ℝ}
    (hbound : TruncatedEvaluationBound E L)
    (q : (V → Bool) → ℝ) (hq : HasBooleanDegree (2 * K) q)
    (hqeval : E.functional ⟨q, hq⟩ = -delta)
    (G : (V → Bool) → EuclideanSpace ℂ J)
    (hre : ∀ j, HasBooleanDegree K (fun z ↦ (G z j).re))
    (him : ∀ j, HasBooleanDegree K (fun z ↦ (G z j).im))
    (herror : ∀ z, |eps + Real.sin t ^ 4 * q z - ‖G z‖ ^ 2| ≤
      6 * D * (eps + t ^ 4))
    (heps : 0 ≤ eps) (ht0 : 0 ≤ t) (hthalf : t ≤ 1 / 2)
    (hA : 6 * L * D ≤ 1) (hAdelta : 6 * L * D ≤ delta / 32) :
    delta * t ^ 4 / 64 ≤ eps :=
  transfer_scalar_bound (6 * L * D) delta eps (Real.sin t) t hA hAdelta heps
    (functional_transfer_inequality E hbound q hq hqeval G hre him herror)
    (half_le_sin_of_le_half ht0 hthalf) ht0

end FunctionalAbsorption

section ActualCertificate

variable {V σ J : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [Fintype J]
    {r K : ℕ}

/-- The uniform transfer for an actual padded sphere certificate. All analytic
estimates use the Euclidean norm on the square family, so no constant depends
on the number of squares or on their individual coefficients. -/
theorem paddedCertificate_uniform_transfer
    (E : TruncatedBooleanPseudoexpectation V K) {L delta ρ : ℝ}
    (hbound : TruncatedEvaluationBound E L)
    (q : MvPolynomial σ ℝ) (hqhom : q.IsHomogeneous 4)
    (hqdegree : q.totalDegree ≤ 2 * K)
    (hqupper : ∀ y : σ → ℝ, (∑ i, y i ^ 2) = 1 → MvPolynomial.eval y q ≤ 1)
    (a : σ → (V → Bool) → ℝ) (hadegree : ∀ i, HasBooleanDegree 1 (a i))
    (haunit : ∀ z, (∑ i, a i z ^ 2) = 1)
    (hqeval : E.functional ⟨fun z ↦ MvPolynomial.eval (fun i ↦ a i z) q,
      hasBooleanDegree_eval_of_totalDegree_le q a hadegree (2 * K) hqdegree⟩ = -delta)
    (eps : ℝ) (h : J → MvPolynomial (Option σ) ℝ)
    (g : MvPolynomial (Option σ) ℝ)
    (certificate : paddedPolynomial q + MvPolynomial.C eps =
      (∑ j : J, h j ^ 2) + (1 - genericRadius) * g)
    (hdegree : ∀ j, (h j).totalDegree ≤ r) (hr : 0 < r) (hK : 0 < K)
    (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2) (hscale : 1 ≤ ρ * (K : ℝ))
    (hD : angularTruncationFactor K ρ ≤ 1)
    (ht : ρ * (K : ℝ) / (r : ℝ) ≤ 1 / 2)
    (hA : 6 * L * angularTruncationFactor K ρ ≤ 1)
    (hAdelta : 6 * L * angularTruncationFactor K ρ ≤ delta / 32) :
    delta * (ρ * (K : ℝ) / (r : ℝ)) ^ 4 / 64 ≤ eps := by
  let t : ℝ := ρ * (K : ℝ) / (r : ℝ)
  have heps : 0 ≤ eps := paddedCertificate_eps_nonneg q hqhom eps h g certificate
  have hreal (z : V → Bool) (u : ℝ) :
      ‖angularVector h (fun i ↦ a i z) (u : ℂ)‖ ≤ Real.sqrt eps + u ^ 2 :=
    paddedCertificate_real_envelope q hqhom eps h g certificate (fun i ↦ a i z)
      (haunit z) (hqupper _ (haunit z)) u
  have herror (z : V → Bool) :
      |eps + Real.sin t ^ 4 * MvPolynomial.eval (fun i ↦ a i z) q -
          ‖angularTaylorVector h (t : ℂ) K (fun i ↦ a i z)‖ ^ 2| ≤
        6 * angularTruncationFactor K ρ * (eps + t ^ 4) := by
    have herr := angularTaylorVector_norm_square_error h (fun i ↦ a i z) hr hK
      hdegree (hreal z) hρ0 hρhalf hscale hD
    rw [Real.sq_sqrt heps] at herr
    change |‖angularVector h (fun i ↦ a i z) (t : ℂ)‖ ^ 2 -
      ‖angularTaylorVector h (t : ℂ) K (fun i ↦ a i z)‖ ^ 2| ≤
      6 * angularTruncationFactor K ρ * (eps + t ^ 4) at herr
    rw [paddedCertificate_angular_norm_sq q hqhom eps h g certificate
      (fun i ↦ a i z) (haunit z)] at herr
    exact herr
  exact functional_transfer_lower_bound E hbound
    (fun z ↦ MvPolynomial.eval (fun i ↦ a i z) q)
    (hasBooleanDegree_eval_of_totalDegree_le q a hadegree (2 * K) hqdegree) hqeval
    (fun z ↦ angularTaylorVector h (t : ℂ) K (fun i ↦ a i z))
    (angularTaylorVector_boolean_re_degree h (t : ℂ) K a hadegree)
    (angularTaylorVector_boolean_im_degree h (t : ℂ) K a hadegree)
    herror heps (by positivity) ht hA hAdelta

omit [DecidableEq V] in
theorem angularTruncationFactor_le_one_of_amplification
    (hρ0 : 0 ≤ ρ) (hA : 6 * cubeSize V * angularTruncationFactor K ρ ≤ 1) :
    angularTruncationFactor K ρ ≤ 1 := by
  have hcube : 1 ≤ cubeSize V := by
    unfold cubeSize
    exact one_le_pow₀ (by norm_num)
  have hD0 : 0 ≤ angularTruncationFactor K ρ := by
    unfold angularTruncationFactor
    positivity
  have hfactor : angularTruncationFactor K ρ ≤
      (6 * cubeSize V) * angularTruncationFactor K ρ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 6 * cubeSize V by linarith) hD0
  exact hfactor.trans hA

/-- A convenient high-order form. The amplified error bound itself supplies
`D ≤ 1`, and `K ≤ r` supplies the required small angular parameter. -/
theorem paddedCertificate_high_order_shift
    (E : TruncatedBooleanPseudoexpectation V K) {delta ρ : ℝ}
    (hbound : TruncatedEvaluationBound E (cubeSize V))
    (q : MvPolynomial σ ℝ) (hqhom : q.IsHomogeneous 4)
    (hqdegree : q.totalDegree ≤ 2 * K)
    (hqupper : ∀ y : σ → ℝ, (∑ i, y i ^ 2) = 1 → MvPolynomial.eval y q ≤ 1)
    (a : σ → (V → Bool) → ℝ) (hadegree : ∀ i, HasBooleanDegree 1 (a i))
    (haunit : ∀ z, (∑ i, a i z ^ 2) = 1)
    (hqeval : E.functional ⟨fun z ↦ MvPolynomial.eval (fun i ↦ a i z) q,
      hasBooleanDegree_eval_of_totalDegree_le q a hadegree (2 * K) hqdegree⟩ = -delta)
    (eps : ℝ) (h : J → MvPolynomial (Option σ) ℝ)
    (g : MvPolynomial (Option σ) ℝ)
    (certificate : paddedPolynomial q + MvPolynomial.C eps =
      (∑ j : J, h j ^ 2) + (1 - genericRadius) * g)
    (hdegree : ∀ j, (h j).totalDegree ≤ r) (hK : 0 < K) (hrK : K ≤ r)
    (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2) (hscale : 1 ≤ ρ * (K : ℝ))
    (hA : 6 * cubeSize V * angularTruncationFactor K ρ ≤ 1)
    (hAdelta : 6 * cubeSize V * angularTruncationFactor K ρ ≤ delta / 32) :
    delta * (ρ * (K : ℝ) / (r : ℝ)) ^ 4 / 64 ≤ eps := by
  have hr : 0 < r := lt_of_lt_of_le hK hrK
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hKrR : (K : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrK
  have ht : ρ * (K : ℝ) / (r : ℝ) ≤ 1 / 2 := by
    apply le_trans _ hρhalf
    exact (div_le_iff₀ hrR).2 (mul_le_mul_of_nonneg_left hKrR hρ0)
  exact paddedCertificate_uniform_transfer E hbound q hqhom hqdegree hqupper
    a hadegree haunit hqeval eps h g certificate hdegree hr hK hρ0 hρhalf hscale
    (angularTruncationFactor_le_one_of_amplification hρ0 hA) ht hA hAdelta

def equatorialPoint (y : σ → ℝ) : Option σ → ℝ
  | none => 0
  | some i => y i

theorem equatorialPoint_unit (y : σ → ℝ) (hy : ∑ i, y i ^ 2 = 1) :
    (∑ i : Option σ, equatorialPoint y i ^ 2) = 1 := by
  simpa [equatorialPoint, Fintype.sum_option] using hy

omit [Fintype σ] in
theorem equatorialPoint_coordinate_degree
    (a : σ → (V → Bool) → ℝ) (ha : ∀ i, HasBooleanDegree 1 (a i))
    (i : Option σ) :
    HasBooleanDegree 1 (fun z ↦ equatorialPoint (fun i ↦ a i z) i) := by
  cases i with
  | none => exact hasBooleanDegree_const 1 0
  | some i => exact ha i

/-- Below the Boolean positivity level, the equator alone obstructs a
certificate; no analytic approximation is needed. -/
theorem paddedCertificate_low_order_shift
    (E : TruncatedBooleanPseudoexpectation V K) {delta : ℝ}
    (q : MvPolynomial σ ℝ) (hqdegree : q.totalDegree ≤ 2 * K)
    (a : σ → (V → Bool) → ℝ) (hadegree : ∀ i, HasBooleanDegree 1 (a i))
    (haunit : ∀ z, (∑ i, a i z ^ 2) = 1)
    (hqeval : E.functional ⟨fun z ↦ MvPolynomial.eval (fun i ↦ a i z) q,
      hasBooleanDegree_eval_of_totalDegree_le q a hadegree (2 * K) hqdegree⟩ = -delta)
    (eps : ℝ) (h : J → MvPolynomial (Option σ) ℝ)
    (g : MvPolynomial (Option σ) ℝ)
    (certificate : paddedPolynomial q + MvPolynomial.C eps =
      (∑ j : J, h j ^ 2) + (1 - genericRadius) * g)
    (hdegree : ∀ j, (h j).totalDegree ≤ r) (hrK : r ≤ K) :
    delta ≤ eps := by
  let f : J → (V → Bool) → ℝ := fun j z ↦
    MvPolynomial.eval (equatorialPoint (fun i ↦ a i z)) (h j)
  have hf (j : J) : HasBooleanDegree K (f j) :=
    hasBooleanDegree_eval_of_totalDegree_le (h j)
      (fun i z ↦ equatorialPoint (fun i ↦ a i z) i)
      (equatorialPoint_coordinate_degree a hadegree) K ((hdegree j).trans hrK)
  let oneE : booleanDegreeSpace (I := V) (2 * K) :=
    ⟨fun _ ↦ 1, hasBooleanDegree_one (2 * K)⟩
  let qE : booleanDegreeSpace (I := V) (2 * K) :=
    ⟨fun z ↦ MvPolynomial.eval (fun i ↦ a i z) q,
      hasBooleanDegree_eval_of_totalDegree_le q a hadegree (2 * K) hqdegree⟩
  let squareE : J → booleanDegreeSpace (I := V) (2 * K) := fun j ↦
    ⟨fun z ↦ f j z ^ 2, hasBooleanDegree_square K (f j) (hf j)⟩
  have hid : (∑ j : J, squareE j) = qE + eps • oneE := by
    apply Subtype.ext
    funext z
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_add,
      Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, squareE, qE, oneE]
    have he := congrArg (MvPolynomial.eval (equatorialPoint (fun i ↦ a i z))) certificate
    have hrad : MvPolynomial.eval (equatorialPoint (fun i ↦ a i z)) genericRadius = 1 := by
      rw [genericRadius_eval, equatorialPoint_unit _ (haunit z)]
    simpa only [map_add, paddedPolynomial, MvPolynomial.eval_rename, Function.comp_def,
      equatorialPoint,
      MvPolynomial.eval_C, map_sum, map_pow, map_mul, map_sub, map_one, hrad,
      sub_self, zero_mul, add_zero, mul_one, f] using he.symm
  have hpos : 0 ≤ E.functional (∑ j : J, squareE j) := by
    rw [map_sum]
    exact Finset.sum_nonneg (fun j _ ↦ E.square_nonneg (f j) (hf j))
  have hone : E.functional oneE = 1 := E.normalized
  have hqE : E.functional qE = -delta := hqeval
  rw [hid, map_add, map_smul, hone, hqE] at hpos
  simp only [smul_eq_mul, mul_one] at hpos
  linarith

end ActualCertificate

namespace HardQuarticData

variable {N K : ℕ} (D : HardQuarticData N K)

theorem polynomial_degree_truncated : D.polynomial.totalDegree ≤ 2 * K := by
  have hK := D.level_ge_two
  exact D.polynomial_totalDegree_le.trans (by omega)

theorem polynomial_eval_negative :
    D.pseudoexpectation.functional
      ⟨fun z ↦ MvPolynomial.eval (D.point z) D.polynomial,
        hasBooleanDegree_eval_of_totalDegree_le D.polynomial
          (fun i z ↦ D.point z i) D.point_coordinate_degree (2 * K)
          D.polynomial_degree_truncated⟩ = -(1 / (8712 * (N : ℝ))) := by
  have heq : (fun z ↦ MvPolynomial.eval (D.point z) D.polynomial) = D.booleanFunction :=
    D.booleanFunction_eq_eval.symm
  simpa only [heq, booleanElement] using D.negative_value

/-- The unconditional hard input obstructs every certificate at or below its
Boolean level, with the original feasible value and no normalization loss. -/
theorem padded_certificate_low_order {r : ℕ} {lam : ℝ}
    (hcert : FiniteSphereCertificate r (paddedPolynomial D.polynomial) lam)
    (hrK : r ≤ K) : lam ≤ -(1 / (8712 * (N : ℝ))) := by
  rcases hcert with ⟨m, h, g, hdegree, hgdegree, hid⟩
  have hcertificate : paddedPolynomial D.polynomial + MvPolynomial.C (-lam) =
      (∑ j : Fin m, h j ^ 2) + (1 - genericRadius) * g := by
    simpa only [MvPolynomial.C_neg, sub_eq_add_neg] using hid
  have hshift := paddedCertificate_low_order_shift D.pseudoexpectation D.polynomial
    D.polynomial_degree_truncated (fun i z ↦ D.point z i) D.point_coordinate_degree
    D.point_unit D.polynomial_eval_negative (-lam) h g hcertificate hdegree hrK
  linarith

/-- The high-order obstruction for the same hard input. The only numerical
premises are the amplified truncation bounds furnished by uniform constants. -/
theorem padded_certificate_high_order {r : ℕ} {lam ρ : ℝ}
    (hcert : FiniteSphereCertificate r (paddedPolynomial D.polynomial) lam)
    (hrK : K ≤ r) (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hscale : 1 ≤ ρ * (K : ℝ))
    (hA : 6 * (2 : ℝ) ^ N * angularTruncationFactor K ρ ≤ 1)
    (hAdelta : 6 * (2 : ℝ) ^ N * angularTruncationFactor K ρ ≤
      (1 / (8712 * (N : ℝ))) / 32) :
    lam ≤ -((1 / (8712 * (N : ℝ))) * (ρ * (K : ℝ) / (r : ℝ)) ^ 4 / 64) := by
  rcases hcert with ⟨m, h, g, hdegree, hgdegree, hid⟩
  have hcertificate : paddedPolynomial D.polynomial + MvPolynomial.C (-lam) =
      (∑ j : Fin m, h j ^ 2) + (1 - genericRadius) * g := by
    simpa only [MvPolynomial.C_neg, sub_eq_add_neg] using hid
  have hK : 0 < K := lt_of_lt_of_le (by norm_num : 0 < 2) D.level_ge_two
  have hAcube : 6 * cubeSize (Fin N) * angularTruncationFactor K ρ ≤ 1 := by
    simpa only [cubeSize, Fintype.card_fin] using hA
  have hAdeltacube : 6 * cubeSize (Fin N) * angularTruncationFactor K ρ ≤
      (1 / (8712 * (N : ℝ))) / 32 := by
    simpa only [cubeSize, Fintype.card_fin] using hAdelta
  have hshift := paddedCertificate_high_order_shift D.pseudoexpectation
    (truncatedEvaluationBound_of_positive D.pseudoexpectation) D.polynomial
    D.polynomial_isHomogeneous D.polynomial_degree_truncated
    (fun y hy ↦ D.polynomial_le_one_on_ball y hy.le)
    (fun i z ↦ D.point z i) D.point_coordinate_degree D.point_unit
    D.polynomial_eval_negative (-lam) h g hcertificate hdegree hK hrK
    hρ0 hρhalf hscale hAcube hAdeltacube
  linarith

end HardQuarticData

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
