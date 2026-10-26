import OptimalConvergenceRates.SphereDimensionBounds.SphereMatrixSmoothing
import OptimalConvergenceRates.SphereDimensionBounds.HomogeneousSOSFromSphere

/-! Odd sphere means, their actual radial polynomial homogenization,
and the eigenvalue-corrected matrix smoothing certificate. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.HomogeneousMatrixSmoothing

open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace
open MeasureTheory Matrix MvPolynomial SphereMeasure PolynomialSmoothingKernel
  SmoothingKernelCoordinates PolynomialKernelFeatures SphereMatrixSmoothing
open HomogeneousSOSFromSphere

abbrev P (n : ℕ) := OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n

def antipode {n : ℕ} : Sphere n→Sphere n :=
  sphereMap (LinearIsometryEquiv.neg ℝ)

abbrev mean {n s d e : ℕ} (F : Sphere n → Matrix (Fin d) (Fin e) ℝ) :
    Matrix (Fin d) (Fin e) (P n) :=
  MatrixKernelSmoothing.meanMatrix (surface n) (coefficient (s:=s)) (featurePolynomial (s:=s)) F

theorem fieldProductsIntegrable {n s d e : ℕ} (hn : 0 < n)
    (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (hFmeas : ∀ u v, Measurable (fun y => F y u v)) {B : ℝ} (hFnorm : ∀ y, ‖F y‖ ≤ B)
    (α β : Feature n s) (u : Fin d) (v : Fin e) :
    Integrable (fun y : Sphere n => coefficient y α*coefficient y β*F y u v) (surface n) := by
  apply weighted_coefficient_products_integrable hn α β _ (hFmeas u v)
  exact ⟨B,fun y => (matrix_entry_le_operatorNorm (F y) u v).trans (hFnorm y)⟩

theorem mean_eval_kernel {n s d e : ℕ} (hn : 0 < n)
    (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (hFmeas : ∀ u v, Measurable (fun y => F y u v)) {B : ℝ} (hFnorm : ∀ y, ‖F y‖ ≤ B)
    (x : E n) (u : Fin d) (v : Fin e) :
    eval (fun i => x i) (mean (s:=s) F u v)=
      ∫y : Sphere n, kernel (2*s) x y*F y u v ∂surface n := by
  rw [mean,MatrixKernelSmoothing.meanMatrix_eval _ _ _ _ (fieldProductsIntegrable hn F hFmeas hFnorm)]
  simp_rw [normalized_root_square]

theorem kernel_neg_antipode {n : ℕ} (k : ℕ) (x : E n) (y : Sphere n) :
    kernel k (-x) (antipode y)=kernel k x y := by
  simp [kernel_eval,antipode,sphereMap,QuarticConvergence.euclideanUnitSphereMap,
    LinearIsometryEquiv.coe_neg]

theorem mean_odd {n s d e : ℕ} (hn : 0 < n)
    (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (hFmeas : ∀ u v, Measurable (fun y => F y u v)) {B : ℝ} (hFnorm : ∀ y, ‖F y‖ ≤ B)
    (hodd : ∀ y, F (antipode y) = -F y) (x : E n) (u : Fin d) (v : Fin e) :
    eval (fun i => (-x) i) (mean (s:=s) F u v)= -eval (fun i => x i) (mean (s:=s) F u v) := by
  rw [mean_eval_kernel hn F hFmeas hFnorm,mean_eval_kernel hn F hFmeas hFnorm]
  let f : Sphere n→ℝ := fun y => kernel (2*s) (-x) y*F y u v
  have hm := (sphereMap_measurePreserving (LinearIsometryEquiv.neg ℝ : E n≃ₗᵢ[ℝ] E n)).integral_comp
    (sphereHomeomorph (LinearIsometryEquiv.neg ℝ)).measurableEmbedding f
  change (∫y : Sphere n, f y ∂surface n)=_
  rw [←hm,←integral_neg]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  change kernel (2*s) (-x) (antipode y)*F (antipode y) u v= -(_)
  rw [kernel_neg_antipode,hodd]
  simp

theorem radialHomogenize_odd_eval {n s : ℕ} (hs : 1 ≤ s) (p : P n) (hp : p.totalDegree ≤ 2 * s)
    (hodd : ∀ x : Fin n→ℝ, eval (fun i => -x i) p= -eval x p)
    (x : Fin n→ℝ) (hx : x∈OptimalConvergenceRates.SphereDimensionBounds.Foundation.unitSphere n) :
    eval x (radialHomogenize p (2*s-1))=eval x p := by
  have hp1 := radialHomogenize_pair_eval (by omega : 1≤2*s) p hp x hx
  have hp2 := radialHomogenize_pair_eval (by omega : 1≤2*s) p hp
    (fun i => -x i) (neg_point_sphere hx)
  have hscale (r : ℕ) : eval (fun i => -x i) (radialHomogenize p r)=
      (-1:ℝ)^r*eval x (radialHomogenize p r) := by
    simpa only [neg_one_mul] using OptimalConvergenceRates.SphereDimensionBounds.Foundation.homogeneous_eval_scale
      (radialHomogenize p r) r (radialHomogenize_homogeneous p r) (-1) x
  have heven : (-1:ℝ)^(2*s)=1 := by rw [pow_mul];norm_num
  have hoddExponent : Odd (2*s-1) := by
    refine ⟨s-1,?_⟩
    omega
  have hoddPower : (-1:ℝ)^(2*s-1)= -1 := hoddExponent.neg_one_pow
  rw [hscale,hscale,heven,hoddPower,hodd x] at hp2
  simp only [one_mul,neg_one_mul] at hp2
  linarith

def liftedMean {n s d e : ℕ} (F : Sphere n → Matrix (Fin d) (Fin e) ℝ) :
    Matrix (Fin d) (Fin e) (P n) := fun u v => radialHomogenize (mean (s:=s) F u v) (2*s-1)

def correctedMean {n s d e : ℕ} (F : Sphere n → Matrix (Fin d) (Fin e) ℝ) :
    Matrix (Fin d) (Fin e) (P n) := fun u v => C ((lambda1 n (2*s))⁻¹)*liftedMean (s:=s) F u v

theorem liftedMean_homogeneous {n s d e : ℕ} (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (u : Fin d) (v : Fin e) : (liftedMean (s:=s) F u v).IsHomogeneous (2*s-1) :=
  radialHomogenize_homogeneous _ _

theorem correctedMean_homogeneous {n s d e : ℕ} (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (u : Fin d) (v : Fin e) : (correctedMean (s:=s) F u v).IsHomogeneous (2*s-1) :=
  (liftedMean_homogeneous F u v).C_mul _

theorem liftedMean_eval_sphere {n s d e : ℕ} (hn : 0 < n) (hs : 1 ≤ s)
    (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (hFmeas : ∀ u v, Measurable (fun y => F y u v)) {B : ℝ} (hFnorm : ∀ y, ‖F y‖ ≤ B)
    (hodd : ∀ y, F (antipode y) = -F y) (x : Fin n → ℝ) (hx : x ∈ OptimalConvergenceRates.SphereDimensionBounds.Foundation.unitSphere n)
    (u : Fin d) (v : Fin e) :
    eval x (liftedMean (s:=s) F u v)=eval x (mean (s:=s) F u v) := by
  apply radialHomogenize_odd_eval hs _ (MatrixKernelSmoothing.meanMatrix_degree _ _ _ featurePolynomial_degree F u v) _ x hx
  intro z
  exact mean_odd hn F hFmeas hFnorm hodd ((WithLp.equiv 2 ((Fin n)→ℝ)).symm z) u v

theorem correctedMean_eval_sphere {n s d e : ℕ} (hn : 0 < n) (hs : 1 ≤ s)
    (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (hFmeas : ∀ u v, Measurable (fun y => F y u v)) {B : ℝ} (hFnorm : ∀ y, ‖F y‖ ≤ B)
    (hodd : ∀ y, F (antipode y) = -F y) (x : Fin n → ℝ) (hx : x ∈ OptimalConvergenceRates.SphereDimensionBounds.Foundation.unitSphere n)
    (u : Fin d) (v : Fin e) :
    eval x (correctedMean (s:=s) F u v)=eval x (mean (s:=s) F u v)/lambda1 n (2*s) := by
  rw [correctedMean,eval_mul,eval_C,liftedMean_eval_sphere hn hs F hFmeas hFnorm hodd x hx]
  ring

end OptimalConvergenceRates.SphereDimensionBounds.HomogeneousMatrixSmoothing
