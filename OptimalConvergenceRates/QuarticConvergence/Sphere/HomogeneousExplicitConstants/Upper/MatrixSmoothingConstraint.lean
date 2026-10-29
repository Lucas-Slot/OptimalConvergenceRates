import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.HomogeneousMatrixBound
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CubicBlockInverse

/-! Exact linear constraints through the actual polynomial sphere mean
and its eigenvalue-corrected homogeneous lift. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace MatrixSmoothingConstraint

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open MeasureTheory Matrix MvPolynomial SphereMeasure SphereMoments
  PolynomialSmoothingKernel SmoothingKernelCoordinates PolynomialKernelFeatures
  HomogeneousMatrixSmoothing HomogeneousMatrixBound
open WeightedQuadraticExistence

abbrev P (n : ℕ) := Foundation.Polynomial n
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def entryLinear {d : ℕ} (u v : Fin d) : Mat d→ₗ[ℝ] ℝ where
  toFun A := A u v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def familyPolynomial {n d : ℕ} (T : E n →ₗ[ℝ] Mat d) : Matrix (Fin d) (Fin d) (P n) :=
  fun u v ↦ ∑i, C (T (SphereMoments.axis i) u v)*X i

theorem familyPolynomial_homogeneous {n d : ℕ} (T : E n →ₗ[ℝ] Mat d) (u v : Fin d) :
    (familyPolynomial T u v).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_X ℝ i).C_mul _

theorem familyPolynomial_eval {n d : ℕ} (T : E n →ₗ[ℝ] Mat d)
    (x : E n) (u v : Fin d) : eval (fun i ↦ x i) (familyPolynomial T u v)=T x u v := by
  have hx := OrderedCubicExpansion.sum_coordinatePiece x
  have ht := congrArg (fun z : E n ↦ T z u v) hx
  simp only [OrderedCubicExpansion.coordinatePiece,map_sum,map_smul,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at ht
  simp only [familyPolynomial,eval_sum,eval_mul,eval_C,eval_X]
  calc
    (∑i, T (SphereMoments.axis i) u v*x i)=∑i, x i*T (OrderedCubicExpansion.coordinateAxis i) u v
      := by
      apply Finset.sum_congr rfl
      intro i _
      have he : OrderedCubicExpansion.coordinateAxis i=SphereMoments.axis i := by
        ext j
        simp [OrderedCubicExpansion.coordinateAxis,SphereMoments.axis,EuclideanSpace.single,
          WithLp.equiv_symm_apply, PiLp.toLp_apply]
      rw [he]
      ring
    _=T x u v := ht

theorem kernel_linear_family {n d : ℕ} (hn : 2 ≤ n) (k : ℕ) (T : E n →ₗ[ℝ] Mat d)
    (x : Sphere n) (u v : Fin d) :
    (∫y : Sphere n, kernel k x.1 y*T y.1 u v ∂surface n)=lambda1 n k*T x.1 u v := by
  let f : E n→L[ℝ] ℝ := ((entryLinear u v).comp T).toContinuousLinearMap
  let z : E n := (InnerProductSpace.toDual ℝ (E n)).symm f
  have hz (y : E n) : ⟪z,y⟫_ℝ=T y u v := InnerProductSpace.toDual_symm_apply
  have h := kernel_linear hn k x z
  have hx : ⟪x.1,z⟫_ℝ=T x.1 u v := (real_inner_comm x.1 z).symm.trans (hz x.1)
  simpa only [hz,hx] using h

set_option backward.isDefEq.respectTransparency.types false in
theorem mean_linear_functional {n s d : ℕ} (hn : 0 < n)
    (F : Sphere n → Mat d) (hFmeas : ∀ u v, Measurable (fun y ↦ F y u v))
    {B : ℝ} (hFnorm : ∀ y, ‖F y‖ ≤ B) (f : Mat d →L[ℝ] ℝ) (x : E n) :
    f (fun u v ↦ eval (fun i ↦ x i) (mean (s:=s) F u v))=
      ∫y : Sphere n, kernel (2*s) x y*f (F y) ∂surface n := by
  let A := functionalMatrix f
  have hrepr (M : Mat d) : f M=∑u,∑v, A u v*M u v := by
    exact (functionalMatrix_represents f M).trans (tracePair_entries _ _)
  have hint (u v : Fin d) : Integrable (fun y : Sphere n ↦ kernel (2*s) x y*F y u v) (surface n)
    := by
    have hh := MatrixKernelSmoothing.root_square_mul_integrable (surface n) (coefficient (s:=s))
      (featurePolynomial (s:=s))
      (fun y ↦ F y u v) (fun α β ↦ fieldProductsIntegrable hn F hFmeas hFnorm α β u v) (fun i ↦ x i)
    simpa only [normalized_root_square] using hh
  have hterm (u v : Fin d) : Integrable
      (fun y : Sphere n ↦ A u v*(kernel (2*s) x y*F y u v)) (surface n) :=
    (hint u v).const_mul _
  have hinner (u : Fin d) : Integrable
      (fun y : Sphere n ↦ ∑v, A u v*(kernel (2*s) x y*F y u v)) (surface n) :=
    integrable_finsetSum _ fun v _ ↦ hterm u v
  rw [hrepr]
  simp_rw [mean_eval_kernel hn F hFmeas hFnorm]
  have heq : (fun y : Sphere n ↦ kernel (2*s) x y*f (F y))=
      (fun y : Sphere n ↦ ∑u,∑v, A u v*(kernel (2*s) x y*F y u v)) := by
    funext y
    rw [hrepr]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [heq,integral_finsetSum _ (fun u _ ↦ hinner u)]
  simp_rw [integral_finsetSum _ (fun v _ ↦ hterm _ v),integral_const_mul]

theorem weightedMean_sphere {n s d : ℕ} (hn : 2 ≤ n) (L : Mat d)
    (T : E n →ₗ[ℝ] Mat d) (F : Sphere n → Mat d)
    (hFmeas : ∀ u v, Measurable (fun y ↦ F y u v))
    {B : ℝ} (hFnorm : ∀ y, ‖F y‖ ≤ B) (hconstraint : ∀ y, weightedMap L (F y) = T y.1)
    (x : Sphere n) :
    weightedMap L (fun u v ↦ eval (fun i ↦ x.1 i) (mean (s:=s) F u v))=
      lambda1 n (2*s) • T x.1 := by
  apply Matrix.ext
  intro u v
  let f : Mat d→L[ℝ] ℝ := ((entryLinear u v).comp (weightedMap L)).toContinuousLinearMap
  have h := mean_linear_functional (s:=s) (by omega : 0<n) F hFmeas hFnorm f x.1
  change weightedMap L (fun i j ↦ eval (fun k ↦ x.1 k) (mean (s:=s) F i j)) u v=_ at h
  rw [h]
  have heq : (fun y : Sphere n ↦ kernel (2*s) x.1 y*f (F y))=
      (fun y : Sphere n ↦ kernel (2*s) x.1 y*T y.1 u v) := by
    funext y
    change kernel (2*s) x.1 y*weightedMap L (F y) u v=_
    rw [hconstraint]
  rw [heq,kernel_linear_family hn]
  rfl

def polynomialWeightedMap {n d : ℕ} (L : Mat d) (M : Matrix (Fin d) (Fin d) (P n)) :
    Matrix (Fin d) (Fin d) (P n) :=
  (C (1/2:ℝ):P n) • (FiniteMatrixVariance.constantMatrix L*M+
    (FiniteMatrixVariance.constantMatrix L*M).transpose)

set_option backward.isDefEq.respectTransparency.types false in
theorem polynomialWeightedMap_eval {n d : ℕ} (L : Mat d)
    (M : Matrix (Fin d) (Fin d) (P n)) (x : Fin n → ℝ) (u v : Fin d) :
    eval x (polynomialWeightedMap L M u v)=weightedMap L (fun i j ↦ eval x (M i j)) u v := by
  simp [polynomialWeightedMap,weightedMap,matrixSym,FiniteMatrixVariance.constantMatrix,
    Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,Matrix.transpose_apply]
  ring

theorem polynomialWeightedMap_homogeneous {n d r : ℕ} (L : Mat d)
    (M : Matrix (Fin d) (Fin d) (P n)) (hM : ∀ u v, (M u v).IsHomogeneous r) (u v : Fin d) :
    (polynomialWeightedMap L M u v).IsHomogeneous r := by
  change (C (1/2:ℝ)*((∑k, C (L u k)*M k v)+(∑k, C (L v k)*M k u))).IsHomogeneous r
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.add
  · apply IsHomogeneous.sum
    intro k _
    exact (hM k v).C_mul _
  · apply IsHomogeneous.sum
    intro k _
    exact (hM k u).C_mul _

set_option backward.isDefEq.respectTransparency.types false in
theorem corrected_constraint_sphere {n s d : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s) (L : Mat d)
    (T : E n →ₗ[ℝ] Mat d) (F : Sphere n → Mat d)
    (hFmeas : ∀ u v, Measurable (fun y ↦ F y u v))
    {B : ℝ} (hFnorm : ∀ y, ‖F y‖ ≤ B) (hconstraint : ∀ y, weightedMap L (F y) = T y.1)
    (hodd : ∀ y, F (antipode y) = -F y) (x : Sphere n) :
    weightedMap L (fun u v ↦ eval (fun i ↦ x.1 i) (correctedMean (s:=s) F u v))=T x.1 := by
  have hspos : 1≤s := by omega
  have hl : lambda1 n (2*s)≠0 := (lambda1_pos hn (by omega : 0<2*s)).ne'
  have hCorr : (fun u v ↦ eval (fun i ↦ x.1 i) (correctedMean (s:=s) F u v))=
      (lambda1 n (2*s))⁻¹ • (fun u v ↦ eval (fun i ↦ x.1 i) (mean (s:=s) F u v)) := by
    apply Matrix.ext
    intro u v
    rw [correctedMean_eval_sphere (by omega : 0<n) hspos F hFmeas hFnorm hodd _
      (SphereMeasure.coordinates_unitSphere x)]
    simp [Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  calc
    _ = (lambda1 n (2*s))⁻¹ • weightedMap L
        (fun u v ↦ eval (fun i ↦ x.1 i) (mean (s:=s) F u v)) :=
      (congrArg (weightedMap L) hCorr).trans ((weightedMap L).map_smul _ _)
    _ = (lambda1 n (2*s))⁻¹ • (lambda1 n (2*s) • T x.1) :=
      congrArg (fun M : Mat d ↦ (lambda1 n (2*s))⁻¹ • M)
        (weightedMean_sphere hn L T F hFmeas hFnorm hconstraint x)
    _ = _ := by rw [smul_smul,inv_mul_cancel₀ hl,one_smul]

/-- Exact ambient polynomial constraint for the actual corrected sphere
mean. The equality has the original Euclidean radius power s-1. -/
theorem corrected_constraint_polynomial {n s d : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s) (L : Mat d)
    (T : E n →ₗ[ℝ] Mat d) (F : Sphere n → Mat d)
    (hFmeas : ∀ u v, Measurable (fun y ↦ F y u v))
    {B : ℝ} (hFnorm : ∀ y, ‖F y‖ ≤ B) (hconstraint : ∀ y, weightedMap L (F y) = T y.1)
    (hodd : ∀ y, F (antipode y) = -F y) :
    polynomialWeightedMap L (correctedMean (s:=s) F)=
      (Foundation.radiusPolynomial n)^(s-1) • familyPolynomial T := by
  have hspos : 1≤s := by omega
  apply Matrix.ext
  intro u v
  apply HomogeneousSOSFromSphere.homogeneous_eq_of_sphere_eq (by omega : 0<2*s-1) _ _
    (polynomialWeightedMap_homogeneous L _ (correctedMean_homogeneous F) u v)
  · change ((Foundation.radiusPolynomial n)^(s-1)*familyPolynomial T u v).IsHomogeneous (2*s-1)
    have hd : 2*(s-1)+1=2*s-1 := by omega
    simpa only [hd] using ((HomogeneousSphereBounds.radius_homogeneous n).pow (s-1)).mul
      (familyPolynomial_homogeneous T u v)
  · intro x hx
    let z : E n := (WithLp.equiv 2 ((Fin n)→ℝ)).symm x
    have hsq : ‖z‖^2=1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simpa only [z,WithLp.equiv_symm_apply, PiLp.toLp_apply,Real.norm_eq_abs,sq_abs,
      Foundation.unitSphere,Set.mem_ofPred_eq] using hx
    have hz : ‖z‖=1 := by nlinarith [norm_nonneg z]
    let q : Sphere n := ⟨z,by simpa only [Metric.mem_sphere,dist_zero_right] using hz⟩
    have hw := corrected_constraint_sphere (s:=s) hn hs L T F hFmeas hFnorm hconstraint hodd q
    have hR : eval x (Foundation.radiusPolynomial n)=1 := by simpa [Foundation.unitSphere] using hx
    rw [polynomialWeightedMap_eval]
    simp only [Matrix.smul_apply,smul_eq_mul,eval_mul,eval_pow,hR,one_pow,one_mul]
    have hwentry : weightedMap L (fun i j ↦ eval x (correctedMean (s:=s) F i j)) u v=T z u v := by
      simpa only [q,z,WithLp.equiv_symm_apply, PiLp.toLp_apply] using congrArg (fun A : Mat d ↦ A
        u v) hw
    rw [hwentry]
    simpa only [z,WithLp.equiv_symm_apply, PiLp.toLp_apply] using (familyPolynomial_eval T z u
      v).symm

theorem quadraticForm_eq_dot {n d : ℕ} (M : Matrix (Fin d) (Fin d) (P n)) (v : Fin d → P n) :
    FiniteMatrixVariance.quadraticForm M v=dotProduct v (M *ᵥ v) := by
  simp only [FiniteMatrixVariance.quadraticForm,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weightedPolynomial_pairing {n d : ℕ} (L : Mat d) (hL : L.transpose = L)
    (M : Matrix (Fin d) (Fin d) (P n)) (v : Fin d → P n) :
    (∑i, (∑j, C (L i j)*v j)*(∑j, M i j*v j))=
      FiniteMatrixVariance.quadraticForm (polynomialWeightedMap L M) v := by
  let A : Matrix (Fin d) (Fin d) (P n) := FiniteMatrixVariance.constantMatrix L
  have hAt : A.transpose=A := by
    apply Matrix.ext
    intro i j
    exact congrArg C (congrArg (fun N : Mat d ↦ N i j) hL)
  have hT (N : Matrix (Fin d) (Fin d) (P n)) :
      dotProduct v (N.transpose *ᵥ v)=dotProduct v (N *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    exact dotProduct_comm _ _
  have hhalf : (C (1/2:ℝ):P n)*2=1 := by
    change C (1/2:ℝ)*C (2:ℝ)=1
    rw [←map_mul]
    norm_num
  change dotProduct (A *ᵥ v) (M *ᵥ v)=_
  symm
  rw [quadraticForm_eq_dot,polynomialWeightedMap,Matrix.smul_mulVec,dotProduct_smul,
    Matrix.add_mulVec,dotProduct_add,hT]
  change C (1/2:ℝ)*(_+_)=_
  calc
    C (1/2:ℝ)*(dotProduct v ((A*M) *ᵥ v)+dotProduct v ((A*M) *ᵥ v))=
      ((C (1/2:ℝ):P n)*2)*dotProduct v ((A*M) *ᵥ v) := by ring
    _ = dotProduct v ((A*M) *ᵥ v) := by rw [hhalf,one_mul]
    _ = _ := by rw [←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose,hAt]

theorem pairing_of_polynomial_constraint {n s d : ℕ} (L : Mat d) (hL : L.transpose = L)
    (M T : Matrix (Fin d) (Fin d) (P n))
    (hconstraint : polynomialWeightedMap L M = (Foundation.radiusPolynomial n) ^ (s - 1) • T)
    (v : Fin d → P n) :
    (∑i, (∑j, C (L i j)*v j)*(∑j, M i j*v j))=
      (Foundation.radiusPolynomial n)^(s-1)*FiniteMatrixVariance.quadraticForm T v := by
  rw [weightedPolynomial_pairing L hL M v,hconstraint]
  simp only [FiniteMatrixVariance.quadraticForm,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Literal polynomial weighted pairing supplied by the actual corrected
mean, with no pairing identity supplied as a hypothesis. -/
theorem corrected_constraint_pairing {n s d : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (L : Mat d) (hL : L.transpose = L) (T : E n →ₗ[ℝ] Mat d) (F : Sphere n → Mat d)
    (hFmeas : ∀ u v, Measurable (fun y ↦ F y u v))
    {B : ℝ} (hFnorm : ∀ y, ‖F y‖ ≤ B) (hconstraint : ∀ y, weightedMap L (F y) = T y.1)
    (hodd : ∀ y, F (antipode y) = -F y) (v : Fin d → P n) :
    (∑i, (∑j, C (L i j)*v j)*(∑j, correctedMean (s:=s) F i j*v j))=
      (Foundation.radiusPolynomial n)^(s-1)*FiniteMatrixVariance.quadraticForm (familyPolynomial
        T) v :=
  pairing_of_polynomial_constraint L hL _ _
    (corrected_constraint_polynomial hn hs L T F hFmeas hFnorm hconstraint hodd) v

end MatrixSmoothingConstraint
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
