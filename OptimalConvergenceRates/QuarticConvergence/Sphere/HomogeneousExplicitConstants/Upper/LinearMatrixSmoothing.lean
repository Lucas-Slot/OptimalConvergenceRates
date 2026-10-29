import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.MixedMatrixSupplier

/-! Exact smoothing of actual rectangular linear matrix fields. The
eigenvalue-corrected mean is the explicit radial lift of the original
linear family; no mean identity is supplied as a hypothesis. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace LinearMatrixSmoothing

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open MeasureTheory Matrix MvPolynomial SphereMeasure SphereMoments
  PolynomialSmoothingKernel SmoothingKernelCoordinates
  HomogeneousMatrixSmoothing HomogeneousMatrixBound SphereMatrixSmoothing

abbrev P (n : ℕ) := Foundation.Polynomial n

def entryLinear {d e : ℕ} (u : Fin d) (v : Fin e) :
    Matrix (Fin d) (Fin e) ℝ→ₗ[ℝ] ℝ where
  toFun A := A u v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def familyPolynomial {n d e : ℕ} (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) :
    Matrix (Fin d) (Fin e) (P n) :=
  fun u v ↦ ∑i, C (T (SphereMoments.axis i) u v)*X i

theorem familyPolynomial_homogeneous {n d e : ℕ}
    (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) (u : Fin d) (v : Fin e) :
    (familyPolynomial T u v).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_X ℝ i).C_mul _

theorem familyPolynomial_eval {n d e : ℕ}
    (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) (x : E n) (u : Fin d) (v : Fin e) :
    eval (fun i ↦ x i) (familyPolynomial T u v)=T x u v := by
  have hx := OrderedCubicExpansion.sum_coordinatePiece x
  have ht := congrArg (fun z : E n ↦ T z u v) hx
  simp only [OrderedCubicExpansion.coordinatePiece,map_sum,map_smul,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at ht
  simp only [familyPolynomial,eval_sum,eval_mul,eval_C,eval_X]
  calc
    (∑i, T (SphereMoments.axis i) u v*x i)=
        ∑i, x i*T (OrderedCubicExpansion.coordinateAxis i) u v := by
      apply Finset.sum_congr rfl
      intro i _
      have he : OrderedCubicExpansion.coordinateAxis i=SphereMoments.axis i := by
        ext j
        simp [OrderedCubicExpansion.coordinateAxis,SphereMoments.axis,EuclideanSpace.single,
          WithLp.equiv_symm_apply, PiLp.toLp_apply]
      rw [he]
      ring
    _=T x u v := ht

theorem field_measurable {n d e : ℕ}
    (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) (u : Fin d) (v : Fin e) :
    Measurable (fun y : Sphere n ↦ T y.1 u v) := by
  exact (((entryLinear u v).comp T).toContinuousLinearMap.continuous.comp
    continuous_subtype_val).measurable

theorem field_norm_le {n d e : ℕ}
    (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) (y : Sphere n) :
    ‖T y.1‖≤‖T.toContinuousLinearMap‖ := by
  have hy : ‖y.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using y.2
  simpa only [LinearMap.coe_toContinuousLinearMap',hy,mul_one] using
    T.toContinuousLinearMap.le_opNorm y.1

theorem field_odd {n d e : ℕ}
    (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) (y : Sphere n) :
    T (antipode y).1= -T y.1 := by
  change T (-y.1)= -T y.1
  exact map_neg T y.1

theorem kernel_linear_family {n d e : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) (x : Sphere n) (u : Fin d) (v : Fin e) :
    (∫y : Sphere n, kernel k x.1 y*T y.1 u v ∂surface n)=lambda1 n k*T x.1 u v := by
  let f : E n→L[ℝ] ℝ := ((entryLinear u v).comp T).toContinuousLinearMap
  let z : E n := (InnerProductSpace.toDual ℝ (E n)).symm f
  have hz (y : E n) : ⟪z,y⟫_ℝ=T y u v := InnerProductSpace.toDual_symm_apply
  have h := kernel_linear hn k x z
  have hx : ⟪x.1,z⟫_ℝ=T x.1 u v := (real_inner_comm x.1 z).symm.trans (hz x.1)
  simpa only [hz,hx] using h

theorem correctedMean_eval_sphere_linear {n s d e : ℕ} (hn : 2 ≤ n) (hs : 1 ≤ s)
    (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) (x : Sphere n) (u : Fin d) (v : Fin e) :
    eval (fun i ↦ x.1 i) (correctedMean (s:=s) (fun y ↦ T y.1) u v)=T x.1 u v := by
  rw [correctedMean_eval_sphere (by omega : 0<n) hs (fun y ↦ T y.1)
    (field_measurable T) (field_norm_le T) (field_odd T) _
    (SphereMeasure.coordinates_unitSphere x),
    mean_eval_kernel (by omega : 0<n) (fun y ↦ T y.1) (field_measurable T) (field_norm_le T),
    kernel_linear_family hn]
  have hl : lambda1 n (2*s)≠0 := (lambda1_pos hn (by omega : 0<2*s)).ne'
  exact mul_div_cancel_left₀ _ hl

/-- Actual ambient polynomial identity for every rectangular linear
family, after the proved sphere mean and homogeneous lift. -/
theorem correctedMean_linear {n s d e : ℕ} (hn : 2 ≤ n) (hs : 1 ≤ s)
    (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) :
    correctedMean (s:=s) (fun y ↦ T y.1)=
      (Foundation.radiusPolynomial n)^(s-1) • familyPolynomial T := by
  apply Matrix.ext
  intro u v
  apply HomogeneousSOSFromSphere.homogeneous_eq_of_sphere_eq (by omega : 0<2*s-1) _ _
    (correctedMean_homogeneous (fun y ↦ T y.1) u v)
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
    have hw := correctedMean_eval_sphere_linear (s:=s) hn hs T q u v
    have hR : eval x (Foundation.radiusPolynomial n)=1 := by simpa [Foundation.unitSphere] using hx
    simp only [Matrix.smul_apply,smul_eq_mul,eval_mul,eval_pow,hR,one_pow,one_mul]
    have hwentry : eval x (correctedMean (s:=s) (fun y ↦ T y.1) u v)=T z u v := by
      simpa only [q,z,WithLp.equiv_symm_apply, PiLp.toLp_apply] using hw
    rw [hwentry]
    simpa only [z,WithLp.equiv_symm_apply, PiLp.toLp_apply] using (familyPolynomial_eval T z u
      v).symm

def radialFamily {n s d e : ℕ} (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) :
    Matrix (Fin d) (Fin e) (P n) :=
  (Foundation.radiusPolynomial n)^(s-1) • familyPolynomial T

theorem radialFamily_homogeneous {n s d e : ℕ} (hs : 1 ≤ s)
    (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ) (u : Fin d) (v : Fin e) :
    (radialFamily (s:=s) T u v).IsHomogeneous (2*s-1) := by
  change ((Foundation.radiusPolynomial n)^(s-1)*familyPolynomial T u v).IsHomogeneous (2*s-1)
  have hd : 2*(s-1)+1=2*s-1 := by omega
  simpa only [hd] using ((HomogeneousSphereBounds.radius_homogeneous n).pow (s-1)).mul
    (familyPolynomial_homogeneous T u v)

/-- A source bound on an actual rectangular linear family directly
produces the finite global pure-radius matrix SOS for its explicit
radial polynomial lift. -/
theorem linear_matrix_smoothing_bound {n s d e : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    {b0 : ℝ} (hb0 : 0 ≤ b0) (U : Finset (Fin n))
    (T : E n →ₗ[ℝ] Matrix (Fin d) (Fin e) ℝ)
    (hT : ∀ x, ‖T x‖ ≤ b0 * ‖CubicBlockInverse.projection U x‖) :
    FiniteMatrixVariance.BoundedMatrixSOS (3*s)
      (radialBound s (4*b0^2) (blockWeight U) (radialFamily (s:=s) T)) := by
  have hFnorm (y : Sphere n) : ‖T y.1‖≤blockBound b0 U y := by
    exact (hT y.1).trans_eq (by rw [MixedMatrixSupplier.projection_norm];rfl)
  have hm := homogeneous_matrix_smoothing_bound (s:=s) hn hs hb0 U (fun y ↦ T y.1)
    (field_measurable T) hFnorm (field_odd T)
  rw [correctedMean_linear hn (by omega : 1≤s) T] at hm
  exact hm

end LinearMatrixSmoothing
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
