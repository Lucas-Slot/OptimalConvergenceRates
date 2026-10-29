import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.TaylorKernelOperator

/-! The actual Taylor operator is near the identity with its sharp
binomial coefficient times the actual fourth chordal kernel moment. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace TaylorKernelNorm

open scoped BigOperators InnerProductSpace
open MeasureTheory MvPolynomial SphereMeasure SpherePolynomialSpace CubicTaylorBounds
  DegreeTaylorBounds
  TaylorKernelData TaylorKernelOperator

theorem pointwise_error {n d : ℕ} (hn : 0 < n) (hd : 4 ≤ d) (m : ℕ) (chi : Polynomial ℝ)
    (hZ : 0 < normalizingMass hn m chi) (F : homogeneousSpace n d) (x : Sphere n) :
    |F.1 x-(operator hn (normalizedKernel hn m chi) F).1 x|≤
      ((d.choose 4:ℝ)*fourthMoment hn m chi)*‖F‖ := by
  let P := normalizedKernel hn m chi
  let p := representativeLinear n d F
  let v : Sphere n → ℝ := fun y ↦ evalForm (cubicModel y.1 p) (x.1-y.1)
  let w : Sphere n → ℝ := fun y ↦ P.eval ⟪x.1,y.1⟫_ℝ
  let e : Sphere n → ℝ := fun y ↦ (F.1 x-v y)*w y
  have hwi : Integrable w (surface n) := by
    apply integrable_continuous hn
    fun_prop
  have hvwi : Integrable (fun y ↦ v y*w y) (surface n) := integrable_section_eval hn P p x
  have hFwi := hwi.const_mul (F.1 x)
  have heq : e=(fun y ↦ F.1 x*w y-v y*w y) := by funext y;dsimp [e];ring
  have hei : Integrable e (surface n) := by rw [heq];exact hFwi.sub hvwi
  have hmass : (∫ y,w y ∂surface n)=1 := normalized_mass hn m chi hZ x
  have herror : F.1 x-(operator hn P F).1 x=∫ y,e y ∂surface n := by
    rw [operator_eval]
    change F.1 x-(∫ y,v y*w y ∂surface n)=∫ y,e y ∂surface n
    rw [heq,integral_sub hFwi hvwi,integral_const_mul,hmass,mul_one]
  have hbound : ∀ z : Fin n → ℝ,(∑ i,z i^2)=1 → |eval z p|≤‖F‖ := by
    intro z hz
    exact homogeneousRepresentative_bound F (coordinateSphere z hz)
  have hpoint (y : Sphere n) : |e y|≤
      ((d.choose 4:ℝ)*‖F‖)*(‖x.1-y.1‖^4*w y) := by
    have hrem := cubic_sphere_remainder hn hd p (representativeLinear_homogeneous F)
      ‖F‖ (norm_nonneg _) hbound x.1 y.1 (sphere_norm_one x) (sphere_norm_one y)
    have hpx : evalForm p x.1=F.1 x := representativeLinear_eval F x
    rw [hpx] at hrem
    have hw0 : 0≤w y := normalizedKernel_nonneg hn m chi _
    calc
      |e y|=|F.1 x-v y| *w y := by
        change |(F.1 x-v y)*w y|=_
        rw [abs_mul,abs_of_nonneg hw0]
      _≤((d.choose 4:ℝ)*‖F‖*‖x.1-y.1‖^4)*w y := mul_le_mul_of_nonneg_right hrem hw0
      _=((d.choose 4:ℝ)*‖F‖)*(‖x.1-y.1‖^4*w y) := by ring
  have hbi : Integrable (fun y : Sphere n ↦
      ((d.choose 4:ℝ)*‖F‖)*(‖x.1-y.1‖^4*w y)) (surface n) := by
    apply integrable_continuous hn
    fun_prop
  calc
    |F.1 x-(operator hn P F).1 x|=|∫ y,e y ∂surface n| := congrArg abs herror
    _≤∫ y,|e y| ∂surface n := abs_integral_le_integral_abs
    _≤∫ y,((d.choose 4:ℝ)*‖F‖)*(‖x.1-y.1‖^4*w y) ∂surface n := integral_mono hei.abs hbi hpoint
    _=((d.choose 4:ℝ)*‖F‖)*fourthMoment hn m chi := by
      rw [integral_const_mul]
      congr 1
      exact fourthMoment_independent hn m chi x
    _=((d.choose 4:ℝ)*fourthMoment hn m chi)*‖F‖ := by ring

/-- No moment estimate is assumed: the coefficient uses the literal
fourth moment of the actual normalized sphere kernel. -/
theorem near_identity {n d : ℕ} (hn : 0 < n) (hd : 4 ≤ d) (m : ℕ) (chi : Polynomial ℝ)
    (hZ : 0 < normalizingMass hn m chi) (F : homogeneousSpace n d) :
    ‖F-operator hn (normalizedKernel hn m chi) F‖≤
      ((d.choose 4:ℝ)*fourthMoment hn m chi)*‖F‖ := by
  have h0 : 0≤((d.choose 4:ℝ)*fourthMoment hn m chi)*‖F‖ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (fourthMoment_nonneg hn m chi)) (norm_nonneg _)
  change ‖F.1-(operator hn (normalizedKernel hn m chi) F).1‖≤_
  apply (ContinuousMap.norm_le _ h0).mpr
  intro x
  rw [ContinuousMap.sub_apply,Real.norm_eq_abs]
  exact pointwise_error hn hd m chi hZ F x

end TaylorKernelNorm
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
