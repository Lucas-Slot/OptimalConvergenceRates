import OptimalConvergenceRates.SphereDimensionBounds.DirectionalSmoothingMoments

/-! Exact action of actual polynomial sphere averaging on directional
linear and quadratic functions. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.ZonalSmoothingAction

open scoped BigOperators InnerProductSpace
open Polynomial MeasureTheory SphereMeasure SphereMoments SphereAngularMoments
  DirectionalSmoothingMoments

theorem integrable_weighted {n : ℕ} (hn : 0 < n) (x v : E n) (j : ℕ) (p : Polynomial ℝ) :
    Integrable (fun y : Sphere n => p.eval ⟪x,y.1⟫_ℝ * ⟪v,y.1⟫_ℝ^j) (surface n) := by
  apply integrable_continuous hn
  fun_prop

def weightedIntegral {n : ℕ} (hn : 0 < n) (x v : E n) (j : ℕ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ y : Sphere n,p.eval ⟪x,y.1⟫_ℝ * ⟪v,y.1⟫_ℝ^j ∂surface n
  map_add' p q := by
    simp only [Polynomial.eval_add,add_mul]
    exact integral_add (integrable_weighted hn x v j p) (integrable_weighted hn x v j q)
  map_smul' a p := by
    simp only [Polynomial.smul_eq_C_mul,Polynomial.eval_mul,Polynomial.eval_C,
      mul_assoc,RingHom.id_apply,smul_eq_mul]
    exact integral_const_mul _ _

@[simp] theorem weightedIntegral_X_pow {n : ℕ} (hn : 0 < n) (x v : E n) (j m : ℕ) :
    weightedIntegral hn x v j (X^m)=mixedMoment m j x v := by
  simp [weightedIntegral,mixedMoment]

def multiplyPower (j : ℕ) : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun p := X^j*p
  map_add' p q := mul_add (X^j) p q
  map_smul' a p := mul_smul_comm a (X^j) p

def axialIntegral {n : ℕ} (hn : 0 < n) (x : E n) (j : ℕ) : Polynomial ℝ →ₗ[ℝ] ℝ :=
  (zonalIntegral hn x).comp (multiplyPower j)

@[simp] theorem axialIntegral_X_pow {n : ℕ} (hn : 0 < n) (x : E n) (j m : ℕ) :
    axialIntegral hn x j (X^m)=linearMoment (m+j) x := by
  change zonalIntegral hn x (X^j*X^m)=linearMoment (m+j) x
  rw [←pow_add,zonalIntegral_X_pow,Nat.add_comm]

theorem weighted_linear_map {n : ℕ} (hn : 0 < n) (x : Sphere n) (v : E n) :
    weightedIntegral hn x.1 v 1=⟪x.1,v⟫_ℝ • axialIntegral hn x.1 1 := by
  apply polynomial_functional_eq_of_moments
  intro m
  simp only [weightedIntegral_X_pow,LinearMap.smul_apply,axialIntegral_X_pow,smul_eq_mul]
  rw [mixedMoment_linear hn]
  ring

theorem weighted_quadratic_map {n : ℕ} (hn : 0 < n) (x : Sphere n) (v : E n) :
    ((n:ℝ)-1) • weightedIntegral hn x.1 v 2=
      ‖v‖^2 • (axialIntegral hn x.1 0-axialIntegral hn x.1 2)+
        ⟪x.1,v⟫_ℝ^2 • ((n:ℝ) • axialIntegral hn x.1 2-axialIntegral hn x.1 0) := by
  apply polynomial_functional_eq_of_moments
  intro m
  simp only [LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    weightedIntegral_X_pow,axialIntegral_X_pow,smul_eq_mul,Nat.add_zero]
  rw [mixedMoment_quadratic hn]
  ring

theorem integral_weighted_linear {n : ℕ} (hn : 0 < n) (x : Sphere n) (v : E n)
    (p : Polynomial ℝ) :
    (∫ y : Sphere n,p.eval ⟪x.1,y.1⟫_ℝ * ⟪v,y.1⟫_ℝ ∂surface n)=
      zonalIntegral hn x.1 (X*p)*⟪x.1,v⟫_ℝ := by
  have h := DFunLike.congr_fun (weighted_linear_map hn x v) p
  simpa only [weightedIntegral,axialIntegral,multiplyPower,LinearMap.comp_apply,
    LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,smul_eq_mul,pow_one,mul_comm] using h

theorem integral_weighted_quadratic {n : ℕ} (hn : 0 < n) (x : Sphere n) (v : E n)
    (p : Polynomial ℝ) :
    ((n:ℝ)-1)*(∫ y : Sphere n,p.eval ⟪x.1,y.1⟫_ℝ * ⟪v,y.1⟫_ℝ^2 ∂surface n)=
      (zonalIntegral hn x.1 p-zonalIntegral hn x.1 (X^2*p))*‖v‖^2+
        ((n:ℝ)*zonalIntegral hn x.1 (X^2*p)-zonalIntegral hn x.1 p)*⟪x.1,v⟫_ℝ^2 := by
  have h := DFunLike.congr_fun (weighted_quadratic_map hn x v) p
  simpa only [weightedIntegral,axialIntegral,multiplyPower,LinearMap.comp_apply,
    LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    smul_eq_mul,pow_zero,one_mul,mul_one,mul_comm] using h

end OptimalConvergenceRates.SphereDimensionBounds.ZonalSmoothingAction
