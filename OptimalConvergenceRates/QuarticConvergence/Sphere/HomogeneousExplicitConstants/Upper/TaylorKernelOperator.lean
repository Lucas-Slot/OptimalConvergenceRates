import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.TaylorKernelData
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.BivariateZonalRange

/-! The actual averaged cubic Taylor operator on the finite-dimensional
homogeneous sphere-function space, with its actual integral evaluation. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace TaylorKernelOperator

open scoped BigOperators InnerProductSpace
open MeasureTheory MvPolynomial SphereMeasure SpherePolynomialSpace CubicTaylorBounds
  DegreeTaylorBounds
  BivariateTaylorPolynomial BivariateZonalRange TaylorKernelData

abbrev Poly (n : ℕ) := Foundation.Polynomial n

theorem shifted_add {n : ℕ} (y : E n) (p q : Poly n) : shifted y (p+q)=shifted y p+shifted y q :=
  map_add _ _ _

theorem shifted_smul {n : ℕ} (y : E n) (a : ℝ) (p : Poly n) : shifted y (a • p)=a • shifted y p :=
  by
  simp [shifted,smul_eq_C_mul]

theorem cubicModel_add {n : ℕ} (y : E n) (p q : Poly n) : cubicModel y (p+q)=cubicModel y
  p+cubicModel y q := by
  simp only [cubicModel,shifted_add,map_add,Finset.sum_add_distrib]

theorem cubicModel_smul {n : ℕ} (y : E n) (a : ℝ) (p : Poly n) : cubicModel y (a • p)=a •
  cubicModel y p := by
  simp only [cubicModel,shifted_smul,map_smul,Finset.smul_sum]

theorem jointEvaluation_continuous {n : ℕ} (B : Joint n) :
    Continuous (fun z : Sphere n×Sphere n ↦
      eval (Sum.elim (fun i ↦ z.2.1 i) (fun i ↦ z.1.1 i)) B) := by
  apply (MvPolynomial.continuous_eval B).comp
  apply continuous_pi
  intro i
  cases i with
  | inl i =>
      exact (PiLp.proj (𝕜:=ℝ) (p:=2) (β:=fun _ : Fin n ↦ ℝ) i).continuous.comp
        (continuous_subtype_val.comp continuous_snd)
  | inr i =>
      exact (PiLp.proj (𝕜:=ℝ) (p:=2) (β:=fun _ : Fin n ↦ ℝ) i).continuous.comp
        (continuous_subtype_val.comp continuous_fst)

def taylorSection {n : ℕ} (P : Polynomial ℝ) (p : Poly n) : C(Sphere n,C(Sphere n,ℝ)) :=
  (⟨fun z : Sphere n×Sphere n ↦
    eval (Sum.elim (fun i ↦ z.2.1 i) (fun i ↦ z.1.1 i)) (bivariateTaylor p)*
      P.eval ⟪z.2.1,z.1.1⟫_ℝ,
    (jointEvaluation_continuous (bivariateTaylor p)).mul (by fun_prop)⟩ :
      C(Sphere n×Sphere n,ℝ)).curry

@[simp] theorem section_apply {n : ℕ} (P : Polynomial ℝ) (p : Poly n) (y x : Sphere n) :
    taylorSection P p y x=evalForm (cubicModel y.1 p) (x.1-y.1)*P.eval ⟪x.1,y.1⟫_ℝ := by
  change eval (Sum.elim (fun i ↦ x.1 i) (fun i ↦ y.1 i)) (bivariateTaylor p)*P.eval ⟪x.1,y.1⟫_ℝ=_
  rw [bivariateTaylor_eval]

def sectionsLinear {n : ℕ} (P : Polynomial ℝ) : Poly n →ₗ[ℝ] C(Sphere n,C(Sphere n,ℝ)) where
  toFun p := taylorSection P p
  map_add' p q := by
    ext y x
    simp only [section_apply,cubicModel_add,evalForm,eval_add,ContinuousMap.add_apply]
    ring
  map_smul' a p := by
    ext y x
    change taylorSection P (a • p) y x=a*taylorSection P p y x
    rw [section_apply,section_apply,cubicModel_smul]
    simp only [evalForm,smul_eq_C_mul,eval_mul,eval_C]
    ring

def integralMap {n : ℕ} (hn : 0 < n) : C(Sphere n,C(Sphere n,ℝ)) →ₗ[ℝ] C(Sphere n,ℝ) where
  toFun f := ∫ y,f y ∂surface n
  map_add' f g := by
    simpa only [ContinuousMap.add_apply] using integral_add
      (integrable_continuous hn f f.continuous) (integrable_continuous hn g g.continuous)
  map_smul' a f := by
    simpa only [ContinuousMap.smul_apply,RingHom.id_apply] using integral_smul a f

def representativeLinear (n d : ℕ) : homogeneousSpace n d →ₗ[ℝ] Poly n :=
  (homogeneousSubmodule (Fin n) ℝ d).subtype.comp (homogeneousRepresentative n d)

theorem representativeLinear_homogeneous {n d : ℕ} (F : homogeneousSpace n d) :
    (representativeLinear n d F).IsHomogeneous d := (homogeneousRepresentative n d F).2

@[simp] theorem representativeLinear_eval {n d : ℕ} (F : homogeneousSpace n d) (x : Sphere n) :
    eval (fun i ↦ x.1 i) (representativeLinear n d F)=F.1 x :=
  homogeneousRepresentative_eval F x

def rawOperator {n d : ℕ} (hn : 0 < n) (P : Polynomial ℝ) :
    homogeneousSpace n d →ₗ[ℝ] C(Sphere n,ℝ) :=
  (integralMap hn).comp ((sectionsLinear P).comp (representativeLinear n d))

theorem rawOperator_eval {n d : ℕ} (hn : 0 < n) (P : Polynomial ℝ)
    (F : homogeneousSpace n d) (x : Sphere n) :
    rawOperator hn P F x=
      ∫ y : Sphere n,evalForm (cubicModel y.1 (representativeLinear n d F)) (x.1-y.1)*
        P.eval ⟪x.1,y.1⟫_ℝ ∂surface n := by
  change (∫ y : Sphere n,taylorSection P (representativeLinear n d F) y ∂surface n) x=_
  rw [ContinuousMap.integral_apply (integrable_continuous hn _ (taylorSection P _).continuous)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y ↦ section_apply P _ y x)

theorem rawOperator_mem {n d : ℕ} (hn : 0 < n) (P : Polynomial ℝ) (F : homogeneousSpace n d) :
    rawOperator hn P F∈homogeneousSpace n d := by
  obtain ⟨q,hq,hqe⟩ := exists_homogeneous_cubicTaylor_range hn (representativeLinear n d F)
    (representativeLinear_homogeneous F) P
  apply (mem_homogeneousSpace _).mpr
  refine ⟨q,hq,?_⟩
  ext x
  rw [restriction_apply,rawOperator_eval,hqe]

def operator {n d : ℕ} (hn : 0 < n) (P : Polynomial ℝ) : homogeneousSpace n d →ₗ[ℝ]
  homogeneousSpace n d :=
  (rawOperator hn P).codRestrict _ (rawOperator_mem hn P)

theorem operator_eval {n d : ℕ} (hn : 0 < n) (P : Polynomial ℝ)
    (F : homogeneousSpace n d) (x : Sphere n) :
    (operator hn P F).1 x=
      ∫ y : Sphere n,evalForm (cubicModel y.1 (representativeLinear n d F)) (x.1-y.1)*
        P.eval ⟪x.1,y.1⟫_ℝ ∂surface n := rawOperator_eval hn P F x

theorem integrable_section_eval {n : ℕ} (hn : 0 < n) (P : Polynomial ℝ) (p : Poly n) (x : Sphere
  n) :
    Integrable (fun y : Sphere n ↦ evalForm (cubicModel y.1 p) (x.1-y.1)*P.eval ⟪x.1,y.1⟫_ℝ)
      (surface n) := by
  have hi : Integrable (fun y : Sphere n ↦ taylorSection P p y x) (surface n) := by
    apply integrable_continuous hn
    exact (ContinuousMap.evalCLM ℝ x).continuous.comp (taylorSection P p).continuous
  simpa only [section_apply] using hi

end TaylorKernelOperator
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
