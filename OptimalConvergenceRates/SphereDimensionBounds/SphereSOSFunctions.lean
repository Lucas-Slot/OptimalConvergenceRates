import OptimalConvergenceRates.SphereDimensionBounds.FiniteSphereAveraging
import OptimalConvergenceRates.SphereDimensionBounds.HomogeneousHierarchyBridge

/-! Finite-square sphere functions and exact continuous averaging. The
final conversion returns the original equality-constrained hierarchy with
its unchanged root and free-multiplier degree budgets. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.SphereSOSFunctions

open scoped BigOperators
open MvPolynomial OptimalConvergenceRates.SphereDimensionBounds.Foundation MeasureTheory SphereMeasure SpherePolynomialSpace ChebyshevSOSKernel

abbrev Poly (n : ℕ) := OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n

def SphereSOS {n : ℕ} (r : ℕ) (F : C(Sphere n, ℝ)) : Prop :=
  ∃ p : Poly n,BoundedSOS r p ∧ restriction n p=F

theorem zero {n r : ℕ} : SphereSOS r (0:C(Sphere n,ℝ)) :=
  ⟨0,BoundedSOS.zero,by simp⟩

theorem add {n r : ℕ} {F G : C(Sphere n, ℝ)} (hF : SphereSOS r F) (hG : SphereSOS r G) :
    SphereSOS r (F+G) := by
  rcases hF with ⟨p,hp,hpF⟩
  rcases hG with ⟨q,hq,hqG⟩
  exact ⟨p+q,hp.add hq,by rw [map_add,hpF,hqG]⟩

theorem smul {n r : ℕ} {F : C(Sphere n, ℝ)} (hF : SphereSOS r F) (c : ℝ) (hc : 0 ≤ c) :
    SphereSOS r (c • F) := by
  rcases hF with ⟨p,hp,hpF⟩
  refine ⟨C c*p,hp.scale c hc,?_⟩
  rw [←smul_eq_C_mul,map_smul,hpF]

theorem constant {n r : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    SphereSOS r (ContinuousMap.const (Sphere n) c) := by
  have h1 : BoundedSOS r (1:Poly n) := by
    simpa only [one_pow] using BoundedSOS.square (1:Poly n) (by simp : (1:Poly n).totalDegree≤r)
  refine ⟨C c,by simpa only [mul_one] using h1.scale c hc,?_⟩
  ext x
  simp

theorem finset_sum {n r : ℕ} {I : Type*} (s : Finset I) (f : I → C(Sphere n, ℝ))
    (hf : ∀ i ∈ s, SphereSOS r (f i)) : SphereSOS r (∑ i∈s,f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro hf;simpa only [Finset.sum_empty] using (zero (n:=n) (r:=r))
  | @insert i s hi ih =>
      intro hf
      rw [Finset.sum_insert hi]
      exact add (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem of_feasible {n r : ℕ} {p : Poly n} (hp : Feasible r p 0) :
    SphereSOS r (restriction n p) := by
  rcases hp with ⟨N,a,g,ha,hg,hid⟩
  refine ⟨∑ i,a i^2,BoundedSOS.of_family a ha,?_⟩
  ext x
  have hrad : eval (fun i => x.1 i) (radiusPolynomial n)=1 := by
    simpa only [radiusPolynomial_eval,unitSphere,Set.mem_ofPred_eq] using coordinates_unitSphere x
  have he := congrArg (eval (fun i => x.1 i)) hid
  simpa only [restriction_apply,map_sub,map_zero,sub_zero,map_add,map_mul,map_one,hrad,
    sub_self,zero_mul,add_zero] using he.symm

/-- Exact averaging of continuous bounded-degree sphere SOS functions.
No choice of their square roots is required to be measurable. -/
theorem integral {n r : ℕ} (hn : 0 < n) (f : Sphere n → C(Sphere n, ℝ)) (hf : Continuous f)
    (hSOS : ∀ y, SphereSOS r (f y)) : SphereSOS r (∫ y,f y ∂surface n) := by
  letI := surface_isProbability n hn
  have hmem (y : Sphere n) : f y∈boundedSpace n (2*r) := by
    rcases hSOS y with ⟨p,hp,hpe⟩
    exact (mem_boundedSpace (f y)).mpr ⟨p,hp.degree,hpe⟩
  let F : Sphere n → boundedSpace n (2*r) := fun y => ⟨f y,hmem y⟩
  have hF : Continuous F := hf.subtype_mk _
  have hFi : Integrable F (surface n) := integrable_continuous hn F hF
  obtain ⟨N,w,y,hw,hs,hcenter⟩ := FiniteSphereAveraging.exists_finite_integral (surface n) F hF
  have heq : (∫ y,f y ∂surface n)=∑ i,w i • f (y i) := by
    calc
      (∫ y,f y ∂surface n)=(boundedSpace n (2*r)).subtypeL (∫ y,F y ∂surface n) :=
        (boundedSpace n (2*r)).subtypeL.integral_comp_comm hFi
      _=∑ i,w i • f (y i) := by
        rw [hcenter,map_sum]
        simp only [map_smul]
        rfl
  rw [heq]
  exact finset_sum Finset.univ _ (fun i _ => smul (hSOS (y i)) (w i) (hw i))

theorem homogeneous_radial_sos {n r l : ℕ} (hr : 1 ≤ r) (hlr : l ≤ r)
    (p : Poly n) (hp : p.IsHomogeneous (2 * l)) (hSOS : SphereSOS r (restriction n p)) :
    BoundedSOS r ((radiusPolynomial n)^(r-l)*p) := by
  rcases hSOS with ⟨q,⟨N,a,ha,hid⟩,hqe⟩
  have hhom : ((radiusPolynomial n)^(r-l)*p).IsHomogeneous (2*r) := by
    have hh := ((HomogeneousSphereBounds.radius_homogeneous n).pow (r-l)).mul hp
    simpa only [show 2*(r-l)+2*l=2*r by omega] using hh
  apply HomogeneousSOSFromSphere.homogeneous_sos_from_sphere hr _ hhom a ha
  intro x hx
  have hval := DFunLike.congr_fun hqe (coordinateSphere x hx)
  change eval x q=eval x p at hval
  have hrad : eval x (radiusPolynomial n)=1 := by
    simpa only [radiusPolynomial_eval,unitSphere,Set.mem_ofPred_eq] using hx
  rw [eval_mul,eval_pow,hrad,one_pow,one_mul,←hval,hid,eval_sum]
  simp only [eval_pow]

/-- The actual homogeneous sphere function certificate gives the original
Feasible predicate at the same order and its exact free-multiplier budget. -/
theorem homogeneous_feasible_of_sphereSOS {n r l : ℕ} (hr : 1 ≤ r) (hlr : l ≤ r)
    (p : Poly n) (hp : p.IsHomogeneous (2 * l)) (lam : ℝ)
    (hSOS : SphereSOS r (restriction n (p - C lam * (radiusPolynomial n) ^ l))) :
    Feasible r p lam := by
  have htarget : (p-C lam*(radiusPolynomial n)^l).IsHomogeneous (2*l) :=
    hp.sub (((HomogeneousSphereBounds.radius_homogeneous n).pow l).C_mul lam)
  exact HomogeneousHierarchyBridge.bounded_sos_homogeneous_certificate_feasible p hp.totalDegree_le hlr lam
    (homogeneous_radial_sos hr hlr _ htarget hSOS)

end OptimalConvergenceRates.SphereDimensionBounds.SphereSOSFunctions
