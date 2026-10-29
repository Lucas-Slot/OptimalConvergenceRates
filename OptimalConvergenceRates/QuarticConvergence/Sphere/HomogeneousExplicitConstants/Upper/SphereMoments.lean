import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.PolynomialMoments
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SphereMeasure

/-! Actual linear-form moments for normalized Euclidean sphere measure.
Rotational invariance and polynomial coefficient extraction are proved for
the same measure used by the kernel construction. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SphereMoments

open scoped BigOperators InnerProductSpace
open MeasureTheory SphereMeasure Polynomial

def linearMoment {n : ℕ} (m : ℕ) (z : E n) : ℝ :=
  ∫ y : Sphere n, ⟪z,y.1⟫_ℝ^m ∂surface n

/-- Euclidean moments are the existing coordinate-sphere moments under measure transport. -/
theorem linearMoment_eq {n : ℕ} (m : ℕ) (z : E n) :
    linearMoment m z = sphereLinearFormMoment m (fun i ↦ z i) := by
  rw [sphereLinearFormMoment, normalizedSphereMeasure,
    (euclideanSphereHomeomorphSphereSet n).measurableEmbedding.integral_map]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  congr 1
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm,
    euclideanSphereHomeomorphSphereSet, euclideanSphereEquivSphereSet,
    euclideanSphereCoordinates]

theorem linearMoment_zero {n : ℕ} (hn : 0 < n) (z : E n) : linearMoment 0 z=1 := by
  letI := surface_isProbability n hn
  simp [linearMoment]

theorem integrable_linearMoment {n : ℕ} (hn : 0 < n) (m : ℕ) (z : E n) :
    Integrable (fun y : Sphere n ↦ ⟪z,y.1⟫_ℝ^m) (surface n) := by
  apply integrable_continuous hn
  exact (continuous_const.inner continuous_subtype_val).pow m

theorem linearMoment_smul {n : ℕ} (m : ℕ) (z : E n) (a : ℝ) :
    linearMoment m (a • z)=a^m*linearMoment m z := by
  rw [linearMoment_eq, linearMoment_eq]
  exact sphereLinearFormMoment_smul a (fun i ↦ z i)

theorem linearMoment_isometry {n : ℕ} (m : ℕ) (z : E n) (L : E n ≃ₗᵢ[ℝ] E n) :
    linearMoment m (L z)=linearMoment m z := by
  rw [linearMoment_eq, linearMoment_eq]
  exact sphereLinearFormMoment_linearIsometry L (fun i ↦ z i)

theorem linearMoment_unit {n : ℕ} (m : ℕ) (x z : Sphere n) :
    linearMoment m x.1=linearMoment m z.1 := by
  let L : E n ≃ₗᵢ[ℝ] E n := (ℝ ∙ (x.1-z.1))ᗮ.reflection
  have hnorm : ‖x.1‖=‖z.1‖ := by
    have hx : ‖x.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.2
    have hz : ‖z.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.2
    rw [hx,hz]
  have hmap : L x.1=z.1 := Submodule.reflection_sub hnorm
  rw [← hmap,linearMoment_isometry]

theorem linearMoment_odd {n m : ℕ} (z : E n) (hm : Odd m) : linearMoment m z=0 := by
  rw [linearMoment_eq]
  exact sphereLinearFormMoment_eq_zero_of_odd _ hm

theorem linearMoment_even_radial {n : ℕ} (hn : 0 < n) (q : ℕ) (base : Sphere n) (z : E n) :
    linearMoment (2*q) z=linearMoment (2*q) base.1*(‖z‖^2)^q := by
  by_cases hz : z=0
  · subst z
    by_cases hq : q=0
    · subst q;simp [linearMoment_zero hn]
    · have hqpos : 0<2*q := by omega
      simp [linearMoment,zero_pow hq,zero_pow hqpos.ne']
  · let u : E n := ‖z‖⁻¹ • z
    have hu : ‖u‖=1 := norm_smul_inv_norm hz
    let unit : Sphere n := ⟨u,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩
    have hrepr : z=‖z‖ • unit.1 := by
      change z=‖z‖ • (‖z‖⁻¹ • z)
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul]
    conv_lhs => rw [hrepr]
    rw [linearMoment_smul,linearMoment_unit (2*q) unit base]
    rw [←pow_mul]
    ring

def mixedMoment {n : ℕ} (a b : ℕ) (x z : E n) : ℝ :=
  ∫ y : Sphere n,⟪x,y.1⟫_ℝ^a*⟪z,y.1⟫_ℝ^b ∂surface n

theorem integrable_mixedMoment {n : ℕ} (hn : 0 < n) (a b : ℕ) (x z : E n) :
    Integrable (fun y : Sphere n ↦ ⟪x,y.1⟫_ℝ^a*⟪z,y.1⟫_ℝ^b) (surface n) := by
  apply integrable_continuous hn
  exact ((continuous_const.inner continuous_subtype_val).pow a).mul
    ((continuous_const.inner continuous_subtype_val).pow b)

def momentLine {n : ℕ} (m : ℕ) (x z : E n) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (m+1),C ((Nat.choose m j:ℝ)*mixedMoment (m-j) j x z)*X^j

theorem momentLine_coeff {n m j : ℕ} (x z : E n) (hj : j ≤ m) :
    (momentLine m x z).coeff j=(Nat.choose m j:ℝ)*mixedMoment (m-j) j x z := by
  classical
  rw [momentLine,Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j,Polynomial.coeff_C_mul_X_pow,ite_eq_left rfl]
  · intro b hb hbj
    rw [Polynomial.coeff_C_mul_X_pow,ite_eq_right hbj.symm]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))).elim

theorem momentLine_eval {n : ℕ} (hn : 0 < n) (m : ℕ) (x z : E n) (t : ℝ) :
    (momentLine m x z).eval t=linearMoment m (x+t • z) := by
  rw [momentLine,Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  unfold linearMoment
  calc
    _=∑ j ∈ Finset.range (m+1),∫ y : Sphere n,
        ((Nat.choose m j:ℝ)*t^j)*(⟪x,y.1⟫_ℝ^(m-j)*⟪z,y.1⟫_ℝ^j) ∂surface n := by
      apply Finset.sum_congr rfl
      intro j _
      rw [mixedMoment,integral_const_mul]
      ring
    _=∫ y : Sphere n,∑ j ∈ Finset.range (m+1),
        ((Nat.choose m j:ℝ)*t^j)*(⟪x,y.1⟫_ℝ^(m-j)*⟪z,y.1⟫_ℝ^j) ∂surface n := by
      rw [integral_finsetSum]
      intro j _
      exact (integrable_mixedMoment hn (m-j) j x z).const_mul _
    _=_ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change (∑ j ∈ Finset.range (m+1),
        ((Nat.choose m j:ℝ)*t^j)*(⟪x,y.1⟫_ℝ^(m-j)*⟪z,y.1⟫_ℝ^j))=
        ⟪x+t • z,y.1⟫_ℝ^m
      rw [inner_add_left,real_inner_smul_left]
      rw [show ⟪x,y.1⟫_ℝ+t*⟪z,y.1⟫_ℝ=t*⟪z,y.1⟫_ℝ+⟪x,y.1⟫_ℝ by ring,add_pow]
      apply Finset.sum_congr rfl
      intro j _
      ring

def normLine {n : ℕ} (x z : E n) : Polynomial ℝ :=
  C (‖x‖^2)+C (2*⟪x,z⟫_ℝ)*X+C (‖z‖^2)*X^2

theorem normLine_eval {n : ℕ} (x z : E n) (t : ℝ) :
    (normLine x z).eval t=‖x+t • z‖^2 := by
  simp only [normLine,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  rw [norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem momentLine_even {n : ℕ} (hn : 0 < n) (q : ℕ) (base : Sphere n) (x z : E n) :
    momentLine (2*q) x z=C (linearMoment (2*q) base.1)*(normLine x z)^q := by
  apply Polynomial.funext
  intro t
  rw [momentLine_eval hn,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    normLine_eval,linearMoment_even_radial hn q base]

theorem choose_mul_mixedMoment {n q j : ℕ} (hn : 0 < n) (base : Sphere n)
    (x z : E n) (hj : j ≤ 2 * q) :
    (Nat.choose (2*q) j:ℝ)*mixedMoment (2*q-j) j x z=
      linearMoment (2*q) base.1*((normLine x z)^q).coeff j := by
  rw [←momentLine_coeff x z hj,momentLine_even hn q base,Polynomial.coeff_C_mul]

def axis {n : ℕ} (i : Fin n) : E n := EuclideanSpace.single i 1

theorem axis_norm {n : ℕ} (i : Fin n) : ‖axis i‖=1 := by
  simp [axis,PiLp.norm_single]

def axisSphere {n : ℕ} (i : Fin n) : Sphere n :=
  ⟨axis i,by simpa only [Metric.mem_sphere,dist_zero_right] using axis_norm i⟩

def coordinateMoment {n : ℕ} (i : Fin n) (m : ℕ) : ℝ :=
  ∫ y : Sphere n,y.1 i^m ∂surface n

theorem linearMoment_axis {n : ℕ} (i : Fin n) (m : ℕ) :
    linearMoment m (axis i)=coordinateMoment i m := by
  simp [linearMoment,coordinateMoment,axis,EuclideanSpace.inner_single_left]

theorem coordinateMoment_zero {n : ℕ} (hn : 0 < n) (i : Fin n) :
    coordinateMoment i 0=1 := by rw [←linearMoment_axis,linearMoment_zero hn]

theorem coordinateMoment_odd {n m : ℕ} (i : Fin n) (hm : Odd m) :
    coordinateMoment i m=0 := by rw [←linearMoment_axis,linearMoment_odd _ hm]

theorem coeff_one_add_X_sq_pow (q : ℕ) :
    (((1:Polynomial ℝ)+Polynomial.X^2)^q).coeff 2=(q:ℝ) := by
  induction q with
  | zero => simp [Polynomial.coeff_one]
  | succ q ih =>
    rw [pow_succ,mul_add,mul_one,Polynomial.coeff_add]
    rw [show 2=0+2 by rfl,Polynomial.coeff_mul_X_pow]
    have hz : (((1:Polynomial ℝ)+Polynomial.X^2)^q).coeff 0=1 := by
      change Polynomial.constantCoeff ((1+Polynomial.X^2:Polynomial ℝ)^q)=1
      rw [map_pow]
      norm_num [Polynomial.constantCoeff,Polynomial.coeff_add,
        Polynomial.coeff_one,Polynomial.coeff_X_pow]
    simp [ih,hz]

theorem normLine_axes {n : ℕ} (a i : Fin n) (hi : i ≠ a) :
    normLine (axis a) (axis i)=1+Polynomial.X^2 := by
  simp [normLine,axis_norm,axis,EuclideanSpace.inner_single_left,
    PiLp.single_apply,hi,Ne.symm hi]

theorem mixed_coordinate_even {n : ℕ} (hn : 0 < n) (a i : Fin n)
    (hi : i ≠ a) (q : ℕ) :
    (2*(q:ℝ)+1)*(∫ y : Sphere n,y.1 a^(2*q)*y.1 i^2 ∂surface n)=
      coordinateMoment a (2*q+2) := by
  have h := choose_mul_mixedMoment (q:=q+1) (j:=2) hn (axisSphere a)
    (axis a) (axis i) (by omega)
  rw [normLine_axes a i hi,coeff_one_add_X_sq_pow] at h
  have hc : (Nat.choose (2*(q+1)) 2:ℝ)=((q:ℝ)+1)*(2*(q:ℝ)+1) := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  rw [hc] at h
  have h' : ((q:ℝ)+1)*((2*(q:ℝ)+1)*
      (∫ y : Sphere n,y.1 a^(2*q)*y.1 i^2 ∂surface n))=
      ((q:ℝ)+1)*coordinateMoment a (2*q+2) := by
    simpa [mixedMoment,axisSphere,axis,EuclideanSpace.inner_single_left,
      linearMoment,coordinateMoment,show 2*(q+1)-2=2*q by omega,
      show 2*(q+1)=2*q+2 by omega,Nat.cast_add,Nat.cast_one,
      mul_assoc,mul_comm,mul_left_comm] using h
  exact mul_left_cancel₀ (by positivity : ((q:ℝ)+1) ≠ 0) h'

theorem coordinateMoment_even_recurrence {n : ℕ} (hn : 0 < n)
    (a : Fin n) (q : ℕ) :
    coordinateMoment a (2*q+2)*(2*(q:ℝ)+(n:ℝ))=
      coordinateMoment a (2*q)*(2*(q:ℝ)+1) := by
  let M : Fin n → ℝ := fun i ↦ ∫ y : Sphere n,y.1 a^(2*q)*y.1 i^2 ∂surface n
  have hint (i : Fin n) : Integrable
      (fun y : Sphere n ↦ y.1 a^(2*q)*y.1 i^2) (surface n) := by
    simpa [axis,EuclideanSpace.inner_single_left] using
      integrable_mixedMoment hn (2*q) 2 (axis a) (axis i)
  have hsum : (∑ i,M i)=coordinateMoment a (2*q) := by
    rw [show (∑ i,M i)=∫ y : Sphere n,∑ i,y.1 a^(2*q)*y.1 i^2 ∂surface n by
      exact (integral_finsetSum _ (fun i _ ↦ hint i)).symm]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    change (∑ i,y.1 a^(2*q)*y.1 i^2)=y.1 a^(2*q)
    rw [←Finset.mul_sum,coordinates_unitSphere y,mul_one]
  have hdiag : M a=coordinateMoment a (2*q+2) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y ↦ (pow_add (y.1 a) (2*q) 2).symm)
  have hterm (i : Fin n) : (2*(q:ℝ)+1)*M i=coordinateMoment a (2*q+2)+
      if i=a then 2*(q:ℝ)*coordinateMoment a (2*q+2) else 0 := by
    by_cases hi : i=a
    · subst i;rw [hdiag,ite_eq_left rfl];ring
    · rw [ite_eq_right hi,add_zero]
      exact mixed_coordinate_even hn a i hi q
  have h := calc
    (2*(q:ℝ)+1)*coordinateMoment a (2*q)=∑ i,(2*(q:ℝ)+1)*M i := by
      rw [←Finset.mul_sum,hsum]
    _=∑ i,(coordinateMoment a (2*q+2)+
        if i=a then 2*(q:ℝ)*coordinateMoment a (2*q+2) else 0) :=
      Finset.sum_congr rfl (fun i _ ↦ hterm i)
    _=(n:ℝ)*coordinateMoment a (2*q+2)+2*(q:ℝ)*coordinateMoment a (2*q+2) := by
      simp [Finset.sum_add_distrib]
  linarith

theorem coordinateMoment_recurrence {n : ℕ} (hn : 0 < n) (a : Fin n) (m : ℕ) :
    coordinateMoment a (m+2)*((m:ℝ)+(n:ℝ))=
      coordinateMoment a m*((m:ℝ)+1) := by
  rcases Nat.even_or_odd m with h|h
  · rcases h with ⟨q,hq⟩
    have hm : m=2*q := by omega
    rw [hm]
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using coordinateMoment_even_recurrence hn a q
  · rw [coordinateMoment_odd a h,coordinateMoment_odd a (h.add_even (by decide : Even 2))]
    simp

theorem moments_unique {n : ℕ} (hn : 0 < n) (a : Fin n) (u : ℕ → ℝ)
    (hzero : u 0 = 1) (hone : u 1 = 0)
    (hrec : ∀ m : ℕ,u (m+2)*((m:ℝ)+(n:ℝ))=u m*((m:ℝ)+1)) :
    ∀ m : ℕ,u m=coordinateMoment a m := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero => rw [hzero,coordinateMoment_zero hn]
  | one => rw [hone,coordinateMoment_odd a (by decide : Odd 1)]
  | more m hm _ =>
    have hnpos : (0:ℝ)<n := by exact_mod_cast hn
    apply mul_right_cancel₀ (by positivity : (m:ℝ)+(n:ℝ) ≠ 0)
    rw [hrec,coordinateMoment_recurrence hn a m,hm]

theorem unit_linearMoment {n : ℕ} (a : Fin n) (x : Sphere n) (m : ℕ) :
    linearMoment m x.1=coordinateMoment a m := by
  rw [linearMoment_unit m x (axisSphere a)]
  exact linearMoment_axis a m

theorem integral_polynomial_inner {n : ℕ} (hn : 0 < n) (z : E n) (p : Polynomial ℝ) :
    (∫ y : Sphere n,p.eval ⟪z,y.1⟫_ℝ ∂surface n)=
      ∑ m ∈ p.support,p.coeff m*linearMoment m z := by
  simp_rw [Polynomial.eval_eq_sum,Polynomial.sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m _
    exact integral_const_mul _ _
  · intro m _
    exact (integrable_linearMoment hn m z).const_mul _

theorem integral_polynomial_zonal {n : ℕ} (hn : 0 < n) (a : Fin n) (x : Sphere n)
    (p : Polynomial ℝ) :
    (∫ y : Sphere n,p.eval ⟪x.1,y.1⟫_ℝ ∂surface n)=
      ∑ m ∈ p.support,p.coeff m*coordinateMoment a m := by
  rw [integral_polynomial_inner hn]
  apply Finset.sum_congr rfl
  intro m _
  rw [unit_linearMoment]

end SphereMoments
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
