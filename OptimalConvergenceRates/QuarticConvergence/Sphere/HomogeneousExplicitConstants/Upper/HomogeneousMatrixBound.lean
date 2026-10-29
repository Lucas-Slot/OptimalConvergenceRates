import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.HomogeneousMatrixSmoothing

/-! Explicit degree-bounded matrix-SOS operations and the homogeneous
block-radius smoothing bound, with the original Euclidean radius. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace HomogeneousMatrixBound

open scoped BigOperators Matrix.Norms.L2Operator
open MvPolynomial Matrix
open ChebyshevSOSKernel FiniteMatrixVariance HomogeneousSOSFromSphere
  SphereMeasure PolynomialSmoothingKernel SmoothingKernelCoordinates
  PolynomialKernelFeatures SphereMatrixSmoothing HomogeneousMatrixSmoothing

abbrev P (n : ℕ) := Foundation.Polynomial n

theorem matrixSOS_scale {n d r : ℕ} {N : Matrix (Fin d) (Fin d) (P n)}
    (hN : BoundedMatrixSOS r N) {c : ℝ} (hc : 0 ≤ c) :
    BoundedMatrixSOS r ((C c : P n) • N) := by
  obtain ⟨m,v,hv,rfl⟩ := hN
  have hsqrt : (C (Real.sqrt c) : P n)^2=C c := by rw [←map_pow,Real.sq_sqrt hc]
  have hid : (C c : P n) • (∑k,outer (v k))=
      ∑k,outer (fun u ↦ C (Real.sqrt c)*v k u) := by
    apply Matrix.ext
    intro u w
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,Finset.mul_sum,outer]
    apply Finset.sum_congr rfl
    intro k _
    linear_combination -(v k u*v k w)*hsqrt
  rw [hid]
  apply BoundedMatrixSOS.of_family
  intro k u
  exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using hv k u)

theorem scalarSOS_diagonal {n d r : ℕ} {p : P n} (hp : BoundedSOS r p) :
    BoundedMatrixSOS r (p • (1:Matrix (Fin d) (Fin d) (P n))) := by
  obtain ⟨m,a,ha,rfl⟩ := hp.exists_squares
  let v := fun z : Fin m×Fin d ↦ fun u : Fin d ↦ if z.2=u then a z.1 else 0
  have hid : (∑k,a k^2) • (1:Matrix (Fin d) (Fin d) (P n))=∑z,outer (v z) := by
    apply Matrix.ext
    intro u w
    by_cases huw : u=w
    · subst w
      simp [v,outer,Matrix.sum_apply,Fintype.sum_prod_type,Matrix.smul_apply,smul_eq_mul,pow_two]
    · have hz (z : Fin m×Fin d) : outer (v z) u w=0 := by
        by_cases hzu : z.2=u
        · have hzw : z.2≠w := by intro hh;exact huw (hzu.symm.trans hh)
          simp [v,outer,hzu,hzw,huw]
        · simp [v,outer,hzu]
      simp [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,huw,Matrix.sum_apply,hz]
  rw [hid]
  apply BoundedMatrixSOS.of_family
  intro z u
  dsimp [v]
  split_ifs
  · exact ha z.1
  · simp

def weightedSquares {n : ℕ} (c : Fin n → ℝ) : P n := ∑i, C (c i)*X i^2

theorem weightedSquares_homogeneous {n : ℕ} (c : Fin n → ℝ) :
    (weightedSquares c).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  exact ((isHomogeneous_X ℝ i).pow 2).C_mul _

theorem weightedSquares_sos {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    BoundedSOS 1 (weightedSquares c) := by
  apply BoundedSOS.sum
  intro i _
  exact (BoundedSOS.square (X i) (by simp)).scale (c i) (hc i)

def rho {n : ℕ} (U : Finset (Fin n)) : ℝ := (U.card:ℝ)/(n:ℝ)

def blockWeight {n : ℕ} (U : Finset (Fin n)) : P n :=
  weightedSquares (fun i ↦ (if i∈U then 1 else 0)+rho U)

def slackCoefficient {n : ℕ} (s : ℕ) (b0 : ℝ) (U : Finset (Fin n)) (i : Fin n) : ℝ :=
  b0^2*((4-(lambda1 n (2*s))⁻¹^2*lambda2 n (2*s))*(if i∈U then 1 else 0)+
    (4-(lambda1 n (2*s))⁻¹^2*(1-lambda2 n (2*s)))*rho U)

theorem inverse_lambda_sq_le_four {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s) :
    (lambda1 n (2*s))⁻¹^2≤4 := by
  have hl := lambda1_gt_half hn hs
  have hlpos : 0<lambda1 n (2*s) := by linarith
  have hi : (lambda1 n (2*s))⁻¹≤2 := (inv_le_iff_one_le_mul₀ hlpos).mpr (by linarith)
  have hi0 := inv_nonneg.mpr hlpos.le
  nlinarith

theorem slackCoefficient_nonnegative {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (b0 : ℝ) (U : Finset (Fin n)) (i : Fin n) : 0≤slackCoefficient s b0 U i := by
  have hl2 := lambda2_nonnegative hn (show 1≤2*s by omega)
  have hl2u := lambda2_le_one (k:=2*s) hn
  have hi := inverse_lambda_sq_le_four hn hs
  have hisq := sq_nonneg ((lambda1 n (2*s))⁻¹)
  have ha : 0≤4-(lambda1 n (2*s))⁻¹^2*lambda2 n (2*s) := by nlinarith
  have hb : 0≤4-(lambda1 n (2*s))⁻¹^2*(1-lambda2 n (2*s)) := by nlinarith
  unfold slackCoefficient
  apply mul_nonneg (sq_nonneg _)
  apply add_nonneg
  · apply mul_nonneg ha
    split_ifs <;> norm_num
  · exact mul_nonneg hb (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem weightedSquares_eval {n : ℕ} (a b : ℝ) (U : Finset (Fin n)) (x : Fin n → ℝ) :
    eval x (weightedSquares (fun i ↦ a*(if i∈U then 1 else 0)+b))=
      a*(∑i∈U,x i^2)+b*(∑i,x i^2) := by
  classical
  have hU : (∑i, if i∈U then x i^2 else 0)=∑i∈U,x i^2 := by
    calc
      (∑i, if i∈U then x i^2 else 0)=∑i∈U,if i∈U then x i^2 else 0 :=
        (Finset.sum_subset (Finset.subset_univ U) (by intro i _ hi;simp [hi])).symm
      _ = _ := by apply Finset.sum_congr rfl;intro i hi;simp [hi]
  simp only [weightedSquares,eval_sum,eval_mul,eval_C,eval_pow,eval_X]
  have hpoint (i : Fin n) : (a*(if i∈U then 1 else 0)+b)*x i^2=
      a*(if i∈U then x i^2 else 0)+b*x i^2 := by
    by_cases hi:i∈U
    · simp [hi,add_mul]
    · simp [hi]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hU]

theorem blockWeight_eval {n : ℕ} (U : Finset (Fin n)) (x : Sphere n) :
    eval (fun i ↦ x.1 i) (blockWeight U)=blockRadius U x.1+rho U := by
  have hx := SphereMeasure.coordinates_unitSphere x
  change (∑i,x.1 i^2)=1 at hx
  simpa only [blockWeight,one_mul,mul_one,hx,blockRadius] using
    weightedSquares_eval 1 (rho U) U (fun i ↦ x.1 i)

theorem slackPolynomial_eval {n : ℕ} (s : ℕ) (b0 : ℝ) (U : Finset (Fin n)) (x : Sphere n) :
    eval (fun i ↦ x.1 i) (weightedSquares (slackCoefficient s b0 U))=
      4*b0^2*(blockRadius U x.1+rho U)-
        (lambda1 n (2*s))⁻¹^2*b0^2*
          (lambda2 n (2*s)*blockRadius U x.1+(1-lambda2 n (2*s))*rho U) := by
  have hx := SphereMeasure.coordinates_unitSphere x
  change (∑i,x.1 i^2)=1 at hx
  have hcoeff : slackCoefficient s b0 U=(fun i ↦
      (b0^2*(4-(lambda1 n (2*s))⁻¹^2*lambda2 n (2*s)))*(if i∈U then 1 else 0)+
      b0^2*(4-(lambda1 n (2*s))⁻¹^2*(1-lambda2 n (2*s)))*rho U) := by
    funext i
    unfold slackCoefficient
    ring
  rw [hcoeff,weightedSquares_eval,hx,mul_one]
  unfold blockRadius
  ring

def radialBound {n d e : ℕ} (s : ℕ) (budget : ℝ) (w : P n)
    (M : Matrix (Fin d) (Fin e) (P n)) : Matrix (Fin d) (Fin d) (P n) := fun u v ↦
  (Foundation.radiusPolynomial n)^(s+1)*
    (C budget*(Foundation.radiusPolynomial n)^(2*s-2)*w*(if u=v then 1 else 0)-
      ∑k, M u k*M v k)

theorem radialBound_homogeneous {n d e s : ℕ} (hs : 1 ≤ s) (budget : ℝ) (w : P n)
    (hw : w.IsHomogeneous 2) (M : Matrix (Fin d) (Fin e) (P n))
    (hM : ∀ u k, (M u k).IsHomogeneous (2 * s - 1)) (u v : Fin d) :
    (radialBound s budget w M u v).IsHomogeneous (2*(3*s)) := by
  have htop : (C budget*(Foundation.radiusPolynomial n)^(2*s-2)*w*
      (if u=v then 1 else 0)).IsHomogeneous (4*s-2) := by
    have hd : 2*(2*s-2)+2=4*s-2 := by omega
    have hq := (((HomogeneousSphereBounds.radius_homogeneous n).pow (2*s-2)).C_mul budget).mul hw
    by_cases huv : u=v
    · simpa only [ite_eq_left huv,mul_one,hd] using hq
    · simp only [ite_eq_right huv,mul_zero]
      exact isHomogeneous_zero _ _ _
  have hsum : (∑k, M u k*M v k).IsHomogeneous (4*s-2) := by
    apply IsHomogeneous.sum
    intro k _
    have hd : (2*s-1)+(2*s-1)=4*s-2 := by omega
    simpa only [hd] using (hM u k).mul (hM v k)
  have hd : 2*(s+1)+(4*s-2)=2*(3*s) := by omega
  exact hd ▸ ((HomogeneousSphereBounds.radius_homogeneous n).pow (s+1)).mul (htop.sub hsum)

theorem radialBound_eval_sphere {n d e s : ℕ} (budget : ℝ) (w : P n)
    (M : Matrix (Fin d) (Fin e) (P n)) (x : Fin n → ℝ) (hx : x ∈ Foundation.unitSphere n)
    (u v : Fin d) :
    eval x (radialBound s budget w M u v)=
      budget*eval x w*(if u=v then 1 else 0)-∑k, eval x (M u k)*eval x (M v k) := by
  have hR : eval x (Foundation.radiusPolynomial n)=1 := by simpa [Foundation.unitSphere] using hx
  simp only [radialBound,eval_mul,eval_pow,eval_C,hR,one_pow,one_mul,mul_one,
    eval_sub,eval_sum,apply_ite (eval x),map_one,map_zero]

theorem exists_corrected_matrix_sphereSOS {n s d e : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    {b0 : ℝ} (hb0 : 0 ≤ b0) (U : Finset (Fin n))
    (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (hFmeas : ∀ u v, Measurable (fun y ↦ F y u v))
    (hFnorm : ∀ y, ‖F y‖ ≤ blockBound b0 U y) (hodd : ∀ y, F (antipode y) = -F y) :
    ∃ N : Matrix (Fin d) (Fin d) (P n), BoundedMatrixSOS (3*s) N ∧
      ∀x : Sphere n,∀u v,eval (fun i ↦ x.1 i) (N u v)=
        (4*b0^2)*eval (fun i ↦ x.1 i) (blockWeight U)*(if u=v then 1 else 0)-
          ∑k,eval (fun i ↦ x.1 i) (correctedMean (s:=s) F u k)*
            eval (fun i ↦ x.1 i) (correctedMean (s:=s) F v k) := by
  have hspos : 1≤s := by omega
  obtain ⟨N,hN,hNeval⟩ := block_field_kernel_sphereSOS (s:=s) hn hb0 U F hFmeas hFnorm
  let c : ℝ := (lambda1 n (2*s))⁻¹^2
  let p := weightedSquares (slackCoefficient s b0 U)
  have hp : BoundedSOS 1 p := weightedSquares_sos _ (slackCoefficient_nonnegative hn hs b0 U)
  have hdiag : BoundedMatrixSOS (3*s) (p • (1:Matrix (Fin d) (Fin d) (P n))) :=
    (scalarSOS_diagonal hp).mono (by omega)
  have hscaled : BoundedMatrixSOS (3*s) ((C c:P n) • N) := matrixSOS_scale hN (sq_nonneg _)
  refine ⟨(C c:P n) • N+p • (1:Matrix (Fin d) (Fin d) (P n)),hscaled.add hdiag,?_⟩
  have hFbound : ∀y, ‖F y‖≤b0 := fun y ↦ (hFnorm y).trans (blockBound_le hb0 U y)
  intro x u v
  have hx := SphereMeasure.coordinates_unitSphere x
  have hcorr (i : Fin d) (k : Fin e) := correctedMean_eval_sphere (by omega : 0<n)
    hspos F hFmeas hFbound hodd (fun j ↦ x.1 j) hx i k
  have hsum : (∑k,eval (fun i ↦ x.1 i) (correctedMean (s:=s) F u k)*
      eval (fun i ↦ x.1 i) (correctedMean (s:=s) F v k))=
      c*(∑k,eval (fun i ↦ x.1 i) (mean (s:=s) F u k)*
        eval (fun i ↦ x.1 i) (mean (s:=s) F v k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hcorr,hcorr]
    dsimp only [c]
    ring
  simp only [Matrix.add_apply,eval_add,Matrix.smul_apply,smul_eq_mul,eval_mul,eval_C,
    Matrix.one_apply,apply_ite (eval (fun i ↦ x.1 i)),map_one,map_zero]
  rw [hNeval x u v,hsum,blockWeight_eval U x]
  change c*(_)+eval (fun i ↦ x.1 i) (weightedSquares (slackCoefficient s b0 U))*_=_
  rw [slackPolynomial_eval s b0 U x]
  dsimp only [c,rho,mean]
  ring

/-- Actual global homogeneous matrix SOS with the pure Euclidean radius
multiplier, corrected eigenvalue, and4b0² block budget. No SOS input or
analytic smoothing premise is assumed. -/
theorem homogeneous_matrix_smoothing_bound {n s d e : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    {b0 : ℝ} (hb0 : 0 ≤ b0) (U : Finset (Fin n))
    (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (hFmeas : ∀ u v, Measurable (fun y ↦ F y u v))
    (hFnorm : ∀ y, ‖F y‖ ≤ blockBound b0 U y) (hodd : ∀ y, F (antipode y) = -F y) :
    BoundedMatrixSOS (3*s) (radialBound s (4*b0^2) (blockWeight U) (correctedMean (s:=s) F)) := by
  have hspos : 1≤s := by omega
  obtain ⟨N,⟨m,a,ha,hid⟩,hNeval⟩ := exists_corrected_matrix_sphereSOS hn hs hb0 U F hFmeas hFnorm
    hodd
  apply homogeneous_matrix_sos_from_sphere (by omega : 1≤3*s) _
    (radialBound_homogeneous hspos _ _ (weightedSquares_homogeneous _) _
      (correctedMean_homogeneous F)) a ha
  intro x hx u v
  let z : E n := (WithLp.equiv 2 ((Fin n)→ℝ)).symm x
  have hsq : ‖z‖^2=1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa only [z,WithLp.equiv_symm_apply, PiLp.toLp_apply,Real.norm_eq_abs,sq_abs,
      Foundation.unitSphere,Set.mem_ofPred_eq] using hx
  have hz : ‖z‖=1 := by nlinarith [norm_nonneg z]
  let q : Sphere n := ⟨z,by simpa only [Metric.mem_sphere,dist_zero_right] using hz⟩
  have he := hNeval q u v
  have hSphere : eval x (radialBound s (4*b0^2) (blockWeight U) (correctedMean (s:=s) F) u v)=eval
    x (N u v) := by
    rw [radialBound_eval_sphere _ _ _ x hx]
    simpa only [q,z,WithLp.equiv_symm_apply, PiLp.toLp_apply] using he.symm
  change eval x (radialBound s (4*b0^2) (blockWeight U) (correctedMean (s:=s) F) u v)=_
  rw [hSphere,hid]
  simp only [Matrix.sum_apply,outer,eval_sum,eval_mul]

end HomogeneousMatrixBound
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
