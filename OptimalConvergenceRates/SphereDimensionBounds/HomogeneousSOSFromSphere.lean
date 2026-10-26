import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.HomogeneousSphereBounds
import OptimalConvergenceRates.SphereDimensionBounds.ChebyshevSOSKernel
import OptimalConvergenceRates.SphereDimensionBounds.FiniteMatrixVariance

/-! Exact parity-preserving homogenization of actual sphere SOS roots.
Every polynomial and root budget is constructed explicitly. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.HomogeneousSOSFromSphere

open scoped BigOperators
open MvPolynomial OptimalConvergenceRates.SphereDimensionBounds.Foundation ChebyshevSOSKernel HomogeneousSphereBounds

abbrev P (n : ℕ) := OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n

theorem sum_components_to_bound {n r : ℕ} (p : P n) (hp : p.totalDegree ≤ r) :
    (∑ j ∈ Finset.range (r+1),homogeneousComponent j p)=p := by
  classical
  calc
    (∑ j ∈ Finset.range (r+1),homogeneousComponent j p)=
        ∑ j ∈ Finset.range (p.totalDegree+1),homogeneousComponent j p := by
      symm
      apply Finset.sum_subset
      · exact Finset.range_mono (by omega)
      · intro j hj hjnot
        exact homogeneousComponent_eq_zero j p (by
          have hnot : ¬j<p.totalDegree+1 := by simpa using hjnot
          omega)
    _=p := sum_homogeneousComponent p

def radialHomogenize {n : ℕ} (p : P n) (r : ℕ) : P n :=
  ∑ j ∈ Finset.range (r+1),if j%2=r%2 then
    (radiusPolynomial n)^((r-j)/2)*homogeneousComponent j p else 0

theorem radialHomogenize_homogeneous {n : ℕ} (p : P n) (r : ℕ) :
    (radialHomogenize p r).IsHomogeneous r := by
  classical
  apply IsHomogeneous.sum
  intro j hj
  by_cases hpar : j%2=r%2
  · simp only [ite_eq_left hpar]
    have hjr : j≤r := by have hh := Finset.mem_range.mp hj; omega
    have hdegree : 2*((r-j)/2)+j=r := by omega
    simpa only [hdegree] using ((radius_homogeneous n).pow ((r-j)/2)).mul
      (homogeneousComponent_isHomogeneous j p)
  · simp only [ite_eq_right hpar]
    exact isHomogeneous_zero (Fin n) ℝ r

theorem radialHomogenize_eval_sphere {n : ℕ} (p : P n) (r : ℕ)
    (x : Fin n → ℝ) (hx : x ∈ unitSphere n) :
    eval x (radialHomogenize p r)=
      ∑ j ∈ Finset.range (r+1),if j%2=r%2 then eval x (homogeneousComponent j p) else 0 := by
  classical
  have hR : eval x (radiusPolynomial n)=1 := by
    rw [OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial_eval]
    exact hx
  simp only [radialHomogenize,eval_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hpar <;> simp [hR]

theorem radialHomogenize_add {n : ℕ} (p q : P n) (r : ℕ) :
    radialHomogenize (p+q) r=radialHomogenize p r+radialHomogenize q r := by
  classical
  unfold radialHomogenize
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp only [map_add,mul_add,add_zero]

theorem radialHomogenize_pair_eval {n r : ℕ} (hr : 1 ≤ r) (p : P n)
    (hp : p.totalDegree ≤ r) (x : Fin n → ℝ) (hx : x ∈ unitSphere n) :
    eval x (radialHomogenize p r)+eval x (radialHomogenize p (r-1))=eval x p := by
  classical
  rw [radialHomogenize_eval_sphere p r x hx,
    radialHomogenize_eval_sphere p (r-1) x hx]
  have hpred : (r-1)%2≠r%2 := by omega
  have hsum : (∑ j ∈ Finset.range ((r-1)+1),
      if j%2=(r-1)%2 then eval x (homogeneousComponent j p) else 0)=
      ∑ j ∈ Finset.range (r+1),
        if j%2=(r-1)%2 then eval x (homogeneousComponent j p) else 0 := by
    rw [show r-1+1=r by omega,Finset.sum_range_succ]
    simp only [ite_eq_right (Ne.symm hpred),add_zero]
  rw [hsum,←Finset.sum_add_distrib]
  have heval := congrArg (eval x) (sum_components_to_bound p hp)
  rw [eval_sum] at heval
  rw [←heval]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hpar : j%2=r%2
  · simp only [ite_eq_left hpar,ite_eq_right (by omega : j%2≠(r-1)%2),add_zero]
  · simp only [ite_eq_right hpar,ite_eq_left (by omega : j%2=(r-1)%2),zero_add]

theorem neg_point_sphere {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ unitSphere n) :
    (fun i => -x i) ∈unitSphere n := by
  simpa only [unitSphere,Set.mem_ofPred_eq,neg_sq] using hx

/-- The two parity classes give the exact average of the original root
square at antipodal points, before summing any certificate. -/
theorem parity_square_identity {n r : ℕ} (hr : 1 ≤ r) (p : P n)
    (hp : p.totalDegree ≤ r) (x : Fin n → ℝ) (hx : x ∈ unitSphere n) :
    2*(eval x (radialHomogenize p r)^2+eval x (radialHomogenize p (r-1))^2)=
      eval x p^2+eval (fun i => -x i) p^2 := by
  have hsum := radialHomogenize_pair_eval hr p hp x hx
  have hneg := radialHomogenize_pair_eval hr p hp (fun i => -x i) (neg_point_sphere hx)
  have hscale (q : P n) (k : ℕ) (hq : q.IsHomogeneous k) :
      eval (fun i => -x i) q=(-1:ℝ)^k*eval x q := by
    simpa only [neg_one_mul] using homogeneous_eval_scale q k hq (-1) x
  rw [hscale _ _ (radialHomogenize_homogeneous p r),
    hscale _ _ (radialHomogenize_homogeneous p (r-1))] at hneg
  have hsign : (-1:ℝ)^r=-(-1:ℝ)^(r-1) := by
    calc
      (-1:ℝ)^r=(-1:ℝ)^((r-1)+1) := congrArg (fun k => (-1:ℝ)^k) (by omega)
      _=_ := by rw [pow_succ];ring
  have hsignsq : ((-1:ℝ)^(r-1))^2=1 := by
    rw [←pow_mul,mul_comm (r-1) 2,pow_mul]
    norm_num
  rw [hsign] at hneg
  have hnegsq : eval (fun i => -x i) p^2=
      (eval x (radialHomogenize p r)-eval x (radialHomogenize p (r-1)))^2 := by
    rw [←hneg]
    calc
      (-((-1:ℝ)^(r-1))*eval x (radialHomogenize p r)+
          (-1:ℝ)^(r-1)*eval x (radialHomogenize p (r-1)))^2=
          ((-1:ℝ)^(r-1))^2*(eval x (radialHomogenize p r)-
            eval x (radialHomogenize p (r-1)))^2 := by ring
      _=_ := by rw [hsignsq,one_mul]
  rw [←hsum,hnegsq]
  ring

theorem parity_product_identity {n r : ℕ} (hr : 1 ≤ r) (p q : P n)
    (hp : p.totalDegree ≤ r) (hq : q.totalDegree ≤ r)
    (x : Fin n → ℝ) (hx : x ∈ unitSphere n) :
    2*(eval x (radialHomogenize p r)*eval x (radialHomogenize q r)+
      eval x (radialHomogenize p (r-1))*eval x (radialHomogenize q (r-1)))=
      eval x p*eval x q+eval (fun i => -x i) p*eval (fun i => -x i) q := by
  have hpq : (p+q).totalDegree≤r := (totalDegree_add _ _).trans (max_le hp hq)
  have hboth := parity_square_identity hr (p+q) hpq x hx
  have hpone := parity_square_identity hr p hp x hx
  have hqone := parity_square_identity hr q hq x hx
  simp only [radialHomogenize_add,eval_add] at hboth
  linear_combination hboth/2-hpone/2-hqone/2

/-- Positive-degree homogeneous polynomials agreeing on the full unit sphere
agree as actual ambient polynomials. -/
theorem homogeneous_eq_of_sphere_eq {n d : ℕ} (hd : 0 < d) (p q : P n)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d)
    (heq : ∀ x ∈ unitSphere n, eval x p = eval x q) : p=q := by
  apply MvPolynomial.funext
  intro x
  classical
  let S : ℝ := ∑ i,x i^2
  have hS : 0≤S := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hz : S=0
  · have hx : x=fun _ => 0 := by
      funext i
      have hi : x i^2≤S := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      have hxi : x i=0 := by nlinarith [sq_nonneg (x i)]
      exact hxi
    have hpzero := homogeneous_eval_scale p d hp 0 x
    have hqzero := homogeneous_eval_scale q d hq 0 x
    simp only [zero_mul,zero_pow (Nat.ne_of_gt hd)] at hpzero hqzero
    rw [hx,hpzero,hqzero]
  · have hSpos : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
    let c : ℝ := Real.sqrt S
    have hc : 0<c := Real.sqrt_pos.mpr hSpos
    have hcsq : c^2=S := Real.sq_sqrt hS
    let y : Fin n → ℝ := fun i => x i/c
    have hy : y ∈unitSphere n := by
      change (∑ i,y i^2)=1
      simp only [y,div_pow,←Finset.sum_div]
      rw [hcsq]
      exact div_self hz
    have hcy : (fun i => c*y i)=x := by
      funext i
      dsimp [y]
      field_simp
    have hpScale := homogeneous_eval_scale p d hp c y
    have hqScale := homogeneous_eval_scale q d hq c y
    rw [hcy] at hpScale hqScale
    rw [hpScale,hqScale,heq y hy]

def homogenizedRoot {n r : ℕ} {J : Type*} (h : J → P n) :
    J ⊕ (J × Fin n) → P n :=
  Sum.elim (fun j => radialHomogenize (h j) r)
    (fun z => X z.2*radialHomogenize (h z.1) (r-1))

theorem homogenizedRoot_homogeneous {n r : ℕ} {J : Type*} (hr : 1 ≤ r)
    (h : J → P n) (z : J ⊕ (J × Fin n)) : (homogenizedRoot (r:=r) h z).IsHomogeneous r := by
  cases z with
  | inl j => exact radialHomogenize_homogeneous (h j) r
  | inr z =>
      change (X z.2*radialHomogenize (h z.1) (r-1)).IsHomogeneous r
      simpa only [show 1+(r-1)=r by omega] using
        (isHomogeneous_X ℝ z.2).mul (radialHomogenize_homogeneous (h z.1) (r-1))

theorem homogeneous_square_representation {n r : ℕ} {J : Type*} [Fintype J]
    (hr : 1 ≤ r) (p : P n) (hp : p.IsHomogeneous (2 * r))
    (h : J → P n) (hh : ∀ j, (h j).totalDegree ≤ r)
    (hsphere : ∀ x ∈ unitSphere n, eval x p = ∑ j, eval x (h j) ^ 2) :
    p=∑ z : J ⊕ (J × Fin n),homogenizedRoot (r:=r) h z^2 := by
  apply homogeneous_eq_of_sphere_eq (by omega) p _ hp
  · apply IsHomogeneous.sum
    intro z hz
    simpa only [Nat.mul_comm] using (homogenizedRoot_homogeneous hr h z).pow 2
  · intro x hx
    have hpneg : eval (fun i => -x i) p=eval x p := by
      have hs := homogeneous_eval_scale p (2*r) hp (-1) x
      simpa only [neg_one_mul,pow_mul,neg_one_sq,one_pow,one_mul] using hs
    have havg : 2*eval x p=∑ j,2*(eval x (radialHomogenize (h j) r)^2+
        eval x (radialHomogenize (h j) (r-1))^2) := by
      calc
        2*eval x p=eval x p+eval (fun i => -x i) p := by rw [hpneg];ring
        _=(∑ j,eval x (h j)^2)+(∑ j,eval (fun i => -x i) (h j)^2) := by
          rw [hsphere x hx,hsphere _ (neg_point_sphere hx)]
        _=∑ j,(eval x (h j)^2+eval (fun i => -x i) (h j)^2) := by rw [Finset.sum_add_distrib]
        _=_ := by apply Finset.sum_congr rfl;intro j hj;exact (parity_square_identity hr (h j) (hh j) x hx).symm
    have hsum : eval x p=∑ j,(eval x (radialHomogenize (h j) r)^2+
        eval x (radialHomogenize (h j) (r-1))^2) := by
      rw [←Finset.mul_sum] at havg
      linarith
    rw [hsum]
    simp only [eval_add,eval_sum,eval_pow,Fintype.sum_sum_type,Fintype.sum_prod_type,
      homogenizedRoot,Sum.elim_inl,Sum.elim_inr,eval_mul,eval_X,mul_pow,
      Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hxsum : (∑ i,x i^2)=1 := hx
    rw [←Finset.sum_mul,hxsum,one_mul]

/-- Lemma 1.4 with an actual bounded finite sphere square family. The output
is a global homogeneous polynomial identity with exactly the same root order. -/
theorem homogeneous_sos_from_sphere {n r : ℕ} {J : Type*} [Fintype J]
    (hr : 1 ≤ r) (p : P n) (hp : p.IsHomogeneous (2 * r))
    (h : J → P n) (hh : ∀ j, (h j).totalDegree ≤ r)
    (hsphere : ∀ x ∈ unitSphere n, eval x p = ∑ j, eval x (h j) ^ 2) :
    BoundedSOS r p := by
  rw [homogeneous_square_representation hr p hp h hh hsphere]
  exact BoundedSOS.of_family _ (fun z => (homogenizedRoot_homogeneous hr h z).totalDegree_le)

/-- Matrix parity homogenization uses the same parity split for all
coordinates of each actual vector root. -/
theorem homogeneous_matrix_representation {n d r : ℕ} {J : Type*} [Fintype J]
    (hr : 1 ≤ r) (M : Matrix (Fin d) (Fin d) (P n))
    (hM : ∀ u v, (M u v).IsHomogeneous (2 * r))
    (h : J → Fin d → P n) (hh : ∀ j u, (h j u).totalDegree ≤ r)
    (hsphere : ∀ x ∈ unitSphere n, ∀ u v, eval x (M u v) =
      ∑ j, eval x (h j u) * eval x (h j v)) :
    M=∑ z : J ⊕ (J × Fin n),FiniteMatrixVariance.outer
      (fun u => homogenizedRoot (r:=r) (fun j => h j u) z) := by
  apply Matrix.ext
  intro u v
  simp only [Matrix.sum_apply,FiniteMatrixVariance.outer]
  apply homogeneous_eq_of_sphere_eq (by omega) _ _ (hM u v)
  · apply IsHomogeneous.sum
    intro z hz
    simpa only [two_mul] using
      (homogenizedRoot_homogeneous hr (fun j => h j u) z).mul
        (homogenizedRoot_homogeneous hr (fun j => h j v) z)
  · intro x hx
    have hneg : eval (fun i => -x i) (M u v)=eval x (M u v) := by
      have hs := homogeneous_eval_scale (M u v) (2*r) (hM u v) (-1) x
      simpa only [neg_one_mul,pow_mul,neg_one_sq,one_pow,one_mul] using hs
    have havg : 2*eval x (M u v)=∑ j,2*
        (eval x (radialHomogenize (h j u) r)*eval x (radialHomogenize (h j v) r)+
          eval x (radialHomogenize (h j u) (r-1))*eval x (radialHomogenize (h j v) (r-1))) := by
      calc
        2*eval x (M u v)=eval x (M u v)+eval (fun i => -x i) (M u v) := by rw [hneg];ring
        _=_ := by
          rw [hsphere x hx,hsphere _ (neg_point_sphere hx),←Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          exact (parity_product_identity hr (h j u) (h j v) (hh j u) (hh j v) x hx).symm
    have hsum : eval x (M u v)=∑ j,
        (eval x (radialHomogenize (h j u) r)*eval x (radialHomogenize (h j v) r)+
          eval x (radialHomogenize (h j u) (r-1))*eval x (radialHomogenize (h j v) (r-1))) := by
      rw [←Finset.mul_sum] at havg
      linarith
    rw [hsum]
    simp only [eval_add,eval_sum,eval_mul,Fintype.sum_sum_type,Fintype.sum_prod_type,
      homogenizedRoot,Sum.elim_inl,Sum.elim_inr,eval_X,Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hpoint (i : Fin n) :
        (x i*eval x (radialHomogenize (h j u) (r-1)))*
          (x i*eval x (radialHomogenize (h j v) (r-1)))=
        x i^2*(eval x (radialHomogenize (h j u) (r-1))*
          eval x (radialHomogenize (h j v) (r-1))) := by ring
    simp_rw [hpoint]
    have hxsum : (∑ i,x i^2)=1 := hx
    rw [←Finset.sum_mul,hxsum,one_mul]

theorem homogeneous_matrix_sos_from_sphere {n d r : ℕ} {J : Type*} [Fintype J]
    (hr : 1 ≤ r) (M : Matrix (Fin d) (Fin d) (P n))
    (hM : ∀ u v, (M u v).IsHomogeneous (2 * r))
    (h : J → Fin d → P n) (hh : ∀ j u, (h j u).totalDegree ≤ r)
    (hsphere : ∀ x ∈ unitSphere n, ∀ u v, eval x (M u v) =
      ∑ j, eval x (h j u) * eval x (h j v)) :
    FiniteMatrixVariance.BoundedMatrixSOS r M := by
  rw [homogeneous_matrix_representation hr M hM h hh hsphere]
  exact FiniteMatrixVariance.BoundedMatrixSOS.of_family _
    (fun z u => (homogenizedRoot_homogeneous hr (fun j => h j u) z).totalDegree_le)

end OptimalConvergenceRates.SphereDimensionBounds.HomogeneousSOSFromSphere
