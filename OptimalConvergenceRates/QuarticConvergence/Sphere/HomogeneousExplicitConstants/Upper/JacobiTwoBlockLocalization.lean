import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.JacobiCoefficientBounds
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.ParabolicPathVector
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.MatrixTwoEigenvalues

/-! Two explicit positive parabolic coordinate blocks localize two
actual eigenvalues of the actual Gegenbauer Jacobi matrix. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace JacobiTwoBlockLocalization

open scoped BigOperators InnerProductSpace
open Matrix GegenbauerJacobi ParabolicPathVector MatrixTwoEigenvalues

def placedVector {ell L : ℕ} (e : Fin L → Fin ell) (x : Fin L → ℝ) : E ell :=
  ∑k, x k • EuclideanSpace.single (e k) (1:ℝ)

theorem placedVector_inner {ell L K : ℕ} (e : Fin L → Fin ell) (f : Fin K → Fin ell)
    (x : Fin L → ℝ) (y : Fin K → ℝ) :
    ⟪placedVector e x,placedVector f y⟫_ℝ=
      ∑k,∑l, x k*y l*(if e k=f l then 1 else 0) := by
  simp only [placedVector,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    EuclideanSpace.inner_single_left,PiLp.single_apply,map_one,star_trivial,one_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases h:e k=f l <;> simp [h,eq_comm,mul_assoc,mul_comm]

theorem placedVector_norm_sq {ell L : ℕ} (e : Fin L → Fin ell) (he : Function.Injective e)
    (x : Fin L → ℝ) : ‖placedVector e x‖^2=∑k,x k^2 := by
  rw [←real_inner_self_eq_norm_sq,placedVector_inner]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single k]
  · simp
    ring
  · intro l _ hl
    have hne : e k≠e l := fun h ↦ hl (he h).symm
    simp [hne]
  · simp

theorem placedVector_bilinear {ell L K : ℕ} (A : Matrix (Fin ell) (Fin ell) ℝ)
    (e : Fin L → Fin ell) (f : Fin K → Fin ell) (x : Fin L → ℝ) (y : Fin K → ℝ) :
    ⟪placedVector e x,Matrix.toEuclideanLin A (placedVector f y)⟫_ℝ=
      ∑k,∑l, x k*y l*A (e k) (f l) := by
  simp only [placedVector,map_sum,map_smul,sum_inner,inner_sum,
    real_inner_smul_left,real_inner_smul_right,EuclideanSpace.inner_single_left,
    map_one,star_trivial,one_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change y l*(x k*(A *ᵥ Pi.single (f l) (1:ℝ)) (e k))=_
  rw [Matrix.mulVec_single_one]
  change y l * (x k * A (e k) (f l)) = _
  ring

def blockEmbedding {ell L : ℕ} (a : ℕ) (ha : a + L ≤ ell) : Fin L→Fin ell :=
  fun k ↦ ⟨a+k.val,by omega⟩

theorem blockEmbedding_injective {ell L : ℕ} (a : ℕ) (ha : a + L ≤ ell) :
    Function.Injective (blockEmbedding a ha) := by
  intro i j hij
  have h := congrArg Fin.val hij
  exact Fin.ext (by dsimp [blockEmbedding] at h;omega)

def block {ell L : ℕ} (a : ℕ) (ha : a + L ≤ ell) : E ell :=
  placedVector (blockEmbedding a ha) (fun k ↦ value (L+1) (k.val+1))

theorem squareSum_shift (L : ℕ) :
    (∑k : Fin L,value (L+1) (k.val+1)^2)=squareSum (L+1) := by
  rw [squareSum,Finset.sum_range_succ']
  simp only [value_zero,zero_pow (by decide : 2≠0),add_zero,zero_add]
  exact (Finset.sum_range (fun k ↦ value (L+1) (k+1)^2)).symm

theorem adjacentSum_shift (L : ℕ) :
    (∑k : Fin L,value (L+1) (k.val+1)*value (L+1) (k.val+2))=adjacentSum (L+1) := by
  rw [adjacentSum,Finset.sum_range_succ']
  simp only [value_zero,zero_mul,add_zero,zero_add,Nat.add_assoc]
  exact (Finset.sum_range (fun k ↦ value (L+1) (k+1)*value (L+1) (k+2))).symm

theorem block_norm_sq {ell L : ℕ} (a : ℕ) (ha : a + L ≤ ell) :
    ‖block a ha‖^2=squareSum (L+1) := by
  rw [block,placedVector_norm_sq _ (blockEmbedding_injective a ha),squareSum_shift]

theorem block_nonzero {ell L : ℕ} (hL : 1 ≤ L) (a : ℕ) (ha : a + L ≤ ell) :
    block a ha≠0 := by
  intro hzero
  have hp := squareSum_pos (by omega : 2≤L+1)
  rw [←block_norm_sq a ha,hzero,norm_zero,zero_pow (by decide : 2≠0)] at hp
  exact (lt_irrefl 0) hp

theorem block_orthogonal {ell L : ℕ} (a b : ℕ) (ha : a + L ≤ ell) (hb : b + L ≤ ell)
    (hab : a + L ≤ b) : ⟪block a ha,block b hb⟫_ℝ=0 := by
  rw [block,block,placedVector_inner]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  have hne : blockEmbedding a ha k≠blockEmbedding b hb l := by
    intro h
    have hh := congrArg Fin.val h
    dsimp [blockEmbedding] at hh
    omega
  simp [hne]

theorem block_cross_zero {N ell L : ℕ} (a b : ℕ) (ha : a + L ≤ ell) (hb : b + L ≤ ell)
    (hab : a + L + 1 ≤ b) :
    ⟪block a ha,Matrix.toEuclideanLin (jacobi N ell) (block b hb)⟫_ℝ=0 := by
  rw [block,block,placedVector_bilinear]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  have h1 : ¬a+k.val+1=b+l.val := by omega
  have h2 : ¬b+l.val+1=a+k.val := by omega
  simp [jacobi,blockEmbedding,h1,h2]

theorem jacobi_block_entry {N ell L : ℕ} (a : ℕ) (ha : a + L ≤ ell) (k l : Fin L) :
    jacobi N ell (blockEmbedding a ha k) (blockEmbedding a ha l)=
      (if k.val+1=l.val then coefficient N (a+k.val) else 0)+
      (if l.val+1=k.val then coefficient N (a+l.val) else 0) := by
  have h1 : a+k.val+1=a+l.val ↔ k.val+1=l.val := by omega
  have h2 : a+l.val+1=a+k.val ↔ l.val+1=k.val := by omega
  simp only [jacobi,blockEmbedding,h1,h2]
  by_cases hk : k.val+1=l.val
  · have hl : ¬l.val+1=k.val := by omega
    simp [hk,hl]
  · by_cases hl : l.val+1=k.val <;> simp [hk,hl]

theorem forward_sum (N a L : ℕ) (k : Fin L) :
    (∑l : Fin L,value (L+1) (k.val+1)*value (L+1) (l.val+1)*
      (if k.val+1=l.val then coefficient N (a+k.val) else 0))=
        coefficient N (a+k.val)*value (L+1) (k.val+1)*value (L+1) (k.val+2) := by
  by_cases hh : k.val+1<L
  · let j : Fin L := ⟨k.val+1,hh⟩
    rw [Finset.sum_eq_single j]
    · simp only [j,ite_true,show k.val+1+1=k.val+2 by omega]
      ring
    · intro l _ hl
      have hne : ¬k.val+1=l.val := by
        intro h
        exact hl (Fin.ext h.symm)
      simp [hne]
    · simp
  · have hk : k.val+2=L+1 := by omega
    rw [hk,value_end,mul_zero]
    apply Finset.sum_eq_zero
    intro l _
    have hne : ¬k.val+1=l.val := by omega
    simp [hne]

theorem block_form {N ell L : ℕ} (a : ℕ) (ha : a + L ≤ ell) :
    form (jacobi N ell) (block a ha)=
      ∑k : Fin L,(2*coefficient N (a+k.val))*
        value (L+1) (k.val+1)*value (L+1) (k.val+2) := by
  rw [form,block,placedVector_bilinear]
  simp_rw [jacobi_block_entry,mul_add]
  simp_rw [Finset.sum_add_distrib]
  have hr :
      (∑k : Fin L,∑l : Fin L,value (L+1) (k.val+1)*value (L+1) (l.val+1)*
        (if l.val+1=k.val then coefficient N (a+l.val) else 0))=
      ∑k : Fin L,∑l : Fin L,value (L+1) (k.val+1)*value (L+1) (l.val+1)*
        (if k.val+1=l.val then coefficient N (a+k.val) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hr]
  simp_rw [forward_sum]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem block_form_lower {N ell L : ℕ} (hN : 15 ≤ N) (hell : 3 * N ≤ ell)
    (a : ℕ) (ha : a + L ≤ ell) (hstart : ell ≤ 3 * (a + 1)) :
    (1-(27/20:ℝ)*(N:ℝ)^2/(ell:ℝ)^2)*adjacentSum (L+1)≤
      form (jacobi N ell) (block a ha) := by
  rw [←adjacentSum_shift,block_form,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hc := JacobiCoefficientBounds.coefficient_lower hN hell
    (show ell≤3*(a+k.val+1) by omega)
  have hp : 0≤value (L+1) (k.val+1) := value_nonneg (by omega)
  have hq : 0≤value (L+1) (k.val+2) := value_nonneg (by omega)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (mul_nonneg hp hq)

theorem block_rayleigh {N ell L : ℕ} (hN : 15 ≤ N) (hell : 3 * N ≤ ell)
    (a : ℕ) (ha : a + L ≤ ell) (hstart : ell ≤ 3 * (a + 1)) (hsize : ell ≤ 3 * (L + 1)) :
    (1-(8/5:ℝ)*(N:ℝ)^2/(ell:ℝ)^2)*‖block a ha‖^2≤
      form (jacobi N ell) (block a ha) := by
  have hE : 0<ell := by omega
  have hER : 0<(ell:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hE)
  have hNR : (15:ℝ)≤N := by exact_mod_cast hN
  have hEL : 3*(N:ℝ)≤ell := by exact_mod_cast hell
  have hsquare : 9*(N:ℝ)^2≤(ell:ℝ)^2 := by nlinarith
  have hratio : (N:ℝ)^2/(ell:ℝ)^2≤1/9 := by
    apply (div_le_iff₀ hER).mpr
    nlinarith
  have hratio0 : 0≤(N:ℝ)^2/(ell:ℝ)^2 := div_nonneg (sq_nonneg _) hER.le
  have halpha : 0≤1-(27/20:ℝ)*(N:ℝ)^2/(ell:ℝ)^2 := by
    have heq : (27/20:ℝ)*(N:ℝ)^2/(ell:ℝ)^2=
        (27/20:ℝ)*((N:ℝ)^2/(ell:ℝ)^2) := by ring
    rw [heq]
    linarith
  have hdiv : 45/(ell:ℝ)^2≤(1/4:ℝ)*(N:ℝ)^2/(ell:ℝ)^2 := by
    apply (div_le_div_iff_of_pos_right hER).mpr
    nlinarith
  have hsmall : 0≤45/(ell:ℝ)^2 := by positivity
  have hproduct :
      1-(8/5:ℝ)*(N:ℝ)^2/(ell:ℝ)^2≤
        (1-(27/20:ℝ)*(N:ℝ)^2/(ell:ℝ)^2)*(1-45/(ell:ℝ)^2) := by
    let q : ℝ := (N:ℝ)^2/(ell:ℝ)^2
    let t : ℝ := 45/(ell:ℝ)^2
    have ht : t≤q/4 := by
      calc
        t≤(1/4:ℝ)*(N:ℝ)^2/(ell:ℝ)^2 := hdiv
        _=q/4 := by dsimp [q];ring
    have hg : 1-(8/5:ℝ)*q≤(1-(27/20:ℝ)*q)*(1-t) := by
      nlinarith only [ht,mul_nonneg (show 0≤q from hratio0) (show 0≤t from hsmall)]
    convert hg using 1 <;> dsimp [q,t] <;> ring
  have hnorm : 0≤squareSum (L+1) := Finset.sum_nonneg (fun k _ ↦ sq_nonneg _)
  rw [block_norm_sq]
  calc
    _≤((1-(27/20:ℝ)*(N:ℝ)^2/(ell:ℝ)^2)*(1-45/(ell:ℝ)^2))*squareSum (L+1) :=
      mul_le_mul_of_nonneg_right hproduct hnorm
    _≤(1-(27/20:ℝ)*(N:ℝ)^2/(ell:ℝ)^2)*adjacentSum (L+1) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (adjacentSum_lower hE hsize) halpha
    _≤_ := block_form_lower hN hell a ha hstart

theorem plane_rayleigh {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : E n)
    (huv : ⟪u, v⟫_ℝ = 0) (hvu : ⟪v, u⟫_ℝ = 0)
    (hcross : ⟪u, Matrix.toEuclideanLin A v⟫_ℝ = 0)
    (hcross' : ⟪v, Matrix.toEuclideanLin A u⟫_ℝ = 0) (c : ℝ)
    (hu : c * ‖u‖ ^ 2 ≤ form A u) (hv : c * ‖v‖ ^ 2 ≤ form A v) (α β : ℝ) :
    c*‖α • u+β • v‖^2≤form A (α • u+β • v) := by
  have hn : ‖α • u+β • v‖^2=α^2*‖u‖^2+β^2*‖v‖^2 := by
    rw [←real_inner_self_eq_norm_sq]
    simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
      huv,hvu,mul_zero,real_inner_self_eq_norm_sq,add_zero,zero_add,
      norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hf : form A (α • u+β • v)=α^2*form A u+β^2*form A v := by
    simp only [form,map_add,map_smul,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,hcross,hcross',mul_zero,add_zero,zero_add]
    ring
  rw [hn,hf]
  have h1 := mul_le_mul_of_nonneg_left hu (sq_nonneg α)
  have h2 := mul_le_mul_of_nonneg_left hv (sq_nonneg β)
  nlinarith only [h1,h2]

theorem jacobi_hermitian (N ell : ℕ) : (jacobi N ell).IsHermitian := by
  change (jacobi N ell).conjTranspose=jacobi N ell
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact jacobi_symmetric N ell

/-- Two distinct actual Jacobi eigenvalue indices lie within
8N²/(5ell²) of 1. All test vectors and the two-dimensional spectral
argument are constructed, without a sorted-spectrum premise. -/
theorem exists_two_localized_eigenvalues {N ell : ℕ} (hN : 15 ≤ N) (hell : 3 * N ≤ ell) :
    ∃i j : Fin ell,i≠j ∧
      1-(8/5:ℝ)*(N:ℝ)^2/(ell:ℝ)^2≤(jacobi_hermitian N ell).eigenvalues i ∧
      1-(8/5:ℝ)*(N:ℝ)^2/(ell:ℝ)^2≤(jacobi_hermitian N ell).eigenvalues j := by
  have hp := block_parameters (by omega : 5≤ell)
  let J := start ell
  let L := length ell
  have hL : 1≤L := hp.1
  have hfit0 : J+L≤ell := by dsimp [J,L];omega
  have hfit1 : J+L+1+L≤ell := by dsimp [J,L];omega
  let u : E ell := block J hfit0
  let v : E ell := block (J+L+1) hfit1
  have hu : u≠0 := block_nonzero hL J hfit0
  have hv : v≠0 := block_nonzero hL (J+L+1) hfit1
  have huv : ⟪u,v⟫_ℝ=0 := block_orthogonal J (J+L+1) hfit0 hfit1 (by omega)
  have hvu : ⟪v,u⟫_ℝ=0 := by rw [real_inner_comm];exact huv
  have hc : ⟪u,Matrix.toEuclideanLin (jacobi N ell) v⟫_ℝ=0 :=
    block_cross_zero J (J+L+1) hfit0 hfit1 (by omega)
  have hc' : ⟪v,Matrix.toEuclideanLin (jacobi N ell) u⟫_ℝ=0 := by
    have hs := (Matrix.isSymmetric_toEuclideanLin_iff.mpr (jacobi_hermitian N ell)) v u
    rw [←hs,real_inner_comm]
    exact hc
  have huq := block_rayleigh hN hell J hfit0 hp.2.2.2 hp.2.2.1
  have hvq := block_rayleigh hN hell (J+L+1) hfit1
    (show ell≤3*(J+L+1+1) by dsimp [J,L];omega) hp.2.2.1
  exact exists_two_eigenvalues (jacobi_hermitian N ell) u v hu hv huv _
    (plane_rayleigh (jacobi N ell) u v huv hvu hc hc' _ huq hvq)

end JacobiTwoBlockLocalization
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
