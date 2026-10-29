import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-! The real Hilbert-space diagonal bound for a symmetric multilinear form.
No polarization constant is introduced. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace BanachDiagonal

open scoped BigOperators InnerProductSpace
open Function

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem linear_norm_attainment (l : E →L[ℝ] ℝ) (x : E) (hx : ‖x‖ = 1)
    (M : ℝ) (hl : ‖l‖ ≤ M) (habs : |l x| = M) (z : E) :
    l z=(l x)*⟪x,z⟫_ℝ := by
  let w : E := (InnerProductSpace.toDual ℝ E).symm l
  have hwNorm : ‖w‖≤M := by
    simpa only [w,LinearIsometryEquiv.norm_map] using hl
  have hwx : ⟪w,x⟫_ℝ=l x := InnerProductSpace.toDual_symm_apply
  have hsq : (l x)^2=M^2 := by
    rw [←sq_abs (l x),habs]
  have hwSq : ‖w‖^2≤M^2 := pow_le_pow_left₀ (norm_nonneg _) hwNorm 2
  have hzSq : ‖w-(l x) • x‖^2≤0 := by
    rw [norm_sub_sq_real,real_inner_smul_right,hwx,norm_smul,hx,mul_one,
      Real.norm_eq_abs,sq_abs]
    nlinarith
  have hwEq : w=(l x) • x := sub_eq_zero.mp (norm_eq_zero.mp (by
    nlinarith [norm_nonneg (w-(l x) • x)]))
  have hwz : ⟪w,z⟫_ℝ=l z := InnerProductSpace.toDual_symm_apply
  rw [hwEq,real_inner_smul_left] at hwz
  exact hwz.symm

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem sum_update {d : ℕ} (v : Fin d → E) (i : Fin d) (x : E) :
    (∑ j,Function.update v i x j)=(∑ j,v j)-v i+x := by
  classical
  have hu := Finset.sum_update_of_mem (Finset.mem_univ i) v x
  have hv := Finset.sum_update_of_mem (Finset.mem_univ i) v (v i)
  simp only [Function.update_eq_self] at hv
  rw [hu,hv]
  abel

def pairUpdate {d : ℕ} (v : Fin d → E) (i j : Fin d) (x y : E) : Fin d → E :=
  Function.update (Function.update v i x) j y

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem pairUpdate_comm {d : ℕ} (v : Fin d → E) (i j : Fin d) (hij : i ≠ j) (x y : E) :
    pairUpdate v i j x y=pairUpdate v j i y x := by
  exact Function.update_comm hij x y v

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem pairUpdate_swap {d : ℕ} (v : Fin d → E) (i j : Fin d) (hij : i ≠ j) (x y : E) :
    pairUpdate v i j x y ∘ Equiv.swap i j=pairUpdate v i j y x := by
  classical
  funext k
  by_cases hki : k=i
  · subst k
    change pairUpdate v i j x y ((Equiv.swap i j) i)=pairUpdate v i j y x i
    rw [Equiv.swap_apply_left]
    simp only [pairUpdate,Function.update_self,Function.update_of_ne hij]
  · by_cases hkj : k=j
    · subst k
      change pairUpdate v i j x y ((Equiv.swap i j) j)=pairUpdate v i j y x j
      rw [Equiv.swap_apply_right]
      simp only [pairUpdate,Function.update_self,Function.update_of_ne hij]
    · simp [pairUpdate,Equiv.swap_apply_of_ne_of_ne hki hkj,hki,hkj]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem pairUpdate_unit {d : ℕ} (v : Fin d → E) (hv : ∀ i, ‖v i‖ = 1)
    (i j : Fin d) (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∀ k,‖pairUpdate v i j x y k‖=1 := by
  classical
  intro k
  by_cases hkj : k=j
  · subst k
    simpa [pairUpdate] using hy
  · by_cases hki : k=i
    · subst k
      simpa [pairUpdate,hkj] using hx
    · simpa [pairUpdate,hkj,hki] using hv k

omit [CompleteSpace E] in
theorem partial_norm_le {d : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (v : Fin d → E) (hv : ∀ i,‖v i‖=1)
    (hmax : ∀ w : Fin d → E,(∀ i,‖w i‖=1) → |A w|≤|A v|) (i : Fin d) :
    ‖A.toContinuousLinearMap v i‖≤|A v| := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (abs_nonneg _)
  intro x hx
  change |A (Function.update v i x)|≤|A v|
  apply hmax
  intro k
  by_cases hki : k=i
  · subst k
    simpa using hx
  · simpa [hki] using hv k

theorem partial_at_max {d : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (v : Fin d → E) (hv : ∀ i,‖v i‖=1)
    (hmax : ∀ w : Fin d → E,(∀ i,‖w i‖=1) → |A w|≤|A v|) (i : Fin d) (x : E) :
    A (Function.update v i x)=A v*⟪v i,x⟫_ℝ := by
  have h := linear_norm_attainment (A.toContinuousLinearMap v i) (v i) (hv i)
    |A v| (partial_norm_le A v hv hmax i) (by simp) x
  simpa using h

omit [CompleteSpace E] in
theorem pairUpdate_add_left {d : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (v : Fin d → E) (i j : Fin d) (hij : i≠j) (x x' y : E) :
    A (pairUpdate v i j (x+x') y)=A (pairUpdate v i j x y)+A (pairUpdate v i j x' y) := by
  rw [pairUpdate_comm v i j hij,pairUpdate_comm v i j hij,pairUpdate_comm v i j hij]
  exact A.map_update_add (Function.update v j y) i x x'

omit [CompleteSpace E] in
theorem pairUpdate_add_right {d : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (v : Fin d → E) (i j : Fin d) (x y y' : E) :
    A (pairUpdate v i j x (y+y'))=A (pairUpdate v i j x y)+A (pairUpdate v i j x y') := by
  exact A.map_update_add (Function.update v i x) j y y'

omit [CompleteSpace E] in
theorem pairUpdate_smul_both {d : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (v : Fin d → E) (i j : Fin d) (hij : i≠j) (c : ℝ) (x y : E) :
    A (pairUpdate v i j (c • x) (c • y))=c^2*A (pairUpdate v i j x y) := by
  unfold pairUpdate
  rw [A.map_update_smul]
  rw [Function.update_comm hij]
  rw [A.map_update_smul]
  rw [Function.update_comm hij]
  simp only [smul_eq_mul]
  ring

theorem pair_sum_value {d : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (hsym : ∀ w i j,A (w ∘ Equiv.swap i j)=A w)
    (v : Fin d → E) (hv : ∀ i,‖v i‖=1)
    (hmax : ∀ w : Fin d → E,(∀ i,‖w i‖=1) → |A w|≤|A v|)
    (i j : Fin d) (hij : i≠j) :
    A (pairUpdate v i j (v i+v j) (v i+v j))=A v*‖v i+v j‖^2 := by
  have hxx : A (pairUpdate v i j (v i) (v i))=A v*⟪v j,v i⟫_ℝ := by
    simpa [pairUpdate] using partial_at_max A v hv hmax j (v i)
  have hyy : A (pairUpdate v i j (v j) (v j))=A v*⟪v i,v j⟫_ℝ := by
    rw [pairUpdate_comm v i j hij]
    simpa [pairUpdate] using partial_at_max A v hv hmax i (v j)
  have hxy : A (pairUpdate v i j (v i) (v j))=A v := by simp [pairUpdate]
  have hyx : A (pairUpdate v i j (v j) (v i))=A v := by
    rw [←pairUpdate_swap v i j hij (v i) (v j),hsym]
    simp [pairUpdate]
  rw [pairUpdate_add_left A v i j hij,pairUpdate_add_right,pairUpdate_add_right,
    hxx,hxy,hyx,hyy,norm_add_sq_real,hv i,hv j,real_inner_comm (v j) (v i)]
  ring

omit [CompleteSpace E] in
theorem maximal_sum_alignment {d : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (v : Fin d → E) (hv : ∀ i,‖v i‖=1)
    (hscore : ∀ w : Fin d → E,(∀ i,‖w i‖=1) → |A w|=|A v| →
      ‖∑ i,w i‖^2≤‖∑ i,v i‖^2) (i : Fin d) :
    1≤⟪∑ j,v j,v i⟫_ℝ := by
  have hunit : ∀ j,‖Function.update v i (-v i) j‖=1 := by
    intro j
    by_cases hji : j=i
    · subst j
      simp [hv]
    · simp [hji,hv]
  have habs : |A (Function.update v i (-v i))|=|A v| := by
    have h := A.toMultilinearMap.map_update_neg v i (v i)
    simpa only [ContinuousMultilinearMap.coe_coe,Function.update_eq_self,abs_neg]
      using congrArg abs h
  have hbound := hscore _ hunit habs
  rw [sum_update] at hbound
  have heq : (∑ j,v j)-v i+-v i=(∑ j,v j)-(2:ℝ) • v i := by module
  rw [heq,norm_sub_sq_real,real_inner_smul_right,norm_smul,hv i] at hbound
  norm_num at hbound
  linarith

/-- A value-maximizing unit tuple with maximal sum norm is diagonal. The
tie-breaking objective is what removes every polarization loss. -/
theorem maximizing_tuple_diagonal {d : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (hsym : ∀ w i j,A (w ∘ Equiv.swap i j)=A w)
    (v : Fin d → E) (hv : ∀ i,‖v i‖=1)
    (hmax : ∀ w : Fin d → E,(∀ i,‖w i‖=1) → |A w|≤|A v|)
    (hscore : ∀ w : Fin d → E,(∀ i,‖w i‖=1) → |A w|=|A v| →
      ‖∑ i,w i‖^2≤‖∑ i,v i‖^2) (i j : Fin d) : v i=v j := by
  by_contra hne
  have hij : i≠j := by intro h;exact hne (congrArg v h)
  let S : E := ∑ k,v k
  let a : E := v i+v j
  have hSa : 2≤⟪S,a⟫_ℝ := by
    dsimp [S,a]
    rw [inner_add_right]
    linarith [maximal_sum_alignment A v hv hscore i,maximal_sum_alignment A v hv hscore j]
  have hane : a≠0 := by intro hz;rw [hz,inner_zero_right] at hSa;linarith
  have ha : 0<‖a‖ := norm_pos_iff.mpr hane
  have hnormsub : 0<‖v i-v j‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  rw [norm_sub_sq_real,hv i,hv j] at hnormsub
  have ha2 : ‖a‖^2<4 := by
    dsimp [a]
    rw [norm_add_sq_real,hv i,hv j]
    nlinarith
  have halt : ‖a‖<2 := by nlinarith
  let u : E := ‖a‖⁻¹ • a
  have hu : ‖u‖=1 := norm_smul_inv_norm hane
  let w := pairUpdate v i j u u
  have hwunit : ∀ k,‖w k‖=1 := pairUpdate_unit v hv i j u u hu hu
  have hwvalue : A w=A v := by
    change A (pairUpdate v i j (‖a‖⁻¹ • a) (‖a‖⁻¹ • a))=A v
    rw [pairUpdate_smul_both A v i j hij]
    change ‖a‖⁻¹^2*A (pairUpdate v i j (v i+v j) (v i+v j))=A v
    rw [pair_sum_value A hsym v hv hmax i j hij]
    change ‖a‖⁻¹^2*(A v*‖a‖^2)=A v
    field_simp
  have hwb := hscore w hwunit (congrArg abs hwvalue)
  let c : ℝ := 2/‖a‖-1
  have hc : 0<c := by
    dsimp [c]
    apply sub_pos.mpr
    exact (lt_div_iff₀ ha).2 (by linarith)
  have hsum : (∑ k,w k)=S+c • a := by
    change (∑ k,pairUpdate v i j u u k)=_
    unfold pairUpdate
    rw [sum_update,sum_update,Function.update_of_ne (Ne.symm hij)]
    dsimp [S,c,u,a]
    rw [div_eq_mul_inv]
    module
  rw [hsum,norm_add_sq_real,real_inner_smul_right,norm_smul,
    Real.norm_eq_abs,abs_of_pos hc,mul_pow] at hwb
  change ‖S‖^2+2*(c*⟪S,a⟫_ℝ)+c^2*‖a‖^2≤‖S‖^2 at hwb
  have hterm : 0<c*⟪S,a⟫_ℝ := mul_pos hc (by linarith)
  nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg ‖a‖)]

/-- Banach's exact diagonal bound on a finite-dimensional real Hilbert
space, proved from the two compact maximizations above. -/
theorem symmetric_unit_bound [FiniteDimensional ℝ E] [Nontrivial E] {d : ℕ}
    (hd : 0 < d) (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (hsym : ∀ w i j,A (w ∘ Equiv.swap i j)=A w) (M : ℝ)
    (hdiag : ∀ x : E,‖x‖=1 → |A (fun _ ↦ x)|≤M)
    (w : Fin d → E) (hw : ∀ i,‖w i‖=1) : |A w|≤M := by
  classical
  obtain ⟨x,hx⟩ := exists_ne (0:E)
  let e : E := ‖x‖⁻¹ • x
  have he : ‖e‖=1 := norm_smul_inv_norm hx
  let T : Set (Fin d → E) := {v | ∀ i,‖v i‖=1}
  have hTcompact : IsCompact T := by
    simpa only [Metric.mem_sphere,dist_zero_right] using
      (isCompact_pi_infinite (fun _ : Fin d ↦ isCompact_sphere (0:E) 1))
  have hTnonempty : T.Nonempty := ⟨fun _ ↦ e,fun _ ↦ he⟩
  obtain ⟨u,hu,hvalueMax⟩ := hTcompact.exists_isMaxOn hTnonempty A.cont.abs.continuousOn
  let B : Set (Fin d → E) := T ∩ {v | |A v|=|A u|}
  have hBcompact : IsCompact B := hTcompact.inter_right (isClosed_eq A.cont.abs continuous_const)
  have hBnonempty : B.Nonempty := ⟨u,hu,rfl⟩
  have hscoreCont : Continuous (fun v : Fin d → E ↦ ‖∑ i,v i‖^2) :=
    (continuous_finsetSum _ (fun i _ ↦ continuous_apply i)).norm.pow 2
  obtain ⟨v,hv,hscoreMax⟩ := hBcompact.exists_isMaxOn hBnonempty hscoreCont.continuousOn
  have hvunit : ∀ i,‖v i‖=1 := hv.1
  have hmax : ∀ z : Fin d → E,(∀ i,‖z i‖=1) → |A z|≤|A v| := by
    intro z hz
    exact (hvalueMax hz).trans_eq hv.2.symm
  have hscore : ∀ z : Fin d → E,(∀ i,‖z i‖=1) → |A z|=|A v| →
      ‖∑ i,z i‖^2≤‖∑ i,v i‖^2 := by
    intro z hz hval
    exact hscoreMax ⟨hz,hval.trans hv.2⟩
  let i₀ : Fin d := ⟨0,hd⟩
  have hvconst : v=fun _ ↦ v i₀ := by
    funext i
    exact maximizing_tuple_diagonal A hsym v hvunit hmax hscore i i₀
  calc
    |A w|≤|A v| := hmax w hw
    _≤M := by rw [hvconst];exact hdiag _ (hvunit i₀)

/-- Exact norm-one real-Hilbert polarization bound for arbitrary vectors. -/
theorem symmetric_multilinear_bound [FiniteDimensional ℝ E] [Nontrivial E] {d : ℕ}
    (hd : 0 < d) (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (hsym : ∀ w i j,A (w ∘ Equiv.swap i j)=A w) (M : ℝ) (hM : 0≤M)
    (hdiag : ∀ x : E,‖x‖=1 → |A (fun _ ↦ x)|≤M) (v : Fin d → E) :
    |A v|≤M*∏ i,‖v i‖ := by
  classical
  by_cases hz : ∃ i,v i=0
  · obtain ⟨i,hi⟩ := hz
    have hzero : A v=0 := A.toMultilinearMap.map_coord_zero i hi
    rw [hzero,abs_zero]
    exact mul_nonneg hM (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)
  · have hnz : ∀ i,v i≠0 := by simpa only [not_exists] using hz
    let w : Fin d → E := fun i ↦ ‖v i‖⁻¹ • v i
    have hw : ∀ i,‖w i‖=1 := fun i ↦ norm_smul_inv_norm (hnz i)
    have hunit := symmetric_unit_bound hd A hsym M hdiag w hw
    have hrepr : v=fun i ↦ ‖v i‖ • w i := by
      funext i
      dsimp [w]
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hnz i)),one_smul]
    have heval : A v=(∏ i,‖v i‖)*A w := by
      conv_lhs => rw [hrepr,A.map_smul_univ]
      rfl
    rw [heval,abs_mul,abs_of_nonneg (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)]
    calc
      (∏ i,‖v i‖)*|A w|≤(∏ i,‖v i‖)*M :=
        mul_le_mul_of_nonneg_left hunit (Finset.prod_nonneg fun i _ ↦ norm_nonneg _)
      _=M*∏ i,‖v i‖ := mul_comm _ _

theorem symmetric_opNorm_bound [FiniteDimensional ℝ E] [Nontrivial E] {d : ℕ}
    (hd : 0 < d) (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (hsym : ∀ w i j,A (w ∘ Equiv.swap i j)=A w) (M : ℝ) (hM : 0≤M)
    (hdiag : ∀ x : E,‖x‖=1 → |A (fun _ ↦ x)|≤M) : ‖A‖≤M := by
  apply ContinuousMultilinearMap.opNorm_le_bound hM
  intro v
  exact symmetric_multilinear_bound hd A hsym M hM hdiag v

end BanachDiagonal
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
