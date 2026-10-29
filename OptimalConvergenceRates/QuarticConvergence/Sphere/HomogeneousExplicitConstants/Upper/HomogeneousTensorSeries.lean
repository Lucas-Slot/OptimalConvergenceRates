import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-! Exact binomial bounds for the translated power series of an actual
homogeneous continuous multilinear form. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace HomogeneousTensorSeries

open scoped BigOperators NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}

def tensorSeries (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ) :
    FormalMultilinearSeries ℝ E ℝ := Function.update 0 d A

theorem tensorSeries_self (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ) :
    tensorSeries A d=A := by simp [tensorSeries]

theorem tensorSeries_ne (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (k : ℕ) (hkd : k≠d) : tensorSeries A k=0 := by
  simp [tensorSeries,Function.update_of_ne hkd]

theorem tensor_hasFiniteFPowerSeries
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ) :
    HasFiniteFPowerSeriesOnBall (fun x : E ↦ A (fun _ ↦ x)) (tensorSeries A) 0 (d+1) ⊤ := by
  classical
  apply HasFiniteFPowerSeriesOnBall.mk'
  · intro k hk
    exact tensorSeries_ne A k (by omega)
  · exact ENNReal.zero_lt_top
  · intro y hy
    rw [Finset.sum_eq_single_of_mem d (Finset.self_mem_range_succ d),zero_add]
    · rw [tensorSeries_self]
    · intro k hk hne
      rw [tensorSeries_ne A k hne]
      rfl

theorem tensor_changeOriginSeries_zero
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ)
    (j l : ℕ) (hjl : j+l≠d) : (tensorSeries A).changeOriginSeries j l=0 := by
  classical
  unfold FormalMultilinearSeries.changeOriginSeries
  apply Finset.sum_eq_zero
  intro s hs
  have hz := (tensorSeries A).norm_changeOriginSeriesTerm j l s.val s.prop
  rw [tensorSeries_ne A _ hjl,norm_zero] at hz
  exact ContinuousMultilinearMap.opNorm_zero_iff.mp hz

theorem tensor_changeOrigin_eq
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ) (z : E)
    (j : ℕ) (hj : j≤d) :
    (tensorSeries A).changeOrigin z j=
      (tensorSeries A).changeOriginSeries j (d-j) (fun _ ↦ z) := by
  change (∑' l,(tensorSeries A).changeOriginSeries j l (fun _ ↦ z))=_
  apply tsum_eq_single (d-j)
  intro l hl
  rw [tensor_changeOriginSeries_zero A j l (by omega)]
  rfl

theorem tensor_changeOrigin_norm
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ) (z : E)
    (j : ℕ) (hj : j≤d) :
    ‖(tensorSeries A).changeOrigin z j‖≤(d.choose j:ℝ)*‖A‖*‖z‖^(d-j) := by
  classical
  rw [tensor_changeOrigin_eq A z j hj]
  have h := (tensorSeries A).nnnorm_changeOriginSeries_apply_le_tsum j (d-j) z
  have hadd : j+(d-j)=d := by omega
  have hcoeff : ‖tensorSeries A (j+(d-j))‖₊=‖A‖₊ := by rw [hadd,tensorSeries_self]
  simp only [hcoeff] at h
  have hnn : ‖(tensorSeries A).changeOriginSeries j (d-j) (fun _ ↦ z)‖₊≤
      (d.choose j:ℝ≥0)*‖A‖₊*‖z‖₊^(d-j) := by
    simpa only [hadd,tensorSeries_self,tsum_fintype,Finset.sum_const,
      Finset.card_univ,Fintype.card_finset_len,Fintype.card_fin,Nat.choose_symm hj,
      nsmul_eq_mul,mul_assoc] using h
  exact_mod_cast hnn

/-- The actual iterated derivative, on a repeated direction, has the exact
factor j! choose(d,j). No tensor symmetry is needed for this series bound. -/
theorem diagonal_iteratedFDeriv_bound
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin d ↦ E) ℝ) (z h : E)
    (j : ℕ) (hj : j≤d) :
    |iteratedFDeriv ℝ j (fun x : E ↦ A (fun _ ↦ x)) z (fun _ ↦ h)|≤
      (j.factorial:ℝ)*(d.choose j:ℝ)*‖A‖*‖z‖^(d-j)*‖h‖^j := by
  have hseries := (tensor_hasFiniteFPowerSeries A).toHasFPowerSeriesOnBall
  have hchanged := hseries.changeOrigin (y:=z) (by simp)
  have hfactor := hchanged.factorial_smul h j
  simp only [zero_add] at hfactor
  rw [←hfactor]
  simp only [nsmul_eq_mul,abs_mul,
    abs_of_nonneg (show (0:ℝ)≤(j.factorial:ℝ) from Nat.cast_nonneg _)]
  have hop := ((tensorSeries A).changeOrigin z j).le_opNorm (fun _ ↦ h)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Real.norm_eq_abs] at hop
  calc
    (j.factorial:ℝ)*|((tensorSeries A).changeOrigin z j) (fun _ ↦ h)|≤
        (j.factorial:ℝ)*(‖(tensorSeries A).changeOrigin z j‖*‖h‖^j) :=
      mul_le_mul_of_nonneg_left hop (Nat.cast_nonneg _)
    _≤(j.factorial:ℝ)*((d.choose j:ℝ)*‖A‖*‖z‖^(d-j)*‖h‖^j) := by
      gcongr
      exact tensor_changeOrigin_norm A z j hj
    _=_ := by ring

end HomogeneousTensorSeries
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
