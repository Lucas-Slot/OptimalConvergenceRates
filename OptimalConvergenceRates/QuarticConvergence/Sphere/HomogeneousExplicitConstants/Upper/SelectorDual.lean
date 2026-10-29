import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SelectorFiniteDual
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SelectorEvaluations

/-! Every positive dual of the actual selector image has a finite PSD
matrix-evaluation representation. The free quadratic entry yields the
exact coordinate consistency equations. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SelectorDual

open Set Topology
open scoped BigOperators Matrix
open SelectorCone SelectorEvaluations

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- An actual positive rank-one matrix, with its nonnegative mass explicit. -/
def rankOneWeight (c : ℝ) (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j ↦ c*v i*v j

theorem rankOneWeight_posSemidef (c : ℝ) (hc : 0 ≤ c) (v : Fin 3 → ℝ) :
    (rankOneWeight c v).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply,rankOneWeight,star_trivial]
    ring
  · intro x
    convert mul_nonneg hc (sq_nonneg (v 0*x 0+v 1*x 1+v 2*x 2)) using 1
    simp only [rankOneWeight,Matrix.mulVec,dotProduct,star_trivial,
      Fin.sum_univ_succ,Finset.sum_empty,add_zero,
      Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
    ring

/-- The five actual coefficient marginals of a selector-dual matrix. -/
def marginalValue {n : ℕ} (h : Fin n → ℝ) (Z : Matrix (Fin 3) (Fin 3) ℝ)
    (q : Coeff n) : ℝ :=
  Z 0 0*q.1 + Z 0 1*linEval h q.2.1 + Z 1 1*quadEval h q.2.2.1 +
    Z 1 2*tensorEval h q.2.2.2.1 + Z 2 2*tensorEval h q.2.2.2.2

theorem marginalValue_zero {n : ℕ} (h : Fin n → ℝ) (Z : Matrix (Fin 3) (Fin 3) ℝ) :
    marginalValue h Z 0=0 := by simp [marginalValue]

/-- The selector's free entry has exactly the coefficient needed for
Hankel consistency; all off-diagonal half factors cancel correctly. -/
theorem weighted_evaluation_eq {n : ℕ} (p : Parameters n) (c : ℝ)
    (q : Coeff n) (u : Quad n) :
    c*evaluation p (q,u) =
      marginalValue (fun i ↦ p.1 i) (rankOneWeight c (fun i ↦ p.2 i)) q +
      2*(rankOneWeight c (fun i ↦ p.2 i) 0 2-
        rankOneWeight c (fun i ↦ p.2 i) 1 1)*quadEval (fun i ↦ p.1 i) u := by
  simp only [evaluation_apply,gramEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
    rankOneWeight,marginalValue]
  ring

theorem quadEval_matrix_unit {n : ℕ} (h : Fin n → ℝ) (i j : Fin n) :
    quadEval h (Pi.single i (Pi.single j 1))=h i*h j := by
  classical
  simp [quadEval,Pi.single_apply,ite_apply,ite_mul]

/-- Exact finite positive evaluations of the pullback of a positive
functional on the ACTUAL closed selector image. -/
theorem exists_finite_evaluation_representation {n : ℕ} (hn : 0 < n)
    (E : Coeff n →L[ℝ] ℝ)
    (hE : ∀ q ∈ quarticSelectorCone n, 0 ≤ E q) :
    ∃ (I : Type) (_ : Fintype I) (w : I → ℝ) (p : I → Parameters n),
      (∀ t, 0≤w t) ∧ (∀ t, p t ∈ unitParameters n) ∧
      ∀ d : Data n, E d.1=∑ t, w t*evaluation (p t) d := by
  let L : Data n →L[ℝ] ℝ := E.comp (ContinuousLinearMap.fst ℝ (Coeff n) (Quad n))
  have hL : ∀ d : Data n,
      (∀ e ∈ normalizedEvaluations n, 0≤e d) → 0≤L d := by
    intro d hd
    have hpos : d ∈ positivityCone n :=
      (positivityCone_iff_unit_evaluations hn d).mpr (fun p hp ↦ hd _ ⟨p,hp,rfl⟩)
    exact hE d.1 ⟨d,hpos,rfl⟩
  obtain ⟨I,hI,w,z,hw,hz,hcombo⟩ := SelectorFiniteDual.finite_dual_of_compact
    (normalizedEvaluations n) (normalizedEvaluations_nonempty hn)
    (normalizedEvaluations_isCompact n) (normalizer n)
    (normalizedEvaluations_normalizer n) L hL
  have hz' (t : I) : ∃ p ∈ unitParameters n, evaluation p=z t := hz t
  choose p hp heval using hz'
  have hcombo' : ∑ t, w t • evaluation (p t)=L := by
    simpa only [heval] using! hcombo
  refine ⟨I,hI,w,p,hw,hp,?_⟩
  intro d
  have h := congrArg (fun a : Data n →L[ℝ] ℝ ↦ a d) hcombo'
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,L,ContinuousLinearMap.comp_apply] at h
  exact h.symm

/-- A finite PSD matrix measure with actual unit transverse points,
coordinate consistency, and all coefficient marginals. No representation
of a positive functional is assumed in this theorem. -/
theorem exists_finite_psd_representation {n : ℕ} (hn : 0 < n)
    (E : Coeff n →L[ℝ] ℝ)
    (hE : ∀ q ∈ quarticSelectorCone n, 0 ≤ E q) :
    ∃ (I : Type) (_ : Fintype I) (h : I → Fin n → ℝ)
      (Z : I → Matrix (Fin 3) (Fin 3) ℝ),
      (∀ t, radius (h t)=1) ∧ (∀ t, (Z t).PosSemidef) ∧
      (∀ i j, (∑ t, (Z t 0 2-Z t 1 1)*(h t i*h t j))=0) ∧
      ∀ q : Coeff n, E q=∑ t, marginalValue (h t) (Z t) q := by
  obtain ⟨I,hI,w,p,hw,hp,hrep⟩ := exists_finite_evaluation_representation hn E hE
  let h : I → Fin n → ℝ := fun t i ↦ (p t).1 i
  let Z : I → Matrix (Fin 3) (Fin 3) ℝ :=
    fun t ↦ rankOneWeight (w t) (fun i ↦ (p t).2 i)
  have hmarg (q : Coeff n) : E q=∑ t, marginalValue (h t) (Z t) q := by
    have hr := hrep (q,0)
    simp only [weighted_evaluation_eq,map_zero,mul_zero,add_zero] at hr
    exact hr
  have hfree (u : Quad n) : (∑ t, 2*(Z t 0 2-Z t 1 1)*quadEval (h t) u)=0 := by
    have hr := hrep (0,u)
    simp only [map_zero,weighted_evaluation_eq,marginalValue_zero,zero_add] at hr
    exact hr.symm
  refine ⟨I,hI,h,Z,?_,?_,?_,hmarg⟩
  · intro t
    have hh : ‖(p t).1‖=1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using (hp t).1
    exact (radius_eq_one_iff_norm (p t).1).mpr hh
  · exact fun t ↦ rankOneWeight_posSemidef _ (hw t) _
  · intro i j
    have hr := hfree (Pi.single i (Pi.single j 1))
    simp only [quadEval_matrix_unit] at hr
    have heq : (∑ t, 2*(Z t 0 2-Z t 1 1)*(h t i*h t j)) =
        2*(∑ t, (Z t 0 2-Z t 1 1)*(h t i*h t j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [heq] at hr
    linarith

end SelectorDual
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
