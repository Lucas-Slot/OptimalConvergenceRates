import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.SelectorFunctionalLower
import OptimalConvergenceRates.SphereDimensionBounds.ClosedConeDuality

/-! Actual polynomial quadratic selector from closed-cone separation and
the constructed all-pole finite dual inequality. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.SelectorExistence
open scoped BigOperators Matrix
open MvPolynomial WeightedQuadraticSplit SelectorCone SelectorPolynomial SelectorFunctional
  SelectorCentering SelectorSchur
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

def selectorBudget (n : ℕ):ℝ:=(383+531200*((Nat.clog 2 n:ℝ)+1)^2)/3

/-- Every actual globally nonnegative homogeneous quartic family has an
actual homogeneous quadratic selector with the published log-squared
bottom budget. No finite-dual representation is assumed. -/
theorem exists_quadratic_selector {n : ℕ} (hn : 0 < n) (a M : ℝ)
    (l H B C0 : Poly n) (hl : l.IsHomogeneous 1) (hH : H.IsHomogeneous 2)
    (hB : B.IsHomogeneous 3) (hC : C0.IsHomogeneous 4)
    (hp :∀ (z : ℝ) (x : Fin n → ℝ), 0 ≤ QuarticCoefficientBounds.quartic a
      (eval x l) (eval x H) (eval x B) (eval x C0) z)
    (hM : 0 ≤ M) (hCM : ∀ x:Fin n→ℝ,eval x C0≤M*(∑ i,x i^2)^2) :
    ∃ u:Poly n,u.IsHomogeneous 2 ∧ ∀ x:Fin n→ℝ,
      (selectorMatrix a (eval x l) (eval x H) (eval x B) (eval x u)
        (selectorBudget n*M*(∑ i,x i^2)^2)).PosSemidef:=by
  obtain ⟨lc,hlc⟩:=exists_linPolynomial l hl
  obtain ⟨Hc,hHc⟩:=exists_quadPolynomial H hH
  obtain ⟨Bc,hBc⟩:=exists_tensorPolynomial B hB
  obtain ⟨Fc,hFc⟩:=exists_tensorPolynomial C0 hC
  let R:=OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n
  have hR:R.IsHomogeneous 2:=SelectorFunctional.radius_homogeneous n
  obtain ⟨Fn,hFn⟩:=exists_tensorPolynomial (C (selectorBudget n*M)*R^2) ((hR.pow 2).C_mul _)
  let q:Coeff n:=(a,(lc,(Hc,(Bc,Fc))))
  let qn:Coeff n:=(a,(lc,(Hc,(Bc,Fn))))
  let p:=QuarticDivisionSOS.model a l H B C0
  have hmodel:modelPolynomial q=p:=by
    rw [modelPolynomial_apply,hlc,hHc,hBc,hFc]
    rfl
  have hph:p.IsHomogeneous 4:=by
    rw [←hmodel]
    exact modelPolynomial_homogeneous q
  have hp0:∀ x:Fin (n+1)→ℝ,0≤eval x p:=by
    intro x
    have hx:x=Fin.cons (x 0) (fun i=>x i.succ):=by
      funext i
      refine Fin.cases rfl (fun _=>rfl) i
    rw [hx,SelectorFunctionalLower.model_eval]
    exact hp _ _
  have hbottom:∀ x:Fin n→ℝ,eval (Fin.cons 0 x) p≤M*(∑ i,x i^2)^2:=by
    intro x
    rw [SelectorFunctionalLower.model_eval]
    simpa [QuarticCoefficientBounds.quartic] using hCM x
  have hnewmodel:modelPolynomial qn=p-transverse C0+C (selectorBudget n*M)*(transverse R)^2:=by
    rw [modelPolynomial_apply,hlc,hHc,hBc,hFn]
    simp only [p,QuarticDivisionSOS.model,QuarticDivisionSOS.s,QuarticDivisionSOS.tr,
      transverse,map_mul,map_pow,rename_C]
    ring
  have hqn:qn∈quarticSelectorCone n:=by
    apply ClosedConeDuality.mem_of_nonneg_duals
    intro E hE
    obtain ⟨I,hI,h,Z,hunit,hZ,hcons,hrep⟩:=exists_polynomial_functional_representation hn E hE
    let v:I→EP n:=fun t=>(WithLp.equiv 2 (Fin n→ℝ)).symm (h t)
    have hv:∀ t,‖v t‖=1:=by
      intro t
      apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
      rw [norm_sq]
      norm_num only [one_pow]
      change (∑ i,(h t i)^2)=1
      exact hunit t
    have hvcons:QuadraticConsistency v Z:=hcons
    let F:=functional h Z
    have hlow:=SelectorFunctionalLower.functional_lower hn v hv Z hZ hvcons p hph hp0 hM hbottom
    change 0≤F p+(332/3:ℝ)*(1+1600*((Nat.clog 2 n:ℝ)+1)^2)*M*diagonalMass Z 2 at hlow
    have hcup:F (transverse C0)≤M*diagonalMass Z 2:=by
      rw [functional_transverse_quartic h Z C0 hC]
      calc
        (∑ t,Z t 2 2*eval (h t) C0)≤∑ t,Z t 2 2*M:=by
          apply Finset.sum_le_sum
          intro t _
          apply mul_le_mul_of_nonneg_left _ (psd_diagonal_nonneg (Z t) (hZ t) 2)
          have hh:=hCM (h t)
          have hr:(∑ i,(h t i)^2)=1:=hunit t
          simpa only [hr,one_pow,mul_one] using hh
        _=M*diagonalMass Z 2:=by simp only [diagonalMass,←Finset.sum_mul];ring
    have hrad:F ((transverse R)^2)=diagonalMass Z 2:=functional_radius_four h hunit Z
    have hW:0≤diagonalMass Z 2:=diagonalMass_nonneg Z hZ 2
    erw [hrep qn]
    change 0 ≤ F (modelPolynomial qn)
    rw [hnewmodel,map_add,map_sub,TensorMomentFunctional.linearMap_C_mul,hrad]
    have hc:0≤M*diagonalMass Z 2-F (transverse C0):=sub_nonneg.mpr hcup
    have hm:0≤M*diagonalMass Z 2:=mul_nonneg hM hW
    dsimp only [selectorBudget]
    linear_combination hlow+hc+16*hm
  change qn∈Prod.fst '' positivityCone n at hqn
  obtain ⟨d,hd,heq⟩:=hqn
  refine ⟨quadPolynomial d.2,quadPolynomial_homogeneous d.2,?_⟩
  intro x
  have hm:=(positivityCone_iff_matrix d).mp hd x
  rw [heq] at hm
  change (selectorMatrix a (linEval x lc) (quadEval x Hc) (tensorEval x Bc)
    (quadEval x d.2) (tensorEval x Fn)).PosSemidef at hm
  have hel:linEval x lc=eval x l:=by rw [←linPolynomial_eval,hlc]
  have heH:quadEval x Hc=eval x H:=by rw [←quadPolynomial_eval,hHc]
  have heB:tensorEval x Bc=eval x B:=by rw [←tensorPolynomial_eval,hBc]
  have heF:tensorEval x Fn=selectorBudget n*M*(∑ i,x i^2)^2:=by
    rw [←tensorPolynomial_eval,hFn]
    simp only [R,map_mul,map_pow,eval_C,OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial_eval]
  rw [hel,heH,heB,heF] at hm
  simpa only [quadPolynomial_eval] using hm

end OptimalConvergenceRates.SphereDimensionBounds.SelectorExistence
