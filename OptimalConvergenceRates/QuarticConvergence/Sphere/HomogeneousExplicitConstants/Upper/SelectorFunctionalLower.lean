import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CenteredQuarticBound

/-! The actual all-pole lower inequality for every finite PSD selector
dual functional. Polynomial centering, SOS roots and error control are
constructed, with no positive-leading-mass assumption. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SelectorFunctionalLower
open scoped BigOperators
open MvPolynomial WeightedQuadraticSplit CubicSpectralDivision SelectorFunctional
  SelectorShear SelectorCentering ChebyshevSOSKernel

abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

theorem model_eval {n : ℕ} (a : ℝ) (l H B C0 : Poly n) (z : ℝ) (x : Fin n → ℝ) :
    eval (Fin.cons z x) (QuarticDivisionSOS.model a l H B C0)=
      QuarticCoefficientBounds.quartic a (eval x l) (eval x H) (eval x B) (eval x C0) z:=by
  simp [QuarticDivisionSOS.model,QuarticCoefficientBounds.quartic,
    QuarticDivisionSOS.s, QuarticDivisionSOS.tr, s, transverse, eval_rename, Function.comp_def,
      mul_comm, mul_left_comm]

theorem boundedSOS_functional_nonneg {n : ℕ} (E : Poly n →ₗ[ℝ] ℝ)
    (hE : ∀ q:Poly n,q.totalDegree≤2→0≤E (q^2)) {p:Poly n} (hp:BoundedSOS 2 p) :
    0≤E p:=by
  obtain ⟨m,q,hq,hid⟩ := hp.exists_squares
  rw [hid,map_sum]
  exact Finset.sum_nonneg (fun i _↦hE _ (hq i))

/-- Every actual nonnegative homogeneous quartic satisfies the finite
selector-dual inequality. The logarithmic constant is derived from the
actual source, including all poles and zero leading mass. -/
theorem functional_lower {I : Type*} [Fintype I] {n : ℕ} (hn : 0 < n)
    (h : I → EP n) (hh : ∀ t, ‖h t‖ = 1) (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : ∀ t, (Z t).PosSemidef) (hcons : QuadraticConsistency h Z)
    (p : Poly (n + 1)) (hp : p.IsHomogeneous 4)
    (hp0 : ∀ x:Fin (n+1)→ℝ,0≤eval x p) {M:ℝ} (hM:0≤M)
    (hbottom:∀ x:Fin n→ℝ,eval (Fin.cons 0 x) p≤M*(∑ i,x i^2)^2) :
    0≤functional (fun t i↦h t i) Z p+
      (332/3:ℝ)*(1+1600*((Nat.clog 2 n:ℝ)+1)^2)*M*diagonalMass Z 2:=by
  let mu:Fin n→ℝ:=fun i↦centeringVector h Z i
  let pp:=composition (shear mu) p
  have hpp:pp.IsHomogeneous 4:=composition_homogeneous _ p hp
  obtain ⟨a,l,H,B,C0,hl,hH,hB,hC,hdec⟩:=SelectorPolynomial.homogeneous_quartic_split pp hpp
  change pp=QuarticDivisionSOS.model a l H B C0 at hdec
  have hpp0:∀ x:Fin (n+1)→ℝ,0≤eval x pp:=by
    intro x
    let xx:Point (Fin (n+1)):=OrderedCubicExpansion.evaluationPoint x
    have hx:=hp0 (fun j↦shear mu xx j)
    change 0≤eval (fun j↦xx j) (composition (shear mu) p)
    rw [composition_eval]
    exact hx
  have hfamily:∀ (z:ℝ) (x:Fin n→ℝ),0≤QuarticCoefficientBounds.quartic a
      (eval x l) (eval x H) (eval x B) (eval x C0) z:=by
    intro z x
    rw [←model_eval,←hdec]
    exact hpp0 _
  have hzero:∀ x:Fin n→ℝ,eval (Fin.cons 0 x) pp=eval (Fin.cons 0 x) p:=by
    intro x
    let xx:Point (Fin (n+1)):=OrderedCubicExpansion.evaluationPoint (Fin.cons 0 x)
    have he:shear mu xx=xx:=by
      ext j
      refine Fin.cases (by rfl) (fun i↦?_) j
      change xx i.succ+mu i*xx 0=xx i.succ
      have hx:xx 0=0:=rfl
      rw [hx,mul_zero,add_zero]
    change eval (fun j↦xx j) (composition (shear mu) p)=eval (fun j↦xx j) p
    rw [composition_eval,he]
  have hCB:∀ x:Fin n→ℝ,eval x C0≤M*(∑ i,x i^2)^2:=by
    intro x
    have hcval:eval x C0=eval (Fin.cons 0 x) pp:=by
      rw [hdec,model_eval]
      simp [QuarticCoefficientBounds.quartic]
    rw [hcval,hzero]
    exact hbottom x
  obtain ⟨Q,hQ,hQbound,hSOS⟩:=QuarticDivisionSOS.exists_error_sos hn a M l H B C0 hH hB hC hfamily
    hM hCB
  rw [←hdec] at hSOS
  have hback:=boundedSOS_composition (shear (-mu)) hSOS
  have hback':BoundedSOS 2 (p-s n^3*centeredSubstitution mu l+centeredSubstitution mu Q):=by
    simpa only [pp,map_add,map_sub,map_mul,map_pow,inverse_shear_composition,
      inverse_shear_scalar,inverse_shear_transverse] using hback
  let E:=functional (fun t i↦h t i) Z
  have hE:∀ q:Poly (n+1),q.totalDegree≤2→0≤E (q^2):=by
    intro q hq
    exact functional_square_nonneg (fun t i↦h t i) Z hZ hcons q hq
  have hpositive:=boundedSOS_functional_nonneg E hE hback'
  have hlzero:E (s n^3*centeredSubstitution mu l)=0:=functional_centered_linear h hh Z hZ l hl
  simp only [map_add,map_sub,hlzero,sub_zero] at hpositive
  have hQabs:=CenteredQuarticBound.functional_centered_quartic_abs_le hn h hh Z hZ hcons Q hQ
    hQbound
  change |E (centeredSubstitution mu Q)|≤_ at hQabs
  have hupper:=le_trans (le_abs_self (E (centeredSubstitution mu Q))) hQabs
  dsimp only [E] at hpositive
  nlinarith

end SelectorFunctionalLower
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
