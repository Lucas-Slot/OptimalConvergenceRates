import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.SelectorShear

/-! Actual centered quartic bound for the finite PSD selector functional.
The centering vector and its zero-leading-mass cases are the frozen ones. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.CenteredQuarticBound
open scoped BigOperators
open MvPolynomial WeightedQuadraticSplit SelectorFunctional SelectorShear SelectorCentering

abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

def centeredProjection {n : ℕ} (mu : Fin n → ℝ) : EP (n+1)→ₗ[ℝ]EP n where
  toFun x:=(WithLp.equiv 2 (Fin n→ℝ)).symm (fun i=>x i.succ-mu i*x 0)
  map_add' x y:=by
    ext i
    change (x i.succ+y i.succ)-mu i*(x 0+y 0)=
      (x i.succ-mu i*x 0)+(y i.succ-mu i*y 0)
    ring
  map_smul' r x:=by
    ext i
    change r*x i.succ-mu i*(r*x 0)=r*(x i.succ-mu i*x 0)
    ring

@[simp] theorem centeredProjection_apply {n : ℕ} (mu : Fin n → ℝ) (x : EP (n + 1)) (i : Fin n) :
    centeredProjection mu x i=x i.succ-mu i*x 0:=rfl

theorem centeredProjection_axis {n : ℕ} (mu : EP n) :
    centeredProjection (fun i=>mu i) (axis n)=-mu:=by
  ext i
  simp [centeredProjection_apply,axis]

theorem centeredProjection_embed {n : ℕ} (mu : Fin n → ℝ) (x : EP n) :
    centeredProjection mu (SelectorFunctional.embed (fun i=>x i))=x:=by
  ext i
  simp [centeredProjection_apply,SelectorFunctional.embed]

theorem centeredProjection_polynomial_eval {n : ℕ} (mu : Fin n → ℝ) (Q : Poly n) (x : EP (n + 1)) :
    euclideanPolynomialEval (centeredSubstitution mu Q) x=
      euclideanPolynomialEval Q (centeredProjection mu x):=by
  change eval (fun i=>x i) (centeredSubstitution mu Q)=
    eval (fun i=>centeredProjection mu x i) Q
  exact centeredSubstitution_eval mu Q x

/-- A pointwise bound on an actual nonnegative polynomial gives the
same bound on the actual sphere supremum norm. -/
theorem sphereSupNorm_le {n : ℕ} (hn : 0 < n) (Q : Poly n) {D : ℝ}
    (hQ : ∀ x:Fin n→ℝ,0≤eval x Q ∧ eval x Q≤D*(∑ i,x i^2)^2) :
    OptimalConvergenceRates.SphereDimensionBounds.Foundation.sphereSupNorm Q≤D:=by
  have hne:{v:ℝ|∃ x∈OptimalConvergenceRates.SphereDimensionBounds.Foundation.unitSphere n,|eval x Q|=v}.Nonempty:=by
    let i:Fin n:=⟨0,hn⟩
    let x:Fin n→ℝ:=Pi.single i 1
    refine ⟨|eval x Q|,x,?_,rfl⟩
    change (∑ j,(x j)^2)=1
    simp [x,Pi.single_apply]
  apply csSup_le hne
  intro v hv
  obtain ⟨x,hx,rfl⟩:=hv
  rw [abs_of_nonneg (hQ x).1]
  have hh:=(hQ x).2
  change (∑ i,x i^2)=1 at hx
  simpa only [hx,one_pow,mul_one] using hh

/-- The actual finite PSD marginal functional obeys the centered quartic
bound with the original pointwise constant. No U>0 or transported
pointwise-positivity premise is required. -/
theorem functional_centered_quartic_abs_le {I : Type*} [Fintype I] {n : ℕ} (hn : 0 < n)
    (h : I → EP n) (hh : ∀ t, ‖h t‖ = 1) (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : ∀ t, (Z t).PosSemidef) (hcons : QuadraticConsistency h Z)
    (Q : Poly n) (hQ : Q.IsHomogeneous 4) {D : ℝ}
    (hbound : ∀ x:Fin n→ℝ,0≤eval x Q ∧ eval x Q≤D*(∑ i,x i^2)^2) :
    |functional (fun t i=>h t i) Z
      (centeredSubstitution (fun i=>centeringVector h Z i) Q)|≤
        (332/3:ℝ)*D*diagonalMass Z 2:=by
  let mu:=centeringVector h Z
  let L:EP (n+1)→L[ℝ]EP n:=(centeredProjection (fun i=>mu i)).toContinuousLinearMap
  have hpull:∀ x,euclideanPolynomialEval (centeredSubstitution (fun i=>mu i) Q) x=
      euclideanPolynomialEval Q (L x):=centeredProjection_polynomial_eval _ Q
  have he:L (axis n)=-centeringVector h Z:=centeredProjection_axis mu
  have hv:∀ t,L (SelectorFunctional.embed (fun i=>h t i))=h t:=fun t=>centeredProjection_embed _ _
  have hmain:=functional_pullback_abs_le hn Q hQ (centeredSubstitution (fun i=>mu i) Q)
    (centeredSubstitution_homogeneous _ Q hQ) L hpull h hh Z hZ hcons he hv
  have hsup:=sphereSupNorm_le hn Q hbound
  have hW:0≤diagonalMass Z 2:=diagonalMass_nonneg Z hZ 2
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsup (by norm_num : (0:ℝ)≤332/3)) hW)

end OptimalConvergenceRates.SphereDimensionBounds.CenteredQuarticBound
