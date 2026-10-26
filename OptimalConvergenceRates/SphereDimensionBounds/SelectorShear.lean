import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.QuarticDivisionSOS
import OptimalConvergenceRates.SphereDimensionBounds.AffineKernelBridge

/-! Actual linear shears and centered polynomial substitution for the
finite selector dual. Degree and centering relations are literal. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.SelectorShear
open scoped BigOperators
open MvPolynomial WeightedQuadraticSplit CubicSpectralDivision SelectorFunctional
  ChebyshevSOSKernel

abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

def shear {n : ℕ} (mu : Fin n → ℝ) : Point (Fin (n+1))→ₗ[ℝ]Point (Fin (n+1)) where
  toFun x:=(WithLp.equiv 2 (Fin (n+1)→ℝ)).symm
    (Fin.cases (x 0) (fun i=>x i.succ+mu i*x 0))
  map_add' x y:=by
    ext i
    refine Fin.cases (by simp) (fun j=>?_) i
    change (x j.succ+y j.succ)+mu j*(x 0+y 0)=
      (x j.succ+mu j*x 0)+(y j.succ+mu j*y 0)
    ring
  map_smul' r x:=by
    ext i
    refine Fin.cases (by simp) (fun j=>?_) i
    change r*x j.succ+mu j*(r*x 0)=r*(x j.succ+mu j*x 0)
    ring

@[simp] theorem shear_zero {n : ℕ} (mu : Fin n → ℝ) (x : Point (Fin (n + 1))) : shear mu x 0=x 0:=rfl
@[simp] theorem shear_succ {n : ℕ} (mu : Fin n → ℝ) (x : Point (Fin (n + 1))) (i : Fin n) :
    shear mu x i.succ=x i.succ+mu i*x 0:=rfl

theorem shear_inverse {n : ℕ} (mu : Fin n → ℝ) (x : Point (Fin (n + 1))) :
    shear mu (shear (-mu) x)=x:=by
  ext i
  refine Fin.cases (by simp) (fun j=>?_) i
  simp only [shear_succ,shear_zero,Pi.neg_apply]
  ring

def centeredSubstitution {n : ℕ} (mu : Fin n → ℝ) : Poly n→+*Poly (n+1):=
  eval₂Hom C (centeredCoordinate mu)

theorem centeredSubstitution_homogeneous {n k : ℕ} (mu : Fin n → ℝ) (p : Poly n)
    (hp : p.IsHomogeneous k) : (centeredSubstitution mu p).IsHomogeneous k:=by
  apply CubicPrefixPadding.homogeneous_linear_substitution _ _ p hp
  intro i
  exact (isHomogeneous_X ℝ i.succ).sub ((isHomogeneous_X ℝ (0:Fin (n+1))).C_mul (mu i))

theorem centeredSubstitution_eval {n : ℕ} (mu : Fin n → ℝ) (p : Poly n) (x : Point (Fin (n + 1))) :
    eval (fun j=>x j) (centeredSubstitution mu p)=eval (fun i=>x i.succ-mu i*x 0) p:=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp [centeredSubstitution]
  | add p q hp hq=>simp [map_add,hp,hq]
  | mul_X p i hp=>
    simp only [map_mul,hp,eval_X]
    congr 1
    simp only [centeredSubstitution,eval₂Hom_X',centeredCoordinate,map_sub,map_mul,eval_C,eval_X,s]

theorem inverse_shear_transverse {n : ℕ} (mu : Fin n → ℝ) (p : Poly n) :
    composition (shear (-mu)) (transverse p)=centeredSubstitution mu p:=by
  apply MvPolynomial.funext
  intro x
  let xx:Point (Fin (n+1)):=OrderedCubicExpansion.evaluationPoint x
  change eval (fun j=>xx j) (composition (shear (-mu)) (transverse p))=
    eval (fun j=>xx j) (centeredSubstitution mu p)
  rw [composition_eval,centeredSubstitution_eval]
  change eval (fun j=>shear (-mu) xx j) (rename Fin.succ p)=_
  rw [eval_rename]
  apply congrArg (fun f:Fin n→ℝ=>eval f p)
  funext i
  change xx i.succ+(-mu i)*xx 0=xx i.succ-mu i*xx 0
  ring

theorem inverse_shear_scalar {n : ℕ} (mu : Fin n → ℝ) : composition (shear (-mu)) (s n)=s n:=by
  apply MvPolynomial.funext
  intro x
  let xx:Point (Fin (n+1)):=OrderedCubicExpansion.evaluationPoint x
  change eval (fun j=>xx j) (composition (shear (-mu)) (s n))=eval (fun j=>xx j) (s n)
  rw [composition_eval]
  simp only [s,eval_X,shear_zero]

theorem inverse_shear_composition {n : ℕ} (mu : Fin n → ℝ) (p : Poly (n + 1)) :
    composition (shear (-mu)) (composition (shear mu) p)=p:=by
  apply MvPolynomial.funext
  intro x
  let xx:Point (Fin (n+1)):=OrderedCubicExpansion.evaluationPoint x
  change eval (fun j=>xx j) (composition (shear (-mu)) (composition (shear mu) p))=eval (fun j=>xx j) p
  rw [composition_eval,composition_eval,shear_inverse]

theorem boundedSOS_composition {n r : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n))
    {p : Poly n} (hp : BoundedSOS r p) : BoundedSOS r (composition F p):=by
  apply AffineKernelBridge.boundedSOS_affine_substitution _ _ hp
  intro i
  exact (coordinatePolynomial_homogeneous F i).totalDegree_le

/-- Every homogeneous centered linear term is annihilated once its
coordinate third moments vanish. -/
theorem centered_linear_annihilated {n : ℕ} (E : Poly (n + 1) →ₗ[ℝ] ℝ)
    (mu : Fin n → ℝ) (l : Poly n) (hl : l.IsHomogeneous 1)
    (hm : ∀ i, E (s n ^ 3 * centeredCoordinate mu i) = 0) :
    E (s n^3*centeredSubstitution mu l)=0:=by
  obtain ⟨c,hc⟩:=SelectorPolynomial.exists_linPolynomial l hl
  rw [←hc,SelectorPolynomial.linPolynomial_apply]
  have heq:centeredSubstitution mu (∑ i,C (c i)*X i)=∑ i,C (c i)*centeredCoordinate mu i:=by
    simp [centeredSubstitution]
  rw [heq,Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hid:s n^3*(C (c i)*centeredCoordinate mu i)=C (c i)*(s n^3*centeredCoordinate mu i):=by ring
  rw [hid,TensorMomentFunctional.linearMap_C_mul,hm,mul_zero]

/-- The actual finite PSD-marginal centering supplies these relations,
including leading mass zero; no U>0 hypothesis is required. -/
theorem functional_centered_linear {I : Type*} [Fintype I] {n : ℕ}
    (h : I → SelectorCentering.EP n) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (l : Poly n) (hl : l.IsHomogeneous 1) :
    functional (fun t i=>h t i) Z (s n^3*centeredSubstitution (fun i=>SelectorCentering.centeringVector h Z i) l)=0:=by
  apply centered_linear_annihilated _ _ l hl
  intro i
  exact functional_centered_third_moment h hh Z hZ i

end OptimalConvergenceRates.SphereDimensionBounds.SelectorShear
