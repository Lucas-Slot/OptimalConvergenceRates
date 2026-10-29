import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CubicTaylorBounds
import Mathlib.Algebra.MvPolynomial.Funext

/-! An actual jointly homogeneous polynomial for the cubic Taylor model.
The old center and displacement variables are kept separate before the
literal substitution h=x-y. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace BivariateTaylorPolynomial

open scoped BigOperators
open MvPolynomial Foundation DegreeTaylorBounds CubicTaylorBounds

theorem weighted_homogeneous_substitution {ι κ : Type*} (w : ι → ℕ)
    (f : ι → MvPolynomial κ ℝ) (hf : ∀ i, (f i).IsHomogeneous (w i))
    (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.IsWeightedHomogeneous w d) :
    ((eval₂Hom C f) p).IsHomogeneous d := by
  classical
  rw [←p.support_sum_monomial_coeff,map_sum]
  apply IsHomogeneous.sum
  intro a ha
  rw [eval₂Hom_monomial]
  have hdeg : (∑ i∈a.support,w i*a i)=d := by
    simpa only [Finsupp.weight_apply,Finsupp.sum,smul_eq_mul,Nat.mul_comm] using
      hp (mem_support_iff.mp ha)
  have hprod : (a.prod (fun i e ↦ f i^e)).IsHomogeneous (∑ i∈a.support,w i*a i) := by
    apply IsHomogeneous.prod
    intro i hi
    exact (hf i).pow (a i)
  simpa only [hdeg] using hprod.C_mul (p.coeff a)

theorem component_homogeneous_substitution {ι κ : Type*} (w : ι → ℕ)
    (f : ι → MvPolynomial κ ℝ) (hf : ∀ i, (f i).IsHomogeneous (w i))
    (p : MvPolynomial ι ℝ) (j : ℕ) :
    (eval₂Hom C f) (weightedHomogeneousComponent w j p)=
      homogeneousComponent j ((eval₂Hom C f) p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial a c =>
      have hmono := isWeightedHomogeneous_monomial w a c rfl
      have hspec := weighted_homogeneous_substitution w f hf (monomial a c) hmono
      rw [weightedHomogeneousComponent_of_mem hmono,homogeneousComponent_of_mem hspec]
      split_ifs <;> simp

theorem weightedComponent_preserves_homogeneous {ι : Type*} (w : ι → ℕ)
    (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.IsHomogeneous d) (j : ℕ) :
    (weightedHomogeneousComponent w j p).IsHomogeneous d := by
  classical
  intro a ha
  apply hp
  intro hz
  simp only [coeff_weightedHomogeneousComponent,hz,ite_self] at ha
  exact ha rfl

theorem eval_substitution {ι κ : Type*} (f : ι → MvPolynomial κ ℝ)
    (p : MvPolynomial ι ℝ) (x : κ → ℝ) :
    eval x ((eval₂Hom C f) p)=eval (fun i ↦ eval x (f i)) p := by
  change eval x (eval₂ C f p)=_
  rw [←eval_assoc]
  rfl

abbrev Joint (n : ℕ) := MvPolynomial (Fin n⊕Fin n) ℝ

def liftVariables (n : ℕ) (i : Fin n) : Joint n := X (Sum.inl i)+X (Sum.inr i)
def jointLift {n : ℕ} (p : P n) : Joint n := (eval₂Hom C (liftVariables n)) p
def displacementWeight {n : ℕ} : (Fin n⊕Fin n) → ℕ := Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)
def jointTruncation {n : ℕ} (p : P n) : Joint n :=
  ∑ j ∈ Finset.range 4,weightedHomogeneousComponent displacementWeight j (jointLift p)

def specializeVariables {n : ℕ} (y : Point n) : (Fin n⊕Fin n) → P n :=
  Sum.elim (fun i ↦ C (y i)) X
def specialize {n : ℕ} (y : Point n) : Joint n →+* P n := eval₂Hom C (specializeVariables y)

theorem specializeVariables_homogeneous {n : ℕ} (y : Point n) (i : Fin n ⊕ Fin n) :
    (specializeVariables y i).IsHomogeneous (displacementWeight i) := by
  cases i with
  | inl i => exact isHomogeneous_C (Fin n) (y i)
  | inr i => exact isHomogeneous_X ℝ _

theorem specialize_eval {n : ℕ} (y h : Point n) (F : Joint n) :
    evalForm (specialize y F) h=eval (Sum.elim (fun i ↦ y i) (fun i ↦ h i)) F := by
  rw [evalForm,show specialize y F=(eval₂Hom C (specializeVariables y)) F from
    rfl,eval_substitution]
  apply congrArg (fun z ↦ eval z F)
  funext i
  cases i <;> simp [specializeVariables]

theorem specialize_jointLift {n : ℕ} (y : Point n) (p : P n) :
    specialize y (jointLift p)=shifted y p := by
  apply MvPolynomial.funext
  intro h
  let hv : Point n := (WithLp.equiv 2 (Fin n → ℝ)).symm h
  change evalForm (specialize y (jointLift p)) hv=evalForm (shifted y p) hv
  rw [specialize_eval,jointLift,eval_substitution,evalForm_shifted]
  apply congrArg (fun z ↦ eval z p)
  funext i
  simp only [liftVariables,eval_add,eval_X,Sum.elim_inl,Sum.elim_inr,PiLp.add_apply]

theorem specialize_jointTruncation {n : ℕ} (y : Point n) (p : P n) :
    specialize y (jointTruncation p)=cubicModel y p := by
  change specialize y (∑ j∈Finset.range 4,weightedHomogeneousComponent displacementWeight j
    (jointLift p))=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show specialize y=(eval₂Hom C (specializeVariables y)) from rfl,
    component_homogeneous_substitution displacementWeight (specializeVariables y)
      (specializeVariables_homogeneous y),←show specialize y=(eval₂Hom C (specializeVariables y))
        from rfl,
    specialize_jointLift]

theorem jointLift_homogeneous {n d : ℕ} (p : P n) (hp : p.IsHomogeneous d) :
    (jointLift p).IsHomogeneous d := by
  apply weighted_homogeneous_substitution 1 (liftVariables n) _ p hp
  intro i
  exact (isHomogeneous_X ℝ (Sum.inl i)).add (isHomogeneous_X ℝ (Sum.inr i))

theorem jointTruncation_homogeneous {n d : ℕ} (p : P n) (hp : p.IsHomogeneous d) :
    (jointTruncation p).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro j hj
  exact weightedComponent_preserves_homogeneous displacementWeight (jointLift p)
    (jointLift_homogeneous p hp) j

def chordVariables (n : ℕ) : (Fin n⊕Fin n) → Joint n :=
  Sum.elim (fun i ↦ X (Sum.inr i)) (fun i ↦ X (Sum.inl i)-X (Sum.inr i))
def bivariateTaylor {n : ℕ} (p : P n) : Joint n := (eval₂Hom C (chordVariables n))
  (jointTruncation p)

theorem bivariateTaylor_homogeneous {n d : ℕ} (p : P n) (hp : p.IsHomogeneous d) :
    (bivariateTaylor p).IsHomogeneous d := by
  apply weighted_homogeneous_substitution 1 (chordVariables n) _ (jointTruncation p)
    (jointTruncation_homogeneous p hp)
  intro i
  cases i with
  | inl i => exact isHomogeneous_X ℝ _
  | inr i => exact (isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _)

theorem bivariateTaylor_eval {n : ℕ} (p : P n) (x y : Point n) :
    eval (Sum.elim (fun i ↦ x i) (fun i ↦ y i)) (bivariateTaylor p)=
      evalForm (cubicModel y p) (x-y) := by
  rw [bivariateTaylor,eval_substitution,←specialize_jointTruncation y p,specialize_eval]
  apply congrArg (fun z ↦ eval z (jointTruncation p))
  funext i
  cases i <;> simp [chordVariables]

end BivariateTaylorPolynomial
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
