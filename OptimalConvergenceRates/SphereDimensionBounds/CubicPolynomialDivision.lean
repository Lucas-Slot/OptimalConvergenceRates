import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.CubicPrefixPadding
import OptimalConvergenceRates.SphereDimensionBounds.SymmetricCubicTensor

/-! Actual polynomial cubic division: no trilinear tensor representation
is an extra hypothesis. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.CubicPolynomialDivision
open scoped BigOperators
open MvPolynomial WeightedQuadraticSplit WeightedCubicSplit OrderedCubicExpansion

local instance (priority := 2000) finOrderDecidableEq (n : ℕ) : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

theorem cubicFromTri_tensor {n : ℕ} (t : Fin n → Fin n → Fin n → ℝ) :
    cubicFromTri (tensorForm t)=cubicPolynomial t:=by
  apply MvPolynomial.funext
  intro x
  rw [cubicFromTri_eval]
  exact (cubicPolynomial_eval t (evaluationPoint x)).symm

/-- Every actual homogeneous cubic satisfying the original diagonal
weighted source bound has genuine homogeneous quadratic polynomial roots. -/
theorem exists_quadratic_division {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 3)
    (hdom : ∀ x:Point (Fin n),|eval (fun i=>x i) p|≤2*‖diagonal a x‖*‖x‖^2) :
    ∃ b:Fin n→MvPolynomial (Fin n) ℝ,(∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,C (a i)*X i*b i)=p ∧
      ∀ h:Point (Fin n),‖(WithLp.equiv 2 (Fin n→ℝ)).symm
        (fun i=>eval (fun j=>h j) (b i))‖≤80*((Nat.clog 2 n:ℝ)+1)*‖h‖^2:=by
  obtain ⟨t,ht12,ht23,htp⟩:=SymmetricCubicTensor.exists_symmetric_tensor p hp
  have hd:∀ x:Point (Fin n),|diagonalCubic (tensorForm t) x|≤2*‖diagonal a x‖*‖x‖^2:=by
    intro x
    rw [←cubicPolynomial_eval,htp]
    exact hdom x
  obtain ⟨b,hb,hid,hbound⟩:=CubicPrefixPadding.exists_quadratic_division hn a ha hmono (tensorForm t)
    (tensorForm_symm12 t ht12) (tensorForm_symm23 t ht23) hd
  rw [cubicFromTri_tensor,htp] at hid
  exact ⟨b,hb,hid,hbound⟩

/-- The squared norm cost is precisely6400L², before selector centering
and radial repair add their separate costs. -/
theorem exists_quadratic_division_sq {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 3)
    (hdom : ∀ x:Point (Fin n),|eval (fun i=>x i) p|≤2*‖diagonal a x‖*‖x‖^2) :
    ∃ b:Fin n→MvPolynomial (Fin n) ℝ,(∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,C (a i)*X i*b i)=p ∧
      ∀ h:Point (Fin n),(∑ i,(eval (fun j=>h j) (b i))^2)≤
        6400*((Nat.clog 2 n:ℝ)+1)^2*‖h‖^4:=by
  obtain ⟨b,hb,hid,hbound⟩:=exists_quadratic_division hn a ha hmono p hp hdom
  refine ⟨b,hb,hid,?_⟩
  intro h
  have hh:=(sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0≤80*((Nat.clog 2 n:ℝ)+1)*‖h‖^2)).mpr (hbound h)
  rw [norm_sq] at hh
  simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply] at hh
  convert hh using 1 <;> ring

end OptimalConvergenceRates.SphereDimensionBounds.CubicPolynomialDivision
