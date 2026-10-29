import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Matrix.Order
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CubicSpectralDivision
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.QuadraticBoundSOS

/-! Actual polynomial division from the quadratic-cubic discriminant
hypothesis. The nonnegative square-root operator is constructed. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace CubicDiscriminantDivision
open scoped BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
open MvPolynomial WeightedQuadraticSplit CubicSpectralDivision SelectorPolynomial

local instance (priority := 2000) finOrderDecidableEq (n : ℕ) : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

theorem nonnegative_quadratic_operator {n : ℕ} (A : MvPolynomial (Fin n) ℝ)
    (hA : A.IsHomogeneous 2) (hpos : ∀ x:Fin n→ℝ,0≤eval x A) :
    ∃ L:Point (Fin n)→ₗ[ℝ]Point (Fin n),L.IsSymmetric ∧
      (∀ x,0≤⟪L x,x⟫_ℝ) ∧ ∀ x:Point (Fin n),‖L x‖^2=eval (fun i↦x i) A:=by
  obtain ⟨H,hH⟩:=SelectorPolynomial.exists_quadPolynomial A hA
  let S:=QuadraticBoundSOS.symmetricMatrix H
  have hSeval (x:Fin n→ℝ) : SelectorCone.quadEval x S=eval x A:=by
    rw [←quadPolynomial_eval,QuadraticBoundSOS.symmetricMatrix_eval,hH]
  have hS:Matrix.PosSemidef S:=by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i j
      simp only [Matrix.conjTranspose_apply,star_trivial,QuadraticBoundSOS.symmetricMatrix,S]
      ring
    · intro x
      have hh:=hpos x
      rw [←hSeval] at hh
      simp only [star_trivial,Matrix.mulVec,dotProduct,Finset.mul_sum]
      simp only [SelectorCone.quadEval,LinearMap.coe_mk,AddHom.coe_mk] at hh
      convert hh using 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  let D:=CFC.sqrt S
  let L:=Matrix.toEuclideanLin D
  have hD:Matrix.PosSemidef D:=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
  have hL:L.IsSymmetric:=Matrix.isSymmetric_toEuclideanLin_iff.mpr hD.1
  have hLL (x:Point (Fin n)) : L (L x)=Matrix.toEuclideanLin S x:=by
    ext i
    change (D*ᵥ(D*ᵥ(fun j↦x j))) i=(S*ᵥ(fun j↦x j)) i
    rw [Matrix.mulVec_mulVec,CFC.sqrt_mul_sqrt_self S hS.nonneg]
  refine ⟨L,hL,?_,?_⟩
  · intro x
    have hh:=hD.dotProduct_mulVec_nonneg (fun i↦x i)
    simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,star_trivial,
      L,Matrix.toLpLin_apply] using! hh
  · intro x
    calc
      ‖L x‖^2=⟪L x,L x⟫_ℝ:=(real_inner_self_eq_norm_sq _).symm
      _=⟪x,L (L x)⟫_ℝ:=hL x (L x)
      _=⟪x,Matrix.toEuclideanLin S x⟫_ℝ:=by rw [hLL]
      _=SelectorCone.quadEval (fun i↦x i) S:=by
        simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
          Matrix.toLpLin_apply,Matrix.mulVec,dotProduct,Finset.sum_mul,
          SelectorCone.quadEval,LinearMap.coe_mk,AddHom.coe_mk]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _=eval (fun i↦x i) A:=hSeval _

/-- The actual discriminant hypothesis produces actual linear roots for
A and actual quadratic roots dividing B, with the sharp logarithmic
squared norm budget. No factorization operator is an input. -/
theorem exists_division_of_discriminant {n : ℕ} (hn : 0 < n)
    (A B : MvPolynomial (Fin n) ℝ) (hA : A.IsHomogeneous 2) (hB : B.IsHomogeneous 3)
    (hA0 : ∀ x:Fin n→ℝ,0≤eval x A) {M:ℝ} (hM:0≤M)
    (hdisc:∀ x:Point (Fin n),(eval (fun i↦x i) B)^2≤4*M*eval (fun i↦x i) A*‖x‖^4) :
    ∃ (l b:Fin n→MvPolynomial (Fin n) ℝ),
      (∀ i,(l i).IsHomogeneous 1) ∧ (∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,l i^2)=A ∧ (∑ i,l i*b i)=B ∧
      ∀ x:Point (Fin n),(∑ i,(eval (fun j↦x j) (b i))^2)≤
        6400*((Nat.clog 2 n:ℝ)+1)^2*M*‖x‖^4:=by
  obtain ⟨L,hL,hLp,hLA⟩:=nonnegative_quadratic_operator A hA hA0
  have hd:∀ x:Point (Fin n),|eval (fun i↦x i) B|≤2*Real.sqrt M*‖L x‖*‖x‖^2:=by
    intro x
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*Real.sqrt M*‖L x‖*‖x‖^2)).mp
    rw [sq_abs]
    have hh:=hdisc x
    rw [←hLA] at hh
    have hs:(2*Real.sqrt M*‖L x‖*‖x‖^2)^2=4*M*‖L x‖^2*‖x‖^4:=by
      simp only [mul_pow,Real.sq_sqrt hM]
      ring
    rw [hs]
    exact hh
  obtain ⟨b,hb,hid,hbound⟩:=CubicSpectralDivision.exists_quadratic_division_scaled hn L hL hLp B
    hB hM hd
  refine ⟨coordinatePolynomial L,b,coordinatePolynomial_homogeneous L,hb,?_,hid,hbound⟩
  apply MvPolynomial.funext
  intro x
  let xx:Point (Fin n):=OrderedCubicExpansion.evaluationPoint x
  simp only [map_sum,map_pow]
  change (∑ i,(eval (fun j↦xx j) (coordinatePolynomial L i))^2)=eval (fun j↦xx j) A
  simp only [coordinatePolynomial_eval]
  rw [←norm_sq]
  exact hLA xx

end CubicDiscriminantDivision
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
