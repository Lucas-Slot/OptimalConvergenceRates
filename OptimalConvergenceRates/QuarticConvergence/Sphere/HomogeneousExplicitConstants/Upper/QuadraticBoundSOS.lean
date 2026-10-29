import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SelectorPolynomial
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.RadialQuarticSOS

/-! Actual finite SOS factorizations for the scalar quadratic remainder
in the local selector proof. Positivity hypotheses are on actual
quadratic polynomials, and the proof constructs linear/quadratic roots. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace QuadraticBoundSOS

open scoped BigOperators Matrix
open MvPolynomial SelectorPolynomial

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℝ

def linearRoot {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Poly n :=
  ∑ j,C (K i j)*X j

theorem linearRoot_homogeneous {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (linearRoot K i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_X ℝ j).C_mul _

@[simp] theorem linearRoot_eval {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    eval x (linearRoot K i)=(K*ᵥx) i := by
  simp [linearRoot,Matrix.mulVec,dotProduct]

def symmetricMatrix {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (H i j+H j i)/2

theorem symmetricMatrix_symm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    (symmetricMatrix H).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply,symmetricMatrix]
  ring

theorem symmetricMatrix_eval {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    eval x (quadPolynomial (symmetricMatrix H))=eval x (quadPolynomial H) := by
  simp only [quadPolynomial_eval,SelectorCone.quadEval,LinearMap.coe_mk,
    AddHom.coe_mk,symmetricMatrix,add_div,add_mul,Finset.sum_add_distrib]
  have heq : (∑ i,∑ j,H j i/2*x i*x j)=(∑ i,∑ j,H i j/2*x i*x j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every globally nonnegative actual homogeneous quadratic has a finite
sum of homogeneous linear squares, with no strict positivity premise. -/
theorem nonnegative_quadratic_exists_squares {n : ℕ} (p : Poly n)
    (hp : p.IsHomogeneous 2) (hpos : ∀ x : Fin n→ℝ,0≤eval x p) :
    ∃ q : Fin n→Poly n,(∀ i,(q i).IsHomogeneous 1) ∧ p=∑ i,q i^2 := by
  obtain ⟨H,hH⟩ := exists_quadPolynomial p hp
  let S := symmetricMatrix H
  have hSeval (x : Fin n→ℝ) : eval x (quadPolynomial S)=eval x p := by
    rw [symmetricMatrix_eval,hH]
  have hform (x : RadialQuarticSOS.Point n) :
      RadialQuarticSOS.matrixBilinear S x x=eval (fun i↦x i) p := by
    rw [←RadialQuarticSOS.coordinateMatrix_eval,RadialQuarticSOS.coordinateMatrix_matrixBilinear,
      ←hSeval,quadPolynomial_eval]
    simp [SelectorCone.quadEval,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc,
      mul_comm,mul_left_comm]
  obtain ⟨K,hK⟩ := RadialQuarticSOS.nonnegative_form_exists_squares
    (RadialQuarticSOS.matrixBilinear S)
    (RadialQuarticSOS.matrixBilinear_symmetric S (symmetricMatrix_symm H))
    (fun x ↦ by rw [hform];exact hpos _)
  refine ⟨linearRoot K,linearRoot_homogeneous K,?_⟩
  apply MvPolynomial.funext
  intro x
  have hx := hK ((WithLp.equiv 2 (Fin n→ℝ)).symm x)
  rw [hform] at hx
  simpa only [map_sum,map_pow,linearRoot_eval] using! hx

/-- A product of globally nonnegative homogeneous quadratics has an
actual finite homogeneous-quadratic square representation. -/
theorem quadratic_product_exists_squares {n : ℕ} (p q : Poly n)
    (hp : p.IsHomogeneous 2) (hq : q.IsHomogeneous 2)
    (hp0 : ∀ x : Fin n→ℝ,0≤eval x p) (hq0 : ∀ x : Fin n→ℝ,0≤eval x q) :
    ∃ b : (Fin n×Fin n)→Poly n,(∀ i,(b i).IsHomogeneous 2) ∧ p*q=∑ i,b i^2 := by
  obtain ⟨u,hu,hequ⟩ := nonnegative_quadratic_exists_squares p hp hp0
  obtain ⟨v,hv,heqv⟩ := nonnegative_quadratic_exists_squares q hq hq0
  refine ⟨fun ij↦u ij.1*v ij.2,fun ij↦(hu ij.1).mul (hv ij.2),?_⟩
  rw [hequ,heqv,Fintype.sum_prod_type]
  simp only [mul_pow,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The scalar free-entry remainder in §1.9 is an actual global SOS,
with root degree exactly2; no radial multiplier is needed here. -/
theorem bounded_quadratic_difference_exists_squares {n : ℕ} (u : Poly n)
    (hu : u.IsHomogeneous 2) (c : ℝ)
    (hbound : ∀ x : Fin n→ℝ,|eval x u|≤c*(∑ i,x i^2)) :
    ∃ b : (Fin n×Fin n)→Poly n,(∀ i,(b i).IsHomogeneous 2) ∧
      C (c^2)*(Foundation.radiusPolynomial n)^2-u^2=∑ i,b i^2 := by
  let R := Foundation.radiusPolynomial n
  have hR : R.IsHomogeneous 2 := by
    apply IsHomogeneous.sum
    intro i _
    exact (isHomogeneous_X ℝ i).pow 2
  have hp : (C c*R-u).IsHomogeneous 2 := (hR.C_mul c).sub hu
  have hq : (C c*R+u).IsHomogeneous 2 := (hR.C_mul c).add hu
  have hp0 (x : Fin n→ℝ) : 0≤eval x (C c*R-u) := by
    have hb := (abs_le.mp (hbound x)).2
    simpa only [R,map_sub,map_mul,eval_C,Foundation.radiusPolynomial_eval,
      sub_nonneg] using hb
  have hq0 (x : Fin n→ℝ) : 0≤eval x (C c*R+u) := by
    have hb := (abs_le.mp (hbound x)).1
    simp only [R,map_add,map_mul,eval_C,Foundation.radiusPolynomial_eval]
    linarith
  obtain ⟨b,hb,heq⟩ := quadratic_product_exists_squares (C c*R-u) (C c*R+u) hp hq hp0 hq0
  refine ⟨b,hb,?_⟩
  rw [←heq,map_pow]
  ring

/-- The exact scaled remainder produced by a positive leading selector
entry is therefore SOS with homogeneous quadratic roots. -/
theorem scaled_quadratic_difference_exists_squares {n : ℕ} (u : Poly n)
    (hu : u.IsHomogeneous 2) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hbound : ∀ x : Fin n→ℝ,(eval x u)^2/a≤c*(∑ i,x i^2)^2) :
    ∃ b : (Fin n×Fin n)→Poly n,(∀ i,(b i).IsHomogeneous 2) ∧
      C c*(Foundation.radiusPolynomial n)^2-C (1/a)*u^2=∑ i,b i^2 := by
  let v : Poly n := C (1/Real.sqrt a)*u
  have hv : v.IsHomogeneous 2 := hu.C_mul _
  have hv2 : v^2=C (1/a)*u^2 := by
    dsimp [v]
    rw [mul_pow,←map_pow]
    congr 1
    congr 1
    rw [div_pow,one_pow,Real.sq_sqrt ha.le]
  have hb (x : Fin n→ℝ) : |eval x v|≤Real.sqrt c*(∑ i,x i^2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤Real.sqrt c*(∑ i,x i^2))).mp
    rw [sq_abs,mul_pow,Real.sq_sqrt hc]
    have hev : (eval x v)^2=(eval x u)^2/a := by
      have hh := congrArg (eval x) hv2
      simpa only [map_pow,map_mul,eval_C,one_div_mul_eq_div] using hh
    rw [hev]
    exact hbound x
  obtain ⟨b,hbdeg,hbeq⟩ := bounded_quadratic_difference_exists_squares v hv (Real.sqrt c) hb
  refine ⟨b,hbdeg,?_⟩
  rw [Real.sq_sqrt hc,hv2] at hbeq
  exact hbeq

end QuadraticBoundSOS
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
