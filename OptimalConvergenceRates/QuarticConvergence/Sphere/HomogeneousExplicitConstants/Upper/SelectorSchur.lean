import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
/-! Pointwise Schur inequalities and exact polynomial square completion
for the quadratic selector constructed in `SelectorExistence`. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SelectorSchur

open scoped BigOperators Matrix

/-- The actual three-by-three selector matrix, with an arbitrary bottom entry. -/
def selectorMatrix (a l H B u F : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![a,l/2,u],![l/2,H-2*u,B/2],![u,B/2,F]]

/-- Its quadratic form on an actual real test vector. -/
theorem selectorMatrix_quadratic_nonneg {a l H B u F : ℝ}
    (hG : (selectorMatrix a l H B u F).PosSemidef) (x y z : ℝ) :
    0 ≤ a*x^2+l*x*y+2*u*x*z+(H-2*u)*y^2+B*y*z+F*z^2 := by
  have h := hG.dotProduct_mulVec_nonneg ![x,y,z]
  simp only [selectorMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    star_trivial, Finset.sum_empty, add_zero] at h
  convert h using 1; ring

/-- Completing the first coordinate gives the full two-by-two Schur form. -/
theorem schur_quadratic_nonneg {a l H B u F : ℝ} (ha : 0 < a)
    (hG : (selectorMatrix a l H B u F).PosSemidef) (y z : ℝ) :
    0 ≤ (H-l^2/(4*a)-2*u)*y^2+(B-l*u/a)*y*z+(F-u^2/a)*z^2 := by
  have h := selectorMatrix_quadratic_nonneg hG (-(l*y/2+u*z)/a) y z
  have hid :
      a*(-(l*y/2+u*z)/a)^2+l*(-(l*y/2+u*z)/a)*y+
        2*u*(-(l*y/2+u*z)/a)*z+(H-2*u)*y^2+B*y*z+F*z^2 =
      (H-l^2/(4*a)-2*u)*y^2+(B-l*u/a)*y*z+(F-u^2/a)*z^2 := by
    field_simp [ha.ne']; ring
  rwa [hid] at h

/-- The two diagonal and determinant inequalities of the actual Schur form. -/
theorem schur_complement_bounds {a l H B u F : ℝ} (ha : 0 < a)
    (hG : (selectorMatrix a l H B u F).PosSemidef) :
    0 ≤ H-l^2/(4*a)-2*u ∧
    0 ≤ F-u^2/a ∧
    (B-l*u/a)^2 ≤ 4*(H-l^2/(4*a)-2*u)*(F-u^2/a) := by
  have hA := schur_quadratic_nonneg ha hG 1 0
  have hJ := schur_quadratic_nonneg ha hG 0 1
  have hd := discrim_le_zero (a:=H-l^2/(4*a)-2*u) (b:=B-l*u/a)
    (c:=F-u^2/a) (fun y ↦ by
      simpa only [pow_two, mul_one, one_pow] using schur_quadratic_nonneg ha hG y 1)
  simp only [one_pow, zero_pow (by norm_num : (2:ℕ)≠0), mul_one,
    mul_zero, zero_add, add_zero] at hA hJ
  exact ⟨hA,hJ,by simpa only [discrim,sub_nonpos] using hd⟩

/-- Bounds in the form needed by the cubic-radius completion. -/
theorem selector_scalar_bounds {a l H B u F : ℝ} (ha : 0 < a)
    (hG : (selectorMatrix a l H B u F).PosSemidef) :
    0 ≤ H-l^2/(4*a)-2*u ∧
    u^2/a ≤ F ∧
    (B-l*u/a)^2 ≤ 4*F*(H-l^2/(4*a)-2*u) := by
  obtain ⟨hA,hJ,hD⟩ := schur_complement_bounds ha hG
  have hu : 0≤u^2/a := div_nonneg (sq_nonneg _) ha.le
  refine ⟨hA,by linarith,?_⟩
  nlinarith [mul_nonneg hA hu]

private theorem scalar_completion_alpha (alpha s l H B u : ℝ) (ha : alpha ≠ 0) :
    alpha^2*s^4+l*s^3+H*s^2+B*s =
      (alpha*s^2+l*s/(2*alpha)+u/alpha)^2+
      s^2*(H-l^2/(4*alpha^2)-2*u)+s*(B-l*u/alpha^2)-u^2/alpha^2 := by
  field_simp [ha]; ring

/-- The real square identity, including all scalar inverse factors. -/
theorem scalar_completion {a : ℝ} (ha : 0 < a) (s l H B u : ℝ) :
    a*s^4+l*s^3+H*s^2+B*s =
      (Real.sqrt a*s^2+l*s/(2*Real.sqrt a)+u/Real.sqrt a)^2+
      s^2*(H-l^2/(4*a)-2*u)+s*(B-l*u/a)-u^2/a := by
  simpa only [Real.sq_sqrt ha.le] using
    scalar_completion_alpha (Real.sqrt a) s l H B u (Real.sqrt_pos.2 ha).ne'

section Polynomials

variable {ι : Type*}
abbrev Poly := MvPolynomial ι ℝ

/-- The remaining quadratic coefficient after the leading square. -/
def schurA (a : ℝ) (l H u : Poly (ι := ι)) : Poly (ι:=ι) :=
  H-MvPolynomial.C (1/(4*a))*l^2-2*u

/-- The remaining cubic coefficient after the leading square. -/
def schurD (a : ℝ) (l B u : Poly (ι := ι)) : Poly (ι:=ι) :=
  B-MvPolynomial.C (1/a)*l*u

/-- The actual polynomial root in the square completion. -/
def squareRoot (a : ℝ) (s l u : Poly (ι := ι)) : Poly (ι:=ι) :=
  MvPolynomial.C (Real.sqrt a)*s^2+
    MvPolynomial.C (1/(2*Real.sqrt a))*l*s+MvPolynomial.C (1/Real.sqrt a)*u

/-- The full quartic model, for arbitrary actual polynomial inputs. -/
def model (a : ℝ) (s l H B C0 : Poly (ι := ι)) : Poly (ι:=ι) :=
  MvPolynomial.C a*s^4+l*s^3+H*s^2+B*s+C0

/-- The uniformly conditioned quartic left after the cubic completion. -/
def radialRemainder (a S M : ℝ) (u R : Poly (ι := ι)) : Poly (ι:=ι) :=
  MvPolynomial.C (2*S*M)*R^2-MvPolynomial.C (1/a)*u^2

theorem schurA_homogeneous (a : ℝ) {l H u : Poly (ι := ι)}
    (hl : l.IsHomogeneous 1) (hH : H.IsHomogeneous 2) (hu : u.IsHomogeneous 2) :
    (schurA a l H u).IsHomogeneous 2 := by
  exact (hH.sub ((hl.pow 2).C_mul _)).sub (by
    simpa only [map_ofNat] using hu.C_mul (2:ℝ))

theorem schurD_homogeneous (a : ℝ) {l B u : Poly (ι := ι)}
    (hl : l.IsHomogeneous 1) (hB : B.IsHomogeneous 3) (hu : u.IsHomogeneous 2) :
    (schurD a l B u).IsHomogeneous 3 := by
  simpa only [schurD,mul_assoc] using hB.sub ((hl.mul hu).C_mul (1/a))

theorem squareRoot_homogeneous (a : ℝ) {s l u : Poly (ι := ι)}
    (hs : s.IsHomogeneous 1) (hl : l.IsHomogeneous 1) (hu : u.IsHomogeneous 2) :
    (squareRoot a s l u).IsHomogeneous 2 := by
  simpa only [squareRoot,mul_assoc] using
    (((hs.pow 2).C_mul (Real.sqrt a)).add
      ((hl.mul hs).C_mul (1/(2*Real.sqrt a)))).add (hu.C_mul (1/Real.sqrt a))

theorem squareRoot_degree (a : ℝ) {s l u : Poly (ι := ι)}
    (hs : s.IsHomogeneous 1) (hl : l.IsHomogeneous 1) (hu : u.IsHomogeneous 2) :
    (squareRoot a s l u).totalDegree ≤ 2 :=
  (squareRoot_homogeneous a hs hl hu).totalDegree_le

theorem model_homogeneous (a : ℝ) {s l H B C0 : Poly (ι := ι)}
    (hs : s.IsHomogeneous 1) (hl : l.IsHomogeneous 1) (hH : H.IsHomogeneous 2)
    (hB : B.IsHomogeneous 3) (hC : C0.IsHomogeneous 4) :
    (model a s l H B C0).IsHomogeneous 4 := by
  exact (((((hs.pow 4).C_mul a).add (hl.mul (hs.pow 3))).add
    (hH.mul (hs.pow 2))).add (hB.mul hs)).add hC

theorem radialRemainder_homogeneous (a S M : ℝ) {u R : Poly (ι := ι)}
    (hu : u.IsHomogeneous 2) (hR : R.IsHomogeneous 2) :
    (radialRemainder a S M u R).IsHomogeneous 4 :=
  ((hR.pow 2).C_mul _).sub ((hu.pow 2).C_mul _)

@[simp] theorem schurA_eval (a : ℝ) (l H u : Poly (ι := ι)) (x : ι → ℝ) :
    MvPolynomial.eval x (schurA a l H u) =
      MvPolynomial.eval x H-(MvPolynomial.eval x l)^2/(4*a)-2*MvPolynomial.eval x u := by
  simp only [schurA,map_sub,map_mul,map_pow,MvPolynomial.eval_C,map_ofNat]
  ring

@[simp] theorem schurD_eval (a : ℝ) (l B u : Poly (ι := ι)) (x : ι → ℝ) :
    MvPolynomial.eval x (schurD a l B u) =
      MvPolynomial.eval x B-MvPolynomial.eval x l*MvPolynomial.eval x u/a := by
  simp only [schurD,map_sub,map_mul,MvPolynomial.eval_C]
  ring

@[simp] theorem squareRoot_eval (a : ℝ) (s l u : Poly (ι := ι)) (x : ι → ℝ) :
    MvPolynomial.eval x (squareRoot a s l u) =
      Real.sqrt a*(MvPolynomial.eval x s)^2+
      MvPolynomial.eval x l*MvPolynomial.eval x s/(2*Real.sqrt a)+
      MvPolynomial.eval x u/Real.sqrt a := by
  simp only [squareRoot,map_add,map_mul,map_pow,MvPolynomial.eval_C]
  ring

/-- An equality of actual multivariate polynomials, not only their sphere
restrictions. Homogeneity assumptions are unnecessary for the algebra. -/
theorem polynomial_completion (a c : ℝ) (ha : 0 < a)
    (s l H B C0 u R : Poly (ι := ι)) :
    model a s l H B C0-C0+MvPolynomial.C c*R^2 =
      squareRoot a s l u^2+s^2*schurA a l H u+s*schurD a l B u+
        MvPolynomial.C c*R^2-MvPolynomial.C (1/a)*u^2 := by
  apply MvPolynomial.funext
  intro x
  simp only [model,map_add,map_sub,map_mul,map_pow,MvPolynomial.eval_C,
    schurA_eval,schurD_eval,squareRoot_eval]
  have h := scalar_completion ha (MvPolynomial.eval x s) (MvPolynomial.eval x l)
    (MvPolynomial.eval x H) (MvPolynomial.eval x B) (MvPolynomial.eval x u)
  linear_combination h

/-- The same actual polynomial identity with the precise two remaining
budgets used by the local radius-multiplier argument. -/
theorem polynomial_completion_budget (a S M c0 : ℝ) (ha : 0 < a)
    (s l H B C0 u R : Poly (ι := ι)) :
    model a s l H B C0-C0+MvPolynomial.C ((c0+2)*S*M)*R^2 =
      squareRoot a s l u^2+
        (s^2*schurA a l H u+s*schurD a l B u+MvPolynomial.C (c0*S*M)*R^2)+
        radialRemainder a S M u R := by
  rw [polynomial_completion a ((c0+2)*S*M) ha s l H B C0 u R]
  simp only [radialRemainder,map_mul,map_add,map_ofNat]
  ring

/-- Pointwise PSD of the actual polynomial selector gives all three
scalar inequalities, with the original radial bottom unchanged. -/
theorem polynomial_selector_bounds (a S M : ℝ) (ha : 0 < a)
    (l H B u R : Poly (ι := ι))
    (hG : ∀ x : ι → ℝ, (selectorMatrix a (MvPolynomial.eval x l)
      (MvPolynomial.eval x H) (MvPolynomial.eval x B) (MvPolynomial.eval x u)
      (S*M*(MvPolynomial.eval x R)^2)).PosSemidef) :
    ∀ x : ι → ℝ,
      0≤MvPolynomial.eval x (schurA a l H u) ∧
      (MvPolynomial.eval x u)^2/a≤S*M*(MvPolynomial.eval x R)^2 ∧
      (MvPolynomial.eval x (schurD a l B u))^2≤
        4*S*M*MvPolynomial.eval x (schurA a l H u)*(MvPolynomial.eval x R)^2 := by
  intro x
  obtain ⟨hA,hu,hD⟩ := selector_scalar_bounds ha (hG x)
  rw [schurA_eval,schurD_eval]
  refine ⟨hA,hu,?_⟩
  nlinarith only [hD]

/-- Pointwise PSD also proves the uniform lower/upper bounds on the
actual residual quartic, before any separate SOS repair is invoked. -/
theorem polynomial_radial_remainder_bounds (a S M : ℝ) (ha : 0 < a)
    (l H B u R : Poly (ι := ι))
    (hG : ∀ x : ι → ℝ, (selectorMatrix a (MvPolynomial.eval x l)
      (MvPolynomial.eval x H) (MvPolynomial.eval x B) (MvPolynomial.eval x u)
      (S*M*(MvPolynomial.eval x R)^2)).PosSemidef) :
    ∀ x : ι → ℝ,
      S*M*(MvPolynomial.eval x R)^2≤MvPolynomial.eval x (radialRemainder a S M u R) ∧
      MvPolynomial.eval x (radialRemainder a S M u R)≤2*S*M*(MvPolynomial.eval x R)^2 := by
  intro x
  have hu := (polynomial_selector_bounds a S M ha l H B u R hG x).2.1
  have hu0 := div_nonneg (sq_nonneg (MvPolynomial.eval x u)) ha.le
  simp only [radialRemainder,map_sub,map_mul,map_pow,MvPolynomial.eval_C]
  constructor
  · linear_combination hu
  · linear_combination hu0

end Polynomials

end SelectorSchur
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
