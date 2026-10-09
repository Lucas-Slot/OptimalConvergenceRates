/-
  OptimalConvergenceRates/ExamplePolynomials/Robinson.lean

  Shared definitions for the Robinson polynomial and its scalings.
-/
import OptimalConvergenceRates.BasicNotions.SOS

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- The symmetric cubic `Phi(a,b,c)` appearing in the Robinson form. -/
def Phi {A : Type*} [CommRing A] (a b c : A) : A :=
  a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c -
    (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b)

/-- The homogeneous Robinson form `Phi(x^2,y^2,w^2)`. -/
def homRobinson : MvPolynomial (Fin 3) ℝ :=
  Phi ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2) ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 2)
    ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2)

/-- The dehomogenized Robinson polynomial `R(x,y) = homRobinson(x,y,1)`. -/
def robinson : MvPolynomial (Fin 2) ℝ :=
  (X 0 : MvPolynomial (Fin 2) ℝ) ^ 6 + (X 1 : MvPolynomial (Fin 2) ℝ) ^ 6 + 1 -
    ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 4 * (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2 +
      (X 0 : MvPolynomial (Fin 2) ℝ) ^ 4 +
      (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 * (X 1 : MvPolynomial (Fin 2) ℝ) ^ 4 +
      (X 1 : MvPolynomial (Fin 2) ℝ) ^ 4 +
      (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2) +
    3 * (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 * (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2

/-- Scaling map `p(x,y) ↦ p(c*x,c*y)` on two-variable polynomials. -/
def scale2 (c : ℝ) :
    MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.aeval fun i => MvPolynomial.C c * MvPolynomial.X i

/-- The scaled Robinson polynomial `R_eps(x,y) = R(x/eps,y/eps)`. -/
def scaledRobinson (eps : ℝ) : MvPolynomial (Fin 2) ℝ :=
  scale2 eps⁻¹ robinson

end ScaledRobinson
end OptimalConvergenceRates

end
