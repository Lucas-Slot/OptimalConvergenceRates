/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/SphereIdeal.lean

  Algebraic infrastructure for the optional ambient-representative compatibility
  theorem.  The main analytic construction works with polynomial functions on the
  sphere; this file supplies the polynomial identity principle needed to compare
  those functions with certificates modulo the defining sphere equation.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Defs
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Order.Interval.Set.Infinite

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A real multivariate polynomial which vanishes on an open coordinate cube is
identically zero.  This is a direct specialization of mathlib's infinite-box
polynomial identity theorem. -/
theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_openCube
    {sigma : Type*} [Finite sigma]
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (p : MvPolynomial sigma ℝ)
    (hp : ∀ x : sigma → ℝ,
      (∀ i, |x i| < epsilon) → MvPolynomial.eval x p = 0) :
    p = 0 := by
  apply MvPolynomial.funext_set (fun _ ↦ Set.Ioo (-epsilon) epsilon)
    (fun _ ↦ Set.Ioo_infinite (by linarith))
  intro x hx
  apply hp x
  intro i
  exact abs_lt.mpr (hx i (Set.mem_univ i))

/-- The cube of radius `1 / (m + 1)` lies strictly inside the Euclidean unit
ball in `ℝ^m`. -/
theorem sum_sq_lt_one_of_mem_openCube (m : ℕ) (x : Fin m → ℝ)
    (hx : ∀ i, |x i| < 1 / (m + 1 : ℝ)) :
    ∑ i, x i ^ 2 < 1 := by
  have hden : 0 < (m + 1 : ℝ) := by positivity
  have hterm (i : Fin m) : x i ^ 2 ≤ (1 / (m + 1 : ℝ)) ^ 2 := by
    have hi := hx i
    have habsnonneg : 0 ≤ |x i| := abs_nonneg _
    have hright : 0 ≤ 1 / (m + 1 : ℝ) := (div_pos zero_lt_one hden).le
    nlinarith [sq_abs (x i)]
  calc
    ∑ i, x i ^ 2 ≤ ∑ _i : Fin m, (1 / (m + 1 : ℝ)) ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ hterm i
    _ = (m : ℝ) * (1 / (m + 1 : ℝ)) ^ 2 := by simp
    _ < 1 := by
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      apply (div_lt_iff₀ (sq_pos_of_pos hden)).2
      have hm : (m : ℝ) < m + 1 := by norm_num
      nlinarith [sq_nonneg (m : ℝ)]

/-- The defining sphere equation in `m + 1` variables, viewed as a monic
quadratic in the zeroth variable. -/
def sphereRelationUPolynomial (m : ℕ) :
    Polynomial (MvPolynomial (Fin m) ℝ) :=
  Polynomial.X ^ 2 +
    Polynomial.C ((∑ i : Fin m, (MvPolynomial.X i) ^ 2) - 1)

theorem sphereRelationUPolynomial_monic (m : ℕ) :
    (sphereRelationUPolynomial m).Monic :=
  Polynomial.monic_X_pow_add_C _ (by norm_num)

/-- The standard sphere relation becomes the expected monic quadratic under
mathlib's `Fin (m + 1)` univariate-polynomial equivalence. -/
theorem finSuccEquiv_sphereRelation (m : ℕ) :
    MvPolynomial.finSuccEquiv ℝ m
        (SphereBallTransfers.sphereRelation (m + 1)) =
      sphereRelationUPolynomial m := by
  unfold SphereBallTransfers.sphereRelation SphereBallTransfers.sphereQuadratic
    sphereRelationUPolynomial
  rw [map_sub, map_sum]
  simp [Fin.sum_univ_succ, MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ, map_pow]
  ring

/-- A real polynomial in a positive number of variables which vanishes on the
unit sphere is divisible by its defining quadratic. The proof divides in the zeroth
variable, evaluates the linear remainder at the two square-root branches over an open
cube, and uses polynomial identity. -/
theorem sphere_vanishing_dvd_relation (m : ℕ)
    (p : MvPolynomial (Fin (m + 1)) ℝ)
    (hp : ∀ x ∈ SphereBallTransfers.sphereSet (m + 1),
      MvPolynomial.eval x p = 0) :
    ∃ a, p = SphereBallTransfers.sphereRelation (m + 1) * a := by
  let rel := sphereRelationUPolynomial m
  let P := MvPolynomial.finSuccEquiv ℝ m p
  let rem := P %ₘ rel
  have hmonic : rel.Monic := sphereRelationUPolynomial_monic m
  have hreldegr : rel.degree = (2 : WithBot ℕ) :=
    Polynomial.degree_X_pow_add_C (by norm_num) _
  have hremdeg : rem.degree ≤ (1 : WithBot ℕ) := by
    have hlt := Polynomial.degree_modByMonic_lt P hmonic
    rw [hreldegr] at hlt
    by_cases hzero : rem = 0
    · simp [hzero]
    · rw [Polynomial.degree_eq_natDegree hzero]
      rw [Polynomial.degree_eq_natDegree hzero] at hlt
      norm_cast at hlt ⊢
      omega
  have hremform : rem =
      Polynomial.C (rem.coeff 1) * Polynomial.X +
        Polynomial.C (rem.coeff 0) :=
    Polynomial.eq_X_add_C_of_degree_le_one hremdeg
  have hcoeffeval (y : Fin m → ℝ)
      (hy : ∀ i, |y i| < 1 / (m + 1 : ℝ)) :
      MvPolynomial.eval y (rem.coeff 1) = 0 ∧
        MvPolynomial.eval y (rem.coeff 0) = 0 := by
    have hsumlt := sum_sq_lt_one_of_mem_openCube m y hy
    let t : ℝ := Real.sqrt (1 - ∑ i, y i ^ 2)
    have htpos : 0 < t := Real.sqrt_pos.2 (sub_pos.mpr hsumlt)
    have htsq : t ^ 2 = 1 - ∑ i, y i ^ 2 :=
      Real.sq_sqrt (sub_nonneg.mpr hsumlt.le)
    have hsphere_pos :
        Fin.cons t y ∈ SphereBallTransfers.sphereSet (m + 1) := by
      simp only [SphereBallTransfers.sphereSet,
        SphereBallTransfers.sphereQuadratic, Set.mem_ofPred_eq, map_sum,
        map_pow, eval_X]
      rw [Fin.sum_univ_succ]
      change t ^ 2 + ∑ i, y i ^ 2 = 1
      linarith
    have hsphere_neg :
        Fin.cons (-t) y ∈ SphereBallTransfers.sphereSet (m + 1) := by
      simp only [SphereBallTransfers.sphereSet,
        SphereBallTransfers.sphereQuadratic, Set.mem_ofPred_eq, map_sum,
        map_pow, eval_X]
      rw [Fin.sum_univ_succ]
      change (-t) ^ 2 + ∑ i, y i ^ 2 = 1
      nlinarith
    have hPpos :
        Polynomial.eval t (Polynomial.map (MvPolynomial.eval y) P) = 0 := by
      rw [← MvPolynomial.eval_eq_eval_mv_eval']
      exact hp _ hsphere_pos
    have hPneg :
        Polynomial.eval (-t) (Polynomial.map (MvPolynomial.eval y) P) = 0 := by
      rw [← MvPolynomial.eval_eq_eval_mv_eval']
      exact hp _ hsphere_neg
    have hrelpos :
        Polynomial.eval t (Polynomial.map (MvPolynomial.eval y) rel) = 0 := by
      change Polynomial.eval t
        (Polynomial.map (MvPolynomial.eval y)
          (sphereRelationUPolynomial m)) = 0
      rw [← finSuccEquiv_sphereRelation,
        ← MvPolynomial.eval_eq_eval_mv_eval']
      exact SphereBallTransfers.eval_sphereRelation_of_mem hsphere_pos
    have hrelneg :
        Polynomial.eval (-t) (Polynomial.map (MvPolynomial.eval y) rel) = 0 := by
      change Polynomial.eval (-t)
        (Polynomial.map (MvPolynomial.eval y)
          (sphereRelationUPolynomial m)) = 0
      rw [← finSuccEquiv_sphereRelation,
        ← MvPolynomial.eval_eq_eval_mv_eval']
      exact SphereBallTransfers.eval_sphereRelation_of_mem hsphere_neg
    have hdivision := Polynomial.modByMonic_add_div P rel
    have hrempos :
        Polynomial.eval t (Polynomial.map (MvPolynomial.eval y) rem) = 0 := by
      have h := congrArg
        (fun Q ↦ Polynomial.eval t
          (Polynomial.map (MvPolynomial.eval y) Q)) hdivision
      simp only [Polynomial.map_add, Polynomial.map_mul,
        Polynomial.eval_add, Polynomial.eval_mul, hrelpos, zero_mul,
        add_zero, hPpos] at h
      exact h
    have hremneg :
        Polynomial.eval (-t) (Polynomial.map (MvPolynomial.eval y) rem) = 0 := by
      have h := congrArg
        (fun Q ↦ Polynomial.eval (-t)
          (Polynomial.map (MvPolynomial.eval y) Q)) hdivision
      simp only [Polynomial.map_add, Polynomial.map_mul,
        Polynomial.eval_add, Polynomial.eval_mul, hrelneg, zero_mul,
        add_zero, hPneg] at h
      exact h
    rw [hremform] at hrempos hremneg
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] at hrempos hremneg
    constructor <;> nlinarith
  have hcoeff1 : rem.coeff 1 = 0 := by
    apply mvPolynomial_eq_zero_of_eval_eq_zero_on_openCube
      (1 / (m + 1 : ℝ)) (by positivity)
    intro y hy
    exact (hcoeffeval y hy).1
  have hcoeff0 : rem.coeff 0 = 0 := by
    apply mvPolynomial_eq_zero_of_eval_eq_zero_on_openCube
      (1 / (m + 1 : ℝ)) (by positivity)
    intro y hy
    exact (hcoeffeval y hy).2
  have hremzero : rem = 0 := by
    rw [hremform, hcoeff1, hcoeff0]
    simp
  have hquot : rel * (P /ₘ rel) = P := by
    calc
      rel * (P /ₘ rel) = 0 + rel * (P /ₘ rel) := by rw [zero_add]
      _ = rem + rel * (P /ₘ rel) := by rw [hremzero]
      _ = P := Polynomial.modByMonic_add_div P rel
  let a := (MvPolynomial.finSuccEquiv ℝ m).symm (P /ₘ rel)
  refine ⟨a, ?_⟩
  apply (MvPolynomial.finSuccEquiv ℝ m).injective
  rw [map_mul, finSuccEquiv_sphereRelation]
  change P = rel * (MvPolynomial.finSuccEquiv ℝ m) a
  rw [show (MvPolynomial.finSuccEquiv ℝ m) a = P /ₘ rel by simp [a]]
  exact hquot.symm

end QuarticConvergence
end OptimalConvergenceRates

end
