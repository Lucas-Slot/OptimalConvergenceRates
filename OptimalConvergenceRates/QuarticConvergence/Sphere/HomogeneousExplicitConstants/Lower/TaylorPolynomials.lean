import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.AngularFrequencies
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Polynomial Taylor coefficients of angular polynomial evaluation

The coefficient polynomials may have complex coefficients. Their degree bound
is independent of the degree of the original certificate polynomial.
-/

open scoped Topology

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

def scalarAngularSeries (ell b : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  cauchyPowerSeries (fun z : ℂ ↦ Complex.sin z ^ ell * Complex.cos z ^ b) 0 1

def scalarAngularCoefficient (ell b j : ℕ) : ℂ := (scalarAngularSeries ell b).coeff j

theorem scalarAngularSeries_hasFPowerSeries (ell b : ℕ) :
    HasFPowerSeriesOnBall (fun z : ℂ ↦ Complex.sin z ^ ell * Complex.cos z ^ b)
      (scalarAngularSeries ell b) 0 ⊤ :=
  ((Complex.differentiable_sin.pow ell).mul (Complex.differentiable_cos.pow
    b)).hasFPowerSeriesOnBall
    0 (R := (1 : NNReal)) (by norm_num)

theorem scalarAngularCoefficient_eq_zero (ell b j : ℕ) (hj : j < ell) :
    scalarAngularCoefficient ell b j = 0 :=
  sin_pow_mul_cos_pow_coefficient_eq_zero ell b j
    (scalarAngularSeries_hasFPowerSeries ell b).hasFPowerSeriesAt hj

def originalExponentDegree {σ : Type*} (d : Option σ →₀ ℕ) : ℕ :=
  d.some.sum (fun _ e ↦ e)

def angularCoefficientPolynomial {σ : Type*} (p : MvPolynomial (Option σ) ℝ) (j : ℕ) :
    MvPolynomial σ ℂ :=
  ∑ d ∈ p.support, MvPolynomial.monomial d.some
    (((p.coeff d : ℝ) : ℂ) *
      scalarAngularCoefficient (originalExponentDegree d) (d none) j)

/-- Every Taylor coefficient of order `j` is a polynomial of degree at most
`j` in the direction variable. -/
theorem angularCoefficientPolynomial_degree_le {σ : Type*}
    (p : MvPolynomial (Option σ) ℝ) (j : ℕ) :
    (angularCoefficientPolynomial p j).totalDegree ≤ j := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  by_cases hdeg : originalExponentDegree d ≤ j
  · exact (MvPolynomial.totalDegree_monomial_le _ _).trans hdeg
  · have hzero := scalarAngularCoefficient_eq_zero
      (originalExponentDegree d) (d none) j (lt_of_not_ge hdeg)
    simp only [hzero, mul_zero, MvPolynomial.monomial_zero, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _

def angularTaylorPolynomial {σ : Type*} (p : MvPolynomial (Option σ) ℝ) (τ : ℂ) (K : ℕ) :
    MvPolynomial σ ℂ :=
  ∑ j ∈ Finset.range (K + 1), MvPolynomial.C (τ ^ j) * angularCoefficientPolynomial p j

/-- Truncation through order `K` has degree at most `K` in the direction. -/
theorem angularTaylorPolynomial_degree_le {σ : Type*}
    (p : MvPolynomial (Option σ) ℝ) (τ : ℂ) (K : ℕ) :
    (angularTaylorPolynomial p τ K).totalDegree ≤ K := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  have hmul := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (τ ^ j)) (angularCoefficientPolynomial p j)
  have hcoef := angularCoefficientPolynomial_degree_le p j
  simp only [MvPolynomial.totalDegree_C, zero_add] at hmul
  exact hmul.trans (hcoef.trans (Nat.le_of_lt_succ (Finset.mem_range.1 hj)))

def angularMonomialWeight {σ : Type*} (d : Option σ →₀ ℕ) (c : ℝ) (y : σ → ℝ) : ℂ :=
  (c : ℂ) * d.some.prod (fun i e ↦ (y i : ℂ) ^ e)

theorem angular_monomial_factorization {σ : Type*} (d : Option σ →₀ ℕ) (c : ℝ)
    (y : σ → ℝ) (z : ℂ) :
    (MvPolynomial.monomial d c).eval₂ Complex.ofRealHom (angularCoordinate y z) =
      angularMonomialWeight d c y *
        (Complex.sin z ^ originalExponentDegree d * Complex.cos z ^ d none) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  rw [d.prod_option_index (fun o e ↦ angularCoordinate y z o ^ e)
    (by intro o; simp) (by intro o m n; exact pow_add _ _ _)]
  simp only [angularCoordinate, Complex.ofRealHom_eq_coe, angularMonomialWeight,
    originalExponentDegree, Finsupp.prod, Finsupp.sum, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem angular_polynomial_as_monomial_sum {σ : Type*}
    (p : MvPolynomial (Option σ) ℝ) (y : σ → ℝ) (z : ℂ) :
    p.eval₂ Complex.ofRealHom (angularCoordinate y z) =
      ∑ d ∈ p.support, angularMonomialWeight d (p.coeff d) y *
        (Complex.sin z ^ originalExponentDegree d * Complex.cos z ^ d none) := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [MvPolynomial.eval₂_sum, angular_monomial_factorization]

def angularPolynomialSeries {σ : Type*} (p : MvPolynomial (Option σ) ℝ) (y : σ → ℝ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  ∑ d ∈ p.support, angularMonomialWeight d (p.coeff d) y •
    scalarAngularSeries (originalExponentDegree d) (d none)

theorem hasFPowerSeriesOnBall_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ) (p : ι → FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : ∀ i ∈ s, HasFPowerSeriesOnBall (f i) (p i) 0 ⊤) :
    HasFPowerSeriesOnBall (fun z ↦ ∑ i ∈ s, f i z) (∑ i ∈ s, p i) 0 ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty, constFormalMultilinearSeries_zero] using
        (hasFPowerSeriesOnBall_const (c := (0 : ℂ)) (e := (0 : ℂ)))
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        ((hf i (by simp)).add (ih (fun j hj ↦ hf j (by simp [hj])))).congr
          (g := fun z ↦ f i z + ∑ j ∈ s, f j z) (fun z _ ↦ rfl)

/-- The explicit finite series constructed from the monomials represents the
actual angular restriction on the entire complex plane. -/
theorem angularPolynomialSeries_hasFPowerSeries {σ : Type*}
    (p : MvPolynomial (Option σ) ℝ) (y : σ → ℝ) :
    HasFPowerSeriesOnBall (fun z ↦ p.eval₂ Complex.ofRealHom (angularCoordinate y z))
      (angularPolynomialSeries p y) 0 ⊤ := by
  classical
  have h := hasFPowerSeriesOnBall_finset_sum p.support
    (fun d z ↦ angularMonomialWeight d (p.coeff d) y *
      (Complex.sin z ^ originalExponentDegree d * Complex.cos z ^ d none))
    (fun d ↦ angularMonomialWeight d (p.coeff d) y •
      scalarAngularSeries (originalExponentDegree d) (d none))
    (fun d _ ↦ by
      simpa only [Pi.smul_apply, smul_eq_mul] using
        ((scalarAngularSeries_hasFPowerSeries (originalExponentDegree d) (d none)).const_smul
          (c := angularMonomialWeight d (p.coeff d) y)).congr
          (g := fun z ↦ angularMonomialWeight d (p.coeff d) y *
            (Complex.sin z ^ originalExponentDegree d * Complex.cos z ^ d none))
          (fun z _ ↦ rfl))
  simpa only [← angular_polynomial_as_monomial_sum, angularPolynomialSeries] using h

theorem formalSeries_finset_sum_apply {ι : Type*} (s : Finset ι)
    (p : ι → FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (∑ i ∈ s, p i) n = ∑ i ∈ s, p i n := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, FormalMultilinearSeries.add_apply, ih]

/-- Evaluation of the coefficient polynomial is the corresponding coefficient
of the explicit analytic series. -/
theorem eval_angularCoefficientPolynomial {σ : Type*}
    (p : MvPolynomial (Option σ) ℝ) (y : σ → ℝ) (j : ℕ) :
    MvPolynomial.eval (fun i ↦ (y i : ℂ)) (angularCoefficientPolynomial p j) =
      (angularPolynomialSeries p y).coeff j := by
  classical
  simp only [angularCoefficientPolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_monomial,
    angularPolynomialSeries, FormalMultilinearSeries.coeff, Finset.sum_apply,
    formalSeries_finset_sum_apply, FormalMultilinearSeries.smul_apply,
    ContinuousMultilinearMap.sum_apply, Pi.smul_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul, angularMonomialWeight, scalarAngularCoefficient]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The polynomial coefficient agrees with every representing power series,
so it is independent of the chosen Cauchy radius or analytic construction. -/
theorem angularCoefficientPolynomial_eval_eq {σ : Type*}
    (p : MvPolynomial (Option σ) ℝ) (y : σ → ℝ) (j : ℕ)
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hq : HasFPowerSeriesAt (fun z ↦ p.eval₂ Complex.ofRealHom (angularCoordinate y z)) q 0) :
    MvPolynomial.eval (fun i ↦ (y i : ℂ)) (angularCoefficientPolynomial p j) = q.coeff j := by
  rw [eval_angularCoefficientPolynomial]
  have hseries := (angularPolynomialSeries_hasFPowerSeries p
    y).hasFPowerSeriesAt.eq_formalMultilinearSeries hq
  rw [hseries]

/-- The direction polynomial of degree at most `K` evaluates to the exact
Taylor partial sum of the angular restriction. -/
theorem angularTaylorPolynomial_eval_eq {σ : Type*}
    (p : MvPolynomial (Option σ) ℝ) (y : σ → ℝ) (τ : ℂ) (K : ℕ)
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hq : HasFPowerSeriesAt (fun z ↦ p.eval₂ Complex.ofRealHom (angularCoordinate y z)) q 0) :
    MvPolynomial.eval (fun i ↦ (y i : ℂ)) (angularTaylorPolynomial p τ K) =
      q.partialSum (K + 1) τ := by
  classical
  simp only [angularTaylorPolynomial, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [angularCoefficientPolynomial_eval_eq p y j hq,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  rfl

def coordinateSeries {J : Type*} [Fintype J]
    (q : FormalMultilinearSeries ℂ ℂ (EuclideanSpace ℂ J)) (j : J) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : J ↦ ℂ) j).compFormalMultilinearSeries q

theorem coordinateSeries_hasFPowerSeries {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (y : σ → ℝ)
    {q : FormalMultilinearSeries ℂ ℂ (EuclideanSpace ℂ J)}
    (hq : HasFPowerSeriesAt (angularVector p y) q 0) (j : J) :
    HasFPowerSeriesAt (fun z ↦ (p j).eval₂ Complex.ofRealHom (angularCoordinate y z))
      (coordinateSeries q j) 0 := by
  obtain ⟨R, hqR⟩ := hq
  have h := ((PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : J ↦ ℂ) j).comp_hasFPowerSeriesOnBall
    hqR).hasFPowerSeriesAt
  simpa only [Function.comp_def, PiLp.proj_apply, angularVector_apply, coordinateSeries] using h

theorem coordinateSeries_partialSum {J : Type*} [Fintype J]
    (q : FormalMultilinearSeries ℂ ℂ (EuclideanSpace ℂ J)) (j : J) (n : ℕ) (τ : ℂ) :
    (coordinateSeries q j).partialSum n τ =
      (PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : J ↦ ℂ) j) (q.partialSum n τ) := by
  simp only [FormalMultilinearSeries.partialSum, map_sum, coordinateSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]

def angularTaylorVector {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (τ : ℂ) (K : ℕ) (y : σ → ℝ) : EuclideanSpace ℂ J :=
  (WithLp.equiv 2 (J → ℂ)).symm
    (fun j ↦ MvPolynomial.eval (fun i ↦ (y i : ℂ)) (angularTaylorPolynomial (p j) τ K))

@[simp]
theorem angularTaylorVector_apply {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (τ : ℂ) (K : ℕ) (y : σ → ℝ) (j : J) :
    angularTaylorVector p τ K y j =
      MvPolynomial.eval (fun i ↦ (y i : ℂ)) (angularTaylorPolynomial (p j) τ K) := rfl

/-- The finite vector of explicitly constructed polynomial truncations is the
Taylor partial sum of the actual angular certificate vector. -/
theorem angularTaylorVector_eq_partialSum {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (τ : ℂ) (K : ℕ) (y : σ → ℝ)
    {q : FormalMultilinearSeries ℂ ℂ (EuclideanSpace ℂ J)}
    (hq : HasFPowerSeriesAt (angularVector p y) q 0) :
    angularTaylorVector p τ K y = q.partialSum (K + 1) τ := by
  apply PiLp.ext
  intro j
  rw [angularTaylorVector_apply]
  change MvPolynomial.eval (fun i ↦ (y i : ℂ)) (angularTaylorPolynomial (p j) τ K) =
    (PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : J ↦ ℂ) j) (q.partialSum (K + 1) τ)
  rw [← coordinateSeries_partialSum]
  exact angularTaylorPolynomial_eval_eq (p j) y τ K (coordinateSeries_hasFPowerSeries p y hq j)

/-- The angular certificate vector is entire, with the actual Euclidean norm
on the finite family, including an empty family. -/
theorem angularVector_differentiable {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (y : σ → ℝ) :
    Differentiable ℂ (angularVector p y) := by
  apply (differentiable_piLp 2).2
  intro j
  change Differentiable ℂ (fun z ↦ (p j).eval₂ Complex.ofRealHom (angularCoordinate y z))
  simpa only [Metric.eball_top, differentiableOn_univ] using
    (angularPolynomialSeries_hasFPowerSeries (p j) y).differentiableOn

theorem angularVector_cauchy_hasFPowerSeries {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (y : σ → ℝ) {R : NNReal} (hR : 0 < R) :
    HasFPowerSeriesOnBall (angularVector p y) (cauchyPowerSeries (angularVector p y) 0 R) 0 ⊤ :=
  (angularVector_differentiable p y).hasFPowerSeriesOnBall 0 hR

/-- In particular the polynomial truncation is the Cauchy partial sum at any
positive circle radius, the interface used by the uniform remainder bound. -/
theorem angularTaylorVector_eq_cauchyPartialSum {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (τ : ℂ) (K : ℕ) (y : σ → ℝ)
    {R : NNReal} (hR : 0 < R) :
    angularTaylorVector p τ K y =
      (cauchyPowerSeries (angularVector p y) 0 R).partialSum (K + 1) τ :=
  angularTaylorVector_eq_partialSum p τ K y
    (angularVector_cauchy_hasFPowerSeries p y hR).hasFPowerSeriesAt

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
