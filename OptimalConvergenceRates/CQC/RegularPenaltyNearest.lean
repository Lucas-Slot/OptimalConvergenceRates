import Mathlib.Analysis.Calculus.LagrangeMultipliers
import OptimalConvergenceRates.CQC.PolynomialCalculus

/-!
# Nearest-point normality for regular polynomial zero sets
-/

noncomputable section

open MvPolynomial Finset Set

namespace OptimalConvergenceRates
namespace CQCInternal

variable {N m : ℕ}

/-- Coordinate gradient of a multivariate polynomial at a point. -/
def polynomialGradientAt (P : MvPolynomial (Fin N) ℝ)
    (x : Fin N → ℝ) : Fin N → ℝ :=
  fun j ↦ MvPolynomial.eval x (MvPolynomial.pderiv j P)

/-- Common real zero set of a finite polynomial family. -/
def polynomialZeroSet (h : Fin m → MvPolynomial (Fin N) ℝ) :
    Set (Fin N → ℝ) :=
  {x | ∀ i, MvPolynomial.eval x (h i) = 0}

/-- Squared coordinate distance from `z`. -/
def squaredDistancePolynomial (z : Fin N → ℝ) :
    MvPolynomial (Fin N) ℝ :=
  ∑ j, (X j - C (z j)) ^ 2

@[simp]
theorem eval_squaredDistancePolynomial (z x : Fin N → ℝ) :
    MvPolynomial.eval x (squaredDistancePolynomial z) =
      ∑ j, (x j - z j) ^ 2 := by
  simp [squaredDistancePolynomial]

@[simp]
theorem eval_pderiv_squaredDistancePolynomial
    (z x : Fin N → ℝ) (k : Fin N) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv k (squaredDistancePolynomial z)) =
      2 * (x k - z k) := by
  simp [squaredDistancePolynomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem mvPolynomialEvalFDeriv_apply
    (P : MvPolynomial (Fin N) ℝ) (x w : Fin N → ℝ) :
    QuarticConvergence.mvPolynomialEvalFDeriv P x w =
      ∑ j, polynomialGradientAt P x j * w j := by
  simp [QuarticConvergence.mvPolynomialEvalFDeriv,
    polynomialGradientAt, Finset.sum_apply]

@[simp]
theorem mvPolynomialEvalFDeriv_single
    (P : MvPolynomial (Fin N) ℝ) (x : Fin N → ℝ) (j : Fin N) :
    QuarticConvergence.mvPolynomialEvalFDeriv P x (Pi.single j 1) =
      polynomialGradientAt P x j := by
  rw [mvPolynomialEvalFDeriv_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

/-- Linear independence of coordinate gradients is equivalent to linear
independence of the corresponding evaluation differentials. -/
theorem evalFDeriv_linearIndependent_of_gradients
    {h : Fin m → MvPolynomial (Fin N) ℝ} {x : Fin N → ℝ}
    (hli : LinearIndependent ℝ (fun i ↦ polynomialGradientAt (h i) x)) :
    LinearIndependent ℝ
      (fun i ↦ QuarticConvergence.mvPolynomialEvalFDeriv (h i) x) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  apply hli c
  funext j
  have hj := congrArg
    (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) hc
  simp only [_root_.sum_apply,
    smul_apply, smul_eq_mul] at hj
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  simpa using hj

/-- A point minimizing squared distance to a regular polynomial zero set has
normal displacement: the displacement is a linear combination of the
constraint gradients. -/
theorem exists_nearestPoint_displacement_eq_gradientCombination
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (hne : (polynomialZeroSet h).Nonempty)
    (hcompact : IsCompact (polynomialZeroSet h))
    (hregular : ∀ v ∈ polynomialZeroSet h,
      LinearIndependent ℝ (fun i ↦ polynomialGradientAt (h i) v))
    (z : Fin N → ℝ) :
    ∃ v ∈ polynomialZeroSet h, ∃ coeff : Fin m → ℝ,
      (∀ u ∈ polynomialZeroSet h,
        MvPolynomial.eval v (squaredDistancePolynomial z) ≤
          MvPolynomial.eval u (squaredDistancePolynomial z)) ∧
      z - v = ∑ i, coeff i • polynomialGradientAt (h i) v := by
  obtain ⟨v, hv, hvmin⟩ := hcompact.exists_isMinOn hne
    (continuous_eval (squaredDistancePolynomial z)).continuousOn
  have hset :
      {u | ∀ i, MvPolynomial.eval u (h i) = MvPolynomial.eval v (h i)} =
        polynomialZeroSet h := by
    ext u
    simp only [Set.mem_ofPred_eq, polynomialZeroSet]
    constructor
    · intro hu i
      rw [hu i, hv i]
    · intro hu i
      rw [hu i, hv i]
  have hextr : IsLocalExtrOn
      (fun u ↦ MvPolynomial.eval u (squaredDistancePolynomial z))
      {u | ∀ i, MvPolynomial.eval u (h i) = MvPolynomial.eval v (h i)} v := by
    rw [hset]
    exact Or.inl hvmin.isLocalMinOn
  obtain ⟨coeff, coeff₀, hnonzero, hrelation⟩ :=
    hextr.exists_multipliers_of_hasStrictFDerivAt
      (fun i ↦ hasStrictFDerivAt_mvPolynomial_eval (h i) v)
      (hasStrictFDerivAt_mvPolynomial_eval (squaredDistancePolynomial z) v)
  have hdiffLI := evalFDeriv_linearIndependent_of_gradients (hregular v hv)
  have hcoeff₀ : coeff₀ ≠ 0 := by
    intro hzero
    have hsum :
        ∑ i, coeff i • QuarticConvergence.mvPolynomialEvalFDeriv (h i) v = 0 := by
      simpa [hzero] using hrelation
    have hcoeff := (Fintype.linearIndependent_iff.mp hdiffLI) coeff hsum
    apply hnonzero
    ext i <;> simp [hzero, hcoeff]
  let normalCoeff : Fin m → ℝ := fun i ↦ coeff i / (2 * coeff₀)
  refine ⟨v, hv, normalCoeff, hvmin, ?_⟩
  funext j
  have hj := congrArg
    (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) hrelation
  simp only [add_apply, _root_.sum_apply,
    smul_apply, smul_eq_mul, zero_apply,
    mvPolynomialEvalFDeriv_single] at hj
  have hsq : polynomialGradientAt (squaredDistancePolynomial z) v j =
      2 * (v j - z j) := by
    simpa [polynomialGradientAt] using
      eval_pderiv_squaredDistancePolynomial z v j
  rw [hsq] at hj
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    normalCoeff]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  have hden : 2 * coeff₀ ≠ 0 := mul_ne_zero (by norm_num) hcoeff₀
  apply (eq_div_iff hden).2
  nlinarith [hj]

end CQCInternal
end OptimalConvergenceRates

end
