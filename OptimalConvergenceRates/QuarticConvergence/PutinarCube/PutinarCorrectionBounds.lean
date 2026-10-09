/-
  Pointwise bounds for the explicit correction in the preordering-to-Putinar
  conversion.  The weighted generator factors are deliberately retained.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarConversion

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n r : ℕ}

/-- On the cube, a product of Chebyshev residual factors lies between zero
and the corresponding product of canonical box generators. -/
theorem eval_putinarSplitSetProduct_nonneg_le
    (k : ℕ) (hk : 1 ≤ k) (L : Finset (Fin n))
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    0 ≤ MvPolynomial.eval x (putinarSplitSetProduct k L) ∧
      MvPolynomial.eval x (putinarSplitSetProduct k L) ≤
        MvPolynomial.eval x (BoxSemialgebraicGeneratorProd L) := by
  simp only [putinarSplitSetProduct, BoxSemialgebraicGeneratorProd,
    map_prod]
  constructor
  · apply Finset.prod_nonneg
    intro i hi
    exact (putinarSplit_bounds_on_hypercube k hk i x hx).2.2.1
  · apply Finset.prod_le_prod
    · intro i hi
      exact (putinarSplit_bounds_on_hypercube k hk i x hx).2.2.1
    · intro i hi
      exact (putinarSplit_bounds_on_hypercube k hk i x hx).2.2.2

/-- The exact weighted expression controlling the conversion correction at a
cube point.  Terms with fewer than two localized coordinates vanish. -/
def putinarConversionCorrectionMajorant
    {q : MvPolynomial (Fin n) ℝ}
    (k : ℕ) (w : BoxPreorderingRootWitness q r)
    (x : Fin n → ℝ) : ℝ :=
  ∑ I ∈ Finset.univ.powerset,
    ∑ J ∈ I.powerset, if 2 ≤ J.card then
      putinarPairMu k ^ J.card *
        MvPolynomial.eval x
          (BoxSemialgebraicGeneratorProd (I \ J) *
            boxPreorderingRootMultiplier w I)
    else 0

/-- A single multiplier correction is nonnegative and is bounded by the
same multiplier with every residual product replaced by its canonical
generator product. -/
theorem eval_putinarCorrectionForMultiplier_nonneg_le
    (k : ℕ) (hk : 1 ≤ k) (I : Finset (Fin n))
    (τ : MvPolynomial (Fin n) ℝ) (hτ : IsSOS τ)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    0 ≤ MvPolynomial.eval x (putinarCorrectionForMultiplier k I τ) ∧
      MvPolynomial.eval x (putinarCorrectionForMultiplier k I τ) ≤
        ∑ J ∈ I.powerset, if 2 ≤ J.card then
          putinarPairMu k ^ J.card *
            MvPolynomial.eval x
              (BoxSemialgebraicGeneratorProd (I \ J) * τ)
        else 0 := by
  have hτeval : 0 ≤ MvPolynomial.eval x τ :=
    IsSOS_nonneg _ hτ x (Set.mem_univ x)
  have hmu : 0 ≤ putinarPairMu k := by
    unfold putinarPairMu delta
    positivity
  unfold putinarCorrectionForMultiplier putinarCorrectionInner
  rw [map_mul, map_sum]
  constructor
  · apply mul_nonneg hτeval
    apply Finset.sum_nonneg
    intro J hJ
    by_cases hcard : 2 ≤ J.card
    · simp only [hcard, if_pos, map_mul, MvPolynomial.eval_C]
      exact mul_nonneg (pow_nonneg hmu _)
        (eval_putinarSplitSetProduct_nonneg_le k hk (I \ J) x hx).1
    · simp [hcard]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro J hJ
    by_cases hcard : 2 ≤ J.card
    · simp only [hcard, if_pos, map_mul, MvPolynomial.eval_C]
      have hs := eval_putinarSplitSetProduct_nonneg_le
        k hk (I \ J) x hx
      calc
        MvPolynomial.eval x τ *
            (putinarPairMu k ^ J.card *
              MvPolynomial.eval x (putinarSplitSetProduct k (I \ J))) =
            putinarPairMu k ^ J.card *
              (MvPolynomial.eval x (putinarSplitSetProduct k (I \ J)) *
                MvPolynomial.eval x τ) := by ring
        _ ≤ putinarPairMu k ^ J.card *
              (MvPolynomial.eval x (BoxSemialgebraicGeneratorProd (I \ J)) *
                MvPolynomial.eval x τ) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hs.2 hτeval) (pow_nonneg hmu _)
    · simp [hcard]

/-- The full conversion correction is nonnegative on the cube and bounded by
the explicit weighted multiplier majorant. -/
theorem eval_putinarConversionCorrection_nonneg_le_majorant
    {q : MvPolynomial (Fin n) ℝ}
    (k : ℕ) (hk : 1 ≤ k) (w : BoxPreorderingRootWitness q r)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    0 ≤ MvPolynomial.eval x (putinarConversionCorrection k w) ∧
      MvPolynomial.eval x (putinarConversionCorrection k w) ≤
        putinarConversionCorrectionMajorant k w x := by
  unfold putinarConversionCorrection putinarConversionCorrectionMajorant
  simp only [map_sum]
  constructor
  · apply Finset.sum_nonneg
    intro I hI
    exact (eval_putinarCorrectionForMultiplier_nonneg_le k hk I
      (boxPreorderingRootMultiplier w I)
      (boxPreorderingRootMultiplier_isSOS w I) x hx).1
  · apply Finset.sum_le_sum
    intro I hI
    exact (eval_putinarCorrectionForMultiplier_nonneg_le k hk I
      (boxPreorderingRootMultiplier w I)
      (boxPreorderingRootMultiplier_isSOS w I) x hx).2

/-- A supplied bound for every weighted multiplier term immediately bounds
the whole correction, without losing or altering its `mu^|J|` weights. -/
theorem eval_putinarConversionCorrection_le_of_weighted
    {q : MvPolynomial (Fin n) ℝ}
    (k : ℕ) (hk : 1 ≤ k) (w : BoxPreorderingRootWitness q r)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n)
    (B : Finset (Fin n) → Finset (Fin n) → ℝ)
    (hweighted : ∀ I ∈ Finset.univ.powerset, ∀ J ∈ I.powerset,
      2 ≤ J.card →
      MvPolynomial.eval x
          (BoxSemialgebraicGeneratorProd (I \ J) *
            boxPreorderingRootMultiplier w I) ≤ B I J) :
    MvPolynomial.eval x (putinarConversionCorrection k w) ≤
      ∑ I ∈ Finset.univ.powerset,
        ∑ J ∈ I.powerset, if 2 ≤ J.card then
          putinarPairMu k ^ J.card * B I J
        else 0 := by
  apply (eval_putinarConversionCorrection_nonneg_le_majorant
    k hk w x hx).2.trans
  unfold putinarConversionCorrectionMajorant
  apply Finset.sum_le_sum
  intro I hI
  apply Finset.sum_le_sum
  intro J hJ
  by_cases hcard : 2 ≤ J.card
  · simp only [hcard, if_pos]
    exact mul_le_mul_of_nonneg_left (hweighted I hI J hJ hcard)
      (pow_nonneg (by unfold putinarPairMu delta; positivity) _)
  · simp [hcard]

end QuarticConvergence
end OptimalConvergenceRates

end
