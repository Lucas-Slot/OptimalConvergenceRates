/-
  Assembly of a quartic quadratic-module approximant from the same parity
  roots and their weighted multiplier estimates.

  This is the algebraic/finite-dimensional endpoint of the controlled-root
  analysis.  Its hypotheses deliberately retain the complete weighted
  multiplier `g_(I \ J) * tau_I`; no unweighted multiplier norm is used.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarParityWitness
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarCorrectionRate
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarApproximationAssembly

open MvPolynomial Finset Set
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n N Broot k : ℕ}

@[simp] theorem finiteCircleParityRootWitness_multiplier
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (hdegree : ∀ ν, (P ν).totalDegree ≤ Broot * k)
    (I : Finset (Fin n)) :
    boxPreorderingRootMultiplier
        (finiteCircleParityRootWitness P hdegree) I =
      finiteCircleParityMultiplier P I := rfl

/-- Every root retained by the finite parity witness has degree at most the
common paired-polynomial degree budget. -/
theorem finiteCircleParityRootWitness_root_totalDegree_le
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (hdegree : ∀ ν, (P ν).totalDegree ≤ Broot * k)
    (I : Finset (Fin n))
    (j : Fin ((finiteCircleParityRootWitness P hdegree).N I)) :
    ((finiteCircleParityRootWitness P hdegree).root I j).totalDegree ≤
      Broot * k := by
  change (circleParityComponent (P j) I).totalDegree ≤ Broot * k
  rcases circleParityComponent_eq_zero_or_totalDegree_add_card_le
      (P j) I with hzero | hweighted
  · rw [hzero]
    exact Nat.zero_le _
  · exact (Nat.le_add_right _ _).trans (hweighted.trans (hdegree j))

/-- Dimension/root-scale constant in the final error after adding the
explicit preordering-to-quadratic-module correction. -/
def putinarWeightedApproximationConstant
    (n Broot : ℕ) (A H : ℝ) : ℝ :=
  A + putinarCorrectionRateConstant n (Broot : ℝ) * H

theorem putinarWeightedApproximationConstant_nonneg
    (n Broot : ℕ) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) :
    0 ≤ putinarWeightedApproximationConstant n Broot A H := by
  unfold putinarWeightedApproximationConstant
  exact add_nonneg hA
    (mul_nonneg (putinarCorrectionRateConstant_nonneg n (Nat.cast_nonneg _)) hH)

/-- Product-circle approximation plus the complete weighted parity estimates
produce a quartic quadratic-module approximant at canonical order linear in
the common root scale.

The output order coefficient is `2 * Broot + 4 * n`: the first summand is
the squared-root order and the second is the explicit localized-product
conversion cost. -/
theorem hasQuarticBoxQMApproximationAt_of_weightedParity
    (h : MvPolynomial (Fin n) ℝ)
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (hk : 1 ≤ k)
    (hnonnegative : IsNonnegOn h (Hypercube n))
    (hdegree : ∀ ν, (P ν).totalDegree ≤ Broot * k)
    (A H : ℝ)
    (hcircle : ∀ (z : CubeCircleVar n → ℝ), z ∈ ProductCircle n →
      |MvPolynomial.eval (fun i ↦ z (i, false)) h -
        ∑ ν, (MvPolynomial.eval z (P ν)) ^ 2| ≤ A / (k : ℝ) ^ 4)
    (hweighted : ∀ (x : Fin n → ℝ), x ∈ Hypercube n →
      ∀ I ∈ Finset.univ.powerset, ∀ J ∈ I.powerset,
        2 ≤ J.card →
        MvPolynomial.eval x
            (BoxSemialgebraicGeneratorProd (I \ J) *
              finiteCircleParityMultiplier P I) ≤
          H * ((Broot : ℝ) * (k : ℝ)) ^ (2 * J.card - 4)) :
    HasQuarticBoxQMApproximationAt h (2 * Broot + 4 * n) k
      (putinarWeightedApproximationConstant n Broot A H) := by
  let q := finiteCircleParityPreorderingPolynomial P
  let w := finiteCircleParityRootWitness P hdegree
  let E := putinarConversionCorrection k w
  refine {
    nonnegative := hnonnegative
    approximant_exists := ?_ }
  refine ⟨q + E, ?_, ?_⟩
  · have hmem : q + E ∈
        BoxQuadraticModule n (2 * (Broot * k) + 4 * n * k) := by
      have hpack := w.putinarCorrection_quarticRate
        (finiteCircleParityRootWitness_root_totalDegree_le P hdegree)
        k hk (fun _ ↦ 0) (by
          intro i _hi
          constructor <;> norm_num) H (Broot : ℝ)
        (by
          intro I hI J hJ hJcard
          simpa [w] using
            hweighted (fun _ ↦ 0) (by
              intro i _hi
              constructor <;> norm_num) I hI J hJ hJcard)
      exact hpack.2.2.1
    have horder :
        2 * (Broot * k) + 4 * n * k = (2 * Broot + 4 * n) * k := by
      ring
    simpa [q, E, w, horder] using hmem
  · apply polySupNorm_le_of_bound
    intro x hx
    have hxabs : ∀ i, |x i| ≤ 1 := by
      intro i
      exact abs_le.mpr (hx i (Set.mem_univ i))
    have hq :
        |MvPolynomial.eval x h - MvPolynomial.eval x q| ≤
          A / (k : ℝ) ^ 4 := by
      apply abs_eval_sub_finiteCircleParityPreorderingPolynomial_le
        h P x hxabs
      intro eps
      exact hcircle (signedCirclePoint x eps)
        (signedCirclePoint_mem_productCircle x eps hxabs)
    have hpack := w.putinarCorrection_quarticRate
      (finiteCircleParityRootWitness_root_totalDegree_le P hdegree)
      k hk x hx H (Broot : ℝ)
      (by
        intro I hI J hJ hJcard
        simpa [w] using hweighted x hx I hI J hJ hJcard)
    have hEnonneg : 0 ≤ MvPolynomial.eval x E := by
      simpa [E] using hpack.2.2.2.1
    have hEupper : MvPolynomial.eval x E ≤
        putinarCorrectionRateConstant n (Broot : ℝ) * H /
          (k : ℝ) ^ 4 := by
      simpa [E] using hpack.2.2.2.2
    rw [map_sub, map_add]
    calc
      |MvPolynomial.eval x h -
          (MvPolynomial.eval x q + MvPolynomial.eval x E)| ≤
          |MvPolynomial.eval x h - MvPolynomial.eval x q| +
            |MvPolynomial.eval x E| := by
        calc
          |MvPolynomial.eval x h -
              (MvPolynomial.eval x q + MvPolynomial.eval x E)| =
              |(MvPolynomial.eval x h - MvPolynomial.eval x q) +
                (-MvPolynomial.eval x E)| := by
            congr 1
            ring
          _ ≤ |MvPolynomial.eval x h - MvPolynomial.eval x q| +
              |-MvPolynomial.eval x E| := abs_add_le _ _
          _ = |MvPolynomial.eval x h - MvPolynomial.eval x q| +
              |MvPolynomial.eval x E| := by rw [abs_neg]
      _ ≤ A / (k : ℝ) ^ 4 +
          putinarCorrectionRateConstant n (Broot : ℝ) * H /
            (k : ℝ) ^ 4 := by
        gcongr
        rw [abs_of_nonneg hEnonneg]
        exact hEupper
      _ = putinarWeightedApproximationConstant n Broot A H /
          (k : ℝ) ^ 4 := by
        unfold putinarWeightedApproximationConstant
        ring

end QuarticConvergence
end OptimalConvergenceRates

end
