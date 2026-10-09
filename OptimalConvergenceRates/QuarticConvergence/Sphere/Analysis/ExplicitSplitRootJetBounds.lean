/-
  Quantitative calculus for the explicit root in the positive-curvature split.

  The key point is to regard

    sqrt (positiveIdentityRegularization a (raw z))

  as one fixed globally smooth scalar outer function composed with `raw`.  This avoids
  differentiating `Real.sqrt` on a moving positive range.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.PositiveValuePatch
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The regularized-positive-square-root jet estimate from the positive-value branch, specialized
to the product coordinates used by the curvature split.  The constant is independent of the
tangential dimension. -/
theorem exists_uniform_regularizedPositiveSqrt_prod_deriv_bound (a M : ℝ)
    (ha : 0 < a) (hM : 1 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {n : ℕ} {Phi : (ℝ × (Fin n → ℝ)) → ℝ}, ContDiff ℝ 4 Phi →
        ∀ x : ℝ × (Fin n → ℝ),
          (∀ q, q ≤ 4 → ‖iteratedFDeriv ℝ q Phi x‖ ≤ M) →
          ∀ j, j ≤ 4 →
            ‖iteratedFDeriv ℝ j (regularizedPositiveSqrt a Phi) x‖ ≤ A := by
  obtain ⟨K, hKnonneg, houterBound⟩ :=
    exists_regularizedPositiveSqrt_scalar_deriv_bound a M ha (zero_le_one.trans hM)
  let outer : ℝ → ℝ := regularizedPositiveSqrt a (fun s : ℝ ↦ s)
  let A : ℝ := (Nat.factorial 4 : ℝ) * K * M ^ 4
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro n Phi hPhi x hPhiBound j hj
  have hvalue : |Phi x| ≤ M := by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hPhiBound 0 (by norm_num)
  have houter : ContDiff ℝ 4 outer :=
    regularizedPositiveSqrt_contDiff ha contDiff_id
  have hinner (i : ℕ) (hiOne : 1 ≤ i) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i Phi x‖ ≤ M ^ i := by
    calc
      ‖iteratedFDeriv ℝ i Phi x‖ ≤ M := hPhiBound i (hi.trans hj)
      _ = M ^ 1 := by ring
      _ ≤ M ^ i := pow_le_pow_right₀ hM hiOne
  have hcomp := norm_iteratedFDeriv_comp_le houter hPhi
    (by exact_mod_cast hj) x
    (C := K) (D := M)
    (fun i hi ↦ houterBound (Phi x) hvalue i (hi.trans hj)) hinner
  have hfactorial : (j.factorial : ℝ) ≤ (Nat.factorial 4 : ℝ) := by
    exact_mod_cast Nat.factorial_le hj
  have hpower : M ^ j ≤ M ^ 4 := pow_le_pow_right₀ hM hj
  rw [show regularizedPositiveSqrt a Phi = outer ∘ Phi by rfl]
  calc
    ‖iteratedFDeriv ℝ j (outer ∘ Phi) x‖ ≤
        (j.factorial : ℝ) * K * M ^ j := hcomp
    _ ≤ (Nat.factorial 4 : ℝ) * K * M ^ 4 := by gcongr
    _ = A := rfl

/-- Uniform four-jet bound for the explicit Taylor root once the displacement and the raw Taylor
coefficient have common four-jet bounds.  This is the generic last step needed after quantitative
implicit-function and integral-remainder estimates have bounded those two inputs.

The coefficient is regularized *before* taking its square root.  Consequently the theorem needs
no pointwise lower-bound hypothesis on `raw`; positivity is built into the fixed outer function. -/
theorem exists_uniform_explicitSplitRoot_deriv_bound
    (a Mdisplacement Mraw : ℝ) (ha : 0 < a)
    (hMdisplacement : 1 ≤ Mdisplacement) (hMraw : 1 ≤ Mraw) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {n : ℕ}
        {displacement raw : (ℝ × (Fin n → ℝ)) → ℝ},
        ContDiff ℝ 4 displacement → ContDiff ℝ 4 raw →
        ∀ x : ℝ × (Fin n → ℝ),
          (∀ q, q ≤ 4 →
            ‖iteratedFDeriv ℝ q displacement x‖ ≤ Mdisplacement) →
          (∀ q, q ≤ 4 → ‖iteratedFDeriv ℝ q raw x‖ ≤ Mraw) →
          ∀ j, j ≤ 4 →
            ‖iteratedFDeriv ℝ j
              (fun z ↦ displacement z *
                Real.sqrt (positiveIdentityRegularization a (raw z))) x‖ ≤ A := by
  obtain ⟨Asqrt, hAsqrt, hsqrt⟩ :=
    exists_uniform_regularizedPositiveSqrt_prod_deriv_bound a Mraw ha hMraw
  let A : ℝ := 16 * Mdisplacement * Asqrt
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro n displacement raw hdisplacement hraw x hdisplacementBound hrawBound j hj
  have hsqrtSmooth : ContDiff ℝ 4 (regularizedPositiveSqrt a raw) :=
    regularizedPositiveSqrt_contDiff ha hraw
  have hproduct := norm_iteratedFDeriv_mul_le hdisplacement hsqrtSmooth x
    (by exact_mod_cast hj)
  have hsum :
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i displacement x‖ *
            ‖iteratedFDeriv ℝ (j - i) (regularizedPositiveSqrt a raw) x‖ ≤
        ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * Mdisplacement * Asqrt := by
    apply Finset.sum_le_sum
    intro i hi
    have hiJ : i ≤ j := Finset.mem_range_succ_iff.mp hi
    have hsubJ : j - i ≤ j := Nat.sub_le j i
    gcongr
    · exact hdisplacementBound i (hiJ.trans hj)
    · exact hsqrt hraw x hrawBound (j - i) (hsubJ.trans hj)
  have hchoose :
      (∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * Mdisplacement * Asqrt) =
        (2 : ℝ) ^ j * Mdisplacement * Asqrt := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    norm_cast
    rw [Nat.sum_range_choose]
  have hpow : (2 : ℝ) ^ j ≤ 16 := by
    interval_cases j <;> norm_num
  change ‖iteratedFDeriv ℝ j
    (fun z ↦ displacement z * regularizedPositiveSqrt a raw z) x‖ ≤ A
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i displacement x‖ *
            ‖iteratedFDeriv ℝ (j - i) (regularizedPositiveSqrt a raw) x‖ := hproduct
    _ ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * Mdisplacement * Asqrt := hsum
    _ = (2 : ℝ) ^ j * Mdisplacement * Asqrt := hchoose
    _ ≤ 16 * Mdisplacement * Asqrt := by gcongr
    _ = A := rfl

end QuarticConvergence
end OptimalConvergenceRates

end
