/-
  Quantitative bounds for the integral Taylor coefficient in the one-normal-coordinate split.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ExplicitSplitRootJetBounds
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ParametricIntegralJetBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The affine normal segment from the minimizing graph to the point `z`, at parameter `s`. -/
def localSquareCoefficientPath {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (s : ℝ)
    (z : ℝ × (Fin n → ℝ)) : ℝ × (Fin n → ℝ) :=
  (graph.graph z.2 + s * (z.1 - graph.graph z.2), z.2)

theorem localSquareCoefficientPath_contDiff {n : ℕ}
    {input : NormalizedLocalSplitInput n} (graph : MinimizingGraphData input) (s : ℝ) :
    ContDiff ℝ 4 (localSquareCoefficientPath graph s) := by
  have hgraph : ContDiff ℝ 4 graph.graph := graph.graph_contDiff.of_le (by norm_num)
  unfold localSquareCoefficientPath
  fun_prop

/-- Applying the two fixed unit normal vectors loses no norm: a `j`-jet of the normal Hessian
is bounded by the ambient `(j+2)`-jet. -/
theorem norm_iteratedFDeriv_localNormalSecondDerivative_le {n j : ℕ}
    (input : NormalizedLocalSplitInput n) (z : ℝ × (Fin n → ℝ)) (hj : j ≤ 4) :
    ‖iteratedFDeriv ℝ j (localNormalSecondDerivative input) z‖ ≤
      ‖iteratedFDeriv ℝ (j + 2) input.function z‖ := by
  let e : ℝ × (Fin n → ℝ) := splitNormalDirection n
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦ fderiv ℝ input.function w e
  have hN : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  have hDN : ContDiff ℝ 4 (fderiv ℝ N) :=
    hN.fderiv_right (m := 4) (by norm_num)
  have hfirst := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ N) (c := e) (x := z) (n := j)
    hDN.contDiffAt (by exact_mod_cast hj)
  have hDF : ContDiff ℝ 5 (fderiv ℝ input.function) :=
    input.contDiff.fderiv_right (m := 5) (by norm_num)
  have hsecond := norm_iteratedFDeriv_clm_apply_const
    (f := fderiv ℝ input.function) (c := e) (x := z) (n := j + 1)
    hDF.contDiffAt (by exact_mod_cast (Nat.add_le_add_right hj 1))
  calc
    ‖iteratedFDeriv ℝ j (localNormalSecondDerivative input) z‖ ≤
        ‖e‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ N) z‖ := by
      simpa [localNormalSecondDerivative, N, e] using hfirst
    _ = ‖iteratedFDeriv ℝ (j + 1) N z‖ := by
      rw [norm_iteratedFDeriv_fderiv]
      simp [e, splitNormalDirection, Prod.norm_def]
    _ ≤ ‖e‖ * ‖iteratedFDeriv ℝ (j + 1) (fderiv ℝ input.function) z‖ :=
      hsecond
    _ = ‖iteratedFDeriv ℝ (j + 2) input.function z‖ := by
      rw [norm_iteratedFDeriv_fderiv]
      simp [e, splitNormalDirection, Prod.norm_def]

/-- Coarse dimension-independent bound for the raw integral coefficient.  The two hypotheses are
exactly the inputs needed by the higher chain rule: ambient normal-Hessian jets along the segment
and jets of the segment map itself. -/
theorem norm_iteratedFDeriv_localRawSquareCoefficientFn_le
    {n j : ℕ} (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input) (z : ℝ × (Fin n → ℝ))
    {MH D : ℝ} (hMH : 0 ≤ MH) (hD : 1 ≤ D) (hj : j ≤ 4)
    (hH : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ q, q ≤ 4 →
      ‖iteratedFDeriv ℝ q (localNormalSecondDerivative input)
        (localSquareCoefficientPath graph s z)‖ ≤ MH)
    (hpath : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ q, 1 ≤ q → q ≤ 4 →
      ‖iteratedFDeriv ℝ q (localSquareCoefficientPath graph s) z‖ ≤ D ^ q) :
    ‖iteratedFDeriv ℝ j (localRawSquareCoefficientFn input graph) z‖ ≤
      (Nat.factorial 4 : ℝ) * MH * D ^ 4 := by
  let B : ℝ := (Nat.factorial 4 : ℝ) * MH * D ^ 4
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hintegrand : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ j
        (fun w ↦ localRawSquareCoefficientIntegrand input graph (w, s)) z‖ ≤ B := by
    intro s hs
    let path := localSquareCoefficientPath graph s
    have hcompSmooth : ContDiff ℝ 4
        (localNormalSecondDerivative input ∘ path) :=
      (localNormalSecondDerivative_contDiff input).comp
        (localSquareCoefficientPath_contDiff graph s)
    have hcomp := norm_iteratedFDeriv_comp_le
      (localNormalSecondDerivative_contDiff input)
      (localSquareCoefficientPath_contDiff graph s)
      (by exact_mod_cast hj) z (C := MH) (D := D)
      (fun q hq ↦ hH s hs q (hq.trans hj))
      (fun q hqOne hq ↦ hpath s hs q hqOne (hq.trans hj))
    have hsAbs : |1 - s| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    have hfactorial : (j.factorial : ℝ) ≤ (Nat.factorial 4 : ℝ) := by
      exact_mod_cast Nat.factorial_le hj
    have hpower : D ^ j ≤ D ^ 4 := pow_le_pow_right₀ hD hj
    have hscale :
        ‖iteratedFDeriv ℝ j
          (fun w ↦ localRawSquareCoefficientIntegrand input graph (w, s)) z‖ =
          |1 - s| *
            ‖iteratedFDeriv ℝ j
              (localNormalSecondDerivative input ∘ path) z‖ := by
      have heq : (fun w ↦ localRawSquareCoefficientIntegrand input graph (w, s)) =
          (1 - s) • (localNormalSecondDerivative input ∘ path) := by
        funext w
        simp [localRawSquareCoefficientIntegrand, localSquareCoefficientPath,
          path, smul_eq_mul]
      rw [heq,
        iteratedFDeriv_const_smul_apply
          (i := j) (a := 1 - s) ((hcompSmooth.of_le (by exact_mod_cast hj)).contDiffAt),
        norm_smul, Real.norm_eq_abs]
    rw [hscale]
    calc
      |1 - s| * ‖iteratedFDeriv ℝ j
          (localNormalSecondDerivative input ∘ path) z‖ ≤
          1 * ((j.factorial : ℝ) * MH * D ^ j) := by gcongr
      _ = (j.factorial : ℝ) * MH * D ^ j := one_mul _
      _ ≤ (Nat.factorial 4 : ℝ) * MH * D ^ 4 := by gcongr
      _ = B := rfl
  have hIntegral := norm_iteratedFDeriv_setIntegral_Icc_le j
    ((localRawSquareCoefficientIntegrand_contDiff input graph).of_le
      (by exact_mod_cast hj)) z hB hintegrand
  simpa [localRawSquareCoefficientFn] using hIntegral

end QuarticConvergence
end OptimalConvergenceRates

end
