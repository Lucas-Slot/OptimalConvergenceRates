/-
  Closing the quantitative implicit-function recurrence through the five graph derivatives
  needed by the curvature split.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ImplicitGraphCompositionBounds

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

def implicitGraphNormalCurvatureAlong {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) : ℝ :=
  implicitGraphNormalCurvatureField input (implicitGraphLift graph y)

def implicitGraphNormalTangentialAlong {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  implicitGraphNormalTangentialField input (implicitGraphLift graph y)

def implicitGraphReciprocalAlong {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) : ℝ :=
  regularizedPositiveReciprocal (1 / 8) (implicitGraphNormalCurvatureAlong graph y)

theorem implicitGraphNormalCurvatureAlong_contDiff {n : ℕ}
    {input : NormalizedLocalSplitInput n} (graph : MinimizingGraphData input) :
    ContDiff ℝ 4 (implicitGraphNormalCurvatureAlong graph) :=
  (implicitGraphNormalCurvatureField_contDiff input).comp
    ((implicitGraphLift_contDiff graph).of_le (by norm_num))

theorem implicitGraphNormalTangentialAlong_contDiff {n : ℕ}
    {input : NormalizedLocalSplitInput n} (graph : MinimizingGraphData input) :
    ContDiff ℝ 4 (implicitGraphNormalTangentialAlong graph) :=
  (implicitGraphNormalTangentialField_contDiff input).comp
    ((implicitGraphLift_contDiff graph).of_le (by norm_num))

theorem implicitGraphReciprocalAlong_contDiff {n : ℕ}
    {input : NormalizedLocalSplitInput n} (graph : MinimizingGraphData input) :
    ContDiff ℝ 4 (implicitGraphReciprocalAlong graph) :=
  (regularizedPositiveReciprocal_contDiff (by norm_num)).comp
    (implicitGraphNormalCurvatureAlong_contDiff graph)

/-- A single common bound for all normal-Hessian factor jets through order four. -/
def implicitGraphFactorJetBound (M B : ℝ) : ℝ :=
  max 1 ((Nat.factorial 4 : ℝ) * M * B ^ 4)

theorem one_le_implicitGraphFactorJetBound (M B : ℝ) :
    1 ≤ implicitGraphFactorJetBound M B :=
  le_max_left _ _

theorem norm_iteratedFDeriv_normalCurvatureAlong_le_factor
    {n q : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) {M B : ℝ}
    (hM : 1 ≤ M) (hB : 1 ≤ B)
    (hambient : ∀ k, k ≤ 6 →
      ‖iteratedFDeriv ℝ k input.function (implicitGraphLift graph y)‖ ≤ M)
    (hgraph : ∀ k, 1 ≤ k → k ≤ q →
      ‖iteratedFDeriv ℝ k graph.graph y‖ ≤ B)
    (hq : q ≤ 4) :
    ‖iteratedFDeriv ℝ q (implicitGraphNormalCurvatureAlong graph) y‖ ≤
      implicitGraphFactorJetBound M B := by
  have hbase := norm_iteratedFDeriv_normalCurvature_comp_graph_le
    graph y hM hB hambient hgraph hq
  have hfac : (q.factorial : ℝ) ≤ (Nat.factorial 4 : ℝ) := by
    exact_mod_cast Nat.factorial_le hq
  have hpow : B ^ q ≤ B ^ 4 := pow_le_pow_right₀ hB hq
  exact hbase.trans <| (show
    (q.factorial : ℝ) * M * B ^ q ≤ implicitGraphFactorJetBound M B by
      apply le_max_of_le_right
      gcongr)

theorem norm_iteratedFDeriv_normalTangentialAlong_le_factor
    {n q : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) {M B : ℝ}
    (hM : 1 ≤ M) (hB : 1 ≤ B)
    (hambient : ∀ k, k ≤ 6 →
      ‖iteratedFDeriv ℝ k input.function (implicitGraphLift graph y)‖ ≤ M)
    (hgraph : ∀ k, 1 ≤ k → k ≤ q →
      ‖iteratedFDeriv ℝ k graph.graph y‖ ≤ B)
    (hq : q ≤ 4) :
    ‖iteratedFDeriv ℝ q (implicitGraphNormalTangentialAlong graph) y‖ ≤
      implicitGraphFactorJetBound M B := by
  have hbase := norm_iteratedFDeriv_normalTangential_comp_graph_le
    graph y hM hB hambient hgraph hq
  have hfac : (q.factorial : ℝ) ≤ (Nat.factorial 4 : ℝ) := by
    exact_mod_cast Nat.factorial_le hq
  have hpow : B ^ q ≤ B ^ 4 := pow_le_pow_right₀ hB hq
  exact hbase.trans <| (show
    (q.factorial : ℝ) * M * B ^ q ≤ implicitGraphFactorJetBound M B by
      apply le_max_of_le_right
      gcongr)

/-- The reciprocal normal-curvature factor has uniformly bounded jets whenever the ambient
function and the already constructed graph jets have common bounds. -/
theorem exists_uniform_implicitGraphReciprocalAlong_deriv_bound (M B : ℝ)
    (hM : 1 ≤ M) (hB : 1 ≤ B) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ {n q : ℕ} {input : NormalizedLocalSplitInput n}
        (graph : MinimizingGraphData input) (y : Fin n → ℝ),
        (∀ k, k ≤ 6 →
          ‖iteratedFDeriv ℝ k input.function (implicitGraphLift graph y)‖ ≤ M) →
        (∀ k, 1 ≤ k → k ≤ q →
          ‖iteratedFDeriv ℝ k graph.graph y‖ ≤ B) →
        q ≤ 4 →
        ‖iteratedFDeriv ℝ q (implicitGraphReciprocalAlong graph) y‖ ≤ R := by
  obtain ⟨Kouter, hKouter, houter⟩ :=
    exists_regularizedPositiveReciprocal_scalar_deriv_bound
      (1 / 8) M (by norm_num) (zero_le_one.trans hM)
  let K := implicitGraphFactorJetBound M B
  let R := max 1 ((Nat.factorial 4 : ℝ) * Kouter * K ^ 4)
  refine ⟨R, zero_le_one.trans (le_max_left _ _), ?_⟩
  intro n q input graph y hambient hgraph hq
  have hcurvSmooth := implicitGraphNormalCurvatureAlong_contDiff graph
  have hcurvValue : |implicitGraphNormalCurvatureAlong graph y| ≤ M := by
    rw [← Real.norm_eq_abs]
    simpa [norm_iteratedFDeriv_zero, implicitGraphNormalCurvatureAlong] using
      (norm_iteratedFDeriv_implicitGraphNormalCurvatureField_le input
        (by norm_num) (implicitGraphLift graph y)).trans (hambient 2 (by norm_num))
  have hK : 1 ≤ K := one_le_implicitGraphFactorJetBound M B
  have hinner (i : ℕ) (hiOne : 1 ≤ i) (hi : i ≤ q) :
      ‖iteratedFDeriv ℝ i (implicitGraphNormalCurvatureAlong graph) y‖ ≤ K ^ i := by
    calc
      _ ≤ K := norm_iteratedFDeriv_normalCurvatureAlong_le_factor
        graph y hM hB hambient
          (fun k hkOne hki ↦ hgraph k hkOne (hki.trans hi)) (hi.trans hq)
      _ = K ^ 1 := by ring
      _ ≤ K ^ i := pow_le_pow_right₀ hK hiOne
  have hcomp := norm_iteratedFDeriv_comp_le (N := 4)
    (regularizedPositiveReciprocal_contDiff (by norm_num))
    hcurvSmooth (by exact_mod_cast hq) y
    (C := Kouter) (D := K)
    (fun i hi ↦ houter (implicitGraphNormalCurvatureAlong graph y)
      hcurvValue i (hi.trans hq))
    hinner
  have hfac : (q.factorial : ℝ) ≤ (Nat.factorial 4 : ℝ) := by
    exact_mod_cast Nat.factorial_le hq
  have hpow : K ^ q ≤ K ^ 4 := pow_le_pow_right₀ hK hq
  change ‖iteratedFDeriv ℝ q
    (regularizedPositiveReciprocal (1 / 8) ∘
      implicitGraphNormalCurvatureAlong graph) y‖ ≤ R
  exact hcomp.trans <| (show
    (q.factorial : ℝ) * Kouter * K ^ q ≤ R by
      apply le_max_of_le_right
      gcongr)

/-- One step of the quantitative implicit recurrence.  Jets of the graph through order q
control its derivative of order q+1, using ambient derivatives only through q+2. -/
theorem exists_uniform_minimizingGraph_next_deriv_bound (q : ℕ) (M B : ℝ)
    (hq : q ≤ 4) (hM : 1 ≤ M) (hB : 1 ≤ B) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {n : ℕ} {input : NormalizedLocalSplitInput n}
        (graph : MinimizingGraphData input) (y : Fin n → ℝ),
        (∀ k, k ≤ 6 →
          ‖iteratedFDeriv ℝ k input.function (implicitGraphLift graph y)‖ ≤ M) →
        (∀ k, 1 ≤ k → k ≤ q →
          ‖iteratedFDeriv ℝ k graph.graph y‖ ≤ B) →
        ‖iteratedFDeriv ℝ (q + 1) graph.graph y‖ ≤ A := by
  obtain ⟨R, hR, hreciprocal⟩ :=
    exists_uniform_implicitGraphReciprocalAlong_deriv_bound M B hM hB
  let K := implicitGraphFactorJetBound M B
  let A := max 1 (16 * R * K)
  have hKnonneg : 0 ≤ K := zero_le_one.trans (one_le_implicitGraphFactorJetBound M B)
  refine ⟨A, le_max_left _ _, ?_⟩
  intro n input graph y hambient hgraph
  have hrecipSmooth := implicitGraphReciprocalAlong_contDiff graph
  have htangentSmooth := implicitGraphNormalTangentialAlong_contDiff graph
  have hproduct := norm_iteratedFDeriv_smul_le hrecipSmooth.neg htangentSmooth y
    (by exact_mod_cast hq)
  have hsum :
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun w ↦ -implicitGraphReciprocalAlong graph w) y‖ *
          ‖iteratedFDeriv ℝ (q - i) (implicitGraphNormalTangentialAlong graph) y‖ ≤
        ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * R * K := by
    apply Finset.sum_le_sum
    intro i hi
    have hiq : i ≤ q := Finset.mem_range_succ_iff.mp hi
    have hsubq : q - i ≤ q := Nat.sub_le q i
    gcongr
    · change ‖iteratedFDeriv ℝ i (-implicitGraphReciprocalAlong graph) y‖ ≤ R
      rw [iteratedFDeriv_neg_apply, norm_neg]
      exact hreciprocal graph y hambient
        (fun k hkOne hki ↦ hgraph k hkOne (hki.trans hiq))
        (hiq.trans hq)
    · exact norm_iteratedFDeriv_normalTangentialAlong_le_factor
        graph y hM hB hambient
          (fun k hkOne hki ↦ hgraph k hkOne (hki.trans hsubq))
          (hsubq.trans hq)
  have hchoose :
      (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * R * K) =
        (2 : ℝ) ^ q * R * K := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    norm_cast
    rw [Nat.sum_range_choose]
  have hpow : (2 : ℝ) ^ q ≤ 16 := by
    interval_cases q <;> norm_num
  rw [← norm_iteratedFDeriv_fderiv (n := q),
    graph.fderiv_eq_regularizedReciprocal_smul_tangential]
  change ‖iteratedFDeriv ℝ q
    (fun w ↦ (-implicitGraphReciprocalAlong graph w) •
      implicitGraphNormalTangentialAlong graph w) y‖ ≤ A
  exact hproduct.trans <| hsum.trans <| (by
    rw [hchoose]
    apply le_max_of_le_right
    gcongr)

end QuarticConvergence
end OptimalConvergenceRates

end
