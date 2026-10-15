/-
  Jet bounds for the affine segment used by the local Taylor coefficient.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.RawSquareCoefficientJetBounds
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.SplitAtomAssembly

open Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The product of two continuous multilinear maps has norm at most the maximum of their norms,
for the max norm on the target product. -/
theorem norm_continuousMultilinearMap_prod_le
    {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ContinuousMultilinearMap ℝ E F) (g : ContinuousMultilinearMap ℝ E G) :
    ‖f.prod g‖ ≤ max ‖f‖ ‖g‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    ((norm_nonneg f).trans (le_max_left ‖f‖ ‖g‖))
  intro m
  rw [ContinuousMultilinearMap.prod_apply, Prod.norm_def]
  apply max_le
  · exact (f.le_opNorm m).trans
      (mul_le_mul_of_nonneg_right (le_max_left ‖f‖ ‖g‖) (by positivity))
  · exact (g.le_opNorm m).trans
      (mul_le_mul_of_nonneg_right (le_max_right ‖f‖ ‖g‖) (by positivity))

/-- Every positive-order jet through order four of either coordinate projection has norm at most
one. -/
theorem norm_iteratedFDeriv_normalCoordinate_le_one {n q : ℕ}
    (z : ℝ × (Fin n → ℝ)) (hqOne : 1 ≤ q) (hq : q ≤ 4) :
    ‖iteratedFDeriv ℝ q (fun w : ℝ × (Fin n → ℝ) ↦ w.1) z‖ ≤ 1 := by
  rcases q with _ | q
  · omega
  rw [← norm_iteratedFDeriv_fderiv (n := q)]
  have hderiv : fderiv ℝ (fun w : ℝ × (Fin n → ℝ) ↦ w.1) =
      fun _ ↦ ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ) := by
    funext w
    exact fderiv_fst
  rw [hderiv]
  by_cases hqZero : q = 0
  · subst q
    rw [norm_iteratedFDeriv_zero]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simpa only [ContinuousLinearMap.coe_fst', one_mul] using norm_fst_le w
  · rw [iteratedFDeriv_const_of_ne hqZero]
    simp

theorem norm_iteratedFDeriv_tangentialCoordinate_le_one {n q : ℕ}
    (z : ℝ × (Fin n → ℝ)) (hqOne : 1 ≤ q) (hq : q ≤ 4) :
    ‖iteratedFDeriv ℝ q (fun w : ℝ × (Fin n → ℝ) ↦ w.2) z‖ ≤ 1 := by
  rcases q with _ | q
  · omega
  rw [← norm_iteratedFDeriv_fderiv (n := q)]
  have hderiv : fderiv ℝ (fun w : ℝ × (Fin n → ℝ) ↦ w.2) =
      fun _ ↦ ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ) := by
    funext w
    exact fderiv_snd
  rw [hderiv]
  by_cases hqZero : q = 0
  · subst q
    rw [norm_iteratedFDeriv_zero]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simpa only [ContinuousLinearMap.coe_snd', one_mul] using norm_snd_le w
  · rw [iteratedFDeriv_const_of_ne hqZero]
    simp

/-- If the minimizing graph has uniformly bounded positive-order jets, then the affine segment
from the graph to `z` has the power-form jet bound required by the higher chain rule. -/
theorem norm_iteratedFDeriv_localSquareCoefficientPath_le
    {n q : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (z : ℝ × (Fin n → ℝ)) {G : ℝ} (hG : 1 ≤ G)
    (hgraph : ∀ k, 1 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k graph.graph z.2‖ ≤ G)
    (hqOne : 1 ≤ q) (hq : q ≤ 4) :
    ‖iteratedFDeriv ℝ q (localSquareCoefficientPath graph s) z‖ ≤
      (2 * G) ^ q := by
  let graphPull : (ℝ × (Fin n → ℝ)) → ℝ :=
    tangentialCoordinatePullback graph.graph
  let normal : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦ w.1
  let tangent : (ℝ × (Fin n → ℝ)) → (Fin n → ℝ) := fun w ↦ w.2
  let first : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦
    (1 - s) * graphPull w + s * normal w
  have hgraphSmooth : ContDiff ℝ 4 graphPull :=
    tangentialCoordinatePullback_contDiff (graph.graph_contDiff.of_le (by norm_num))
  have hnormalSmooth : ContDiff ℝ 4 normal := by
    fun_prop
  have htangentSmooth : ContDiff ℝ 4 tangent := by
    fun_prop
  have hfirstSmooth : ContDiff ℝ 4 first := by
    dsimp [first]
    fun_prop
  have hgraphPull : ‖iteratedFDeriv ℝ q graphPull z‖ ≤ G := by
    exact (norm_iteratedFDeriv_tangentialCoordinatePullback_le
      (graph.graph_contDiff.of_le (by norm_num)) hq z).trans
        (hgraph q hqOne hq)
  have hnormal : ‖iteratedFDeriv ℝ q normal z‖ ≤ 1 :=
    norm_iteratedFDeriv_normalCoordinate_le_one z hqOne hq
  have htangent : ‖iteratedFDeriv ℝ q tangent z‖ ≤ 1 :=
    norm_iteratedFDeriv_tangentialCoordinate_le_one z hqOne hq
  have hsAbs : |s| ≤ 1 := by
    rw [abs_of_nonneg hs.1]
    exact hs.2
  have honeSubAbs : |1 - s| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]
    linarith [hs.1, hs.2]
  have hfirstDeriv : ‖iteratedFDeriv ℝ q first z‖ ≤ 2 * G := by
    change ‖iteratedFDeriv ℝ q
      ((fun w ↦ (1 - s) • graphPull w) + fun w ↦ s • normal w) z‖ ≤ 2 * G
    rw [iteratedFDeriv_add_apply (i := q)
      (((hgraphSmooth.const_smul (1 - s)).of_le (by exact_mod_cast hq)).contDiffAt)
      (((hnormalSmooth.const_smul s).of_le (by exact_mod_cast hq)).contDiffAt),
      iteratedFDeriv_const_smul_apply'
        (i := q) (a := 1 - s)
          ((hgraphSmooth.of_le (by exact_mod_cast hq)).contDiffAt),
      iteratedFDeriv_const_smul_apply'
        (i := q) (a := s)
          ((hnormalSmooth.of_le (by exact_mod_cast hq)).contDiffAt)]
    calc
      ‖(1 - s) • iteratedFDeriv ℝ q graphPull z +
          s • iteratedFDeriv ℝ q normal z‖ ≤
          ‖(1 - s) • iteratedFDeriv ℝ q graphPull z‖ +
            ‖s • iteratedFDeriv ℝ q normal z‖ := norm_add_le _ _
      _ = |1 - s| * ‖iteratedFDeriv ℝ q graphPull z‖ +
          |s| * ‖iteratedFDeriv ℝ q normal z‖ := by
            simp [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * G + 1 * 1 := by gcongr
      _ ≤ 2 * G := by linarith
  have hpathEq : localSquareCoefficientPath graph s = fun w ↦ (first w, tangent w) := by
    funext w
    simp [localSquareCoefficientPath, first, graphPull, normal, tangent,
      tangentialCoordinatePullback]
    ring
  rw [hpathEq, iteratedFDeriv_prodMk hfirstSmooth.contDiffAt
    htangentSmooth.contDiffAt (by exact_mod_cast hq)]
  calc
    ‖(iteratedFDeriv ℝ q first z).prod (iteratedFDeriv ℝ q tangent z)‖ ≤
        max ‖iteratedFDeriv ℝ q first z‖ ‖iteratedFDeriv ℝ q tangent z‖ :=
      norm_continuousMultilinearMap_prod_le _ _
    _ ≤ 2 * G := max_le hfirstDeriv (htangent.trans (by linarith))
    _ ≤ (2 * G) ^ q := by
      have htwoG : 1 ≤ 2 * G := by linarith
      calc
        2 * G = (2 * G) ^ 1 := by ring
        _ ≤ (2 * G) ^ q := pow_le_pow_right₀ htwoG hqOne


/-- The normal displacement from the minimizing graph. -/
def splitNormalDisplacement {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  z.1 - graph.graph z.2

@[fun_prop]
theorem splitNormalDisplacement_contDiff {n : ℕ}
    {input : NormalizedLocalSplitInput n} (graph : MinimizingGraphData input) :
    ContDiff ℝ 4 (splitNormalDisplacement graph) := by
  unfold splitNormalDisplacement
  exact contDiff_fst.sub
    ((graph.graph_contDiff.of_le (by norm_num)).comp contDiff_snd)

/-- Positive-order jets of the normal displacement cost at most the sum of the normal-coordinate
jet and the corresponding graph jet. -/
theorem norm_iteratedFDeriv_splitNormalDisplacement_le {n q : ℕ}
    {input : NormalizedLocalSplitInput n} (graph : MinimizingGraphData input)
    (z : ℝ × (Fin n → ℝ)) {G : ℝ} (hG : 1 ≤ G)
    (hgraph : ∀ k, 1 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k graph.graph z.2‖ ≤ G)
    (hqOne : 1 ≤ q) (hq : q ≤ 4) :
    ‖iteratedFDeriv ℝ q (splitNormalDisplacement graph) z‖ ≤ 2 * G := by
  let graphPull : (ℝ × (Fin n → ℝ)) → ℝ :=
    tangentialCoordinatePullback graph.graph
  let normal : (ℝ × (Fin n → ℝ)) → ℝ := fun w ↦ w.1
  have hgraphSmooth : ContDiff ℝ 4 graphPull :=
    tangentialCoordinatePullback_contDiff (graph.graph_contDiff.of_le (by norm_num))
  have hnormalSmooth : ContDiff ℝ 4 normal := by
    fun_prop
  have hgraphPull : ‖iteratedFDeriv ℝ q graphPull z‖ ≤ G := by
    exact (norm_iteratedFDeriv_tangentialCoordinatePullback_le
      (graph.graph_contDiff.of_le (by norm_num)) hq z).trans
        (hgraph q hqOne hq)
  have hnormal : ‖iteratedFDeriv ℝ q normal z‖ ≤ 1 :=
    norm_iteratedFDeriv_normalCoordinate_le_one z hqOne hq
  have hdisplacementEq : splitNormalDisplacement graph =
      normal + (-1 : ℝ) • graphPull := by
    funext w
    simp [splitNormalDisplacement, normal, graphPull,
      tangentialCoordinatePullback, sub_eq_add_neg]
  rw [hdisplacementEq]
  change ‖iteratedFDeriv ℝ q
    (normal + fun w ↦ (-1 : ℝ) • graphPull w) z‖ ≤ 2 * G
  rw [iteratedFDeriv_add_apply
    ((hnormalSmooth.of_le (by exact_mod_cast hq)).contDiffAt)
    (((hgraphSmooth.const_smul (-1 : ℝ)).of_le
      (by exact_mod_cast hq)).contDiffAt),
    iteratedFDeriv_const_smul_apply'
      (i := q) (a := (-1 : ℝ))
        ((hgraphSmooth.of_le (by exact_mod_cast hq)).contDiffAt)]
  calc
    ‖iteratedFDeriv ℝ q normal z +
        (-1 : ℝ) • iteratedFDeriv ℝ q graphPull z‖ ≤
        ‖iteratedFDeriv ℝ q normal z‖ +
          ‖(-1 : ℝ) • iteratedFDeriv ℝ q graphPull z‖ := norm_add_le _ _
    _ = ‖iteratedFDeriv ℝ q normal z‖ +
        ‖iteratedFDeriv ℝ q graphPull z‖ := by simp
    _ ≤ 1 + G := add_le_add hnormal hgraphPull
    _ ≤ 2 * G := by linarith

/-- The zero-jet displacement bound obtained directly from bounds on the normal coordinate and the
minimizing graph value. -/
theorem norm_iteratedFDeriv_zero_splitNormalDisplacement_le {n : ℕ}
    {input : NormalizedLocalSplitInput n} (graph : MinimizingGraphData input)
    (z : ℝ × (Fin n → ℝ)) {R : ℝ}
    (hnormal : |z.1| ≤ R) (hgraph : |graph.graph z.2| ≤ R) :
    ‖iteratedFDeriv ℝ 0 (splitNormalDisplacement graph) z‖ ≤ 2 * R := by
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  change |z.1 - graph.graph z.2| ≤ 2 * R
  calc
    |z.1 - graph.graph z.2| ≤ |z.1| + |graph.graph z.2| := by
      simpa [sub_eq_add_neg] using abs_add_le z.1 (-graph.graph z.2)
    _ ≤ R + R := add_le_add hnormal hgraph
    _ = 2 * R := by ring

/-- One common bound for all displacement jets through order four. -/
theorem norm_iteratedFDeriv_splitNormalDisplacement_le_of_bounds {n q : ℕ}
    {input : NormalizedLocalSplitInput n} (graph : MinimizingGraphData input)
    (z : ℝ × (Fin n → ℝ)) {R G : ℝ} (hG : 1 ≤ G)
    (hnormal : |z.1| ≤ R) (hgraphValue : |graph.graph z.2| ≤ R)
    (hgraphJet : ∀ k, 1 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k graph.graph z.2‖ ≤ G)
    (hq : q ≤ 4) :
    ‖iteratedFDeriv ℝ q (splitNormalDisplacement graph) z‖ ≤
      max (2 * R) (2 * G) := by
  by_cases hqZero : q = 0
  · subst q
    exact (norm_iteratedFDeriv_zero_splitNormalDisplacement_le
      graph z hnormal hgraphValue).trans (le_max_left _ _)
  · exact (norm_iteratedFDeriv_splitNormalDisplacement_le graph z hG hgraphJet
      (Nat.one_le_iff_ne_zero.mpr hqZero) hq).trans (le_max_right _ _)

/-- The ambient six-jet and graph four-jet estimates imply the coarse four-jet estimate for the
raw Taylor coefficient, with no hidden parameter-integral loss. -/
theorem norm_iteratedFDeriv_localRawSquareCoefficientFn_le_of_function_and_graph
    {n j : ℕ} (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input) (z : ℝ × (Fin n → ℝ))
    {M G : ℝ} (hM : 0 ≤ M) (hG : 1 ≤ G) (hj : j ≤ 4)
    (hfunction : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ k, k ≤ 6 →
      ‖iteratedFDeriv ℝ k input.function
        (localSquareCoefficientPath graph s z)‖ ≤ M)
    (hgraph : ∀ k, 1 ≤ k → k ≤ 4 →
      ‖iteratedFDeriv ℝ k graph.graph z.2‖ ≤ G) :
    ‖iteratedFDeriv ℝ j (localRawSquareCoefficientFn input graph) z‖ ≤
      (Nat.factorial 4 : ℝ) * M * (2 * G) ^ 4 := by
  apply norm_iteratedFDeriv_localRawSquareCoefficientFn_le
    input graph z hM (by linarith) hj
  · intro s hs q hq
    exact (norm_iteratedFDeriv_localNormalSecondDerivative_le
      input (localSquareCoefficientPath graph s z) hq).trans
        (hfunction s hs (q + 2) (by omega))
  · intro s hs q hqOne hq
    exact norm_iteratedFDeriv_localSquareCoefficientPath_le
      graph s hs z hG hgraph hqOne hq

/-- The explicit regularized square root associated to the normal Taylor coefficient. -/
def explicitLocalSplitRoot {n : ℕ} (a : ℝ) (input : NormalizedLocalSplitInput n)
    (graph : MinimizingGraphData input) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  splitNormalDisplacement graph z *
    Real.sqrt (positiveIdentityRegularization a
      (localRawSquareCoefficientFn input graph z))

@[fun_prop]
theorem explicitLocalSplitRoot_contDiff {n : ℕ} {a : ℝ} (ha : 0 < a)
    (input : NormalizedLocalSplitInput n) (graph : MinimizingGraphData input) :
    ContDiff ℝ 4 (explicitLocalSplitRoot a input graph) := by
  exact (splitNormalDisplacement_contDiff graph).mul
    (regularizedPositiveSqrt_contDiff ha
      (localRawSquareCoefficientFn_contDiff input graph))

/-- A fully concrete, dimension-independent four-jet bound for the explicit split root.  Its inputs
are precisely a six-jet bound for the ambient function along the Taylor segments, bounds on the
first four minimizing-graph jets, and zero-order bounds for the normal displacement. -/
theorem exists_uniform_explicitLocalSplitRoot_deriv_bound
    (a R M G : ℝ) (ha : 0 < a) (hM : 0 ≤ M) (hG : 1 ≤ G) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {n : ℕ} (input : NormalizedLocalSplitInput n)
        (graph : MinimizingGraphData input) (z : ℝ × (Fin n → ℝ)),
        |z.1| ≤ R → |graph.graph z.2| ≤ R →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ k, k ≤ 6 →
          ‖iteratedFDeriv ℝ k input.function
            (localSquareCoefficientPath graph s z)‖ ≤ M) →
        (∀ k, 1 ≤ k → k ≤ 4 →
          ‖iteratedFDeriv ℝ k graph.graph z.2‖ ≤ G) →
        ∀ j, j ≤ 4 →
          ‖iteratedFDeriv ℝ j (explicitLocalSplitRoot a input graph) z‖ ≤ A := by
  let Mdisplacement : ℝ := max 1 (max (2 * R) (2 * G))
  let Mraw : ℝ := max 1 ((Nat.factorial 4 : ℝ) * M * (2 * G) ^ 4)
  obtain ⟨A, hA, hroot⟩ :=
    exists_uniform_explicitSplitRoot_deriv_bound a Mdisplacement Mraw ha
      (by exact le_max_left _ _) (by exact le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro n input graph z hnormal hgraphValue hfunction hgraphJet j hj
  apply hroot (splitNormalDisplacement_contDiff graph)
    (localRawSquareCoefficientFn_contDiff input graph) z
  · intro q hq
    exact (norm_iteratedFDeriv_splitNormalDisplacement_le_of_bounds
      graph z hG hnormal hgraphValue hgraphJet hq).trans
        (le_max_right 1 (max (2 * R) (2 * G)))
  · intro q hq
    exact (norm_iteratedFDeriv_localRawSquareCoefficientFn_le_of_function_and_graph
      input graph z hM hG hq hfunction hgraphJet).trans
        (le_max_right 1 ((Nat.factorial 4 : ℝ) * M * (2 * G) ^ 4))
  · exact hj
end QuarticConvergence
end OptimalConvergenceRates

end
