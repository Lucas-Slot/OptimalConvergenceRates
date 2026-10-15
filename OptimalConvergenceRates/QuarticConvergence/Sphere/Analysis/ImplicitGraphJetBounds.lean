/-
  Quantitative jet bootstrapping for the one-dimensional implicit graph used by the
  positive-curvature split.

  The main device is the exact identity

    DX = -(\partial_tt F \circ G)⁻¹ • (\partial_ty F \circ G),

  with `G y = (X y, y)`.  Strict normal curvature makes the reciprocal harmless.  We
  implement it by a fixed globally smooth positive regularization, so ordinary global
  `ContDiff` composition bounds apply without introducing a punctured-domain calculus.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.PositiveValuePatch
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A globally smooth reciprocal which agrees with `x⁻¹` for `x ≥ a`. -/
def regularizedPositiveReciprocal (a x : ℝ) : ℝ :=
  (positiveIdentityRegularization a x)⁻¹

theorem regularizedPositiveReciprocal_contDiff {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ 4 (regularizedPositiveReciprocal a) := by
  exact (positiveIdentityRegularization_contDiff a).inv
    (fun x ↦ ne_of_gt (positiveIdentityRegularization_pos ha))

theorem regularizedPositiveReciprocal_eq_inv {a x : ℝ} (ha : 0 < a)
    (hax : a ≤ x) : regularizedPositiveReciprocal a x = x⁻¹ := by
  rw [regularizedPositiveReciprocal, positiveIdentityRegularization_eq_self ha hax]

/-- On a bounded interval the fixed regularized reciprocal has one common four-jet bound. -/
theorem exists_regularizedPositiveReciprocal_scalar_deriv_bound (a B : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t : ℝ, |t| ≤ B → ∀ j, j ≤ 4 →
        ‖iteratedFDeriv ℝ j (regularizedPositiveReciprocal a) t‖ ≤ K := by
  have houter : ContDiff ℝ 4 (regularizedPositiveReciprocal a) :=
    regularizedPositiveReciprocal_contDiff ha
  have hbound (j : ℕ) (hj : j ≤ 4) :
      ∃ K : ℝ, ∀ t ∈ Set.Icc (-B) B,
        ‖iteratedFDeriv ℝ j (regularizedPositiveReciprocal a) t‖ ≤ K :=
    isCompact_Icc.exists_bound_of_continuousOn
      ((houter.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn)
  obtain ⟨K0, hK0⟩ := hbound 0 (by norm_num)
  obtain ⟨K1, hK1⟩ := hbound 1 (by norm_num)
  obtain ⟨K2, hK2⟩ := hbound 2 (by norm_num)
  obtain ⟨K3, hK3⟩ := hbound 3 (by norm_num)
  obtain ⟨K4, hK4⟩ := hbound 4 (by norm_num)
  have hzero : (0 : ℝ) ∈ Set.Icc (-B) B := ⟨by linarith, hB⟩
  have hK0nonneg : 0 ≤ K0 := (norm_nonneg _).trans (hK0 0 hzero)
  have hK1nonneg : 0 ≤ K1 := (norm_nonneg _).trans (hK1 0 hzero)
  have hK2nonneg : 0 ≤ K2 := (norm_nonneg _).trans (hK2 0 hzero)
  have hK3nonneg : 0 ≤ K3 := (norm_nonneg _).trans (hK3 0 hzero)
  have hK4nonneg : 0 ≤ K4 := (norm_nonneg _).trans (hK4 0 hzero)
  let K := K0 + K1 + K2 + K3 + K4
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro t ht j hj
  have htIcc : t ∈ Set.Icc (-B) B := abs_le.mp ht
  interval_cases j
  · exact (hK0 t htIcc).trans (by dsimp [K]; linarith)
  · exact (hK1 t htIcc).trans (by dsimp [K]; linarith)
  · exact (hK2 t htIcc).trans (by dsimp [K]; linarith)
  · exact (hK3 t htIcc).trans (by dsimp [K]; linarith)
  · exact (hK4 t htIcc).trans (by dsimp [K]; linarith)

/-- The graph embedding `y ↦ (X(y),y)`. -/
def implicitGraphLift {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) (y : Fin n → ℝ) : ℝ × (Fin n → ℝ) :=
  (graph.graph y, y)

/-- The normal Hessian coefficient `∂_tt F`. -/
def implicitGraphNormalCurvatureField {n : ℕ} (input : NormalizedLocalSplitInput n)
    (z : ℝ × (Fin n → ℝ)) : ℝ :=
  fderiv ℝ (fun w ↦ fderiv ℝ input.function w (splitNormalDirection n)) z
    (splitNormalDirection n)

/-- The mixed normal-tangential Hessian coefficient `∂_ty F`. -/
def implicitGraphNormalTangentialField {n : ℕ} (input : NormalizedLocalSplitInput n)
    (z : ℝ × (Fin n → ℝ)) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (fderiv ℝ (fun w ↦ fderiv ℝ input.function w (splitNormalDirection n)) z).comp
    (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ))

/-- Exact first-derivative identity for the minimizing graph, in a form suited to repeated
quantitative differentiation. -/
theorem MinimizingGraphData.fderiv_eq_regularizedReciprocal_smul_tangential
    {n : ℕ} {input : NormalizedLocalSplitInput n}
    (graph : MinimizingGraphData input) :
    fderiv ℝ graph.graph = fun y ↦
      (-regularizedPositiveReciprocal (1 / 8)
        (implicitGraphNormalCurvatureField input (implicitGraphLift graph y))) •
          implicitGraphNormalTangentialField input (implicitGraphLift graph y) := by
  funext y
  let N : (ℝ × (Fin n → ℝ)) → ℝ := fun z ↦
    fderiv ℝ input.function z (splitNormalDirection n)
  let G : (Fin n → ℝ) → (ℝ × (Fin n → ℝ)) := fun w ↦ (graph.graph w, w)
  let T : (Fin n → ℝ) →L[ℝ] (ℝ × (Fin n → ℝ)) :=
    ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)
  have hN : ContDiff ℝ 5 N := by
    exact (input.contDiff.fderiv_right (m := 5) (by norm_num)).clm_apply contDiff_const
  have hG : ContDiff ℝ 5 G := graph.graph_contDiff.prodMk contDiff_id
  have hGderiv : fderiv ℝ G y =
      (fderiv ℝ graph.graph y).prod
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)) := by
    simpa [G, fderiv_fun_id] using
      (graph.graph_contDiff.differentiable (by norm_num) y).fderiv_prodMk differentiableAt_id
  have hstationary : N ∘ G = fun _ ↦ 0 := by
    funext w
    exact graph.first_derivative_zero w
  have hstationaryDeriv :
      (fderiv ℝ N (G y)).comp (fderiv ℝ G y) = 0 := by
    have h := congrArg (fun f ↦ fderiv ℝ f y) hstationary
    change fderiv ℝ (N ∘ G) y = fderiv ℝ (fun _ ↦ (0 : ℝ)) y at h
    rw [fderiv_comp y (hN.differentiable (by norm_num) (G y))
      (hG.differentiable (by norm_num) y)] at h
    simpa using h
  have hcurvature : (1 / 4 : ℝ) ≤
      implicitGraphNormalCurvatureField input (implicitGraphLift graph y) := by
    exact input.normal_curvature (graph.graph y, y) (graph.graph_point_mem y)
  have hreg : regularizedPositiveReciprocal (1 / 8)
      (implicitGraphNormalCurvatureField input (implicitGraphLift graph y)) =
        (implicitGraphNormalCurvatureField input (implicitGraphLift graph y))⁻¹ := by
    apply regularizedPositiveReciprocal_eq_inv (by norm_num)
    linarith
  ext v
  have hzero : fderiv ℝ N (G y) (fderiv ℝ graph.graph y v, v) = 0 := by
    have happ := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ ↦ L v) hstationaryDeriv
    rw [hGderiv] at happ
    simpa using happ
  have hdecomp : (fderiv ℝ graph.graph y v, v) =
      (fderiv ℝ graph.graph y v) • splitNormalDirection n + T v := by
    ext <;> simp [splitNormalDirection, T]
  rw [hdecomp, map_add, map_smul] at hzero
  have hcurvatureNe :
      implicitGraphNormalCurvatureField input (implicitGraphLift graph y) = 0 -> False :=
    ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hcurvature)
  change fderiv ℝ graph.graph y v =
    (-regularizedPositiveReciprocal (1 / 8)
      (implicitGraphNormalCurvatureField input (implicitGraphLift graph y))) *
        implicitGraphNormalTangentialField input (implicitGraphLift graph y) v
  rw [hreg]
  have heq : implicitGraphNormalCurvatureField input (implicitGraphLift graph y) *
      fderiv ℝ graph.graph y v =
        -implicitGraphNormalTangentialField input (implicitGraphLift graph y) v := by
    simpa [implicitGraphNormalCurvatureField, implicitGraphNormalTangentialField,
      implicitGraphLift, N, G, T, mul_comm] using eq_neg_of_add_eq_zero_left hzero
  calc
    fderiv ℝ graph.graph y v =
        (implicitGraphNormalCurvatureField input (implicitGraphLift graph y))⁻¹ *
          (implicitGraphNormalCurvatureField input (implicitGraphLift graph y) *
            fderiv ℝ graph.graph y v) := by field_simp
    _ = (implicitGraphNormalCurvatureField input (implicitGraphLift graph y))⁻¹ *
        (-implicitGraphNormalTangentialField input (implicitGraphLift graph y) v) := by rw [heq]
    _ = (-(implicitGraphNormalCurvatureField input (implicitGraphLift graph y))⁻¹) *
        implicitGraphNormalTangentialField input (implicitGraphLift graph y) v := by ring

end QuarticConvergence
end OptimalConvergenceRates

end
