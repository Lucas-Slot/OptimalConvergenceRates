/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/FineScaleCover.lean

  Quantitative square partitions with an arbitrarily prescribed upper scale.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ScaleCover

open Finset Set
open scoped BigOperators Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A quantitative scale cover whose active radii are at most the prescribed fraction
`σ` of the intrinsic nonnegative-jet scale. -/
structure FineQuantitativeScaleCover {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (D σ A : ℝ) (B : ℕ) extends QuantitativeScaleCover u D A B where
  radius_le_fine : ∀ i, i ∈ active →
    radius i ≤ σ * nonnegativeJetScale u (center i)

/-- Uniform existence of quantitative square covers at every prescribed sufficiently fine
fraction of the intrinsic scale. -/
def HasUniformFineScaleCover (n : ℕ) : Prop :=
  ∀ D : ℝ, 2 ≤ D → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    ∃ A : ℝ, ∃ B : ℕ, 1 ≤ A ∧ 0 < B ∧
      ∀ u : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 u →
        Nonempty (FineQuantitativeScaleCover u D σ A B)

namespace FineQuantitativeScaleCover

/-- Forgetting the prescribed fine-scale bound recovers the original quantitative cover. -/
abbrev toScaleCover {n : ℕ} {u : (Fin n → ℝ) → ℝ} {D σ A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D σ A B) : QuantitativeScaleCover u D A B :=
  cover.toQuantitativeScaleCover

/-- Every active cover radius is a positive fraction of its intrinsic scale. -/
theorem radiusRatio_pos {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D σ A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D σ A B) {i : ℕ}
    (hi : i ∈ cover.active) :
    0 < cover.radius i / nonnegativeJetScale u (cover.center i) := by
  exact div_pos (cover.radius_pos i hi)
    ((cover.radius_pos i hi).trans_le (cover.radius_comparable i hi).1)

/-- The intrinsic radius ratio is at most one. -/
theorem radiusRatio_le_one {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D σ A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D σ A B) {i : ℕ}
    (hi : i ∈ cover.active) :
    cover.radius i / nonnegativeJetScale u (cover.center i) ≤ 1 := by
  exact (div_le_one
    ((cover.radius_pos i hi).trans_le (cover.radius_comparable i hi).1)).2
      (cover.radius_comparable i hi).1

/-- The reciprocal cutoff constant is a uniform lower bound for every active intrinsic
radius ratio. This is the lower scale bound used to choose one child radius cap for all
parents in a fine cover. -/
theorem inv_le_radiusRatio {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D σ A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D σ A B) {i : ℕ}
    (hi : i ∈ cover.active) (hA : 0 < A) :
    A⁻¹ ≤ cover.radius i / nonnegativeJetScale u (cover.center i) := by
  have hr : 0 < cover.radius i := cover.radius_pos i hi
  have hR : 0 < nonnegativeJetScale u (cover.center i) :=
    hr.trans_le (cover.radius_comparable i hi).1
  rw [inv_eq_one_div, div_le_div_iff₀ hA hR]
  simpa [mul_comm] using (cover.radius_comparable i hi).2

end FineQuantitativeScaleCover

/-- A uniformly fine cover in particular supplies the original quantitative cover API. -/
theorem HasUniformFineScaleCover.toUniformScaleCover {n : ℕ}
    (hfine : HasUniformFineScaleCover n) : HasUniformScaleCover n := by
  intro D hD
  obtain ⟨A, B, hA, hB, hcover⟩ := hfine D hD 1 zero_lt_one le_rfl
  refine ⟨A, B, hA, hB, ?_⟩
  intro u hu
  exact (hcover u hu).map FineQuantitativeScaleCover.toScaleCover

/-- Slow variation yields quantitative square partitions at every prescribed fraction of the
intrinsic scale. This is the fine-radius version of
`quantitativeSquarePartition_of_slowVariation`; its construction uses
`ε = min (c / (4L)) σ`. -/
theorem fineQuantitativeSquarePartition_of_slowVariation {n : ℕ}
    (hslow : HasIntrinsicScaleSlowVariation n) : HasUniformFineScaleCover n := by
  rcases hslow with ⟨c₀, C, hc₀, hC, hvariation⟩
  intro D hD σ hσ hσone
  let c := min c₀ 1
  classical
  let L := max D (C + 3)
  let ε := min (c / (4 * L)) σ
  have hc : 0 < c := by simp [c, hc₀]
  have hc_le_c₀ : c ≤ c₀ := min_le_left _ _
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hL_lower : C + 3 ≤ L := le_max_right _ _
  have hDL : D ≤ L := le_max_left _ _
  have hLpos : 0 < L := by linarith
  have hL0 : 0 ≤ L := hLpos.le
  have hLstrict : C + 2 < L := by linarith
  have hbaseε : 0 < c / (4 * L) := by positivity
  have hε : 0 < ε := by simp [ε, hbaseε, hσ]
  have hε_le_base : ε ≤ c / (4 * L) := min_le_left _ _
  have hε_le_σ : ε ≤ σ := min_le_right _ _
  have hε_le_one : ε ≤ 1 := hε_le_σ.trans hσone
  have hsmallL : 2 * L * ε ≤ c := by
    calc
      2 * L * ε ≤ 2 * L * (c / (4 * L)) := by gcongr
      _ = c / 2 := by field_simp; ring
      _ ≤ c := by linarith
  have hsmallD : 2 * D * ε ≤ c := by
    calc
      2 * D * ε ≤ 2 * L * ε := by gcongr
      _ ≤ c := hsmallL
  obtain ⟨Aderiv, hAderiv, hderiv⟩ :=
    exists_uniform_selectedSquareNormalizedFamily_scaled_deriv_bound
      n C L ε hC hLstrict hε
  let A := max Aderiv ε⁻¹
  have hA : 1 ≤ A := hAderiv.trans (le_max_left _ _)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hinv_le_A : ε⁻¹ ≤ A := le_max_right _ _
  have hAε : 1 ≤ A * ε := by
    calc
      1 = ε⁻¹ * ε := by field_simp
      _ ≤ A * ε := mul_le_mul_of_nonneg_right hinv_le_A hε.le
  have hD0 : 0 ≤ D := by linarith
  let BD := intrinsicOverlapBound n hD0 hC
  let B := max BD 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨A, B, hA, hB, ?_⟩
  intro u hu
  have hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x := by
    intro x y hxy
    apply hvariation u hu x y
    exact hxy.trans (mul_le_mul_of_nonneg_right hc_le_c₀
      (nonnegativeJetScale_nonneg u x))
  obtain ⟨s, hdis, hcover⟩ := exists_disjoint_intrinsic_covering_families hu ε hε
  let I := selectedIntrinsicCentersNatIndexing hε s hdis
  let bump := activeIntrinsicRawBump u I.value I.active ε
  let cutoff := squareNormalizedFamily bump
  let radius : ℕ → ℝ := fun i => if i ∈ I.active then
    ε * nonnegativeJetScale u (I.value i) else 1
  have hcenter : ∀ i, i ∈ I.active → 0 < nonnegativeJetScale u (I.value i) := by
    exact selectedIntrinsicCentersNatIndexing_value_pos hε s hdis
  have hoverlapL := selectedIntrinsicCentersNatIndexing_overlap_bound n hL0 hC hε
    hsmallL hvar s hdis
  have hoverlapD := selectedIntrinsicCentersNatIndexing_overlap_bound n hD0 hC hε
    hsmallD hvar s hdis
  have hcont := selectedSquareNormalizedFamily_contDiff hC hLstrict hε hsmallL
    hvar s hdis hcover hoverlapL
  have hderiv' := hderiv hsmallL hvar s hdis hcover
  refine ⟨{
    two_le_dilation := hD
    center := I.value
    radius := radius
    cutoff := cutoff
    active := I.active
    cutoff_eq_zero_of_not_active := ?_
    radius_pos := ?_
    radius_comparable := ?_
    cutoff_contDiff := ?_
    cutoff_support := ?_
    square_partition := ?_
    overlap := ?_
    scaled_cutoff := ?_
    radius_le_fine := ?_ }⟩
  · intro i hi
    funext x
    simp [cutoff, squareNormalizedFamily, bump, activeIntrinsicRawBump, hi]
  · intro i hi
    simp [radius, hi, mul_pos hε (hcenter i hi)]
  · intro i hi
    have hRi : 0 ≤ nonnegativeJetScale u (I.value i) :=
      nonnegativeJetScale_nonneg u (I.value i)
    constructor
    · simp only [radius, ite_eq_left hi]
      calc
        ε * nonnegativeJetScale u (I.value i) ≤
            1 * nonnegativeJetScale u (I.value i) :=
          mul_le_mul_of_nonneg_right hε_le_one hRi
        _ = nonnegativeJetScale u (I.value i) := one_mul _
    · simp only [radius, ite_eq_left hi]
      calc
        nonnegativeJetScale u (I.value i) ≤
            (A * ε) * nonnegativeJetScale u (I.value i) :=
          by simpa only [one_mul] using mul_le_mul_of_nonneg_right hAε hRi
        _ = A * (ε * nonnegativeJetScale u (I.value i)) := by ring
  · intro i
    simpa [cutoff, bump, I] using hcont i
  · intro i
    by_cases hi : i ∈ I.active
    · have hsupp := support_squareNormalizedFamily_subset bump i
      have hraw := support_activeIntrinsicRawBump hε hcenter i
      rw [hraw] at hsupp
      simpa [cutoff, radius, activeScaledBall, hi] using hsupp
    · have hzero : cutoff i = 0 := by
        funext x
        simp [cutoff, squareNormalizedFamily, bump, activeIntrinsicRawBump, hi]
      rw [hzero]
      simp [Function.support]
  · intro x hx
    have hL2 : 2 ≤ L := by linarith
    have hpoint : ∀ y, Set.Finite {i | bump i y ≠ 0} := by
      exact activeIntrinsicRawBump_pointFinite hL2 hε hcenter hoverlapL
    obtain ⟨i, hi, hone⟩ := exists_selectedIntrinsicRawBump_eq_one hε s hdis hcover hx
    have hone' : bump i x = 1 := by simpa [bump, I] using hone
    have hsum : 0 < ∑' k, bump k x ^ 2 :=
      zero_lt_one.trans_le (one_le_raw_square_tsum bump hpoint x i hone')
    simpa [cutoff] using squareNormalizedFamily_square_tsum bump hpoint x hsum
  · intro x t
    have hbound := hoverlapD x t
    have hrewrite : {i | i ∈ t ∧ i ∈ I.active ∧
        x ∈ Metric.ball (I.value i) (D * radius i)} =
        {i | i ∈ t ∧ i ∈ I.active ∧
          x ∈ Metric.ball (I.value i)
            (D * (ε * nonnegativeJetScale u (I.value i)))} := by
      ext i
      by_cases hi : i ∈ I.active <;> simp [radius, hi]
    rw [hrewrite]
    exact hbound.trans (le_max_left _ _)
  · intro i j hj x
    by_cases hi : i ∈ I.active
    · have hb := hderiv' i hi j hj x
      simpa only [cutoff, bump, I, radius, ite_eq_left hi] using
        hb.trans (show Aderiv ≤ A from le_max_left _ _)
    · have hzero : cutoff i = 0 := by
        funext y
        simp [cutoff, squareNormalizedFamily, bump, activeIntrinsicRawBump, hi]
      rw [hzero]
      change ‖iteratedFDeriv ℝ j (fun _ : Fin n → ℝ => (0 : ℝ)) x‖ * radius i ^ j ≤ A
      rw [iteratedFDeriv_fun_zero]
      simpa using hA0
  · intro i hi
    simp only [radius, ite_eq_left hi]
    exact mul_le_mul_of_nonneg_right hε_le_σ
      (nonnegativeJetScale_nonneg u (I.value i))

/-- Uniform nonnegative jet bounds supply fine quantitative covers at every prescribed
fraction of the intrinsic scale. -/
theorem uniformFineScaleCover_of_jetBounds {n : ℕ}
    (hjets : HasUniformNonnegativeJetBounds n) : HasUniformFineScaleCover n := by
  exact fineQuantitativeSquarePartition_of_slowVariation
    (intrinsicScale_slowVariation_of_jetBounds hjets)

end QuarticConvergence
end OptimalConvergenceRates

end
