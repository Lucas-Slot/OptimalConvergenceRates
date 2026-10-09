/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/PositiveValueCutoff.lean

  A concrete geometric cutoff for the positive-value branch.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.PositiveValuePatch
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FineScaleCover

open Set
open scoped Topology

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence

/-- The outer radius of the positive-value cutoff. -/
def positiveValueCutoffRadius (C delta : ℝ) : ℝ :=
  positiveValuePersistenceRadius delta (4 * (C + 1))

/-- The inner radius of the positive-value cutoff.  The factor two is exactly the ratio between
the inner and outer radii of `unitScaleBump`. -/
def positiveValueCutoffInnerRadius (C delta : ℝ) : ℝ :=
  positiveValueCutoffRadius C delta / 2

/-- The fixed radial cutoff used in the positive-value alternative.  It is one on the closed
half-radius ball and has support exactly the open persistence ball. -/
def positiveValueCutoff (n : ℕ) (C delta : ℝ) : (Fin n → ℝ) → ℝ :=
  rescaledUnitBump 0 (positiveValueCutoffInnerRadius C delta)

theorem positiveValueCutoffRadius_pos {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta) :
    0 < positiveValueCutoffRadius C delta := by
  apply positiveValuePersistenceRadius_pos hdelta
  positivity

theorem positiveValueCutoffRadius_le_one (C delta : ℝ) :
    positiveValueCutoffRadius C delta ≤ 1 :=
  positiveValuePersistenceRadius_le_one _ _

theorem positiveValueCutoffInnerRadius_pos {C delta : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta) :
    0 < positiveValueCutoffInnerRadius C delta := by
  exact half_pos (positiveValueCutoffRadius_pos hC hdelta)

theorem positiveValueCutoffInnerRadius_le_one {C delta : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta) :
    positiveValueCutoffInnerRadius C delta ≤ 1 := by
  have hpos := positiveValueCutoffRadius_pos hC hdelta
  have hle := positiveValueCutoffRadius_le_one C delta
  dsimp [positiveValueCutoffInnerRadius]
  linarith

theorem two_mul_positiveValueCutoffInnerRadius (C delta : ℝ) :
    2 * positiveValueCutoffInnerRadius C delta = positiveValueCutoffRadius C delta := by
  dsimp [positiveValueCutoffInnerRadius]
  ring

theorem positiveValueCutoff_contDiff (n : ℕ) (C delta : ℝ) :
    ContDiff ℝ 6 (positiveValueCutoff n C delta) := by
  exact rescaledUnitBump_contDiff 0 (positiveValueCutoffInnerRadius C delta)

theorem positiveValueCutoff_compactSupport (n : ℕ) {C delta : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta) :
    HasCompactSupport (positiveValueCutoff n C delta) := by
  let r := positiveValueCutoffInnerRadius C delta
  have hr : 0 < r := positiveValueCutoffInnerRadius_pos hC hdelta
  rw [positiveValueCutoff, ← centeredScaleBump_eq_rescaledUnitBump (0 : Fin n → ℝ) hr]
  exact (centeredScaleBump (0 : Fin n → ℝ) r hr).hasCompactSupport

/-- The nonzero locus is exactly the explicit persistence ball, including in dimension zero. -/
theorem support_positiveValueCutoff (n : ℕ) {C delta : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta) :
    Function.support (positiveValueCutoff n C delta) =
      Metric.ball 0 (positiveValueCutoffRadius C delta) := by
  rw [positiveValueCutoff, support_rescaledUnitBump 0
    (positiveValueCutoffInnerRadius_pos hC hdelta),
    two_mul_positiveValueCutoffInnerRadius]

theorem positiveValueCutoff_eq_one (n : ℕ) {C delta : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta) {z : Fin n → ℝ}
    (hz : z ∈ Metric.closedBall 0 (positiveValueCutoffInnerRadius C delta)) :
    positiveValueCutoff n C delta z = 1 := by
  exact rescaledUnitBump_eq_one 0 (positiveValueCutoffInnerRadius_pos hC hdelta) hz

theorem positiveValueCutoff_mem_Icc (n : ℕ) (C delta : ℝ) (z : Fin n → ℝ) :
    positiveValueCutoff n C delta z ∈ Set.Icc (0 : ℝ) 1 := by
  exact rescaledUnitBump_mem_Icc 0 (positiveValueCutoffInnerRadius C delta) z

/-- Every nonzero cutoff value lies where the positive patch is bounded below. -/
theorem norm_lt_positiveValueCutoffRadius_of_ne_zero (n : ℕ) {C delta : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta) {z : Fin n → ℝ}
    (hz : positiveValueCutoff n C delta z ≠ 0) :
    ‖z‖ < positiveValueCutoffRadius C delta := by
  have hzSupport : z ∈ Function.support (positiveValueCutoff n C delta) := hz
  rw [support_positiveValueCutoff n hC hdelta, Metric.mem_ball, dist_zero_right] at hzSupport
  exact hzSupport

theorem support_positiveValueCutoff_subset_closedBall_one (n : ℕ) {C delta : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta) :
    Function.support (positiveValueCutoff n C delta) ⊆ Metric.closedBall 0 1 := by
  rw [support_positiveValueCutoff n hC hdelta]
  exact (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (positiveValueCutoffRadius_le_one C delta)))

/-- The fixed profile supplies scale-invariant `C⁶` bounds for the cutoff.  For each ambient
dimension the constant is independent of `C`, `delta`, and hence of the persistence radius. -/
theorem exists_positiveValueCutoff_scaled_deriv_bound (n : ℕ) {C delta : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ j, j ≤ 6 → ∀ z,
      ‖iteratedFDeriv ℝ j (positiveValueCutoff n C delta) z‖ *
          positiveValueCutoffInnerRadius C delta ^ j ≤ A := by
  obtain ⟨A, hA, hprofile⟩ := unitScaleBump_uniform_deriv_bound n
  refine ⟨A, hA, ?_⟩
  intro j hj z
  exact rescaledUnitBump_scaled_deriv_bound hprofile 0
    (positiveValueCutoffInnerRadius_pos hC hdelta) j hj z

/-- A common unscaled `C⁴` bound for the concrete cutoff. -/
theorem exists_positiveValueCutoff_deriv_bound (n : ℕ) {C delta : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ Mcut : ℝ, 1 ≤ Mcut ∧ ∀ z j, j ≤ 4 →
      ‖iteratedFDeriv ℝ j (positiveValueCutoff n C delta) z‖ ≤ Mcut := by
  obtain ⟨A, hA, hscaled⟩ := exists_positiveValueCutoff_scaled_deriv_bound n hC hdelta
  let r := positiveValueCutoffInnerRadius C delta
  have hr : 0 < r := positiveValueCutoffInnerRadius_pos hC hdelta
  have hrOne : r ≤ 1 := positiveValueCutoffInnerRadius_le_one hC hdelta
  have hinv : 1 ≤ r⁻¹ := (one_le_inv₀ hr).2 hrOne
  let Mcut := A * r⁻¹ ^ 4
  have hinvPow : 1 ≤ r⁻¹ ^ 4 := by
    simpa only [pow_zero] using pow_le_pow_right₀ hinv (Nat.zero_le 4)
  have hMcut : 1 ≤ Mcut := by
    dsimp [Mcut]
    simpa only [one_mul] using
      mul_le_mul hA hinvPow (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hA)
  refine ⟨Mcut, hMcut, ?_⟩
  intro z j hj
  have hs := hscaled j (hj.trans (by norm_num)) z
  have hdiv : ‖iteratedFDeriv ℝ j (positiveValueCutoff n C delta) z‖ ≤
      A / r ^ j := (le_div_iff₀ (pow_pos hr j)).2 hs
  calc
    ‖iteratedFDeriv ℝ j (positiveValueCutoff n C delta) z‖ ≤ A / r ^ j := hdiv
    _ = A * r⁻¹ ^ j := by rw [div_eq_mul_inv, inv_pow]
    _ ≤ A * r⁻¹ ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hinv hj) (zero_le_one.trans hA)
    _ = Mcut := rfl

/-- The concrete positive cutoff makes the regularized root an exact square globally. -/
theorem positiveValueCutoff_root_sq
    {n : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c) {delta : ℝ} (hdelta : 0 < delta)
    (hcenter : delta ≤ intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0)
    (z : Fin n → ℝ) :
    positiveValuePatchRoot (delta / 2) (positiveValueCutoff n C delta)
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) z ^ 2 =
      positiveValueCutoff n C delta z ^ 2 *
        intrinsicRescaledPatch u c (nonnegativeJetScale u c) z := by
  have hC : 0 ≤ C := hcontrol.constant_nonneg
  apply intrinsic_positiveValuePatchRoot_sq hu hcontrol c hR hdelta hcenter
  intro w hw
  exact (norm_lt_positiveValueCutoffRadius_of_ne_zero n hC hdelta hw).le

/-- The complete analytic package needed for the positive branch: a globally bounded compactly
supported `C⁴` root, uniform over the normalized input and its center. -/
theorem exists_positiveValueCutoff_root_global_deriv_bound
    (n : ℕ) {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ Aroot : ℝ, 0 ≤ Aroot ∧
      ∀ {u : (Fin n → ℝ) → ℝ}, NormalizedNonnegativeC6 u →
        NonnegativeJetControl u C → ∀ (c : Fin n → ℝ),
          0 < nonnegativeJetScale u c → ∀ z j, j ≤ 4 →
            ‖iteratedFDeriv ℝ j
              (positiveValuePatchRoot (delta / 2) (positiveValueCutoff n C delta)
                (intrinsicRescaledPatch u c (nonnegativeJetScale u c))) z‖ ≤ Aroot := by
  obtain ⟨Mcut, hMcut, hcutoffBound⟩ :=
    exists_positiveValueCutoff_deriv_bound n hC hdelta
  obtain ⟨Aroot, hAroot, hroot⟩ :=
    exists_uniform_intrinsicPositiveValuePatchRoot_global_deriv_bound
      C delta Mcut hC hdelta (zero_le_one.trans hMcut)
  refine ⟨Aroot, hAroot, ?_⟩
  intro u hu hcontrol c hR z j hj
  exact hroot hu hcontrol ((positiveValueCutoff_contDiff n C delta).of_le (by norm_num))
    c hR (support_positiveValueCutoff_subset_closedBall_one n hC hdelta)
    hcutoffBound z j hj

/-- Atom-scale form of the preceding global bound.  The right side is exactly the normalization
used by `EuclideanAtomFamily.scaled_jets` when the normalized positive root is assigned the
persistence-radius ball. -/
theorem exists_positiveValueCutoff_root_atom_bound
    (n : ℕ) {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ Katom : ℝ, 0 < Katom ∧
      ∀ {u : (Fin n → ℝ) → ℝ}, NormalizedNonnegativeC6 u →
        NonnegativeJetControl u C → ∀ (c : Fin n → ℝ),
          0 < nonnegativeJetScale u c → ∀ z j, j ≤ 4 →
            ‖iteratedFDeriv ℝ j
                (positiveValuePatchRoot (delta / 2) (positiveValueCutoff n C delta)
                  (intrinsicRescaledPatch u c (nonnegativeJetScale u c))) z‖ *
                positiveValueCutoffRadius C delta ^ j ≤
              Katom * positiveValueCutoffRadius C delta ^ 2 := by
  obtain ⟨Aroot, hAroot, hroot⟩ :=
    exists_positiveValueCutoff_root_global_deriv_bound n hC hdelta
  let rho := positiveValueCutoffRadius C delta
  have hrho : 0 < rho := positiveValueCutoffRadius_pos hC hdelta
  have hrhoOne : rho ≤ 1 := positiveValueCutoffRadius_le_one C delta
  let A := max 1 Aroot
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  let Katom := A / rho ^ 2
  have hKatom : 0 < Katom := div_pos hA (pow_pos hrho 2)
  refine ⟨Katom, hKatom, ?_⟩
  intro u hu hcontrol c hR z j hj
  have hpow : rho ^ j ≤ 1 := by
    simpa only [one_pow] using pow_le_one₀ (n := j) hrho.le hrhoOne
  have hnorm : ‖iteratedFDeriv ℝ j
      (positiveValuePatchRoot (delta / 2) (positiveValueCutoff n C delta)
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c))) z‖ ≤ A :=
    (hroot hu hcontrol c hR z j hj).trans (le_max_right _ _)
  calc
    ‖iteratedFDeriv ℝ j
          (positiveValuePatchRoot (delta / 2) (positiveValueCutoff n C delta)
            (intrinsicRescaledPatch u c (nonnegativeJetScale u c))) z‖ * rho ^ j
        ≤ A * 1 := mul_le_mul hnorm hpow (pow_nonneg hrho.le j) hA.le
    _ = A := mul_one A
    _ = Katom * rho ^ 2 := by
      dsimp [Katom]
      field_simp

namespace FineQuantitativeScaleCover

/-- A fine-cover cutoff written in the intrinsic coordinates of its own center. -/
def intrinsicCutoff {n : ℕ} {u : (Fin n → ℝ) → ℝ} {D sigma A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B) (i : ℕ) :
    (Fin n → ℝ) → ℝ :=
  fun z ↦ cover.cutoff i
    (cover.center i + nonnegativeJetScale u (cover.center i) • z)

theorem intrinsicCutoff_contDiff {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D sigma A : ℝ} {B : ℕ} (cover : FineQuantitativeScaleCover u D sigma A B)
    (i : ℕ) : ContDiff ℝ 6 (cover.intrinsicCutoff i) := by
  exact (cover.cutoff_contDiff i).comp (by fun_prop)

theorem intrinsicCutoff_support_subset {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D sigma A : ℝ} {B : ℕ} (cover : FineQuantitativeScaleCover u D sigma A B)
    {i : ℕ} (hi : i ∈ cover.active) :
    Function.support (cover.intrinsicCutoff i) ⊆ Metric.ball 0 (2 * sigma) := by
  intro z hz
  let R := nonnegativeJetScale u (cover.center i)
  let r := cover.radius i
  have hr : 0 < r := cover.radius_pos i hi
  have hrR : r ≤ R := (cover.radius_comparable i hi).1
  have hR : 0 < R := hr.trans_le hrR
  have hcut : cover.center i + R • z ∈ Function.support (cover.cutoff i) := hz
  have hball := cover.cutoff_support i hcut
  have hdist : R * ‖z‖ < 2 * r := by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hR.le] using hball
  have hratio : ‖z‖ < (2 * r) / R := by
    rw [lt_div_iff₀ hR]
    simpa [mul_comm] using hdist
  have hrFine : r ≤ sigma * R := cover.radius_le_fine i hi
  have hratioFine : (2 * r) / R ≤ 2 * sigma := by
    rw [div_le_iff₀ hR]
    nlinarith
  have hzNorm : ‖z‖ < 2 * sigma := hratio.trans_le hratioFine
  simpa only [Metric.mem_ball, dist_zero_right] using hzNorm

theorem intrinsicCutoff_compactSupport {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D sigma A : ℝ} {B : ℕ} (cover : FineQuantitativeScaleCover u D sigma A B)
    {i : ℕ} (hi : i ∈ cover.active) : HasCompactSupport (cover.intrinsicCutoff i) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin n → ℝ) (2 * sigma))
  exact (cover.intrinsicCutoff_support_subset hi).trans Metric.ball_subset_closedBall

theorem intrinsicCutoff_ne_zero_norm_lt {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D sigma A : ℝ} {B : ℕ} (cover : FineQuantitativeScaleCover u D sigma A B)
    {i : ℕ} (hi : i ∈ cover.active) {z : Fin n → ℝ}
    (hz : cover.intrinsicCutoff i z ≠ 0) : ‖z‖ < 2 * sigma := by
  have := cover.intrinsicCutoff_support_subset hi hz
  simpa only [Metric.mem_ball, dist_zero_right] using this


/-- The derivative of an intrinsic pullback gains the expected power of the parent scale. -/
theorem norm_iteratedFDeriv_intrinsicCutoff_le {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {D sigma A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B) {i : ℕ}
    (hi : i ∈ cover.active) (j : ℕ) (hj : j ≤ 6) (z : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j (cover.intrinsicCutoff i) z‖ ≤
      ‖iteratedFDeriv ℝ j (cover.cutoff i)
          (cover.center i + nonnegativeJetScale u (cover.center i) • z)‖ *
        nonnegativeJetScale u (cover.center i) ^ j := by
  let R := nonnegativeJetScale u (cover.center i)
  let shifted : (Fin n → ℝ) → ℝ := fun w ↦ cover.cutoff i (cover.center i + w)
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    R • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hr : 0 < cover.radius i := cover.radius_pos i hi
  have hR : 0 < R := hr.trans_le (cover.radius_comparable i hi).1
  have hshift : ContDiff ℝ 6 shifted := (cover.cutoff_contDiff i).comp (by fun_prop)
  have hfun : cover.intrinsicCutoff i = shifted ∘ L := rfl
  have hcomp : iteratedFDeriv ℝ j (shifted ∘ L) z =
      (iteratedFDeriv ℝ j shifted (L z)).compContinuousLinearMap (fun _ ↦ L) :=
    L.iteratedFDeriv_comp_right hshift z (by exact_mod_cast hj)
  have htranslate : iteratedFDeriv ℝ j shifted (L z) =
      iteratedFDeriv ℝ j (cover.cutoff i) (cover.center i + L z) := by
    simpa [shifted] using
      iteratedFDeriv_comp_add_left (𝕜 := ℝ) j (cover.center i) (L z)
  have hnormL : ‖L‖ ≤ R := by
    dsimp only [L]
    calc
      ‖R • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
          ‖R‖ * ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ :=
        norm_smul_le R (ContinuousLinearMap.id ℝ (Fin n → ℝ))
      _ ≤ R * 1 := by
        rw [Real.norm_of_nonneg hR.le]
        gcongr
        exact ContinuousLinearMap.norm_id_le
      _ = R := mul_one R
  have hprod : (∏ _ : Fin j, ‖L‖) ≤ R ^ j := by
    calc
      (∏ _ : Fin j, ‖L‖) ≤ ∏ _ : Fin j, R :=
        Finset.prod_le_prod (fun _ _ ↦ norm_nonneg L) (fun _ _ ↦ hnormL)
      _ = R ^ j := by simp
  rw [hfun, hcomp, htranslate]
  calc
    ‖(iteratedFDeriv ℝ j (cover.cutoff i) (cover.center i + L z)).compContinuousLinearMap
        (fun _ ↦ L)‖ ≤
      ‖iteratedFDeriv ℝ j (cover.cutoff i) (cover.center i + L z)‖ *
        ∏ _ : Fin j, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j (cover.cutoff i) (cover.center i + L z)‖ * R ^ j :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j (cover.cutoff i)
          (cover.center i + nonnegativeJetScale u (cover.center i) • z)‖ *
        nonnegativeJetScale u (cover.center i) ^ j := by
      simp only [L, R, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]

/-- Fine-cover radius comparability turns the scaled cover estimate into a global intrinsic
derivative bound independent of the ambient dimension and the active index. -/
theorem intrinsicCutoff_uniform_deriv_bound {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {D sigma A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B) (hA : 1 ≤ A)
    {i : ℕ} (hi : i ∈ cover.active) (z : Fin n → ℝ) (j : ℕ) (hj : j ≤ 6) :
    ‖iteratedFDeriv ℝ j (cover.intrinsicCutoff i) z‖ ≤ A ^ 7 := by
  let R := nonnegativeJetScale u (cover.center i)
  let r := cover.radius i
  have hr : 0 < r := cover.radius_pos i hi
  have hR : 0 < R := hr.trans_le (cover.radius_comparable i hi).1
  have hcompare : R ≤ A * r := (cover.radius_comparable i hi).2
  have hRpow : R ^ j ≤ (A * r) ^ j := pow_le_pow_left₀ hR.le hcompare j
  have hpull := cover.norm_iteratedFDeriv_intrinsicCutoff_le hi j hj z
  calc
    ‖iteratedFDeriv ℝ j (cover.intrinsicCutoff i) z‖ ≤
        ‖iteratedFDeriv ℝ j (cover.cutoff i) (cover.center i + R • z)‖ * R ^ j :=
      hpull
    _ ≤ ‖iteratedFDeriv ℝ j (cover.cutoff i) (cover.center i + R • z)‖ *
        (A * r) ^ j := mul_le_mul_of_nonneg_left hRpow (norm_nonneg _)
    _ = A ^ j *
        (‖iteratedFDeriv ℝ j (cover.cutoff i) (cover.center i + R • z)‖ * r ^ j) := by
      rw [mul_pow]
      ring
    _ ≤ A ^ j * A := by
      exact mul_le_mul_of_nonneg_left (cover.scaled_cutoff i j hj _)
        (pow_nonneg (zero_le_one.trans hA) j)
    _ = A ^ (j + 1) := by rw [pow_succ]
    _ ≤ A ^ 7 := pow_le_pow_right₀ hA (Nat.succ_le_succ hj)

/-- The natural radius of a cover cutoff in intrinsic coordinates.  After undoing the parent
normalization it becomes exactly twice the physical cover radius. -/
def intrinsicCutoffRadius {n : ℕ} {u : (Fin n → ℝ) → ℝ} {D sigma A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B) (i : ℕ) : ℝ :=
  2 * cover.radius i / nonnegativeJetScale u (cover.center i)

theorem intrinsicCutoffRadius_pos {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D sigma A : ℝ} {B : ℕ} (cover : FineQuantitativeScaleCover u D sigma A B)
    {i : ℕ} (hi : i ∈ cover.active) : 0 < cover.intrinsicCutoffRadius i := by
  have hr : 0 < cover.radius i := cover.radius_pos i hi
  have hR : 0 < nonnegativeJetScale u (cover.center i) :=
    hr.trans_le (cover.radius_comparable i hi).1
  exact div_pos (mul_pos (by norm_num) hr) hR

theorem intrinsicCutoffRadius_le_two_mul {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D sigma A : ℝ} {B : ℕ} (cover : FineQuantitativeScaleCover u D sigma A B)
    {i : ℕ} (hi : i ∈ cover.active) : cover.intrinsicCutoffRadius i ≤ 2 * sigma := by
  have hr : 0 < cover.radius i := cover.radius_pos i hi
  have hR : 0 < nonnegativeJetScale u (cover.center i) :=
    hr.trans_le (cover.radius_comparable i hi).1
  rw [intrinsicCutoffRadius, div_le_iff₀ hR]
  nlinarith [cover.radius_le_fine i hi]

theorem intrinsicCutoff_support_subset_radius {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {D sigma A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B) {i : ℕ}
    (hi : i ∈ cover.active) :
    Function.support (cover.intrinsicCutoff i) ⊆
      Metric.ball 0 (cover.intrinsicCutoffRadius i) := by
  intro z hz
  let R := nonnegativeJetScale u (cover.center i)
  let r := cover.radius i
  have hr : 0 < r := cover.radius_pos i hi
  have hR : 0 < R := hr.trans_le (cover.radius_comparable i hi).1
  have hcut : cover.center i + R • z ∈ Function.support (cover.cutoff i) := hz
  have hball := cover.cutoff_support i hcut
  have hdist : R * ‖z‖ < 2 * r := by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hR.le] using hball
  rw [Metric.mem_ball, dist_zero_right, intrinsicCutoffRadius]
  rw [lt_div_iff₀ hR]
  simpa [R, r, mul_comm] using hdist

theorem intrinsicCutoff_support_subset_persistenceBall {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {D sigma A C delta : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B) {i : ℕ}
    (hi : i ∈ cover.active)
    (hsigma : 2 * sigma ≤ positiveValueCutoffRadius C delta) :
    Function.support (cover.intrinsicCutoff i) ⊆
      Metric.closedBall 0 (positiveValueCutoffRadius C delta) := by
  intro z hz
  have hzBall := cover.intrinsicCutoff_support_subset hi hz
  rw [Metric.mem_ball, dist_zero_right] at hzBall
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hzBall.le.trans hsigma

theorem intrinsicCutoff_support_subset_closedBall_one {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {D sigma A C delta : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B) {i : ℕ}
    (hi : i ∈ cover.active)
    (hsigma : 2 * sigma ≤ positiveValueCutoffRadius C delta) :
    Function.support (cover.intrinsicCutoff i) ⊆ Metric.closedBall 0 1 :=
  (cover.intrinsicCutoff_support_subset_persistenceBall hi hsigma).trans
    (Metric.closedBall_subset_closedBall (positiveValueCutoffRadius_le_one C delta))

/-- The positive-value root for an actual fine-cover summand, in intrinsic parent coordinates. -/
def positiveRoot {n : ℕ} {u : (Fin n → ℝ) → ℝ} {D sigma A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B) (i : ℕ) (delta : ℝ) :
    (Fin n → ℝ) → ℝ :=
  positiveValuePatchRoot (delta / 2) (cover.intrinsicCutoff i)
    (intrinsicRescaledPatch u (cover.center i)
      (nonnegativeJetScale u (cover.center i)))

theorem positiveRoot_contDiff {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D sigma A : ℝ} {B : ℕ} (cover : FineQuantitativeScaleCover u D sigma A B)
    (hu : NormalizedNonnegativeC6 u) (i : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ContDiff ℝ 4 (cover.positiveRoot i delta) := by
  exact positiveValuePatchRoot_contDiff (half_pos hdelta)
    ((cover.intrinsicCutoff_contDiff i).of_le (by norm_num))
    ((intrinsicRescaledPatch_contDiff hu.contDiff (cover.center i)
      (nonnegativeJetScale u (cover.center i))).of_le (by norm_num))

theorem positiveRoot_compactSupport {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D sigma A : ℝ} {B : ℕ} (cover : FineQuantitativeScaleCover u D sigma A B)
    {i : ℕ} (hi : i ∈ cover.active) (delta : ℝ) :
    HasCompactSupport (cover.positiveRoot i delta) := by
  exact positiveValuePatchRoot_compactSupport (cover.intrinsicCutoff_compactSupport hi)

theorem support_positiveRoot_subset {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D sigma A : ℝ} {B : ℕ} (cover : FineQuantitativeScaleCover u D sigma A B)
    {i : ℕ} (hi : i ∈ cover.active) (delta : ℝ) :
    Function.support (cover.positiveRoot i delta) ⊆
      Metric.ball 0 (cover.intrinsicCutoffRadius i) := by
  exact (support_positiveValuePatchRoot_subset _ _ _).trans
    (cover.intrinsicCutoff_support_subset_radius hi)

/-- In the positive alternative, the fine-cover parent summand is one exact global square. -/
theorem positiveRoot_sq {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D sigma A C : ℝ} {B : ℕ} (cover : FineQuantitativeScaleCover u D sigma A B)
    (hu : NormalizedNonnegativeC6 u) (hcontrol : NonnegativeJetControl u C)
    {i : ℕ} (hi : i ∈ cover.active) {delta : ℝ} (hdelta : 0 < delta)
    (hcenter : delta ≤ intrinsicRescaledPatch u (cover.center i)
      (nonnegativeJetScale u (cover.center i)) 0)
    (hsigma : 2 * sigma ≤ positiveValueCutoffRadius C delta) (z : Fin n → ℝ) :
    cover.positiveRoot i delta z ^ 2 = cover.intrinsicCutoff i z ^ 2 *
      intrinsicRescaledPatch u (cover.center i)
        (nonnegativeJetScale u (cover.center i)) z := by
  have hR : 0 < nonnegativeJetScale u (cover.center i) :=
    (cover.radius_pos i hi).trans_le (cover.radius_comparable i hi).1
  apply intrinsic_positiveValuePatchRoot_sq hu hcontrol (cover.center i) hR hdelta hcenter
  intro w hw
  have hmem := cover.intrinsicCutoff_support_subset_persistenceBall hi hsigma hw
  simpa only [Metric.mem_closedBall, dist_zero_right] using hmem

/-- A single constant controls every positive fine-cover root in every ambient dimension.  The
only cutoff constant entering the bound is the scale-cover constant `A`; intrinsic rescaling
removes both the parent radius and the fine parameter. -/
theorem exists_positiveRoot_uniform_global_deriv_bound
    (C delta A : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) (hA : 1 ≤ A) :
    ∃ Aroot : ℝ, 0 ≤ Aroot ∧
      ∀ {n : ℕ} {u : (Fin n → ℝ) → ℝ} {D sigma : ℝ} {B : ℕ}
        (cover : FineQuantitativeScaleCover u D sigma A B),
        NormalizedNonnegativeC6 u → NonnegativeJetControl u C →
        ∀ {i : ℕ}, i ∈ cover.active →
          2 * sigma ≤ positiveValueCutoffRadius C delta →
          ∀ z j, j ≤ 4 →
            ‖iteratedFDeriv ℝ j (cover.positiveRoot i delta) z‖ ≤ Aroot := by
  obtain ⟨Aroot, hAroot, hroot⟩ :=
    exists_uniform_intrinsicPositiveValuePatchRoot_global_deriv_bound
      C delta (A ^ 7) hC hdelta (pow_nonneg (zero_le_one.trans hA) 7)
  refine ⟨Aroot, hAroot, ?_⟩
  intro n u D sigma B cover hu hcontrol i hi hsigma z j hj
  have hR : 0 < nonnegativeJetScale u (cover.center i) :=
    (cover.radius_pos i hi).trans_le (cover.radius_comparable i hi).1
  simpa only [positiveRoot] using
    hroot hu hcontrol ((cover.intrinsicCutoff_contDiff i).of_le (by norm_num))
      (cover.center i) hR (cover.intrinsicCutoff_support_subset_closedBall_one hi hsigma)
      (fun w q hq ↦ cover.intrinsicCutoff_uniform_deriv_bound hA hi w q
        (hq.trans (by norm_num))) z j hj

/-- Uniform atom normalization for the positive parent root at its natural intrinsic radius.
This is the exact inequality expected by `EuclideanAtomFamily.scaled_jets`; importantly, its
constant is independent of dimension, the parent index, and the parent scale. -/
theorem exists_positiveRoot_uniform_atom_bound
    (C delta A : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) (hA : 1 ≤ A) :
    ∃ Katom : ℝ, 0 < Katom ∧
      ∀ {n : ℕ} {u : (Fin n → ℝ) → ℝ} {D sigma : ℝ} {B : ℕ}
        (cover : FineQuantitativeScaleCover u D sigma A B),
        NormalizedNonnegativeC6 u → NonnegativeJetControl u C →
        ∀ {i : ℕ}, i ∈ cover.active →
          2 * sigma ≤ positiveValueCutoffRadius C delta →
          ∀ z j, j ≤ 4 →
            ‖iteratedFDeriv ℝ j (cover.positiveRoot i delta) z‖ *
                cover.intrinsicCutoffRadius i ^ j ≤
              Katom * cover.intrinsicCutoffRadius i ^ 2 := by
  obtain ⟨Aroot, hAroot, hroot⟩ :=
    exists_positiveRoot_uniform_global_deriv_bound C delta A hC hdelta hA
  let Aroot' := max 1 Aroot
  have hAroot' : 0 < Aroot' := zero_lt_one.trans_le (le_max_left _ _)
  let Katom := Aroot' * A ^ 2
  have hKatom : 0 < Katom := mul_pos hAroot' (pow_pos (zero_lt_one.trans_le hA) 2)
  refine ⟨Katom, hKatom, ?_⟩
  intro n u D sigma B cover hu hcontrol i hi hsigma z j hj
  let R := nonnegativeJetScale u (cover.center i)
  let r := cover.radius i
  let s := cover.intrinsicCutoffRadius i
  have hr : 0 < r := cover.radius_pos i hi
  have hR : 0 < R := hr.trans_le (cover.radius_comparable i hi).1
  have hs : 0 < s := cover.intrinsicCutoffRadius_pos hi
  have hsOne : s ≤ 1 := by
    calc
      s ≤ 2 * sigma := cover.intrinsicCutoffRadius_le_two_mul hi
      _ ≤ positiveValueCutoffRadius C delta := hsigma
      _ ≤ 1 := positiveValueCutoffRadius_le_one C delta
  have hbase : 1 ≤ A * r / R := by
    rw [le_div_iff₀ hR]
    simpa only [one_mul] using (cover.radius_comparable i hi).2
  have hdouble : A * r / R ≤ A * (2 * r) / R := by
    apply div_le_div_of_nonneg_right _ hR.le
    exact mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans hA)
  have hAs : 1 ≤ A * s := by
    calc
      1 ≤ A * r / R := hbase
      _ ≤ A * (2 * r) / R := hdouble
      _ = A * s := by
        dsimp [s, intrinsicCutoffRadius, r, R]
        ring
  have hAsSq : 1 ≤ A ^ 2 * s ^ 2 := by
    calc
      1 = 1 ^ 2 := by norm_num
      _ ≤ (A * s) ^ 2 := pow_le_pow_left₀ zero_le_one hAs 2
      _ = A ^ 2 * s ^ 2 := mul_pow A s 2
  have hsPow : s ^ j ≤ 1 := by
    simpa only [one_pow] using pow_le_one₀ (n := j) hs.le hsOne
  have hnorm : ‖iteratedFDeriv ℝ j (cover.positiveRoot i delta) z‖ ≤ Aroot' :=
    (hroot cover hu hcontrol hi hsigma z j hj).trans (le_max_right _ _)
  calc
    ‖iteratedFDeriv ℝ j (cover.positiveRoot i delta) z‖ * s ^ j ≤
        Aroot' * 1 := mul_le_mul hnorm hsPow (pow_nonneg hs.le j) hAroot'.le
    _ = Aroot' := mul_one Aroot'
    _ ≤ Aroot' * (A ^ 2 * s ^ 2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hAsSq hAroot'.le
    _ = Katom * s ^ 2 := by
      dsimp [Katom]
      ring

/-- An inactive fine-cover cutoff remains identically zero after intrinsic pullback. -/
theorem intrinsicCutoff_eq_zero_of_not_active {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {D sigma A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B) {i : ℕ}
    (hi : i ∉ cover.active) : cover.intrinsicCutoff i = 0 := by
  funext z
  simp [intrinsicCutoff, cover.cutoff_eq_zero_of_not_active i hi]

/-- Consequently the positive root attached to an inactive cover index is identically zero. -/
theorem positiveRoot_eq_zero_of_not_active {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {D sigma A : ℝ} {B : ℕ}
    (cover : FineQuantitativeScaleCover u D sigma A B) {i : ℕ}
    (hi : i ∉ cover.active) (delta : ℝ) : cover.positiveRoot i delta = 0 := by
  funext z
  simp [positiveRoot, intrinsicCutoff_eq_zero_of_not_active cover hi,
    positiveValuePatchRoot]
end FineQuantitativeScaleCover
end OptimalConvergenceRates.QuarticConvergence

end
