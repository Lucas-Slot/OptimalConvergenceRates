/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/IntervalPartition.lean

  A scaled smooth square partition of the real line for the normal-coordinate split.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ScaleCover
import Mathlib.Data.Int.Interval

open Finset Set
open scoped BigOperators Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The integer represented by a natural-number interval-partition index. -/
def intervalIndexInteger (i : ℕ) : ℤ := Equiv.intEquivNat.symm i

/-- The integer-lattice center assigned to an index at physical scale `r`. -/
def intervalPartitionCenter (r : ℝ) (i : ℕ) : ℝ :=
  r * (intervalIndexInteger i : ℝ)

theorem intervalIndexInteger_injective : Function.Injective intervalIndexInteger :=
  Equiv.intEquivNat.symm.injective

/-- Distinct integer-lattice centers are separated by at least one at unit scale. -/
theorem one_le_dist_intervalIndexInteger {i k : ℕ} (hik : i ≠ k) :
    1 ≤ dist (intervalIndexInteger i : ℝ) (intervalIndexInteger k : ℝ) := by
  have hne : intervalIndexInteger i - intervalIndexInteger k ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hik (intervalIndexInteger_injective h)
  have habs : (1 : ℤ) ≤ |intervalIndexInteger i - intervalIndexInteger k| :=
    Int.one_le_abs hne
  rw [Real.dist_eq, ← Int.cast_sub, ← Int.cast_abs]
  exact_mod_cast habs

/-- At scale `r > 0`, distinct assigned centers are separated by at least `r`. -/
theorem intervalPartitionCenter_separated {r : ℝ} (hr : 0 < r) {i k : ℕ}
    (hik : i ≠ k) :
    r ≤ dist (intervalPartitionCenter r i) (intervalPartitionCenter r k) := by
  rw [intervalPartitionCenter, intervalPartitionCenter, Real.dist_eq]
  have hunit := one_le_dist_intervalIndexInteger hik
  rw [Real.dist_eq] at hunit
  rw [← mul_sub, abs_mul, abs_of_pos hr]
  simpa using mul_le_mul_of_nonneg_left hunit hr.le

/-- Uniform packing of the scaled integer lattice in every dilated assigned interval.
The bound depends only on the dilation, not on the scale, point, or finite test family. -/
theorem exists_intervalPartitionCenter_overlap_bound (D : ℝ) (_hD : 0 ≤ D) :
    ∃ B : ℕ, ∀ {r : ℝ}, 0 < r → ∀ x (s : Finset ℕ),
      Set.ncard {i | i ∈ s ∧
        x ∈ Metric.ball (intervalPartitionCenter r i) (D * r)} ≤ B := by
  obtain ⟨B, hB⟩ := exists_finset_card_bound_of_separated_mem_compact
    (X := ℝ) (K := Metric.closedBall (0 : ℝ) D) (isCompact_closedBall (0 : ℝ) D)
    (δ := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨B, ?_⟩
  intro r hr x s
  classical
  let selected : Finset ℕ := s.filter fun i =>
    x ∈ Metric.ball (intervalPartitionCenter r i) (D * r)
  let F : ℕ → ℝ := fun i => r⁻¹ * (intervalPartitionCenter r i - x)
  have hFinj : Function.Injective F := by
    intro i k hik
    have hsub : intervalPartitionCenter r i - x = intervalPartitionCenter r k - x :=
      mul_left_cancel₀ (inv_ne_zero hr.ne') hik
    have hcenter : intervalPartitionCenter r i = intervalPartitionCenter r k := by
      linarith
    have hcast : (intervalIndexInteger i : ℝ) = (intervalIndexInteger k : ℝ) := by
      exact mul_left_cancel₀ hr.ne' (by simpa [intervalPartitionCenter] using hcenter)
    exact intervalIndexInteger_injective (by exact_mod_cast hcast)
  have himage_mem : ∀ y ∈ selected.image F, y ∈ Metric.closedBall (0 : ℝ) D := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    have hiball : x ∈ Metric.ball (intervalPartitionCenter r i) (D * r) := by
      simpa [selected] using (Finset.mem_filter.mp hi).2
    have hdist : ‖intervalPartitionCenter r i - x‖ < D * r := by
      simpa [dist_eq_norm, norm_sub_rev] using Metric.mem_ball.mp hiball
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    calc
      r⁻¹ * ‖intervalPartitionCenter r i - x‖ ≤ r⁻¹ * (D * r) :=
        mul_le_mul_of_nonneg_left hdist.le (inv_nonneg.mpr hr.le)
      _ = D := by field_simp
  have himage_sep : ∀ y ∈ selected.image F, ∀ z ∈ selected.image F, y ≠ z →
      2 * (1 / 2 : ℝ) ≤ dist y z := by
    intro y hy z hz hyz
    rw [Finset.mem_image] at hy hz
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨k, hk, rfl⟩ := hz
    have hik : i ≠ k := fun h => hyz (congr_arg F h)
    have hcenter := intervalPartitionCenter_separated hr hik
    have hdist : dist (F i) (F k) = r⁻¹ *
        dist (intervalPartitionCenter r i) (intervalPartitionCenter r k) := by
      rw [Real.dist_eq, Real.dist_eq]
      simp only [F]
      rw [← mul_sub, sub_sub_sub_cancel_right, abs_mul, abs_of_pos (inv_pos.mpr hr)]
    rw [hdist]
    have := mul_le_mul_of_nonneg_left hcenter (inv_nonneg.mpr hr.le)
    simpa [hr.ne'] using this
  have hcard := hB (selected.image F) himage_mem himage_sep
  rw [Finset.card_image_of_injective _ hFinj] at hcard
  have hset : {i | i ∈ s ∧
      x ∈ Metric.ball (intervalPartitionCenter r i) (D * r)} =
      (selected : Set ℕ) := by
    ext i
    simp [selected]
  rw [hset]
  simpa using hcard

/-- A fixed scalar bump equal to one on `[-1,1]` and supported in `(-2,2)`. -/
def intervalUnitRawBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The translate of the unit raw bump centered at an integer. -/
def intervalRawBumpInt (z : ℤ) (t : ℝ) : ℝ :=
  intervalUnitRawBump (t - (z : ℝ))

/-- The natural-number indexing of the integer-lattice raw bump family. -/
def intervalRawBump (i : ℕ) : ℝ → ℝ :=
  intervalRawBumpInt (intervalIndexInteger i)

theorem intervalRawBumpInt_contDiff (z : ℤ) :
    ContDiff ℝ 6 (intervalRawBumpInt z) := by
  exact intervalUnitRawBump.contDiff.comp (contDiff_id.sub contDiff_const)

theorem intervalRawBump_contDiff (i : ℕ) : ContDiff ℝ 6 (intervalRawBump i) :=
  intervalRawBumpInt_contDiff _

theorem support_intervalRawBumpInt (z : ℤ) :
    Function.support (intervalRawBumpInt z) = Metric.ball (z : ℝ) 2 := by
  ext t
  change intervalUnitRawBump (t - (z : ℝ)) ≠ 0 ↔ dist t (z : ℝ) < 2
  rw [← Function.mem_support, intervalUnitRawBump.support_eq]
  simp [intervalUnitRawBump, Real.dist_eq]

theorem support_intervalRawBump (i : ℕ) :
    Function.support (intervalRawBump i) =
      Metric.ball (intervalIndexInteger i : ℝ) 2 :=
  support_intervalRawBumpInt _

theorem intervalRawBumpInt_eq_one {z : ℤ} {t : ℝ}
    (ht : t ∈ Metric.closedBall (z : ℝ) 1) :
    intervalRawBumpInt z t = 1 := by
  apply intervalUnitRawBump.one_of_mem_closedBall
  simpa [intervalUnitRawBump, Metric.mem_closedBall, Real.dist_eq] using ht

/-- Every real point lies in the unit core of one integer-lattice bump. -/
theorem exists_intervalRawBump_eq_one (t : ℝ) :
    ∃ i : ℕ, intervalRawBump i t = 1 := by
  let z : ℤ := ⌊t⌋
  let i : ℕ := Equiv.intEquivNat z
  refine ⟨i, ?_⟩
  have hnonneg : 0 ≤ t - (z : ℝ) := by
    exact sub_nonneg.mpr (Int.floor_le t)
  have hlt : t - (z : ℝ) < 1 := by
    simpa [z, Int.self_sub_floor] using Int.fract_lt_one t
  have ht : t ∈ Metric.closedBall (z : ℝ) 1 := by
    rw [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg hnonneg]
    exact hlt.le
  simpa [intervalRawBump, intervalIndexInteger, i] using
    (intervalRawBumpInt_eq_one ht)

/-- The integer-lattice raw supports form a locally finite family. -/
theorem intervalRawBump_support_locallyFiniteAt (x : ℝ) :
    ∃ V ∈ 𝓝 x,
      Set.Finite {i | (Function.support (intervalRawBump i) ∩ V).Nonempty} := by
  obtain ⟨B, hB⟩ := exists_intervalPartitionCenter_overlap_bound 3 (by norm_num)
  have hpoint : Set.Finite {i | x ∈ Metric.ball (intervalIndexInteger i : ℝ) 3} := by
    apply finite_of_uniform_finset_ncard_le (B := B)
    intro s
    simpa [intervalPartitionCenter] using hB (r := 1) zero_lt_one x s
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, hpoint.subset ?_⟩
  intro i hi
  change x ∈ Metric.ball (intervalIndexInteger i : ℝ) 3
  obtain ⟨y, hyraw, hyx⟩ := hi
  rw [support_intervalRawBump] at hyraw
  rw [Metric.mem_ball]
  calc
    dist x (intervalIndexInteger i : ℝ) ≤ dist x y + dist y (intervalIndexInteger i : ℝ) :=
      dist_triangle _ _ _
    _ < 1 + 2 := add_lt_add (by simpa [dist_comm] using Metric.mem_ball.mp hyx)
      (Metric.mem_ball.mp hyraw)
    _ = 3 := by norm_num

/-- Only finitely many raw bumps are nonzero at a given point. -/
theorem intervalRawBump_pointFinite (x : ℝ) :
    Set.Finite {i | intervalRawBump i x ≠ 0} := by
  obtain ⟨V, hxV, hfinite⟩ := intervalRawBump_support_locallyFiniteAt x
  apply hfinite.subset
  intro i hi
  exact ⟨x, hi, mem_of_mem_nhds hxV⟩

/-- The raw square sum, indexed intrinsically by all integers. -/
def intervalRawSquareSum (t : ℝ) : ℝ :=
  ∑' z : ℤ, intervalRawBumpInt z t ^ 2

theorem intervalRawSquareSum_eq_nat_tsum (t : ℝ) :
    intervalRawSquareSum t = ∑' i : ℕ, intervalRawBump i t ^ 2 := by
  simpa [intervalRawSquareSum, intervalRawBump, intervalIndexInteger] using
    (Equiv.intEquivNat.tsum_eq (fun i : ℕ => intervalRawBump i t ^ 2))

/-- The raw square sum is invariant under every integer translation. -/
theorem intervalRawSquareSum_sub_intCast (t : ℝ) (a : ℤ) :
    intervalRawSquareSum (t - (a : ℝ)) = intervalRawSquareSum t := by
  calc
    intervalRawSquareSum (t - (a : ℝ)) =
        ∑' z : ℤ, intervalRawBumpInt (z + a) t ^ 2 := by
      apply tsum_congr
      intro z
      simp only [intervalRawBumpInt]
      congr 2
      push_cast
      ring
    _ = intervalRawSquareSum t := by
      simpa [intervalRawSquareSum] using
        (Equiv.addRight a).tsum_eq (fun z : ℤ => intervalRawBumpInt z t ^ 2)

/-- The integer-indexed square-normalized cutoff at unit scale. -/
def intervalUnitCutoffInt (z : ℤ) (t : ℝ) : ℝ :=
  intervalRawBumpInt z t / Real.sqrt (intervalRawSquareSum t)

/-- Its natural-number indexing. -/
def intervalUnitCutoff (i : ℕ) : ℝ → ℝ :=
  intervalUnitCutoffInt (intervalIndexInteger i)

theorem intervalUnitCutoff_eq_squareNormalizedFamily (i : ℕ) :
    intervalUnitCutoff i = squareNormalizedFamily intervalRawBump i := by
  funext t
  simp only [intervalUnitCutoff, intervalUnitCutoffInt, squareNormalizedFamily]
  rw [intervalRawSquareSum_eq_nat_tsum]
  rfl

theorem intervalRawSquareSum_pos (t : ℝ) : 0 < intervalRawSquareSum t := by
  obtain ⟨i, hi⟩ := exists_intervalRawBump_eq_one t
  rw [intervalRawSquareSum_eq_nat_tsum]
  have hone := one_le_raw_square_tsum intervalRawBump intervalRawBump_pointFinite t i hi
  exact zero_lt_one.trans_le hone

/-- The normalized integer-lattice cutoffs form an exact square partition of one. -/
theorem intervalUnitCutoff_square_tsum (t : ℝ) :
    ∑' i : ℕ, intervalUnitCutoff i t ^ 2 = 1 := by
  rw [funext intervalUnitCutoff_eq_squareNormalizedFamily]
  exact squareNormalizedFamily_square_tsum intervalRawBump intervalRawBump_pointFinite t
    (by simpa [← intervalRawSquareSum_eq_nat_tsum] using intervalRawSquareSum_pos t)

theorem intervalUnitCutoff_contDiff (i : ℕ) : ContDiff ℝ 6 (intervalUnitCutoff i) := by
  rw [intervalUnitCutoff_eq_squareNormalizedFamily]
  apply squareNormalizedFamily_contDiff_of_locallyFiniteOn (fun _ : ℝ => True)
  · exact intervalRawBump_contDiff
  · intro x hx
    exact intervalRawBump_support_locallyFiniteAt x
  · intro x hx
    simpa [← intervalRawSquareSum_eq_nat_tsum] using intervalRawSquareSum_pos x
  · simp

theorem intervalUnitCutoffInt_contDiff (z : ℤ) :
    ContDiff ℝ 6 (intervalUnitCutoffInt z) := by
  have h := intervalUnitCutoff_contDiff (Equiv.intEquivNat z)
  simpa [intervalUnitCutoff, intervalIndexInteger] using h

/-- Integer translation covariance reduces every unit cutoff to the zero-centered profile. -/
theorem intervalUnitCutoffInt_eq_translate (z : ℤ) :
    intervalUnitCutoffInt z = fun t => intervalUnitCutoffInt 0 (t - (z : ℝ)) := by
  funext t
  simp only [intervalUnitCutoffInt, intervalRawBumpInt]
  rw [intervalRawSquareSum_sub_intCast]
  congr 2
  norm_num

theorem support_intervalUnitCutoffInt_subset (z : ℤ) :
    Function.support (intervalUnitCutoffInt z) ⊆ Metric.ball (z : ℝ) 2 := by
  intro t ht
  have hraw : intervalRawBumpInt z t ≠ 0 := by
    intro hzero
    exact ht (by simp [intervalUnitCutoffInt, hzero])
  rw [← support_intervalRawBumpInt z]
  exact hraw

theorem intervalUnitCutoffInt_zero_hasCompactSupport :
    HasCompactSupport (intervalUnitCutoffInt 0) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 2)
  have hs : Function.support (intervalUnitCutoffInt 0) ⊆ Metric.ball (0 : ℝ) 2 := by
    simpa only [Int.cast_zero] using support_intervalUnitCutoffInt_subset 0
  exact hs.trans Metric.ball_subset_closedBall

/-- One common bound controls every integer translate through derivative order four. -/
theorem intervalUnitCutoff_uniform_deriv_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℤ, ∀ j, j ≤ 4 → ∀ t,
      ‖iteratedFDeriv ℝ j (intervalUnitCutoffInt z) t‖ ≤ C := by
  have hbound : ∀ j : Fin 7, ∃ M : ℝ, ∀ t,
      ‖iteratedFDeriv ℝ j (intervalUnitCutoffInt 0) t‖ ≤ M := by
    intro j
    have hj : (j : ℕ) ≤ 6 := Nat.le_of_lt_succ j.isLt
    have hbdd : BddAbove (Set.range fun t =>
        ‖iteratedFDeriv ℝ j (intervalUnitCutoffInt 0) t‖) := by
      apply ((intervalUnitCutoffInt_contDiff 0).continuous_iteratedFDeriv
        (by exact_mod_cast hj)).norm.bddAbove_range_of_hasCompactSupport
      apply HasCompactSupport.comp_left _ norm_zero
      exact intervalUnitCutoffInt_zero_hasCompactSupport.iteratedFDeriv j
    rcases hbdd with ⟨M, hM⟩
    exact ⟨M, fun t => hM (Set.mem_range_self t)⟩
  choose M hM using hbound
  let C := max ((Finset.univ.image M).max' (by simp)) 1
  refine ⟨C, le_max_right _ _, ?_⟩
  intro z j hj t
  let q : Fin 7 := ⟨j, lt_of_le_of_lt hj (by norm_num)⟩
  rw [intervalUnitCutoffInt_eq_translate z, iteratedFDeriv_comp_sub]
  exact (hM q (t - (z : ℝ))).trans <| (Finset.le_max'
    (Finset.univ.image M) (M q) (Finset.mem_image_of_mem M (Finset.mem_univ q))).trans
      (le_max_left _ _)

/-- Scalar inverse-radius rescaling transfers profile bounds to scale-invariant bounds. -/
theorem real_rescaledFunction_scaled_deriv_bound
    {f : ℝ → ℝ} {C : ℝ} (hf : ContDiff ℝ 6 f)
    (hC : ∀ j, j ≤ 4 → ∀ t, ‖iteratedFDeriv ℝ j f t‖ ≤ C)
    {r : ℝ} (hr : 0 < r) (j : ℕ) (hj : j ≤ 4) (t : ℝ) :
    ‖iteratedFDeriv ℝ j (fun s => f (r⁻¹ • s)) t‖ * r ^ j ≤ C := by
  let L : ℝ →L[ℝ] ℝ := r⁻¹ • ContinuousLinearMap.id ℝ ℝ
  have hcomp : iteratedFDeriv ℝ j (f ∘ L) t =
      (iteratedFDeriv ℝ j f (L t)).compContinuousLinearMap (fun _ => L) :=
    L.iteratedFDeriv_comp_right hf t (by exact_mod_cast hj.trans (by norm_num : 4 ≤ 6))
  change ‖iteratedFDeriv ℝ j (f ∘ L) t‖ * r ^ j ≤ C
  rw [hcomp]
  have hC0 : 0 ≤ C :=
    (norm_nonneg (iteratedFDeriv ℝ 0 f 0)).trans (hC 0 (by norm_num) 0)
  have hnormL : ‖L‖ ≤ r⁻¹ := by
    calc
      ‖L‖ ≤ ‖r⁻¹‖ * ‖ContinuousLinearMap.id ℝ ℝ‖ :=
        norm_smul_le (r⁻¹ : ℝ) (ContinuousLinearMap.id ℝ ℝ)
      _ ≤ r⁻¹ * 1 := by
        rw [Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        gcongr
        exact ContinuousLinearMap.norm_id_le
      _ = r⁻¹ := mul_one _
  have hprod : (∏ _ : Fin j, ‖L‖) ≤ (r⁻¹) ^ j := by
    calc
      (∏ _ : Fin j, ‖L‖) ≤ ∏ _ : Fin j, r⁻¹ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg L) (fun _ _ => hnormL)
      _ = (r⁻¹) ^ j := by simp
  calc
    ‖(iteratedFDeriv ℝ j f (L t)).compContinuousLinearMap (fun _ => L)‖ * r ^ j ≤
        (‖iteratedFDeriv ℝ j f (L t)‖ * ∏ _ : Fin j, ‖L‖) * r ^ j := by
      gcongr
      exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (C * ∏ _ : Fin j, ‖L‖) * r ^ j := by
      gcongr
      exact hC j hj _
    _ ≤ (C * (r⁻¹) ^ j) * r ^ j := by gcongr
    _ = C := by
      rw [inv_pow]
      field_simp

/-- The scale-dependent cutoff `eta(r,l)` with natural index `l`. -/
def scaledIntervalCutoff (r : ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  intervalUnitCutoffInt (intervalIndexInteger i) (r⁻¹ • t)

theorem scaledIntervalCutoff_contDiff (r : ℝ) (i : ℕ) :
    ContDiff ℝ 6 (scaledIntervalCutoff r i) := by
  exact (intervalUnitCutoffInt_contDiff _).comp (by fun_prop)

theorem scaledIntervalCutoff_square_tsum {r : ℝ} (_hr : 0 < r) (t : ℝ) :
    ∑' i : ℕ, scaledIntervalCutoff r i t ^ 2 = 1 := by
  simpa [scaledIntervalCutoff, intervalUnitCutoff, intervalIndexInteger] using
    intervalUnitCutoff_square_tsum (r⁻¹ • t)

theorem support_scaledIntervalCutoff_subset {r : ℝ} (hr : 0 < r) (i : ℕ) :
    Function.support (scaledIntervalCutoff r i) ⊆
      Metric.ball (intervalPartitionCenter r i) (2 * r) := by
  intro t ht
  have hunit : r⁻¹ • t ∈ Metric.ball (intervalIndexInteger i : ℝ) 2 :=
    support_intervalUnitCutoffInt_subset _ ht
  have htEq : t = r • (r⁻¹ • t) := by
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [Metric.mem_ball] at hunit ⊢
  rw [htEq, intervalPartitionCenter, show r * (intervalIndexInteger i : ℝ) =
    r • (intervalIndexInteger i : ℝ) by rfl, dist_smul₀, Real.norm_of_nonneg hr.le]
  simpa [mul_comm] using (mul_lt_mul_iff_right₀ hr).2 hunit

theorem scaledIntervalCutoff_scaled_deriv_bound {C : ℝ}
    (hC : ∀ z : ℤ, ∀ j, j ≤ 4 → ∀ t,
      ‖iteratedFDeriv ℝ j (intervalUnitCutoffInt z) t‖ ≤ C)
    {r : ℝ} (hr : 0 < r) (i j : ℕ) (hj : j ≤ 4) (t : ℝ) :
    ‖iteratedFDeriv ℝ j (scaledIntervalCutoff r i) t‖ * r ^ j ≤ C := by
  exact real_rescaledFunction_scaled_deriv_bound
    (intervalUnitCutoffInt_contDiff _) (hC (intervalIndexInteger i)) hr j hj t

theorem intervalUnitCutoffInt_nonneg (z : ℤ) (t : ℝ) :
    0 ≤ intervalUnitCutoffInt z t := by
  exact div_nonneg intervalUnitRawBump.nonneg (Real.sqrt_nonneg _)

theorem scaledIntervalCutoff_nonneg (r : ℝ) (i : ℕ) (t : ℝ) :
    0 ≤ scaledIntervalCutoff r i t :=
  intervalUnitCutoffInt_nonneg _ _

/-- At every point only finitely many scaled interval cutoffs are nonzero. -/
theorem scaledIntervalCutoff_pointFinite (r t : ℝ) :
    Set.Finite {i | scaledIntervalCutoff r i t ≠ 0} := by
  apply (intervalRawBump_pointFinite (r⁻¹ • t)).subset
  intro i hi
  change intervalRawBump i (r⁻¹ • t) ≠ 0
  intro hraw
  apply hi
  change intervalRawBumpInt (intervalIndexInteger i) (r⁻¹ • t) = 0 at hraw
  change intervalUnitCutoffInt (intervalIndexInteger i) (r⁻¹ • t) = 0
  apply (div_eq_zero_iff).2
  exact Or.inl (by simpa only [smul_eq_mul] using hraw)

/-- Multiplying a scalar by every cutoff and summing squares recovers its square exactly. -/
theorem scaledIntervalCutoff_mul_square_tsum {r : ℝ} (hr : 0 < r) (t a : ℝ) :
    ∑' i : ℕ, (scaledIntervalCutoff r i t * a) ^ 2 = a ^ 2 := by
  have hsummable : Summable (fun i : ℕ => scaledIntervalCutoff r i t ^ 2) := by
    apply summable_of_hasFiniteSupport
    exact (scaledIntervalCutoff_pointFinite r t).subset (by
      intro i hi
      change scaledIntervalCutoff r i t ≠ 0
      intro hzero
      exact hi (by simp [hzero]))
  calc
    ∑' i : ℕ, (scaledIntervalCutoff r i t * a) ^ 2 =
        ∑' i : ℕ, scaledIntervalCutoff r i t ^ 2 * a ^ 2 := by
      apply tsum_congr
      intro i
      ring
    _ = (∑' i : ℕ, scaledIntervalCutoff r i t ^ 2) * a ^ 2 :=
      (hsummable.hasSum.mul_right (a ^ 2)).tsum_eq
    _ = a ^ 2 := by rw [scaledIntervalCutoff_square_tsum hr]; ring

/-- The complete quantitative one-dimensional square-partition package. -/
structure ScaledIntervalSquarePartition (r D C : ℝ) (B : ℕ) where
  radius_pos : 0 < r
  dilation_nonneg : 0 ≤ D
  center : ℕ → ℝ
  cutoff : ℕ → ℝ → ℝ
  center_eq : center = intervalPartitionCenter r
  cutoff_contDiff : ∀ i, ContDiff ℝ 6 (cutoff i)
  cutoff_support : ∀ i, Function.support (cutoff i) ⊆ Metric.ball (center i) (2 * r)
  cutoff_nonnegative : ∀ i t, 0 ≤ cutoff i t
  point_finite : ∀ t, Set.Finite {i | cutoff i t ≠ 0}
  square_partition : ∀ t, ∑' i, cutoff i t ^ 2 = 1
  overlap : ∀ t (s : Finset ℕ),
    Set.ncard {i | i ∈ s ∧ t ∈ Metric.ball (center i) (D * r)} ≤ B
  scaled_cutoff : ∀ i j, j ≤ 4 → ∀ t,
    ‖iteratedFDeriv ℝ j (cutoff i) t‖ * r ^ j ≤ C


namespace ScaledIntervalSquarePartition

theorem summable_cutoff_sq {r D C : ℝ} {B : ℕ}
    (partition : ScaledIntervalSquarePartition r D C B) (t : ℝ) :
    Summable (fun i : ℕ => partition.cutoff i t ^ 2) := by
  apply summable_of_hasFiniteSupport
  exact (partition.point_finite t).subset (by
    intro i hi
    change partition.cutoff i t ≠ 0
    intro hzero
    exact hi (by simp [hzero]))

/-- The abstract package retains the exact square identity after multiplication by a scalar. -/
theorem mul_square_tsum {r D C : ℝ} {B : ℕ}
    (partition : ScaledIntervalSquarePartition r D C B) (t a : ℝ) :
    ∑' i : ℕ, (partition.cutoff i t * a) ^ 2 = a ^ 2 := by
  calc
    ∑' i : ℕ, (partition.cutoff i t * a) ^ 2 =
        ∑' i : ℕ, partition.cutoff i t ^ 2 * a ^ 2 := by
      apply tsum_congr
      intro i
      ring
    _ = (∑' i : ℕ, partition.cutoff i t ^ 2) * a ^ 2 :=
      ((partition.summable_cutoff_sq t).hasSum.mul_right (a ^ 2)).tsum_eq
    _ = a ^ 2 := by rw [partition.square_partition]; ring

end ScaledIntervalSquarePartition

/-- For every prescribed nonnegative dilation there are uniform jet and overlap constants,
valid at every positive physical scale. -/
theorem exists_scaledIntervalSquarePartition (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, ∃ B : ℕ, 1 ≤ C ∧ 0 < B ∧ ∀ r : ℝ, 0 < r →
      Nonempty (ScaledIntervalSquarePartition r D C B) := by
  obtain ⟨C, hCone, hC⟩ := intervalUnitCutoff_uniform_deriv_bound
  obtain ⟨B₀, hB₀⟩ := exists_intervalPartitionCenter_overlap_bound D hD
  let B := max B₀ 1
  refine ⟨C, B, hCone, by simp [B], ?_⟩
  intro r hr
  refine ⟨{
    radius_pos := hr
    dilation_nonneg := hD
    center := intervalPartitionCenter r
    cutoff := scaledIntervalCutoff r
    center_eq := rfl
    cutoff_contDiff := scaledIntervalCutoff_contDiff r
    cutoff_support := ?_
    cutoff_nonnegative := scaledIntervalCutoff_nonneg r
    point_finite := scaledIntervalCutoff_pointFinite r
    square_partition := scaledIntervalCutoff_square_tsum hr
    overlap := ?_
    scaled_cutoff := ?_ }⟩
  · exact support_scaledIntervalCutoff_subset hr
  · intro t s
    exact (hB₀ hr t s).trans (Nat.le_max_left _ _)
  · intro i j hj t
    exact scaledIntervalCutoff_scaled_deriv_bound hC hr i j hj t

end QuarticConvergence
end OptimalConvergenceRates
