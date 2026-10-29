import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.QuarticPolarizationAlgebra

/-! Dimension-free bounds for an actual symmetric continuous four-linear form.
The polynomial-to-multilinear representation and sphere approximation remain separate. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ)

def quarticPolarizationSum (a b c d : E) : ℝ :=
  ∑ s0 : Bool, ∑ s1 : Bool, ∑ s2 : Bool, ∑ s3 : Bool,
    (quarticSign s0 * quarticSign s1 * quarticSign s2 * quarticSign s3) *
      quarticDiagonal A (quarticSign s0 • a + quarticSign s1 • b +
        quarticSign s2 • c + quarticSign s3 • d)

theorem quarticPolarizationSum_eq (a b c d : E) :
    quarticPolarizationSum A a b c d =
      quarticHalfPolarizationSum A a b c d - quarticHalfPolarizationSum A (-a) b c d := by
  simp only [quarticPolarizationSum, quarticHalfPolarizationSum, Fintype.sum_bool,
    quarticSign, one_smul, neg_one_smul, one_mul, mul_one, neg_mul, mul_neg, neg_neg]
  ring

/-- The exact sixteen-sign polarization identity. -/
theorem quarticPolarization_identity (hA : SymmetricQuarticForm A) (a b c d : E) :
    quarticPolarizationSum A a b c d = 384 * quarticApply A a b c d := by
  rw [quarticPolarizationSum_eq, quarticHalfPolarization_identity A hA,
    quarticHalfPolarization_identity A hA, quarticApply_neg0]
  ring

theorem quarticSign_abs (s : Bool) : |quarticSign s| = 1 := by
  cases s <;> norm_num [quarticSign]

theorem quarticSignedVector_norm_le (a b c d : E)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (s1 s2 s3 : Bool) :
    ‖a + quarticSign s1 • b + quarticSign s2 • c + quarticSign s3 • d‖ ≤ 4 := by
  have hnorm (s : Bool) (v : E) : ‖quarticSign s • v‖ = ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, quarticSign_abs, one_mul]
  calc
    _ ≤ ‖a + quarticSign s1 • b + quarticSign s2 • c‖ + ‖quarticSign s3 • d‖ := norm_add_le _ _
    _ ≤ (‖a + quarticSign s1 • b‖ + ‖quarticSign s2 • c‖) + ‖quarticSign s3 • d‖ := by
      linarith [norm_add_le (a + quarticSign s1 • b) (quarticSign s2 • c)]
    _ ≤ ((‖a‖ + ‖quarticSign s1 • b‖) + ‖quarticSign s2 • c‖) + ‖quarticSign s3 • d‖ := by
      linarith [norm_add_le a (quarticSign s1 • b)]
    _ ≤ 4 := by simp only [hnorm]; linarith

theorem quarticHalfPolarizationSum_abs_le (M : ℝ) (hM : 0 ≤ M)
    (hdiag : ∀ x : E, |A (fun _ ↦ x)| ≤ M * ‖x‖ ^ 4)
    (a b c d : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    |quarticHalfPolarizationSum A a b c d| ≤ 2048 * M := by
  have hterm (s1 s2 s3 : Bool) :
      |(quarticSign s1 * quarticSign s2 * quarticSign s3) *
        quarticDiagonal A (a + quarticSign s1 • b + quarticSign s2 • c + quarticSign s3 • d)| ≤
          256 * M := by
    rw [abs_mul, abs_mul, abs_mul, quarticSign_abs, quarticSign_abs, quarticSign_abs,
      one_mul, one_mul, one_mul, quarticDiagonal_eq]
    calc
      _ ≤ M * ‖a + quarticSign s1 • b + quarticSign s2 • c + quarticSign s3 • d‖ ^ 4 := hdiag _
      _ ≤ M * (4 : ℝ) ^ 4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (quarticSignedVector_norm_le a b c d ha hb hc hd s1 s2
          s3) 4) hM
      _ = 256 * M := by ring
  let t : Bool → Bool → Bool → ℝ := fun s1 s2 s3 ↦
    (quarticSign s1 * quarticSign s2 * quarticSign s3) *
      quarticDiagonal A (a + quarticSign s1 • b + quarticSign s2 • c + quarticSign s3 • d)
  change |∑ s1 : Bool, ∑ s2 : Bool, ∑ s3 : Bool, t s1 s2 s3| ≤ 2048 * M
  calc
    _ ≤ ∑ s1 : Bool, |∑ s2 : Bool, ∑ s3 : Bool, t s1 s2 s3| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s1 : Bool, ∑ s2 : Bool, |∑ s3 : Bool, t s1 s2 s3| := by
      apply Finset.sum_le_sum
      intro s1 _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s1 : Bool, ∑ s2 : Bool, ∑ s3 : Bool, |t s1 s2 s3| := by
      apply Finset.sum_le_sum
      intro s1 _
      apply Finset.sum_le_sum
      intro s2 _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s1 : Bool, ∑ s2 : Bool, ∑ s3 : Bool, (256 : ℝ) * M := by
      apply Finset.sum_le_sum
      intro s1 _
      apply Finset.sum_le_sum
      intro s2 _
      apply Finset.sum_le_sum
      intro s3 _
      exact hterm s1 s2 s3
    _ = 2048 * M := by simp only [Fintype.sum_bool]; ring

/-- The dimension-free real quartic polarization bound for four unit inputs. -/
theorem symmetricQuarticForm_unit_bound (hA : SymmetricQuarticForm A) (M : ℝ)
    (hM : 0 ≤ M) (hdiag : ∀ x : E, |A (fun _ ↦ x)| ≤ M * ‖x‖ ^ 4)
    (a b c d : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    ‖quarticApply A a b c d‖ ≤ (32 / 3 : ℝ) * M := by
  have h := quarticHalfPolarizationSum_abs_le A M hM hdiag a b c d ha hb hc hd
  rw [quarticHalfPolarization_identity A hA, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 192)] at h
  rw [Real.norm_eq_abs]
  linarith

theorem symmetricQuarticForm_unit_bound_fin (hA : SymmetricQuarticForm A) (M : ℝ)
    (hM : 0 ≤ M) (hdiag : ∀ x : E, |A (fun _ ↦ x)| ≤ M * ‖x‖ ^ 4)
    (v : Fin 4 → E) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ‖A v‖ ≤ (32 / 3 : ℝ) * M := by
  have ht : ![v 0, v 1, v 2, v 3] = v := by ext i; fin_cases i <;> rfl
  simpa only [quarticApply, ht] using symmetricQuarticForm_unit_bound A hA M hM hdiag
    (v 0) (v 1) (v 2) (v 3) (hv 0) (hv 1) (hv 2) (hv 3)

theorem symmetricQuarticForm_product_bound (hA : SymmetricQuarticForm A) (M : ℝ)
    (hM : 0 ≤ M) (hdiag : ∀ x : E, |A (fun _ ↦ x)| ≤ M * ‖x‖ ^ 4)
    (v : Fin 4 → E) :
    ‖A v‖ ≤ ((32 / 3 : ℝ) * M) * ∏ i, ‖v i‖ := by
  let w : Fin 4 → E := fun i ↦ ‖v i‖⁻¹ • v i
  have hw (i : Fin 4) : ‖w i‖ ≤ 1 := by
    exact (mem_closedBall_zero_iff).1 (inv_norm_smul_mem_unitClosedBall (v i))
  have hv : (fun i ↦ ‖v i‖ • w i) = v := by
    ext i
    dsimp [w]
    by_cases hi : v i = 0
    · simp [hi]
    · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hi), one_smul]
  have hscale : A v = (∏ i, ‖v i‖) • A w := by
    calc
      A v = A (fun i ↦ ‖v i‖ • w i) := congrArg A hv.symm
      _ = _ := A.map_smul_univ _ _
  have hprod : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _)
  rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_nonneg hprod]
  calc
    _ ≤ (∏ i, ‖v i‖) * ((32 / 3 : ℝ) * M) :=
      mul_le_mul_of_nonneg_left (symmetricQuarticForm_unit_bound_fin A hA M hM hdiag w hw) hprod
    _ = _ := mul_comm _ _

/-- The actual operator norm, with no ambient-dimension factor. -/
theorem symmetricQuarticForm_opNorm_bound (hA : SymmetricQuarticForm A) (M : ℝ)
    (hM : 0 ≤ M) (hdiag : ∀ x : E, |A (fun _ ↦ x)| ≤ M * ‖x‖ ^ 4) :
    ‖A‖ ≤ (32 / 3 : ℝ) * M := by
  apply A.opNorm_le_bound (by positivity)
  exact symmetricQuarticForm_product_bound A hA M hM hdiag

end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
