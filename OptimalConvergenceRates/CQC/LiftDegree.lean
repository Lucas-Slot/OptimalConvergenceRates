import OptimalConvergenceRates.CQC.AffineBox
import OptimalConvergenceRates.QuarticConvergence.Sphere.Defs
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ProductCircle

/-! # Degree bounds for the fixed CQC lift -/

noncomputable section
open MvPolynomial Finset Matrix
namespace OptimalConvergenceRates.CQCInternal

variable {n m : ℕ}

/-- A determinant has degree bounded by the sum of rowwise degree bounds. -/
theorem totalDegree_det_le_sum_rowBounds
    (A : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (b : Fin m → ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ b i) :
    A.det.totalDegree ≤ ∑ i, b i := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  calc
    (Equiv.Perm.sign σ • ∏ i, A (σ i) i).totalDegree ≤
        (∏ i, A (σ i) i).totalDegree :=
      MvPolynomial.totalDegree_smul_le _ _
    _ ≤ ∑ i, (A (σ i) i).totalDegree :=
      MvPolynomial.totalDegree_finsetProd Finset.univ (fun i ↦ A (σ i) i)
    _ ≤ ∑ i, b (σ i) := Finset.sum_le_sum fun i _ ↦ hA (σ i) i
    _ = ∑ i, b i := Equiv.sum_comp σ b

/-- Uniform-entry specialization of the determinant degree estimate. -/
theorem totalDegree_det_le
    (A : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (D : ℕ) (hA : ∀ i j, (A i j).totalDegree ≤ D) :
    A.det.totalDegree ≤ m * D := by
  calc
    A.det.totalDegree ≤ ∑ _ : Fin m, D :=
      totalDegree_det_le_sum_rowBounds A (fun _ ↦ D) hA
    _ = m * D := by simp

/-- Every adjugate entry has the degree of a product of at most `m - 1`
matrix entries. -/
theorem totalDegree_adjugate_le
    (A : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) ℝ))
    (D : ℕ) (hA : ∀ i j, (A i j).totalDegree ≤ D)
    (i j : Fin m) :
    (A.adjugate i j).totalDegree ≤ (m - 1) * D := by
  classical
  rw [Matrix.adjugate_apply]
  let b : Fin m → ℕ := fun k ↦ if k = j then 0 else D
  calc
    (A.updateRow j (Pi.single i 1)).det.totalDegree ≤ ∑ k, b k := by
      apply totalDegree_det_le_sum_rowBounds
      intro k l
      simp only [Matrix.updateRow_apply, b]
      by_cases hkj : k = j
      · subst k
        by_cases hli : l = i <;> simp [Pi.single_apply, hli]
      · simp only [hkj, ↓reduceIte]
        exact hA k l
    _ = (m - 1) * D := by
      simp only [b]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      have hsum :
          (∑ k ∈ Finset.univ.erase j, if k = j then 0 else D) =
            ∑ _k ∈ Finset.univ.erase j, D := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ite_eq_right (Finset.ne_of_mem_erase hk)]
      rw [hsum]
      simp

theorem totalDegree_liftBasePolynomial_le
    (p : MvPolynomial (Fin n) ℝ) :
    (liftBasePolynomial (m := m) p).totalDegree ≤ p.totalDegree :=
  MvPolynomial.totalDegree_rename_le _ _

theorem totalDegree_slackValueGramPolynomial_le
    {e : ℕ} (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e)
    (i k : Fin m) :
    (slackValueGramPolynomial g i k).totalDegree ≤ 2 * (e - 1) := by
  unfold slackValueGramPolynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have hi : (pderiv j (g i)).totalDegree ≤ e - 1 :=
      (QuarticConvergence.totalDegree_pderiv_le_pred j (g i)).trans
        (Nat.sub_le_sub_right (hg i) 1)
    have hk : (pderiv j (g k)).totalDegree ≤ e - 1 :=
      (QuarticConvergence.totalDegree_pderiv_le_pred j (g k)).trans
        (Nat.sub_le_sub_right (hg k) 1)
    simpa only [two_mul] using Nat.add_le_add
      ((totalDegree_liftBasePolynomial_le (m := m) _).trans hi)
      ((totalDegree_liftBasePolynomial_le (m := m) _).trans hk)
  · by_cases hik : i = k
    · simp only [hik, ↓reduceIte]
      calc
        (C (4 : ℝ) * X (Fin.natAdd n k)).totalDegree ≤
            (C (4 : ℝ)).totalDegree + (X (Fin.natAdd n k)).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ 1 := by simp
        _ ≤ 2 * (e - 1) := by omega
    · simp [hik]

theorem totalDegree_slackValueDeterminant_le
    {e : ℕ} (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e) :
    (slackValueDeterminant g).totalDegree ≤ 2 * m * (e - 1) := by
  unfold slackValueDeterminant
  exact (totalDegree_det_le (slackValueGramPolynomial g) (2 * (e - 1))
    (totalDegree_slackValueGramPolynomial_le he g hg)).trans (by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
      exact le_rfl)

theorem totalDegree_slackValueAdjugate_le
    {e : ℕ} (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e)
    (i k : Fin m) :
    ((slackValueGramPolynomial g).adjugate i k).totalDegree ≤
      2 * (m - 1) * (e - 1) := by
  exact (totalDegree_adjugate_le (slackValueGramPolynomial g) (2 * (e - 1))
    (totalDegree_slackValueGramPolynomial_le he g hg) i k).trans (by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
      exact le_rfl)

theorem pderiv_eq_zero_of_totalDegree_eq_zero
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree = 0) (j : Fin n) :
    pderiv j p = 0 := by
  rw [(MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp),
    MvPolynomial.pderiv_C]

theorem totalDegree_slackValueBaseW_le
    {e d : ℕ} (hm : 0 < m) (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e)
    (hp : p.totalDegree ≤ d)
    (j : Fin n) :
    (slackValueBaseW g p j).totalDegree ≤
      d + 2 * m * (e - 1) - 1 := by
  let D := 2 * m * (e - 1)
  have hD : 0 < D := by
    dsimp [D]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hm) (by omega)
  have hdet : (slackValueDeterminant g).totalDegree ≤ D := by
    simpa only [D] using totalDegree_slackValueDeterminant_le he g hg
  have hdd : (pderiv (Fin.castAdd m j) (slackValueDeterminant g)).totalDegree ≤
      D - 1 :=
    (QuarticConvergence.totalDegree_pderiv_le_pred _ _).trans
      (Nat.sub_le_sub_right hdet 1)
  unfold slackValueBaseW
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · calc
      (C (2 : ℝ) * liftBasePolynomial p *
          pderiv (Fin.castAdd m j) (slackValueDeterminant g)).totalDegree ≤
          (C (2 : ℝ) * liftBasePolynomial p).totalDegree +
            (pderiv (Fin.castAdd m j)
              (slackValueDeterminant g)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ ((C (2 : ℝ)).totalDegree + (liftBasePolynomial p).totalDegree) +
            (D - 1) :=
        Nat.add_le_add
          (MvPolynomial.totalDegree_mul _ _)
          hdd
      _ ≤ d + D - 1 := by
        have hlift := (totalDegree_liftBasePolynomial_le (m := m) p).trans hp
        simp only [MvPolynomial.totalDegree_C, zero_add]
        omega
      _ = d + 2 * m * (e - 1) - 1 := by rfl
  · by_cases hd : d = 0
    · have hp0 : p.totalDegree = 0 := by omega
      rw [pderiv_eq_zero_of_totalDegree_eq_zero p hp0 j]
      simp only [liftBasePolynomial, map_zero, mul_zero]
      exact Nat.zero_le _
    · have hpd : (pderiv j p).totalDegree ≤ d - 1 :=
        (QuarticConvergence.totalDegree_pderiv_le_pred j p).trans
          (Nat.sub_le_sub_right hp 1)
      calc
        (slackValueDeterminant g *
            liftBasePolynomial (pderiv j p)).totalDegree ≤
            (slackValueDeterminant g).totalDegree +
              (liftBasePolynomial (pderiv j p)).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ D + (d - 1) :=
          Nat.add_le_add hdet
            ((totalDegree_liftBasePolynomial_le (m := m) _).trans hpd)
        _ ≤ d + D - 1 := by omega
        _ = d + 2 * m * (e - 1) - 1 := by rfl

theorem totalDegree_slackValueCorrectionRhs_le
    {e d : ℕ} (hm : 0 < m) (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e)
    (hp : p.totalDegree ≤ d)
    (i : Fin m) :
    (slackValueCorrectionRhs g p i).totalDegree ≤
      d + 2 * m * (e - 1) + (e - 2) := by
  let D := 2 * m * (e - 1)
  have hD : 0 < D := by
    dsimp [D]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hm) (by omega)
  have hdet : (slackValueDeterminant g).totalDegree ≤ D := by
    simpa only [D] using totalDegree_slackValueDeterminant_le he g hg
  have hdd : (pderiv (Fin.natAdd n i) (slackValueDeterminant g)).totalDegree ≤
      D - 1 :=
    (QuarticConvergence.totalDegree_pderiv_le_pred _ _).trans
      (Nat.sub_le_sub_right hdet 1)
  unfold slackValueCorrectionRhs
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    apply (MvPolynomial.totalDegree_mul _ _).trans
    have hgj : (liftBasePolynomial (pderiv j (g i))).totalDegree ≤ e - 1 :=
      (totalDegree_liftBasePolynomial_le (m := m) _).trans
        ((QuarticConvergence.totalDegree_pderiv_le_pred j (g i)).trans
          (Nat.sub_le_sub_right (hg i) 1))
    have hw := totalDegree_slackValueBaseW_le hm he g p hg hp j
    omega
  · calc
      (C (8 : ℝ) * liftBasePolynomial p * X (Fin.natAdd n i) *
          pderiv (Fin.natAdd n i) (slackValueDeterminant g)).totalDegree ≤
          (C (8 : ℝ) * liftBasePolynomial p * X (Fin.natAdd n i)).totalDegree +
            (pderiv (Fin.natAdd n i) (slackValueDeterminant g)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ ((C (8 : ℝ) * liftBasePolynomial p).totalDegree +
            (X (Fin.natAdd n i)).totalDegree) + (D - 1) :=
        Nat.add_le_add (MvPolynomial.totalDegree_mul _ _) hdd
      _ ≤ (((C (8 : ℝ)).totalDegree +
            (liftBasePolynomial p).totalDegree) + 1) + (D - 1) := by
        gcongr
        · exact MvPolynomial.totalDegree_mul _ _
        · simp
      _ ≤ d + D := by
        have hlift := (totalDegree_liftBasePolynomial_le (m := m) p).trans hp
        simp only [MvPolynomial.totalDegree_C]
        omega
      _ ≤ d + D + (e - 2) := Nat.le_add_right _ _
      _ = d + 2 * m * (e - 1) + (e - 2) := by rfl


theorem totalDegree_slackValueCorrection_le
    {e d : ℕ} (hm : 0 < m) (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e)
    (hp : p.totalDegree ≤ d)
    (i : Fin m) :
    (slackValueCorrection g p i).totalDegree ≤
      2 * (m - 1) * (e - 1) +
        (d + 2 * m * (e - 1) + (e - 2)) := by
  unfold slackValueCorrection Matrix.mulVec dotProduct
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (Nat.add_le_add
      (totalDegree_slackValueAdjugate_le he g hg i k)
      (totalDegree_slackValueCorrectionRhs_le hm he g p hg hp k))


theorem correctionDegreeArithmetic
    {e d : ℕ} (hm : 0 < m) (he : 2 ≤ e) :
    e + (2 * (m - 1) * (e - 1) +
      (d + 2 * m * (e - 1) + (e - 2))) =
        d + 4 * m * (e - 1) := by
  have heq : e + (e - 2) = 2 * (e - 1) := by omega
  have hm1 : 1 ≤ m := by omega
  have hmeq :
      2 * (m - 1) * (e - 1) + 2 * (e - 1) =
        2 * m * (e - 1) := by
    calc
      2 * (m - 1) * (e - 1) + 2 * (e - 1) =
          2 * ((m - 1) + 1) * (e - 1) := by ring
      _ = 2 * m * (e - 1) := by rw [Nat.sub_add_cancel hm1]
  calc
    e + (2 * (m - 1) * (e - 1) +
        (d + 2 * m * (e - 1) + (e - 2))) =
        d + ((2 * (m - 1) * (e - 1) + 2 * (e - 1)) +
          2 * m * (e - 1)) := by omega
    _ = d + (2 * m * (e - 1) + 2 * m * (e - 1)) := by rw [hmeq]
    _ = d + 4 * m * (e - 1) := by ring


theorem totalDegree_descendedSlackObjective_le
    {e d : ℕ} (hm : 0 < m) (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (M : ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e)
    (hp : p.totalDegree ≤ d) :
    (descendedSlackObjective g p M).totalDegree ≤
      d + 4 * m * (e - 1) := by
  have hfactor (i : Fin m) :
      (liftBasePolynomial (g i) - X (Fin.natAdd n i)).totalDegree ≤ e := by
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le
      ((totalDegree_liftBasePolynomial_le (m := m) (g i)).trans (hg i))
      (by simp; omega))
  have hdet := totalDegree_slackValueDeterminant_le he g hg
  have hmain :
      ((slackValueDeterminant g) ^ 2 *
        liftBasePolynomial p).totalDegree ≤ d + 4 * m * (e - 1) := by
    calc
      ((slackValueDeterminant g) ^ 2 *
          liftBasePolynomial p).totalDegree ≤
          ((slackValueDeterminant g) ^ 2).totalDegree +
            (liftBasePolynomial p).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * (slackValueDeterminant g).totalDegree +
            (liftBasePolynomial p).totalDegree :=
        Nat.add_le_add (MvPolynomial.totalDegree_pow _ _) le_rfl
      _ ≤ 2 * (2 * m * (e - 1)) + d :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 hdet)
          ((totalDegree_liftBasePolynomial_le (m := m) p).trans hp)
      _ = d + 4 * m * (e - 1) := by ring
  have hcorrection :
      (∑ i, (liftBasePolynomial (g i) - X (Fin.natAdd n i)) *
        slackValueCorrection g p i).totalDegree ≤
          d + 4 * m * (e - 1) := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    calc
      ((liftBasePolynomial (g i) - X (Fin.natAdd n i)) *
          slackValueCorrection g p i).totalDegree ≤
          (liftBasePolynomial (g i) - X (Fin.natAdd n i)).totalDegree +
            (slackValueCorrection g p i).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ e + (2 * (m - 1) * (e - 1) +
            (d + 2 * m * (e - 1) + (e - 2))) :=
        Nat.add_le_add (hfactor i) (totalDegree_slackValueCorrection_le hm he g p hg hp i)
      _ = d + 4 * m * (e - 1) :=
        correctionDegreeArithmetic hm he
  have hpenalty :
      (C M * ∑ i,
        (liftBasePolynomial (g i) - X (Fin.natAdd n i)) ^ 2).totalDegree ≤
          d + 4 * m * (e - 1) := by
    calc
      (C M * ∑ i,
          (liftBasePolynomial (g i) - X (Fin.natAdd n i)) ^ 2).totalDegree ≤
          (C M).totalDegree +
            (∑ i, (liftBasePolynomial (g i) -
              X (Fin.natAdd n i)) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 2 * e := by
        apply Nat.add_le_add
        · simp
        · apply MvPolynomial.totalDegree_finsetSum_le
          intro i _
          exact (MvPolynomial.totalDegree_pow _ _).trans
            (Nat.mul_le_mul_left 2 (hfactor i))
      _ ≤ d + 4 * m * (e - 1) := by
        have hm1 : 1 ≤ m := by omega
        have heBound : 2 * e ≤ 4 * (e - 1) := by omega
        have hmBound : 4 * (e - 1) ≤ 4 * m * (e - 1) := by
          calc
            4 * (e - 1) = (4 * 1) * (e - 1) := by ring
            _ ≤ (4 * m) * (e - 1) :=
              Nat.mul_le_mul_right (e - 1) (Nat.mul_le_mul_left 4 hm1)
            _ = 4 * m * (e - 1) := by ring
        omega
  unfold descendedSlackObjective
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le
    ((MvPolynomial.totalDegree_sub _ _).trans (max_le hmain hcorrection))
    hpenalty)


theorem unitToSlackValueMap_totalDegree_le_one
    (R : ℝ) (j : Fin (n + m)) :
    (unitToSlackValueMap R j).totalDegree ≤ 1 := by
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp only [unitToSlackValueMap, Fin.addCases_left]
    calc
      (C R * X (Fin.castAdd m k)).totalDegree ≤
          (C R).totalDegree + (X (Fin.castAdd m k)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 := by simp
  · intro i
    simp only [unitToSlackValueMap, Fin.addCases_right]
    calc
      (C (R ^ 2 / 2) *
          ((X (Fin.natAdd n i) : MvPolynomial (Fin (n + m)) ℝ) + 1)).totalDegree ≤
          (C (R ^ 2 / 2)).totalDegree +
            ((X (Fin.natAdd n i) : MvPolynomial (Fin (n + m)) ℝ) + 1).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + max 1 0 :=
        Nat.add_le_add (by simp)
          ((MvPolynomial.totalDegree_add _ _).trans (by simp))
      _ ≤ 1 := by norm_num

theorem totalDegree_unitBoxLiftPolynomial_descended_le
    {e d : ℕ} (hm : 0 < m) (he : 2 ≤ e)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (M R : ℝ)
    (hg : ∀ i, (g i).totalDegree ≤ e)
    (hp : p.totalDegree ≤ d) :
    (unitBoxLiftPolynomial R (descendedSlackObjective g p M)).totalDegree ≤
      d + 4 * m * (e - 1) := by
  calc
    (unitBoxLiftPolynomial R
        (descendedSlackObjective g p M)).totalDegree ≤
        1 * (descendedSlackObjective g p M).totalDegree := by
      exact QuarticConvergence.totalDegree_aeval_le_mul_general
        (unitToSlackValueMap R) (unitToSlackValueMap_totalDegree_le_one R)
        (descendedSlackObjective g p M)
    _ ≤ 1 * (d + 4 * m * (e - 1)) :=
      Nat.mul_le_mul_left 1 (totalDegree_descendedSlackObjective_le hm he g p M hg hp)
    _ = d + 4 * m * (e - 1) := by omega

end OptimalConvergenceRates.CQCInternal
end

