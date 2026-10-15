import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import OptimalConvergenceRates.CQC.RegularPenaltyLinear

/-!
# Uniform normal estimates on a compact regular zero set
-/

noncomputable section

open MvPolynomial Finset Set Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {N m : ℕ}

theorem continuous_polynomialJacobianAt
    (h : Fin m → MvPolynomial (Fin N) ℝ) :
    Continuous (polynomialJacobianAt h) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_eval (MvPolynomial.pderiv j (h i))

theorem continuous_matrix_det {X k : Type*} [TopologicalSpace X]
    [Fintype k] [DecidableEq k]
    (A : X → Matrix k k ℝ)
    (hA : ∀ i j, Continuous (fun x ↦ A x i j)) :
    Continuous (fun x ↦ (A x).det) := by
  simp_rw [Matrix.det_apply']
  apply continuous_finsetSum
  intro σ _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i _
  exact hA (σ i) i

theorem continuous_polynomialGramAt
    (h : Fin m → MvPolynomial (Fin N) ℝ) :
    Continuous (polynomialGramAt h) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  simp only [polynomialGramAt, Matrix.mul_apply, Matrix.transpose_apply]
  apply continuous_finsetSum
  intro j _
  exact (continuous_eval (MvPolynomial.pderiv j (h i))).mul
    (continuous_eval (MvPolynomial.pderiv j (h k)))

theorem continuous_polynomialGramAt_entry
    (h : Fin m → MvPolynomial (Fin N) ℝ) (i j : Fin m) :
    Continuous (fun v ↦ polynomialGramAt h v i j) :=
  (continuous_apply j).comp
    ((continuous_apply i).comp (continuous_polynomialGramAt h))

theorem continuous_det_polynomialGramAt
    (h : Fin m → MvPolynomial (Fin N) ℝ) :
    Continuous (fun v ↦ (polynomialGramAt h v).det) := by
  apply continuous_matrix_det
  exact continuous_polynomialGramAt_entry h

theorem continuous_adjugate_polynomialGramAt_entry
    (h : Fin m → MvPolynomial (Fin N) ℝ) (i j : Fin m) :
    Continuous (fun v ↦ (polynomialGramAt h v).adjugate i j) := by
  simp_rw [Matrix.adjugate_apply]
  apply continuous_matrix_det
  intro k l
  simp only [Matrix.updateRow_apply]
  by_cases hkj : k = j
  · simp only [hkj, ↓reduceIte]
    exact continuous_const
  · simp only [hkj, ↓reduceIte]
    exact continuous_polynomialGramAt_entry h k l

theorem continuous_normalRecoveryAt
    (h : Fin m → MvPolynomial (Fin N) ℝ) :
    Continuous (normalRecoveryAt h) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro i
  simp only [normalRecoveryAt, Matrix.mul_apply, Matrix.transpose_apply]
  apply continuous_finsetSum
  intro k _
  exact (continuous_eval (MvPolynomial.pderiv j (h k))).mul
    (continuous_adjugate_polynomialGramAt_entry h k i)

theorem polynomialJacobianAt_vecMul_injective
    {h : Fin m → MvPolynomial (Fin N) ℝ} {v : Fin N → ℝ}
    (hli : LinearIndependent ℝ (fun i ↦ polynomialGradientAt (h i) v)) :
    Function.Injective (polynomialJacobianAt h v).vecMul := by
  intro c d hcd
  have hsum : ∑ i, (c i - d i) • polynomialGradientAt (h i) v = 0 := by
    funext j
    have hj := congrFun hcd j
    simp only [Matrix.vecMul, dotProduct, polynomialJacobianAt] at hj
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hj
  have hzero := (Fintype.linearIndependent_iff.mp hli)
    (fun i ↦ c i - d i) hsum
  funext i
  exact sub_eq_zero.mp (hzero i)

theorem polynomialGramAt_posDef
    {h : Fin m → MvPolynomial (Fin N) ℝ} {v : Fin N → ℝ}
    (hli : LinearIndependent ℝ (fun i ↦ polynomialGradientAt (h i) v)) :
    (polynomialGramAt h v).PosDef := by
  have hinj := polynomialJacobianAt_vecMul_injective hli
  simpa [polynomialGramAt] using
    Matrix.PosDef.mul_conjTranspose_self (polynomialJacobianAt h v) hinj

/-- On a compact set where the equation gradients are independent, the
Jacobian is uniformly bounded below on its row span. -/
theorem exists_uniform_normal_lower_bound
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (hne : (polynomialZeroSet h).Nonempty)
    (hcompact : IsCompact (polynomialZeroSet h))
    (hregular : ∀ v ∈ polynomialZeroSet h,
      LinearIndependent ℝ (fun i ↦ polynomialGradientAt (h i) v)) :
    ∃ sigma : ℝ, 0 < sigma ∧
      ∀ v ∈ polynomialZeroSet h, ∀ w : Fin N → ℝ,
        (∃ coeff : Fin m → ℝ,
          w = ∑ i, coeff i • polynomialGradientAt (h i) v) →
        sigma * ‖w‖ ≤ ‖(polynomialJacobianAt h v) *ᵥ w‖ := by
  let detAt : (Fin N → ℝ) → ℝ := fun v ↦ (polynomialGramAt h v).det
  obtain ⟨v₀, hv₀, hv₀min⟩ := hcompact.exists_isMinOn hne
    (continuous_det_polynomialGramAt h).continuousOn
  let d := detAt v₀
  have hd : 0 < d := (polynomialGramAt_posDef (hregular v₀ hv₀)).det_pos
  have hdet : ∀ v ∈ polynomialZeroSet h, d ≤ detAt v :=
    fun v hv ↦ hv₀min hv
  let recovery : (Fin N → ℝ) → (Fin N → Fin m → ℝ) :=
    fun v ↦ normalRecoveryAt h v
  have hrecovery_cont : Continuous recovery := continuous_normalRecoveryAt h
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, ∀ v ∈ polynomialZeroSet h,
      ‖recovery v‖ ≤ B₀ :=
    IsCompact.exists_bound_of_continuousOn
      (f := recovery) hcompact hrecovery_cont.continuousOn
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hentry : ∀ v ∈ polynomialZeroSet h, ∀ j i,
      |normalRecoveryAt h v j i| ≤ B := by
    intro v hv j i
    calc
      |normalRecoveryAt h v j i| = ‖recovery v j i‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ‖recovery v j‖ := norm_le_pi_norm _ i
      _ ≤ ‖recovery v‖ := norm_le_pi_norm _ j
      _ ≤ B₀ := hB₀ v hv
      _ ≤ B := le_max_left _ _
  let D := (m : ℝ) * B + 1
  let sigma := d / D
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hsigma : 0 < sigma := div_pos hd hD
  refine ⟨sigma, hsigma, ?_⟩
  intro v hv w hw
  obtain ⟨coeff, hcoeff⟩ := hw
  have hid := normalRecoveryAt_mulVec_jacobian h v w coeff hcoeff
  have hnorm := norm_matrix_mulVec_le_of_entries
    (normalRecoveryAt h v) ((polynomialJacobianAt h v) *ᵥ w)
    hB (hentry v hv)
  rw [hid, norm_smul, Real.norm_of_nonneg
    (le_of_lt (hd.trans_le (hdet v hv)))] at hnorm
  have hbase : d * ‖w‖ ≤
      (m : ℝ) * B * ‖(polynomialJacobianAt h v) *ᵥ w‖ :=
    (mul_le_mul_of_nonneg_right (hdet v hv) (norm_nonneg _)).trans hnorm
  dsimp [sigma]
  rw [div_mul_eq_mul_div]
  calc
    d * ‖w‖ / D ≤
        ((m : ℝ) * B * ‖(polynomialJacobianAt h v) *ᵥ w‖) / D :=
      div_le_div_of_nonneg_right hbase hD.le
    _ ≤ ‖(polynomialJacobianAt h v) *ᵥ w‖ := by
      apply (div_le_iff₀ hD).2
      dsimp [D]
      nlinarith [norm_nonneg ((polynomialJacobianAt h v) *ᵥ w),
        mul_nonneg (Nat.cast_nonneg m) hB]

end CQCInternal
end OptimalConvergenceRates

end
