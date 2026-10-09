import OptimalConvergenceRates.CQC.RegularPenaltyLocal

/-!
# Global error and penalty bounds on a compact convex set
-/

noncomputable section

open MvPolynomial Finset Set Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {N m : ℕ}

theorem norm_sq_le_sum_sq {k : ℕ} (x : Fin k → ℝ) :
    ‖x‖ ^ 2 ≤ ∑ i, (x i) ^ 2 := by
  let S := ∑ i, (x i) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i)
  have hcoord : ∀ i, ‖x i‖ ≤ Real.sqrt S := by
    intro i
    have hi : (x i) ^ 2 ≤ S :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
    have hsqrt := Real.sq_sqrt hS
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (x i), abs_nonneg (x i), Real.sqrt_nonneg S]
  have hnorm : ‖x‖ ≤ Real.sqrt S :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2 hcoord
  have hsqrt := Real.sq_sqrt hS
  nlinarith [norm_nonneg x, Real.sqrt_nonneg S]

theorem sum_sq_le_card_mul_norm_sq {k : ℕ} (x : Fin k → ℝ) :
    (∑ i, (x i) ^ 2) ≤ (k : ℝ) * ‖x‖ ^ 2 := by
  calc
    (∑ i, (x i) ^ 2) ≤ ∑ _i : Fin k, ‖x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at hi
      nlinarith [sq_abs (x i), abs_nonneg (x i), norm_nonneg x]
    _ = (k : ℝ) * ‖x‖ ^ 2 := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

theorem eval_equationSquareSum_eq_zero_iff
    (h : Fin m → MvPolynomial (Fin N) ℝ) (z : Fin N → ℝ) :
    MvPolynomial.eval z (equationSquareSum h) = 0 ↔
      z ∈ polynomialZeroSet h := by
  rw [eval_equationSquareSum]
  constructor
  · intro hsum i
    have hi : (MvPolynomial.eval z (h i)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ sq_nonneg (MvPolynomial.eval z (h j)))).mp hsum i
        (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  · intro hz
    apply Finset.sum_eq_zero
    intro i _
    rw [hz i, zero_pow]
    norm_num

/-- Points at least `tau` from every point of `V`, restricted to `A`. -/
def farFromSet (A V : Set (Fin N → ℝ)) (tau : ℝ) : Set (Fin N → ℝ) :=
  A ∩ ⋂ v ∈ V, {z | tau ≤ ‖z - v‖}

theorem farFromSet_isCompact (A V : Set (Fin N → ℝ)) (tau : ℝ)
    (hA : IsCompact A) : IsCompact (farFromSet A V tau) := by
  apply hA.inter_right
  apply isClosed_biInter
  intro v _
  exact isClosed_le continuous_const
    (continuous_norm.comp (continuous_id.sub continuous_const))

/-- A large Euclidean-nearest displacement is uniformly far, in the product
norm, from every point of the zero set. -/
theorem mem_farFromSet_of_nearest_large
    (hN : 0 < N) (h : Fin m → MvPolynomial (Fin N) ℝ)
    (A : Set (Fin N → ℝ)) {rho : ℝ} (hrho : 0 < rho)
    {z v : Fin N → ℝ} (hz : z ∈ A) (hv : v ∈ polynomialZeroSet h)
    (hvmin : ∀ u ∈ polynomialZeroSet h,
      MvPolynomial.eval v (squaredDistancePolynomial z) ≤
        MvPolynomial.eval u (squaredDistancePolynomial z))
    (hlarge : rho < ‖z - v‖) :
    z ∈ farFromSet A (polynomialZeroSet h) (rho / ((N : ℝ) + 1)) := by
  refine ⟨hz, ?_⟩
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  intro u hu
  by_contra hnot
  have hzu : ‖z - u‖ < rho / ((N : ℝ) + 1) := lt_of_not_ge hnot
  have hvLower : rho ^ 2 <
      MvPolynomial.eval v (squaredDistancePolynomial z) := by
    rw [eval_squaredDistancePolynomial]
    have hnormLower : rho ^ 2 < ‖z - v‖ ^ 2 := by
      nlinarith [norm_nonneg (z - v)]
    have hsumLower : ‖z - v‖ ^ 2 ≤ ∑ i, (v i - z i) ^ 2 := by
      calc
        ‖z - v‖ ^ 2 ≤ ∑ i, ((z - v) i) ^ 2 := norm_sq_le_sum_sq (z - v)
        _ = ∑ i, (v i - z i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [Pi.sub_apply]
          ring
    exact hnormLower.trans_le hsumLower
  have huUpper : MvPolynomial.eval u (squaredDistancePolynomial z) < rho ^ 2 := by
    rw [eval_squaredDistancePolynomial]
    have hupper := sum_sq_le_card_mul_norm_sq (u - z)
    have hnormeq : ‖u - z‖ = ‖z - u‖ := by
      rw [← norm_neg]
      congr 1
      abel
    rw [hnormeq] at hupper
    have htauUpper : (N : ℝ) * (rho / ((N : ℝ) + 1)) ^ 2 < rho ^ 2 := by
      have hden : 0 < (N : ℝ) + 1 := by positivity
      have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      field_simp
      nlinarith [sq_nonneg (N : ℝ)]
    have hsq : ‖z - u‖ ^ 2 < (rho / ((N : ℝ) + 1)) ^ 2 := by
      nlinarith [norm_nonneg (z - u)]
    exact hupper.trans_lt <|
      (mul_lt_mul_of_pos_left hsq (Nat.cast_pos.mpr hN)).trans htauUpper
  exact (not_lt_of_ge (hvmin u hu)) (huUpper.trans hvLower)

/-- The local regular error estimate extends over a compact convex set. -/
theorem exists_global_regular_error_bound
    (hN : 0 < N)
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (A : Set (Fin N → ℝ))
    (hAcompact : IsCompact A) (hAconvex : Convex ℝ A)
    (hVsub : polynomialZeroSet h ⊆ A)
    (hne : (polynomialZeroSet h).Nonempty)
    (hcompact : IsCompact (polynomialZeroSet h))
    (hregular : ∀ v ∈ polynomialZeroSet h,
      LinearIndependent ℝ (fun i ↦ polynomialGradientAt (h i) v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ A,
      ∃ v ∈ polynomialZeroSet h, ∃ coeff : Fin m → ℝ,
        z - v = ∑ i, coeff i • polynomialGradientAt (h i) v ∧
        ‖z - v‖ ^ 2 ≤
          C * MvPolynomial.eval z (equationSquareSum h) := by
  obtain ⟨rho, Clocal, hrho, hClocal, hlocal⟩ :=
    exists_local_regular_error_bound h A hAcompact hAconvex hVsub
      hne hcompact hregular
  let tau := rho / ((N : ℝ) + 1)
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  let D := farFromSet A (polynomialZeroSet h) tau
  have hDcompact : IsCompact D :=
    farFromSet_isCompact A (polynomialZeroSet h) tau hAcompact
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, ∀ x ∈ A, ‖x‖ ≤ R₀ :=
    IsCompact.exists_bound_of_continuousOn
      (f := fun x : Fin N → ℝ ↦ x) hAcompact continuous_id.continuousOn
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hAbound : ∀ x ∈ A, ‖x‖ ≤ R := fun x hx ↦
    (hR₀ x hx).trans (le_max_left _ _)
  by_cases hDne : D.Nonempty
  · obtain ⟨z₀, hz₀, hz₀min⟩ := hDcompact.exists_isMinOn hDne
      (continuous_eval (equationSquareSum h)).continuousOn
    let q := MvPolynomial.eval z₀ (equationSquareSum h)
    have hq : 0 < q := by
      have hq0 : 0 ≤ q := eval_equationSquareSum_nonneg h z₀
      apply hq0.lt_of_ne
      intro hzero
      have hzV : z₀ ∈ polynomialZeroSet h :=
        (eval_equationSquareSum_eq_zero_iff h z₀).mp hzero.symm
      have hzfar : tau ≤ ‖z₀ - z₀‖ := by
        have hfar := hz₀.2
        simp only [Set.mem_iInter, Set.mem_setOf_eq] at hfar
        exact hfar z₀ hzV
      exact (not_le_of_gt htau) (by simpa using hzfar)
    let Cfar := 4 * R ^ 2 / q
    let C := max Clocal Cfar
    have hCfar : 0 ≤ Cfar := by
      dsimp [Cfar]
      positivity
    have hC : 0 ≤ C := hClocal.trans (le_max_left _ _)
    refine ⟨C, hC, ?_⟩
    intro z hz
    obtain ⟨v, hv, coeff, hvmin, hw⟩ :=
      exists_nearestPoint_displacement_eq_gradientCombination
        h hne hcompact hregular z
    refine ⟨v, hv, coeff, hw, ?_⟩
    by_cases hsmall : ‖z - v‖ ≤ rho
    · exact (hlocal z hz v hv coeff hw hsmall).trans <|
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (eval_equationSquareSum_nonneg h z)
    · have hfar : z ∈ D := by
        exact mem_farFromSet_of_nearest_large hN h A hrho hz hv hvmin
          (lt_of_not_ge hsmall)
      have hqle : q ≤ MvPolynomial.eval z (equationSquareSum h) := hz₀min hfar
      have hvA : v ∈ A := hVsub hv
      have hwbound : ‖z - v‖ ≤ 2 * R := by
        calc
          ‖z - v‖ ≤ ‖z‖ + ‖v‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add (hAbound z hz) (hAbound v hvA)
          _ = 2 * R := by ring
      have hwsq : ‖z - v‖ ^ 2 ≤ 4 * R ^ 2 := by
        nlinarith [norm_nonneg (z - v)]
      have haway : ‖z - v‖ ^ 2 ≤
          Cfar * MvPolynomial.eval z (equationSquareSum h) := by
        apply hwsq.trans
        dsimp [Cfar]
        have hfactor : 0 ≤ 4 * R ^ 2 / q := by positivity
        calc
          4 * R ^ 2 = (4 * R ^ 2 / q) * q := by field_simp
          _ ≤ (4 * R ^ 2 / q) * MvPolynomial.eval z (equationSquareSum h) :=
            mul_le_mul_of_nonneg_left hqle hfactor
      exact haway.trans <|
        mul_le_mul_of_nonneg_right (le_max_right _ _)
          (eval_equationSquareSum_nonneg h z)
  · refine ⟨Clocal, hClocal, ?_⟩
    intro z hz
    obtain ⟨v, hv, coeff, hvmin, hw⟩ :=
      exists_nearestPoint_displacement_eq_gradientCombination
        h hne hcompact hregular z
    refine ⟨v, hv, coeff, hw, ?_⟩
    apply hlocal z hz v hv coeff hw
    by_contra hlarge
    apply hDne
    refine ⟨z, ?_⟩
    exact mem_farFromSet_of_nearest_large hN h A hrho hz hv hvmin
      (lt_of_not_ge hlarge)

/-- Full regular-equation quadratic penalty lemma for polynomial equations. -/
theorem exists_regularPolynomialPenalty
    (hN : 0 < N)
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (G : MvPolynomial (Fin N) ℝ)
    (A : Set (Fin N → ℝ))
    (hAcompact : IsCompact A) (hAconvex : Convex ℝ A)
    (hVsub : polynomialZeroSet h ⊆ A)
    (hne : (polynomialZeroSet h).Nonempty)
    (hcompact : IsCompact (polynomialZeroSet h))
    (hregular : ∀ v ∈ polynomialZeroSet h,
      LinearIndependent ℝ (fun i ↦ polynomialGradientAt (h i) v))
    (hGnonneg : ∀ v ∈ polynomialZeroSet h, 0 ≤ MvPolynomial.eval v G)
    (hnormal : ∀ v ∈ polynomialZeroSet h, ∀ i,
      QuarticConvergence.mvPolynomialEvalFDeriv G v
        (polynomialGradientAt (h i) v) = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ A,
      0 ≤ MvPolynomial.eval z
        (G + MvPolynomial.C M * equationSquareSum h) := by
  obtain ⟨C, hC, herror⟩ := exists_global_regular_error_bound hN h A
    hAcompact hAconvex hVsub hne hcompact hregular
  exact exists_regularPolynomialPenalty_of_errorBound h G A hAcompact hAconvex
    hVsub hGnonneg hnormal hC herror

end CQCInternal
end OptimalConvergenceRates

end
