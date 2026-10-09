/-
  Dimension-free second-derivative control for polynomial vectors whose
  amplitude grows only linearly away from the origin.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.EvenTail
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Common.VectorPolynomialEstimates
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.VectorMarkov

noncomputable section

open Polynomial Finset

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

private theorem evenTail_vector_bound
    {N D : ℕ} {A B y : ℝ} (hD : 2 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (P : Fin N → Polynomial ℝ) (hdegree : ∀ i, (P i).natDegree ≤ D)
    (hbound : ∀ s : ℝ, |s| ≤ 1 →
      interiorVecNorm (fun i ↦ (P i).eval s) ≤ A * |s| + B)
    (hyLower : ((D : ℝ)⁻¹) ^ 2 ≤ y) (hyUpper : y ≤ 1) :
    interiorVecNorm (fun i ↦ (evenTail (P i)).eval y) ≤
      (D : ℝ) * A + 2 * (D : ℝ) ^ 2 * B := by
  let s := Real.sqrt y
  have hDR : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hD)
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity : 0 < ((D : ℝ)⁻¹) ^ 2) hyLower
  have hs0 : 0 ≤ s := Real.sqrt_nonneg y
  have hsSq : s ^ 2 = y := Real.sq_sqrt hy0.le
  have hs1 : |s| ≤ 1 := by
    rw [abs_of_nonneg hs0]
    nlinarith [sq_nonneg (s - 1)]
  have hminusS1 : |-s| ≤ 1 := by simpa using hs1
  have hPzero := hbound 0 (by norm_num)
  have hPzero' : interiorVecNorm (fun i ↦ (P i).eval 0) ≤ B := by
    simpa using hPzero
  have hPs := hbound s hs1
  have hPminus := hbound (-s) hminusS1
  have heven :
      interiorVecNorm (fun i ↦ ((P i).eval s + (P i).eval (-s)) / 2) ≤
        A * s + B := by
    have hadd := interiorVecNorm_add_le
      (fun i ↦ (P i).eval s) (fun i ↦ (P i).eval (-s))
    have hscale := interiorVecNorm_smul_abs (N := N) ((2 : ℝ)⁻¹)
      (fun i ↦ (P i).eval s + (P i).eval (-s))
    have heq :
        interiorVecNorm (fun i ↦ ((P i).eval s + (P i).eval (-s)) / 2) =
          (2 : ℝ)⁻¹ * interiorVecNorm
            (fun i ↦ (P i).eval s + (P i).eval (-s)) := by
      rw [show (fun i ↦ ((P i).eval s + (P i).eval (-s)) / 2) =
          fun i ↦ (2 : ℝ)⁻¹ * ((P i).eval s + (P i).eval (-s)) by
        funext i; ring]
      simpa using hscale
    rw [heq]
    have hsabs : |s| = s := abs_of_nonneg hs0
    rw [hsabs] at hPs
    have hminusabs : |-s| = s := by rw [abs_neg, hsabs]
    rw [hminusabs] at hPminus
    nlinarith
  have hnumerator :
      interiorVecNorm (fun i ↦
        ((P i).eval s + (P i).eval (-s)) / 2 - (P i).eval 0) ≤
        A * s + 2 * B := by
    exact (interiorVecNorm_sub_le
      (fun i ↦ ((P i).eval s + (P i).eval (-s)) / 2)
      (fun i ↦ (P i).eval 0)).trans (by linarith [heven, hPzero'])
  have hvec : (fun i ↦ (evenTail (P i)).eval y) =
      fun i ↦ y⁻¹ *
        (((P i).eval s + (P i).eval (-s)) / 2 - (P i).eval 0) := by
    funext i
    have htail := evenTail_eval (P i) s
    rw [hsSq] at htail
    field_simp [hy0.ne'] at htail ⊢
    nlinarith
  rw [hvec]
  have hscale := interiorVecNorm_smul_abs (N := N) y⁻¹
    (fun i ↦ ((P i).eval s + (P i).eval (-s)) / 2 - (P i).eval 0)
  rw [hscale, abs_of_nonneg (inv_nonneg.mpr hy0.le)]
  have hfirst :
      y⁻¹ * interiorVecNorm (fun i ↦
        ((P i).eval s + (P i).eval (-s)) / 2 - (P i).eval 0) ≤
        y⁻¹ * (A * s + 2 * B) :=
    mul_le_mul_of_nonneg_left hnumerator (inv_nonneg.mpr hy0.le)
  apply hfirst.trans
  have hsLower : (D : ℝ)⁻¹ ≤ s := by
    have hsqrt := Real.sqrt_le_sqrt hyLower
    rw [show Real.sqrt (((D : ℝ)⁻¹) ^ 2) = (D : ℝ)⁻¹ by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hDR)]] at hsqrt
    exact hsqrt
  have hDs : 1 ≤ (D : ℝ) * s := by
    calc
      1 = (D : ℝ) * (D : ℝ)⁻¹ := by field_simp
      _ ≤ (D : ℝ) * s := mul_le_mul_of_nonneg_left hsLower hDR.le
  have hD2y : 1 ≤ (D : ℝ) ^ 2 * y := by
    rw [← hsSq]
    nlinarith [sq_nonneg ((D : ℝ) * s - 1)]
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hy0).2
  have htermA : 0 ≤ A * s * ((D : ℝ) * s - 1) :=
    mul_nonneg (mul_nonneg hA hs0) (sub_nonneg.mpr hDs)
  have htermB : 0 ≤ 2 * B * ((D : ℝ) ^ 2 * y - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hB) (sub_nonneg.mpr hD2y)
  rw [← hsSq]
  nlinarith

/-- If a polynomial vector of degree at most `D ≥ 2` has norm bounded by
`A|s|+B` on `[-1,1]`, then its second derivative at zero is bounded by
`6DA + 12D²B`.  The constant is independent of the vector dimension. -/
theorem secondDerivative_of_linear_growth
    {N D : ℕ} {A B : ℝ} (hD : 2 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (P : Fin N → Polynomial ℝ) (hdegree : ∀ i, (P i).natDegree ≤ D)
    (hbound : ∀ s : ℝ, |s| ≤ 1 →
      interiorVecNorm (fun i ↦ (P i).eval s) ≤ A * |s| + B) :
    interiorVecNorm (fun i ↦
      (Polynomial.derivative (Polynomial.derivative (P i))).eval 0) ≤
      6 * (D : ℝ) * A + 12 * (D : ℝ) ^ 2 * B := by
  let d : ℕ := D / 2
  let a : ℝ := ((D : ℝ)⁻¹) ^ 2
  let scale : ℝ := 4 * (1 - a)
  let R : Fin N → Polynomial ℝ := fun i ↦ evenTail (P i)
  let S : Fin N → Polynomial ℝ := fun i ↦
    (R i).comp (Polynomial.C scale * Polynomial.X + Polynomial.C a)
  let M : ℝ := (D : ℝ) * A + 2 * (D : ℝ) ^ 2 * B
  let x₀ : ℝ := -a / scale
  let q : ℝ := 2 * (d : ℝ) ^ 2 * a / (1 - a)
  have hDR : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hD)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha4 : a ≤ 1 / 4 := by
    dsimp [a]
    have hDsq : (4 : ℝ) ≤ (D : ℝ) ^ 2 := by
      have htwo : (2 : ℝ) ≤ D := by exact_mod_cast hD
      nlinarith
    rw [inv_pow]
    simpa [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hDsq
  have hOneA : 0 < 1 - a := by linarith
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hRdegree : ∀ i, (R i).natDegree ≤ d := by
    intro i
    exact evenTail_natDegree_le_half (hdegree i)
  have hSdegree : ∀ i, (S i).natDegree ≤ d := by
    intro i
    dsimp [S]
    calc
      ((R i).comp (Polynomial.C scale * Polynomial.X + Polynomial.C a)).natDegree ≤
          (R i).natDegree *
            (Polynomial.C scale * Polynomial.X + Polynomial.C a).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ (R i).natDegree * 1 := by
        apply Nat.mul_le_mul_left
        apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
        · simp
      _ = (R i).natDegree := by omega
      _ ≤ d := hRdegree i
  have hSbound : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 4 →
      interiorVecNorm (fun i ↦ (S i).eval x) ≤ M := by
    intro x hx0 hx4
    let y := a + scale * x
    have hya : a ≤ y := by
      dsimp [y]
      exact le_add_of_nonneg_right (mul_nonneg hscale.le hx0)
    have hy1 : y ≤ 1 := by
      dsimp [y, scale]
      have hmul := mul_le_mul_of_nonneg_left hx4 hscale.le
      dsimp [scale] at hmul
      nlinarith
    have hRbound := evenTail_vector_bound hD hA hB P hdegree hbound hya hy1
    simpa [S, R, M, y, Polynomial.eval_comp, add_comm] using hRbound
  have hcoeff (k : ℕ) :
      interiorVecNorm (fun i ↦ (S i).coeff k) ≤
        (8 : ℝ) ^ k * (d : ℝ) ^ (2 * k) * M :=
    GeneralArchimedean.quarterInterval_vector_coeff S hM hSdegree hSbound
  have hxEval : (fun i ↦ (S i).eval x₀) = fun i ↦ (R i).eval 0 := by
    funext i
    dsimp [S, x₀]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    have hscaleNe : scale ≠ 0 := hscale.ne'
    congr 1
    field_simp
    ring
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hdCast : (d : ℝ) ≤ (D : ℝ) / 2 := by
    have hdNat : 2 * d ≤ D := by
      dsimp [d]
      omega
    have hdReal : (2 : ℝ) * d ≤ D := by exact_mod_cast hdNat
    linarith
  have hDa : (D : ℝ) ^ 2 * a = 1 := by
    dsimp [a]
    field_simp
  have hq23 : q ≤ 2 / 3 := by
    dsimp [q]
    apply (div_le_iff₀ hOneA).2
    have hdSq : (d : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 / 4 := by nlinarith
    have hmain : 2 * (d : ℝ) ^ 2 * a ≤ 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hdSq ha0.le]
    nlinarith
  have hgeom : ∑ k ∈ Finset.range (d + 1), q ^ k ≤ 3 := by
    have hstrong : ∀ n : ℕ, ∑ k ∈ Finset.range n, q ^ k ≤ 3 - 3 * q ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Finset.sum_range_succ, pow_succ]
          have hpow : 0 ≤ q ^ n := pow_nonneg hq0 n
          have hmul := mul_le_mul_of_nonneg_left hq23 hpow
          nlinarith
    have hmain := hstrong (d + 1)
    nlinarith [pow_nonneg hq0 (d + 1)]
  have hterm (k : ℕ) :
      interiorVecNorm (fun i ↦ (S i).coeff k * x₀ ^ k) ≤ q ^ k * M := by
    have hscaleNorm := interiorVecNorm_smul_abs (N := N) (x₀ ^ k)
      (fun i ↦ (S i).coeff k)
    rw [show (fun i ↦ (S i).coeff k * x₀ ^ k) =
        fun i ↦ x₀ ^ k * (S i).coeff k by funext i; ring]
    rw [hscaleNorm]
    calc
      |x₀ ^ k| * interiorVecNorm (fun i ↦ (S i).coeff k) ≤
          |x₀ ^ k| * ((8 : ℝ) ^ k * (d : ℝ) ^ (2 * k) * M) :=
        mul_le_mul_of_nonneg_left (hcoeff k) (abs_nonneg _)
      _ = q ^ k * M := by
        have hx₀abs : |x₀| = a / scale := by
          dsimp [x₀]
          rw [abs_div, abs_neg, abs_of_pos ha0, abs_of_pos hscale]
        rw [abs_pow, hx₀abs]
        have hbase : a / scale * 8 * (d : ℝ) ^ 2 = q := by
          dsimp [q, scale]
          field_simp
          ring
        rw [show (d : ℝ) ^ (2 * k) = ((d : ℝ) ^ 2) ^ k by
          rw [pow_mul]]
        rw [show (a / scale) ^ k * (8 ^ k * ((d : ℝ) ^ 2) ^ k * M) =
            (a / scale * 8 * (d : ℝ) ^ 2) ^ k * M by ring]
        rw [hbase]
  have hevalRange (i : Fin N) :
      (S i).eval x₀ = ∑ k ∈ Finset.range (d + 1), (S i).coeff k * x₀ ^ k :=
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hSdegree i)) x₀
  have hRzero : interiorVecNorm (fun i ↦ (R i).eval 0) ≤ 3 * M := by
    rw [← hxEval]
    rw [show (fun i ↦ (S i).eval x₀) =
        fun i ↦ ∑ k ∈ Finset.range (d + 1), (S i).coeff k * x₀ ^ k by
      funext i; exact hevalRange i]
    calc
      interiorVecNorm (fun i ↦ ∑ k ∈ Finset.range (d + 1),
          (S i).coeff k * x₀ ^ k) ≤
          ∑ k ∈ Finset.range (d + 1),
            interiorVecNorm (fun i ↦ (S i).coeff k * x₀ ^ k) :=
        interiorVecNorm_finset_sum_le_sum_norm _ _
      _ ≤ ∑ k ∈ Finset.range (d + 1), q ^ k * M := by
        exact Finset.sum_le_sum fun k _ ↦ hterm k
      _ = (∑ k ∈ Finset.range (d + 1), q ^ k) * M := by
        rw [Finset.sum_mul]
      _ ≤ 3 * M := mul_le_mul_of_nonneg_right hgeom hM
  have hsecond :
      (fun i ↦ (Polynomial.derivative (Polynomial.derivative (P i))).eval 0) =
        fun i ↦ 2 * (R i).eval 0 := by
    funext i
    exact secondDerivative_eval_zero_eq (P i)
  rw [hsecond]
  rw [interiorVecNorm_smul_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  dsimp [M] at hRzero ⊢
  nlinarith

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
