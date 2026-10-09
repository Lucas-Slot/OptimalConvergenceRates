import OptimalConvergenceRates.GeneralArchimedean.SharpExample.CertificateMomentObstruction

noncomputable section
open MvPolynomial
open OptimalConvergenceRates

namespace OptimalConvergenceRates.GeneralArchimedean

theorem sharpRestrictedTauEnvelope_upper {t : Real} {r : Nat}
    (ht0 : 0 < t) (ht1 : t <= 1) (hr : 1 <= r) :
    sharpRestrictedTauEnvelope t r <=
      Real.exp (19 + 2 * Real.log (r : Real) +
        5 * Real.log (1 / t) + 100 * (r : Real) * Real.sqrt t) := by
  have hrR : (1 : Real) <= (r : Real) := by exact_mod_cast hr
  have hr0 : (0 : Real) < (r : Real) := lt_of_lt_of_le (by norm_num) hrR
  have ht4pos : 0 < t ^ 4 := pow_pos ht0 _
  have ht2le : t ^ 2 <= 1 := by
    nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht1)]
  have ht4le : t ^ 4 <= 1 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2le)]
  have hX : (1 : Real) <= (r : Real) ^ 2 / t ^ 4 := by
    rw [le_div_iff₀ ht4pos]
    nlinarith [sq_nonneg ((r : Real) - 1)]
  have he8 : (8 : Real) <= Real.exp 8 := by
    linarith [Real.add_one_le_exp (8 : Real)]
  have he14four : (4 : Real) <= Real.exp 14 := by
    linarith [Real.add_one_le_exp (14 : Real)]
  have he3two : (2 : Real) <= Real.exp 3 := by
    linarith [Real.add_one_le_exp (3 : Real)]
  have h8e6 : (8 : Real) * Real.exp 6 <= Real.exp 14 := by
    calc
      (8 : Real) * Real.exp 6 <= Real.exp 8 * Real.exp 6 :=
        mul_le_mul_of_nonneg_right he8 (Real.exp_pos _).le
      _ = Real.exp 14 := by rw [← Real.exp_add]; norm_num
  have hconst : (4 : Real) + 8 * Real.exp 6 <= Real.exp 17 := by
    calc
      (4 : Real) + 8 * Real.exp 6 <= 2 * Real.exp 14 := by
        nlinarith
      _ <= Real.exp 3 * Real.exp 14 :=
        mul_le_mul_of_nonneg_right he3two (Real.exp_pos _).le
      _ = Real.exp 17 := by rw [← Real.exp_add]; norm_num
  have hslab : sharpSlabEnvelope t r <=
      Real.exp 17 * (r : Real) ^ 2 / t ^ 4 := by
    unfold sharpSlabEnvelope
    calc
      2 + 8 * Real.exp 6 * (r : Real) ^ 2 + 2 / t ^ 4 <=
          (4 + 8 * Real.exp 6) * ((r : Real) ^ 2 / t ^ 4) := by
        have hdivR : (r : Real) ^ 2 <= (r : Real) ^ 2 / t ^ 4 := by
          rw [le_div_iff₀ ht4pos]
          nlinarith [sq_nonneg (r : Real)]
        have hdivTwo : 2 / t ^ 4 <= 2 * ((r : Real) ^ 2 / t ^ 4) := by
          calc
            2 / t ^ 4 = 2 * (1 / t ^ 4) := by ring
            _ <= 2 * ((r : Real) ^ 2 * (1 / t ^ 4)) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              calc
                1 / t ^ 4 = 1 * (1 / t ^ 4) := by ring
                _ <= (r : Real) ^ 2 * (1 / t ^ 4) :=
                  mul_le_mul_of_nonneg_right (by
                    nlinarith [sq_nonneg ((r : Real) - 1)]) (by positivity)
            _ = 2 * ((r : Real) ^ 2 / t ^ 4) := by ring
        nlinarith [mul_le_mul_of_nonneg_left hdivR
          (show 0 <= 8 * Real.exp 6 by positivity)]
      _ <= Real.exp 17 * ((r : Real) ^ 2 / t ^ 4) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = Real.exp 17 * (r : Real) ^ 2 / t ^ 4 := by ring
  have he2 : (2 : Real) <= Real.exp 2 := by
    linarith [Real.add_one_le_exp (2 : Real)]
  unfold sharpRestrictedTauEnvelope sharpNegativeSlabEnvelope
  calc
    (2 / t) * (Real.exp (100 * (r : Real) * Real.sqrt t) *
        sharpSlabEnvelope t r) <=
        (2 / t) * (Real.exp (100 * (r : Real) * Real.sqrt t) *
          (Real.exp 17 * (r : Real) ^ 2 / t ^ 4)) := by
      gcongr
    _ <= (Real.exp 2 / t) *
        (Real.exp (100 * (r : Real) * Real.sqrt t) *
          (Real.exp 17 * (r : Real) ^ 2 / t ^ 4)) := by
      gcongr
    _ = Real.exp (19 + 2 * Real.log (r : Real) +
        5 * Real.log (1 / t) + 100 * (r : Real) * Real.sqrt t) := by
      have harg :
          19 + 2 * Real.log (r : Real) + 5 * Real.log (1 / t) +
              100 * (r : Real) * Real.sqrt t =
            2 + 17 + Real.log ((r : Real) ^ 2) +
              Real.log ((1 / t)^5) + 100 * (r : Real) * Real.sqrt t := by
        rw [Real.log_pow, Real.log_pow]
        norm_num
      rw [harg]
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
      rw [Real.exp_log (pow_pos hr0 2),
        Real.exp_log (pow_pos (show 0 < (1 / t : Real) by positivity) 5)]
      field_simp

theorem sharpMomentRhs_upper {t : Real} {r D : Nat}
    (ht0 : 0 < t) (ht1 : t <= 1) (hr : 3 <= r) (hD : 1 <= D) :
    24 * ((2 * D + 1 : Nat) : Real) ^ 2 *
        ((2 * r + 1 : Nat) : Real) ^ 2 * sharpRestrictedTauEnvelope t r *
          Real.exp (16 - 16 * (D : Real) ^ 2) <=
      Real.exp (100 * (r : Real) * Real.sqrt t + 4 * (D : Real) +
        6 * Real.log (r : Real) + 5 * Real.log (1 / t) + 59 -
          16 * (D : Real) ^ 2) := by
  have hrOne : 1 <= r := by omega
  have hrR : (3 : Real) <= (r : Real) := by exact_mod_cast hr
  have hr0 : (0 : Real) < (r : Real) := by linarith
  have hDR : (1 : Real) <= (D : Real) := by exact_mod_cast hD
  have hDlin : 2 * (D : Real) + 1 <= Real.exp (2 * (D : Real)) :=
    Real.add_one_le_exp _
  have hDbound : ((2 * D + 1 : Nat) : Real) ^ 2 <=
      Real.exp (4 * (D : Real)) := by
    calc
      ((2 * D + 1 : Nat) : Real) ^ 2 = (2 * (D : Real) + 1) ^ 2 := by norm_num
      _ <= (Real.exp (2 * (D : Real))) ^ 2 := by gcongr
      _ = Real.exp (4 * (D : Real)) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
  have hrQuad : 2 * (r : Real) + 1 <= (r : Real) ^ 2 := by
    nlinarith [sq_nonneg ((r : Real) - 3)]
  have hrExp : (r : Real) ^ 4 = Real.exp (4 * Real.log (r : Real)) := by
    symm
    rw [show 4 * Real.log (r : Real) = Real.log ((r : Real) ^ 4) by
      rw [Real.log_pow]; norm_num]
    exact Real.exp_log (pow_pos hr0 4)
  have hrbound : ((2 * r + 1 : Nat) : Real) ^ 2 <=
      Real.exp (4 * Real.log (r : Real)) := by
    calc
      ((2 * r + 1 : Nat) : Real) ^ 2 = (2 * (r : Real) + 1) ^ 2 := by norm_num
      _ <= ((r : Real) ^ 2) ^ 2 := by gcongr
      _ = (r : Real) ^ 4 := by ring
      _ = Real.exp (4 * Real.log (r : Real)) := hrExp
  have h24 : (24 : Real) <= Real.exp 24 := by
    linarith [Real.add_one_le_exp (24 : Real)]
  have henv0 : 0 <= sharpRestrictedTauEnvelope t r := by
    unfold sharpRestrictedTauEnvelope sharpNegativeSlabEnvelope
      sharpSlabEnvelope
    positivity
  have henv := sharpRestrictedTauEnvelope_upper ht0 ht1 hrOne
  calc
    24 * ((2 * D + 1 : Nat) : Real) ^ 2 *
        ((2 * r + 1 : Nat) : Real) ^ 2 * sharpRestrictedTauEnvelope t r *
          Real.exp (16 - 16 * (D : Real) ^ 2) <=
      Real.exp 24 * Real.exp (4 * (D : Real)) *
        Real.exp (4 * Real.log (r : Real)) *
        Real.exp (19 + 2 * Real.log (r : Real) +
          5 * Real.log (1 / t) + 100 * (r : Real) * Real.sqrt t) *
        Real.exp (16 - 16 * (D : Real) ^ 2) := by gcongr
    _ = Real.exp (100 * (r : Real) * Real.sqrt t + 4 * (D : Real) +
        6 * Real.log (r : Real) + 5 * Real.log (1 / t) + 59 -
          16 * (D : Real) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
end OptimalConvergenceRates.GeneralArchimedean

namespace OptimalConvergenceRates.GeneralArchimedean

set_option maxHeartbeats 800000 in
-- The floor choice uses several large nonlinear normalizations.

/-- The floor choice used in the signed-moment argument. -/
theorem sharpChooseMomentOrder {t : Real} {r : Nat}
    (ht0 : 0 < t) (ht1 : t <= 1) (hr : 3 <= r)
    (hL : (100000 : Real) <= Real.log (r : Real))
    (hu : (r : Real) * Real.sqrt t <=
      Real.log (r : Real) ^ 2 / 100000000)
    (hBsmall : (8 : Real) * (r : Real) ^ 3 * t ^ 2 <= 1) :
    ∃ D : Nat, 1 <= D /\
      t ^ 4 * Real.exp (32 * (D : Real) + 16) <= (1 : Real) / 12 /\
      (8 : Real) * (r : Real) ^ 2 * t ^ 2 <=
        Real.exp (-((32 : Real) * (D : Real) + 32)) /\
      100 * (r : Real) * Real.sqrt t + 4 * (D : Real) +
        6 * Real.log (r : Real) + 5 * Real.log (1 / t) + 59 -
          16 * (D : Real) ^ 2 < 0 := by
  let R : Real := r
  let L : Real := Real.log R
  let B : Real := 8 * R^2 * t ^ 2
  let A : Real := Real.log (1 / B)
  let D : Nat := ⌊A / 64⌋₊
  have hR3 : (3 : Real) <= R := by
    change (3 : Real) <= (r : Real)
    exact_mod_cast hr
  have hR0 : 0 < R := by linarith
  have hLbig : (100000 : Real) <= L := by simpa [L, R] using hL
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hLbig
  have hB0 : 0 < B := by unfold B; positivity
  have hBR : B * R <= 1 := by
    calc
      B * R = 8 * R^3 * t ^ 2 := by unfold B; ring
      _ <= 1 := by simpa [R] using hBsmall
  have hRinvB : R <= 1 / B := by
    rw [le_div_iff₀ hB0]
    simpa [mul_comm] using hBR
  have hLA : L <= A := by
    unfold A
    exact Real.log_le_log hR0 hRinvB
  have hAbig : (100000 : Real) <= A := hLbig.trans hLA
  have hA0 : 0 <= A := le_trans (by norm_num) hAbig
  have hDupper : (D : Real) <= A / 64 := by
    exact Nat.floor_le (div_nonneg hA0 (by norm_num))
  have hDstrict : A / 64 < (D : Real) + 1 := by
    exact Nat.lt_floor_add_one (A / 64)
  have hDlower : A / 128 <= (D : Real) := by
    nlinarith
  have hD : 1 <= D := by
    exact_mod_cast (show (1 : Real) <= (D : Real) by nlinarith)
  have hlog8 : Real.log 8 <= 7 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 8 by norm_num)
    norm_num at h
    exact h
  have hAid : A = 2 * Real.log (1 / t) - 2 * L - Real.log 8 := by
    calc
      A = -Real.log B := by unfold A; rw [one_div, Real.log_inv]
      _ = -(Real.log 8 + Real.log (R^2) + Real.log (t ^ 2)) := by
        unfold B
        rw [Real.log_mul (by positivity : (8 * R^2 : Real) ≠ 0)
          (by positivity : t ^ 2 ≠ 0),
          Real.log_mul (by norm_num : (8 : Real) ≠ 0)
            (by positivity : R^2 ≠ 0)]
      _ = 2 * Real.log (1 / t) - 2 * L - Real.log 8 := by
        rw [Real.log_pow, Real.log_pow, one_div, Real.log_inv]
        norm_num
        dsimp [L]
        ring
  have hT : Real.log (1 / t) <= 2 * A := by
    have hlog8A : Real.log 8 <= A := hlog8.trans (by linarith)
    nlinarith [hAid]
  have hC : (32 : Real) * (D : Real) + 32 <= A := by
    nlinarith
  have hbase : (8 : Real) * (r : Real) ^ 2 * t ^ 2 <=
      Real.exp (-((32 : Real) * (D : Real) + 32)) := by
    have hBexp : B = Real.exp (-A) := by
      unfold A
      rw [one_div, Real.log_inv, neg_neg, Real.exp_log hB0]
    change B <= _
    rw [hBexp, Real.exp_le_exp]
    linarith
  have hBE : B * Real.exp ((32 : Real) * (D : Real) + 32) <= 1 := by
    calc
      B * Real.exp ((32 : Real) * (D : Real) + 32) <=
          Real.exp (-((32 : Real) * (D : Real) + 32)) *
            Real.exp ((32 : Real) * (D : Real) + 32) := by
        exact mul_le_mul_of_nonneg_right (by simpa [B, R] using hbase)
          (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hratio : t ^ 2 /
      (8 * R^2 * Real.exp 16) <= (1 : Real) / 12 := by
    have ht2 : t ^ 2 <= 1 := by
      nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht1)]
    have hden : (12 : Real) <= 8 * R^2 * Real.exp 16 := by
      have he16 : (17 : Real) <= Real.exp 16 := by
        have h := Real.add_one_le_exp (16 : Real)
        norm_num at h ⊢
        exact h
      have hR2 : (9 : Real) <= R^2 := by
        nlinarith [sq_nonneg (R - 3)]
      calc
        (12 : Real) <= 8 * 9 * 17 := by norm_num
        _ <= 8 * R^2 * 17 := by gcongr
        _ <= 8 * R^2 * Real.exp 16 := by gcongr
    rw [div_le_iff₀ (by positivity : 0 < 8 * R^2 * Real.exp 16)]
    nlinarith
  have hsmall : t ^ 4 * Real.exp (32 * (D : Real) + 16) <=
      (1 : Real) / 12 := by
    calc
      t ^ 4 * Real.exp (32 * (D : Real) + 16) =
          t ^ 4 * (Real.exp (32 * (D : Real) + 32) / Real.exp 16) := by
        rw [← Real.exp_sub]
        congr 2; ring
      _ = (B * Real.exp (32 * (D : Real) + 32)) *
            (t ^ 2 / (8 * R^2 * Real.exp 16)) := by
        unfold B
        field_simp
      _ <= 1 * (t ^ 2 / (8 * R^2 * Real.exp 16)) := by
        exact mul_le_mul_of_nonneg_right hBE (by positivity)
      _ <= (1 : Real) / 12 := by simpa using hratio
  have hLsq : L^2 <= A^2 := by nlinarith
  have huA : 100 * R * Real.sqrt t <= A^2 / 1000000 := by
    have huL : R * Real.sqrt t <= L^2 / 100000000 := by
      simpa [R, L] using hu
    nlinarith
  have hlinear : 4 * (D : Real) + 6 * L +
      5 * Real.log (1 / t) + 59 <= 18 * A := by
    nlinarith [hlog8]
  have hquad : A^2 / 1024 <= 16 * (D : Real) ^ 2 := by
    nlinarith [sq_nonneg ((D : Real) - A / 128)]
  have hAlinear : 18 * A <= A^2 / 5000 := by
    nlinarith [mul_nonneg hA0 (sub_nonneg.mpr (show (90000 : Real) <= A by
      linarith))]
  have hnegative : 100 * R * Real.sqrt t + 4 * (D : Real) +
      6 * L + 5 * Real.log (1 / t) + 59 - 16 * (D : Real) ^ 2 < 0 := by
    have hcoeffPos : 0 < (1 : Real) / 1024 -
        (1 / 1000000 + 1 / 5000) := by
      norm_num
    have hA2pos : 0 < A^2 := sq_pos_of_pos
      (lt_of_lt_of_le (by norm_num) hAbig)
    nlinarith [sq_nonneg A, mul_pos hA2pos hcoeffPos]
  refine ⟨D, hD, ?_, ?_, ?_⟩
  · exact hsmall
  · simpa [R] using hbase
  · simpa [R, L] using hnegative

/-- Under the three elementary large-order inequalities, a perturbation
certificate is incompatible with the signed-moment obstruction. -/
theorem sharpNoSmallCertificate
    {eps : Real} {r : Nat} (hr : 3 <= r) (heps : 0 < eps)
    (htsmall : 2 * eps <= (1 : Real) / 64)
    (hL : (100000 : Real) <= Real.log (r : Real))
    (hu : (r : Real) * Real.sqrt (2 * eps) <=
      Real.log (r : Real) ^ 2 / 100000000)
    (hBsmall : (8 : Real) * (r : Real) ^ 3 * (2 * eps) ^ 2 <= 1)
    (hcert : sharpArchimedeanObjective + MvPolynomial.C eps ∈
      GenQuadraticModule sharpArchimedeanGenerators r) : False := by
  have ht0 : 0 < 2 * eps := by positivity
  have ht1 : 2 * eps <= 1 := htsmall.trans (by norm_num)
  obtain ⟨D, hD, hsmall, hbase, hnegative⟩ :=
    sharpChooseMomentOrder ht0 ht1 hr hL hu hBsmall
  have hobs := sharpCertificate_moment_obstruction (r := r) (D := D)
    (by omega) heps htsmall hcert hD (by
      convert hsmall using 1; ring) hbase
  have hupp := sharpMomentRhs_upper (t := 2 * eps) (r := r) (D := D)
    ht0 ht1 hr hD
  have hexp : Real.exp
      (100 * (r : Real) * Real.sqrt (2 * eps) + 4 * (D : Real) +
        6 * Real.log (r : Real) + 5 * Real.log (1 / (2 * eps)) + 59 -
          16 * (D : Real) ^ 2) < 1 := by
    calc
      _ < Real.exp 0 := (Real.exp_lt_exp).2 hnegative
      _ = 1 := Real.exp_zero
  linarith

end OptimalConvergenceRates.GeneralArchimedean

end
