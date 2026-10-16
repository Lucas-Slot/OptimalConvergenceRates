import OptimalConvergenceRates.CQC.EqualityTransfer
import OptimalConvergenceRates.QuarticConvergence.MainResults
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.OrderConventions

/-! # Quartic Putinar rate with encoded equalities -/

noncomputable section
open MvPolynomial
namespace OptimalConvergenceRates
namespace CQCInternal
open GeneralArchimedean
variable {n m : ℕ}

theorem putinarQuarticRateWithEqualities_internal
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : CQCWithEqualities g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r := by
  obtain ⟨P, a, c, Clog, s, hc, hClog, hP, _hPdegree, ha, _hPzero, htransfer⟩ :=
    exists_fixedInstanceTransferWithEqualities_raw hn hne harch hcqc hp
  let d := generatorDegree g
  have hd : 0 < d := by simpa only [d] using generatorDegree_pos g
  have hnm : 0 < n + m := by omega
  obtain ⟨Acube, ccube, hAcube, hccube, hcube⟩ :=
    QuarticConvergence.putinarCubeQuarticRate_membership hnm
  let D := P.totalDegree
  let E : ℝ := Acube * ((max D 1 : ℕ) : ℝ) ^ 6 * polySupNorm P
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg hAcube.le (pow_nonneg (by positivity) 6))
      (polySupNorm_nonneg P)
  let B : ℝ := max 1 (c * E)
  have hB : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  let K : ℕ := Nat.ceil (Clog * (5 + Real.log c)) + 1
  have hK : 0 < K := by simp [K]
  let L : ℕ := s + d + K
  have hL : 0 < L := by dsimp [L]; omega
  obtain ⟨q₀, hq₀⟩ := exists_nat_gt
    (max (2 * B) (((ccube * max D 1 : ℕ) : ℝ)))
  let qmin : ℕ := max q₀ 1
  have hqmin : 0 < qmin := by dsimp [qmin]; omega
  let r₀ : ℕ := L * qmin
  have hr₀ : 0 < r₀ := Nat.mul_pos hL hqmin
  let A : ℝ := B * (((2 * L : ℕ) : ℝ) ^ 4)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, r₀, hA, hr₀, ?_⟩
  intro r hrr₀
  let q : ℕ := r / L
  have hqminq : qmin ≤ q := by
    apply (Nat.le_div_iff_mul_le hL).2
    simpa only [r₀, Nat.mul_comm] using hrr₀
  have hqpos : 0 < q := hqmin.trans_le hqminq
  have hqone : 1 ≤ q := hqpos
  have hq₀q : q₀ ≤ q := (le_max_left q₀ 1).trans hqminq
  have hcubeOrder : ccube * max D 1 ≤ q := by
    have hreal : (((ccube * max D 1 : ℕ) : ℝ)) < (q₀ : ℝ) :=
      (le_max_right (2 * B) _).trans_lt hq₀
    have hnat : ccube * max D 1 < q₀ := by exact_mod_cast hreal
    exact hnat.le.trans hq₀q
  let epsilon : ℝ := B / (q : ℝ) ^ 4
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hqB : 2 * B < (q : ℝ) := by
    exact (le_max_left (2 * B) _).trans_lt hq₀ |>.trans_le
      (by exact_mod_cast hq₀q)
  have hqpow : (q : ℝ) ≤ (q : ℝ) ^ 4 := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqone
    have hq2 : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hq24 : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((q : ℝ) ^ 2 - q)]
    exact hq2.trans hq24
  have hepsilonHalf : epsilon ≤ 1 / 2 := by
    dsimp [epsilon]
    apply (div_le_iff₀ (by positivity : 0 < (q : ℝ) ^ 4)).2
    nlinarith [hqB.le.trans hqpow]
  have hcubeBase := hcube P D q (by rfl) hP hcubeOrder
  have hBE : E ≤ B / c := by
    apply (le_div_iff₀ hcpos).2
    have hcE : c * E ≤ B := by
      dsimp [B]
      exact le_max_right 1 (c * E)
    simpa [mul_comm] using hcE
  have hboxGap : 0 ≤ epsilon / c - E / (q : ℝ) ^ 4 := by
    dsimp [epsilon]
    have hq4 : 0 ≤ (q : ℝ) ^ 4 := by positivity
    calc
      0 ≤ (B / c - E) / (q : ℝ) ^ 4 := div_nonneg (sub_nonneg.mpr hBE) hq4
      _ = B / (q : ℝ) ^ 4 / c - E / (q : ℝ) ^ 4 := by field_simp
  have hboxConst := QuarticConvergence.nonneg_const_mem_BoxQuadraticModule
    hboxGap (n + m) q
  have hbox : P + C (epsilon / c) ∈ BoxQuadraticModule (n + m) q := by
    have hsum := BoxQuadraticModule_add hcubeBase hboxConst
    have hC : (C (epsilon / c) : MvPolynomial (Fin (n + m)) ℝ) =
        C (E / (q : ℝ) ^ 4) + C (epsilon / c - E / (q : ℝ) ^ 4) := by
      rw [← map_add]
      congr 1
      ring
    rw [hC]
    simpa only [add_assoc] using hsum
  have hbaseCert : p + C epsilon ∈ GenQuadraticModule g
      ((s + d * q) + Nat.ceil (Clog * (1 + Real.log (c / epsilon)))) := by
    simpa only [d] using htransfer hepsilon hepsilonHalf hbox
  have hratioPos : 0 < c / B := div_pos hcpos hBpos
  have hratioLe : c / B ≤ c := by
    apply (div_le_iff₀ hBpos).2
    nlinarith [mul_le_mul_of_nonneg_left hB hcpos.le]
  have hlogRatio : Real.log (c / B) ≤ Real.log c :=
    Real.log_le_log hratioPos hratioLe
  have hlogq : Real.log (q : ℝ) ≤ (q : ℝ) :=
    Real.log_le_self hqreal.le
  have hquotient : c / epsilon = (c / B) * (q : ℝ) ^ 4 := by
    dsimp [epsilon]
    field_simp
  have hlogFormula : Real.log (c / epsilon) =
      Real.log (c / B) + 4 * Real.log (q : ℝ) := by
    rw [hquotient, Real.log_mul hratioPos.ne' (pow_ne_zero 4 hqreal.ne'),
      Real.log_pow]
    norm_num
  have hlogBound : 1 + Real.log (c / epsilon) ≤
      (5 + Real.log c) * (q : ℝ) := by
    rw [hlogFormula]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqone
    nlinarith
  have hceilBound : Nat.ceil (Clog * (1 + Real.log (c / epsilon))) ≤ K * q := by
    apply Nat.ceil_le.mpr
    calc
      Clog * (1 + Real.log (c / epsilon)) ≤
          Clog * ((5 + Real.log c) * (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogBound hClog.le
      _ = (Clog * (5 + Real.log c)) * (q : ℝ) := by ring
      _ ≤ (Nat.ceil (Clog * (5 + Real.log c)) : ℝ) * (q : ℝ) := by
        gcongr
        exact Nat.le_ceil _
      _ ≤ ((K * q : ℕ) : ℝ) := by
        norm_cast
        exact Nat.mul_le_mul_right q (by dsimp [K]; omega)
  have hcertificateOrder :
      (s + d * q) + Nat.ceil (Clog * (1 + Real.log (c / epsilon))) ≤ L * q := by
    calc
      (s + d * q) + Nat.ceil (Clog * (1 + Real.log (c / epsilon))) ≤
          (s + d * q) + K * q := Nat.add_le_add_left hceilBound _
      _ ≤ (s * q + d * q) + K * q := by
        have hs : s ≤ s * q := by
          simpa using Nat.mul_le_mul_left s hqone
        exact Nat.add_le_add_right (Nat.add_le_add_right hs (d * q)) (K * q)
      _ = (s + d + K) * q := by simp only [Nat.add_mul]
      _ = L * q := by rfl
  have hfloorOrder : L * q ≤ r := by
    have hfloor := Nat.div_mul_le_self r L
    simpa only [q, Nat.mul_comm] using hfloor
  have hcertAtR : p + C epsilon ∈ GenQuadraticModule g r :=
    GenQuadraticModule_mono (hcertificateOrder.trans hfloorOrder) hbaseCert
  have hrlt : r < L * (q + 1) := by
    simpa only [q] using Nat.lt_mul_div_succ r hL
  have hqdouble : q + 1 ≤ 2 * q := by omega
  have hrle : r ≤ 2 * L * q := by
    exact (Nat.le_of_lt hrlt).trans <| by
      calc
        L * (q + 1) ≤ L * (2 * q) := Nat.mul_le_mul_left L hqdouble
        _ = 2 * L * q := by
          simp only [Nat.mul_comm, Nat.mul_left_comm]
  have hrpos : 0 < r := hr₀.trans_le hrr₀
  have hrleReal : (r : ℝ) ≤ ((2 * L * q : ℕ) : ℝ) := by exact_mod_cast hrle
  have hpow : (r : ℝ) ^ 4 ≤ (((2 * L : ℕ) : ℝ) ^ 4) * (q : ℝ) ^ 4 := by
    calc
      (r : ℝ) ^ 4 ≤ (((2 * L * q : ℕ) : ℝ) ^ 4) :=
        pow_le_pow_left₀ (by positivity) hrleReal 4
      _ = (((2 * L : ℕ) : ℝ) ^ 4) * (q : ℝ) ^ 4 := by
        push_cast
        ring
  have hepsilonTarget : epsilon ≤ A / (r : ℝ) ^ 4 := by
    dsimp [epsilon, A]
    apply (div_le_div_iff₀ (by positivity : 0 < (q : ℝ) ^ 4)
      (by positivity : 0 < (r : ℝ) ^ 4)).2
    calc
      B * (r : ℝ) ^ 4 ≤ B * ((((2 * L : ℕ) : ℝ) ^ 4) * (q : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hpow hBpos.le
      _ = B * (((2 * L : ℕ) : ℝ) ^ 4) * (q : ℝ) ^ 4 := by ring
  have hgap := genQuadraticModule_C_nonneg g
    (sub_nonneg.mpr hepsilonTarget)
  have hsum := genQuadraticModule_add hcertAtR hgap
  have hC : (C (A / (r : ℝ) ^ 4) : MvPolynomial (Fin n) ℝ) =
      C epsilon + C (A / (r : ℝ) ^ 4 - epsilon) := by
    rw [← map_add]
    congr 1
    ring
  rw [hC]
  simpa only [add_assoc, max_eq_left (Nat.zero_le r)] using hsum

end CQCInternal
end OptimalConvergenceRates
end
