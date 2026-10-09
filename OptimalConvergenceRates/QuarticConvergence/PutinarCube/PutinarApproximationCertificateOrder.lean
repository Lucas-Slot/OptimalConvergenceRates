/-
  Arbitrary-order certificate form of quartic Putinar approximation and repair.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarApproximationAssembly

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Approximation plus degree-linear repair gives a certificate at every
sufficiently large canonical order, not merely at orders in an arithmetic
progression.  The factor `(2*q)^4`, where `q = Aq*B`, absorbs the floor in
`m = r/q`. -/
theorem quarticBoxQMApproximation_certificate_arbitrary_order
    {n Aq B k₀ d r : ℕ} {h : MvPolynomial (Fin n) ℝ} {L : ℝ}
    (hAq : 1 ≤ Aq) (hrepair : HasPutinarDegreeLinearRepair (n := n) Aq)
    (hB : 1 ≤ B) (hk₀ : 1 ≤ k₀) (hL : 0 ≤ L)
    (hDegree : h.totalDegree ≤ d)
    (happrox : ∀ m, k₀ ≤ m →
      HasQuarticBoxQMApproximationAt h B m L)
    (hr : 2 * (Aq * B) * max d k₀ ≤ r) :
    h + MvPolynomial.C
        (2 * (2 * (((Aq * B : ℕ) : ℝ))) ^ 4 * L / (r : ℝ) ^ 4) ∈
      BoxQuadraticModule n r := by
  let q : ℕ := Aq * B
  let m : ℕ := r / q
  let small : ℝ := 2 * (L / (m : ℝ) ^ 4)
  let large : ℝ :=
    2 * (2 * (q : ℝ)) ^ 4 * L / (r : ℝ) ^ 4
  have hq : 1 ≤ q := Nat.mul_le_mul hAq hB
  have hqpos : 0 < q := hq
  have hthreshold : q * max d k₀ ≤ r := by
    calc
      q * max d k₀ ≤ q * max d k₀ + q * max d k₀ :=
        Nat.le_add_right _ _
      _ = 2 * q * max d k₀ := by ring
      _ = 2 * (Aq * B) * max d k₀ := by rfl
      _ ≤ r := hr
  have hmThreshold : max d k₀ ≤ m := by
    apply (Nat.le_div_iff_mul_le hqpos).2
    simpa only [Nat.mul_comm] using hthreshold
  have hdm : d ≤ m := (le_max_left d k₀).trans hmThreshold
  have hk₀m : k₀ ≤ m := (le_max_right d k₀).trans hmThreshold
  have hm : 1 ≤ m := hk₀.trans hk₀m
  have hqm : q * m ≤ r := Nat.mul_div_le r q
  have hsmallCertificate : h + MvPolynomial.C small ∈
      BoxQuadraticModule n (q * m) := by
    have hcert := quarticBoxQMApproximation_repaired_mem_of_degree_le_scale
      hAq hrepair hB hm hL hDegree hdm (happrox m hk₀m)
    simpa only [small, q, Nat.mul_assoc] using hcert
  have hsmallCertificateR : h + MvPolynomial.C small ∈
      BoxQuadraticModule n r :=
    BoxQuadraticModule_mono hqm hsmallCertificate
  have hrlt : r < q * (m + 1) := by
    simpa only [m] using Nat.lt_mul_div_succ r hqpos
  have hq_le_qm : q ≤ q * m := by
    simpa only [mul_one] using Nat.mul_le_mul_left q hm
  have hrleNat : r ≤ 2 * q * m := by
    apply (Nat.le_of_lt hrlt).trans
    calc
      q * (m + 1) = q * m + q := by ring
      _ ≤ q * m + q * m := Nat.add_le_add_left hq_le_qm _
      _ = 2 * q * m := by ring
  have hrposNat : 0 < r := lt_of_lt_of_le
    (Nat.mul_pos (Nat.mul_pos (by omega) hqpos)
      (lt_of_lt_of_le (by omega : 0 < k₀) (le_max_right d k₀))) hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hrposNat
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m from hm)
  have hrle : (r : ℝ) ≤ 2 * (q : ℝ) * (m : ℝ) := by
    exact_mod_cast hrleNat
  have hpow : (r : ℝ) ^ 4 ≤
      (2 * (q : ℝ)) ^ 4 * (m : ℝ) ^ 4 := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r) hrle 4
    calc
      (r : ℝ) ^ 4 ≤ (2 * (q : ℝ) * (m : ℝ)) ^ 4 := hp
      _ = (2 * (q : ℝ)) ^ 4 * (m : ℝ) ^ 4 := by ring
  have hsmallLarge : small ≤ large := by
    dsimp only [small, large]
    rw [show 2 * (L / (m : ℝ) ^ 4) = 2 * L / (m : ℝ) ^ 4 by ring]
    apply (div_le_div_iff₀ (pow_pos hmpos 4) (pow_pos hrpos 4)).2
    have hscaled := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL)
    convert hscaled using 1; ring
  have hconstant : MvPolynomial.C (large - small) ∈
      BoxQuadraticModule n r :=
    nonneg_const_mem_BoxQuadraticModule (sub_nonneg.mpr hsmallLarge) n r
  have hadd := BoxQuadraticModule_add hsmallCertificateR hconstant
  have hpoly :
      (h + MvPolynomial.C small) + MvPolynomial.C (large - small) =
        h + MvPolynomial.C large := by
    simp only [map_sub]
    ring
  rw [hpoly] at hadd
  simpa only [large, q] using hadd

end QuarticConvergence
end OptimalConvergenceRates

end
