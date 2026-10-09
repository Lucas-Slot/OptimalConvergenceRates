/-
  Conversion from an internal approximation scale to every sufficiently large
  canonical quadratic-module order.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarApproximationAssembly

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A family of quartic approximants at the linear orders `Aq * B * m`
gives an `O(r⁻⁴)` Putinar hierarchy gap at every sufficiently large
canonical total-certificate-degree order `r`.

The harmless factor `2` in the threshold makes `m = r / (Aq * B)` at least
the required degree/root threshold and bounds the floor loss uniformly. -/
theorem lasserre_bound_box_qm_gap_arbitrary_order
    {n Aq B k₀ d r : ℕ} {f : MvPolynomial (Fin n) ℝ} {L : ℝ}
    (hAq : 1 ≤ Aq) (hrepair : HasPutinarDegreeLinearRepair (n := n) Aq)
    (hB : 1 ≤ B) (hk₀ : 1 ≤ k₀) (hL : 0 ≤ L)
    (hfDegree : f.totalDegree ≤ d)
    (happrox : ∀ m, k₀ ≤ m →
      HasQuarticBoxQMApproximationAt
        (f - MvPolynomial.C (polyMin f)) B m L)
    (hr : 2 * (Aq * B) * max d k₀ ≤ r) :
    ∃ ℓ : ℝ,
      lasserre_bound_box_qm f r = (ℓ : WithBot ℝ) ∧
        0 ≤ polyMin f - ℓ ∧
          polyMin f - ℓ ≤
            2 * (2 * ((Aq * B : ℕ) : ℝ)) ^ 4 * L / (r : ℝ) ^ 4 := by
  let q : ℕ := Aq * B
  let m : ℕ := r / q
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
  have hqm : q * m ≤ r := by
    exact Nat.mul_div_le r q
  have hcertificate := centered_quarticBoxQMApproximation_feasible
    hAq hrepair hB hm hL hfDegree hdm (happrox m hk₀m)
  have hcertificateR :
      f - MvPolynomial.C (polyMin f - 2 * (L / (m : ℝ) ^ 4)) ∈
        BoxQuadraticModule n r := by
    apply BoxQuadraticModule_mono _ hcertificate
    simpa only [q, Nat.mul_assoc] using hqm
  obtain ⟨ℓ, hℓ⟩ :=
    exists_real_lasserre_bound_box_qm_of_feasible f r hcertificateR
  have hlower := lasserre_bound_box_qm_ge_feasible f r hcertificateR
  have hupper := lasserre_bound_box_qm_le_polyMin f r
  rw [hℓ, WithBot.coe_le_coe] at hlower hupper
  refine ⟨ℓ, hℓ, by linarith, ?_⟩
  have hgap : polyMin f - ℓ ≤ 2 * L / (m : ℝ) ^ 4 := by
    have herrorForm :
        2 * L / (m : ℝ) ^ 4 = 2 * (L / (m : ℝ) ^ 4) := by ring
    rw [herrorForm]
    linarith
  apply hgap.trans
  have hrlt : r < q * (m + 1) := by
    simpa only [m] using Nat.lt_mul_div_succ r hqpos
  have hrleNat : r ≤ 2 * q * m := by
    have hq_le_qm : q ≤ q * m := by
      simpa only [mul_one] using Nat.mul_le_mul_left q hm
    apply (Nat.le_of_lt hrlt).trans
    calc
      q * (m + 1) = q * m + q := by ring
      _ ≤ q * m + q * m := Nat.add_le_add_left hq_le_qm _
      _ = 2 * q * m := by ring
  have hrle : (r : ℝ) ≤ 2 * (q : ℝ) * (m : ℝ) := by
    exact_mod_cast hrleNat
  have hrposNat : 0 < r := lt_of_lt_of_le
    (Nat.mul_pos (Nat.mul_pos (by omega) hqpos)
      (lt_of_lt_of_le (by omega : 0 < k₀) (le_max_right d k₀))) hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hrposNat
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m from hm)
  have hpow : (r : ℝ) ^ 4 ≤
      (2 * (q : ℝ)) ^ 4 * (m : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r) hrle 4
    calc
      (r : ℝ) ^ 4 ≤ (2 * (q : ℝ) * (m : ℝ)) ^ 4 := this
      _ = (2 * (q : ℝ)) ^ 4 * (m : ℝ) ^ 4 := by ring
  apply (div_le_div_iff₀ (pow_pos hmpos 4) (pow_pos hrpos 4)).2
  have hscaled := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL)
  dsimp only [q] at hscaled ⊢
  convert hscaled using 1; ring

end QuarticConvergence
end OptimalConvergenceRates

end
