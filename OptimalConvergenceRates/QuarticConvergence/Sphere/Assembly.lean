/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Assembly.lean

  Algebraic assembly of quartic approximation and degree-linear repair.

  This module packages the conditional intermediate results used by the final sphere theorem.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Defs

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

variable {n : ℕ}

/-- Quartic approximation by ordinary degree-bounded sums of squares. -/
def HasQuarticSOSApproximation (F : MvPolynomial (Fin n) ℝ) (M C : ℝ)
    (b k₀ : ℕ) : Prop :=
  ∀ k, k₀ ≤ k →
    ∃ Q : MvPolynomial (Fin n) ℝ,
      Nonempty (DegreeBoundedSOS Q (b * k)) ∧ sphereSupNorm (F - Q) ≤ C * M / (k : ℝ) ^ 4

/-- Zero as an ordinary SOS with any prescribed square-root degree bound. -/
def DegreeBoundedSOS.zero (n r : ℕ) :
    DegreeBoundedSOS (0 : MvPolynomial (Fin n) ℝ) r where
  N := 1
  P := fun _ ↦ 0
  decomp := by simp
  degree := by simp

/-- Multiplication by a nonnegative real scalar preserves both an SOS witness
and its square-root degree bound. -/
noncomputable def DegreeBoundedSOS.nonnegScale
    {r : ℕ} {Q : MvPolynomial (Fin n) ℝ}
    (hQ : DegreeBoundedSOS Q r) (c : ℝ) (hc : 0 ≤ c) :
    DegreeBoundedSOS (MvPolynomial.C c * Q) r where
  N := hQ.N
  P := fun i ↦ MvPolynomial.C (Real.sqrt c) * hQ.P i
  decomp := by
    calc
      MvPolynomial.C c * Q =
          MvPolynomial.C c * ∑ i : Fin hQ.N, (hQ.P i) ^ 2 := by
            exact congrArg (MvPolynomial.C c * ·) hQ.decomp
      _ = ∑ i : Fin hQ.N,
          (MvPolynomial.C (Real.sqrt c) * hQ.P i) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            simp only [mul_pow, ← MvPolynomial.C_pow]
            rw [Real.sq_sqrt hc]
  degree := by
    intro i
    calc
      (MvPolynomial.C (Real.sqrt c) * hQ.P i).totalDegree ≤
          (MvPolynomial.C (Real.sqrt c)).totalDegree + (hQ.P i).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ r := by simpa using hQ.degree i

/-- Every degree-`D` residual can be repaired at root degree linear in `D`. -/
def HasDegreeLinearRepair (A : ℕ) : Prop :=
  ∀ (D : ℕ) (h : MvPolynomial (Fin n) ℝ),
    1 ≤ D → h.totalDegree ≤ D →
      SphereSOSMod (h + MvPolynomial.C (2 * sphereSupNorm h)) (A * D)

/-- Fixed-resolution certificate assembly from the two substantive interfaces. -/
theorem assembleQuarticCertificateAt
    {F : MvPolynomial (Fin n) ℝ} {M C : ℝ} {A b k₀ d k : ℕ}
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hdeg : F.totalDegree ≤ d)
    (hk : max k₀ (max d 1) ≤ k) (happrox : HasQuarticSOSApproximation F M C b k₀)
    (hrepair : HasDegreeLinearRepair (n := n) A) :
    SphereSOSMod (F + MvPolynomial.C (2 * C * M / (k : ℝ) ^ 4)) (2 * A * b * k) := by
  have hk₀ : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have hdk : d ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right k₀ _)) hk
  have hkpos : 1 ≤ k := le_trans (le_trans (le_max_right d 1) (le_max_right k₀ _)) hk
  obtain ⟨Q, ⟨hQ⟩, herr⟩ := happrox k hk₀
  let h := F - Q
  have hQdeg : Q.totalDegree ≤ 2 * (b * k) := hQ.totalDegree_le_two_mul
  have hk_bk : k ≤ b * k := by
    simpa only [one_mul] using Nat.mul_le_mul_right k hb
  have hbk_two : b * k ≤ 2 * (b * k) := by omega
  have hFdeg : F.totalDegree ≤ 2 * (b * k) :=
    hdeg.trans (hdk.trans (hk_bk.trans hbk_two))
  have hhdeg : h.totalDegree ≤ 2 * (b * k) := by
    exact (MvPolynomial.totalDegree_sub F Q).trans (max_le hFdeg hQdeg)
  have hbkpos : 0 < b * k := Nat.mul_pos (by omega) (by omega)
  have hDpos : 1 ≤ 2 * (b * k) := by omega
  have hrepair' := hrepair (2 * (b * k)) h hDpos hhdeg
  have hrepairCert :
      SphereSOSMod (h + MvPolynomial.C (2 * sphereSupNorm h)) (2 * A * b * k) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hrepair'
  have hQCert : SphereSOSMod Q (2 * A * b * k) := by
    have hbase : SphereSOSMod Q (b * k) :=
      SphereBallTransfers.DegreeBoundedSOS.toSphereSOSMod hQ
    have hfactor : 1 ≤ 2 * A := by omega
    apply hbase.mono
    simpa only [one_mul, Nat.mul_assoc] using Nat.mul_le_mul_right (b * k) hfactor
  have herr' : sphereSupNorm h ≤ C * M / (k : ℝ) ^ 4 := by
    simpa only [h] using herr
  have hextra : 0 ≤ 2 * C * M / (k : ℝ) ^ 4 - 2 * sphereSupNorm h := by
    calc
      0 ≤ 2 * (C * M / (k : ℝ) ^ 4 - sphereSupNorm h) :=
        mul_nonneg (by norm_num) (sub_nonneg.mpr herr')
      _ = 2 * C * M / (k : ℝ) ^ 4 - 2 * sphereSupNorm h := by ring
  have hconst :
      SphereSOSMod
        (MvPolynomial.C (2 * C * M / (k : ℝ) ^ 4 - 2 * sphereSupNorm h) :
          MvPolynomial (Fin n) ℝ)
        (2 * A * b * k) :=
    sphereSOSMod_const hextra
  have hsum := (hrepairCert.add hQCert).add hconst
  convert hsum using 1
  dsimp [h]
  simp only [map_sub]
  ring

/-- At hierarchy orders exactly divisible by the assembly degree factor, the fixed-resolution
estimate has the expected inverse fourth power of the hierarchy order. -/
theorem assembleQuarticCertificateAtDivisibleOrder
    {F : MvPolynomial (Fin n) ℝ} {M C : ℝ} {A b k₀ d k : ℕ}
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hdeg : F.totalDegree ≤ d)
    (hk : max k₀ (max d 1) ≤ k) (happrox : HasQuarticSOSApproximation F M C b k₀)
    (hrepair : HasDegreeLinearRepair (n := n) A) :
    SphereSOSMod
      (F + MvPolynomial.C
        (2 * C * M * (((2 * A * b : ℕ) : ℝ) ^ 4) /
          (((2 * A * b * k : ℕ) : ℝ) ^ 4)))
      (2 * A * b * k) := by
  have hkpos : 0 < k := by
    have : 1 ≤ k := le_trans (le_max_right d 1) ((le_max_right k₀ _).trans hk)
    omega
  have hA0 : (A : ℝ) ≠ 0 := by positivity
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hepsilon :
      2 * C * M * (((2 * A * b : ℕ) : ℝ) ^ 4) /
          (((2 * A * b * k : ℕ) : ℝ) ^ 4) =
        2 * C * M / (k : ℝ) ^ 4 := by
    push_cast
    field_simp [hA0, hb0, hk0]
  rw [hepsilon]
  exact assembleQuarticCertificateAt hA hb hdeg hk happrox hrepair

/-- The fixed-resolution assembly gives an inverse-fourth-power certificate at every
sufficiently large hierarchy order.  Passing from an arbitrary order `r` to the
largest construction order below it costs at most the explicit factor
`(2 * (2 * A * b)) ^ 4`. -/
theorem assembleQuarticCertificateAtArbitraryOrder
    {F : MvPolynomial (Fin n) ℝ} {M C : ℝ} {A b k₀ d r : ℕ}
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hdeg : F.totalDegree ≤ d)
    (hr : (2 * A * b) * max k₀ (max d 1) ≤ r)
    (happrox : HasQuarticSOSApproximation F M C b k₀)
    (hrepair : HasDegreeLinearRepair (n := n) A) :
    SphereSOSMod
      (F + MvPolynomial.C
        (2 * C * M * (((2 * (2 * A * b) : ℕ) : ℝ) ^ 4) / (r : ℝ) ^ 4))
      r := by
  let s : ℕ := 2 * A * b
  let k : ℕ := r / s
  have hs : 0 < s := by
    dsimp [s]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hk :
      max k₀ (max d 1) ≤ k := by
    apply (Nat.le_div_iff_mul_le hs).2
    simpa only [s, Nat.mul_comm] using hr
  have hkpos : 0 < k := by
    have hkone : 1 ≤ k :=
      (le_max_right d 1).trans ((le_max_right k₀ (max d 1)).trans hk)
    omega
  have horder : s * k ≤ r := by
    have hfloor := Nat.div_mul_le_self r s
    simpa only [k, Nat.mul_comm] using hfloor
  have hbase :
      SphereSOSMod (F + MvPolynomial.C (2 * C * M / (k : ℝ) ^ 4)) (s * k) := by
    simpa only [s] using
      assembleQuarticCertificateAt hA hb hdeg hk happrox hrepair
  have hbaseAtR :
      SphereSOSMod (F + MvPolynomial.C (2 * C * M / (k : ℝ) ^ 4)) r :=
    hbase.mono horder
  have hrlt : r < s * (k + 1) := by
    simpa only [k] using Nat.lt_mul_div_succ r hs
  have hkdouble : k + 1 ≤ 2 * k := by omega
  have hnext : s * (k + 1) ≤ 2 * s * k := by
    calc
      s * (k + 1) ≤ s * (2 * k) := Nat.mul_le_mul_left s hkdouble
      _ = 2 * s * k := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]
  have hrle : r ≤ 2 * s * k :=
    (Nat.le_of_lt hrlt).trans hnext
  have hrpos : 0 < r := by
    exact lt_of_lt_of_le (Nat.mul_pos hs hkpos) horder
  have hrleReal : (r : ℝ) ≤ ((2 * s * k : ℕ) : ℝ) := by
    exact_mod_cast hrle
  have hpow :
      (r : ℝ) ^ 4 ≤ (((2 * s : ℕ) : ℝ) ^ 4) * (k : ℝ) ^ 4 := by
    calc
      (r : ℝ) ^ 4 ≤ (((2 * s * k : ℕ) : ℝ) ^ 4) :=
        pow_le_pow_left₀ (by positivity) hrleReal 4
      _ = (((2 * s : ℕ) : ℝ) ^ 4) * (k : ℝ) ^ 4 := by
        push_cast
        ring
  have hepsilon :
      2 * C * M / (k : ℝ) ^ 4 ≤
        2 * C * M * (((2 * s : ℕ) : ℝ) ^ 4) / (r : ℝ) ^ 4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < (k : ℝ) ^ 4)
      (by positivity : 0 < (r : ℝ) ^ 4)).2
    calc
      (2 * C * M) * (r : ℝ) ^ 4 ≤
          (2 * C * M) * ((((2 * s : ℕ) : ℝ) ^ 4) * (k : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (2 * C * M * (((2 * s : ℕ) : ℝ) ^ 4)) * (k : ℝ) ^ 4 := by ring
  have hconst :
      SphereSOSMod
        (MvPolynomial.C
          (2 * C * M * (((2 * s : ℕ) : ℝ) ^ 4) / (r : ℝ) ^ 4 -
            2 * C * M / (k : ℝ) ^ 4) :
          MvPolynomial (Fin n) ℝ)
        r :=
    sphereSOSMod_const (sub_nonneg.mpr hepsilon)
  have hsum := hbaseAtR.add hconst
  convert hsum using 1
  simp only [map_sub]
  ring

end QuarticConvergence
end OptimalConvergenceRates

end
