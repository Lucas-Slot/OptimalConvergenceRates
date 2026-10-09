/-
  From normalized quartic cube approximations to the explicit Putinar rate.

  This module is the final quantitative adapter.  Its sole substantive input
  is a normalized approximation family; the controlled-root analysis supplies
  that input in a separate module.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.LiftRegularity
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarCubeNormalization
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarArbitraryOrder

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Uniform normalized Putinar approximations in a fixed cube dimension.
The order parameter is the repository's canonical total-certificate-degree
order. -/
def HasNormalizedQuarticBoxQMApproximation
    (n B k₀ : ℕ) (L₀ : ℝ) : Prop :=
  ∀ h : MvPolynomial (Fin n) ℝ,
    IsNonnegOn h (Hypercube n) → cubeSphereC6Norm n h ≤ 1 →
      ∀ m, k₀ ≤ m → HasQuarticBoxQMApproximationAt h B m L₀

/-- Homogeneity turns a normalized approximation family into an approximation
for every nonnegative cube polynomial. -/
theorem HasNormalizedQuarticBoxQMApproximation.approximation
    {n B k₀ : ℕ} {L₀ : ℝ} (hn : 0 < n)
    (hfamily : HasNormalizedQuarticBoxQMApproximation n B k₀ L₀)
    (h : MvPolynomial (Fin n) ℝ)
    (hnonnegative : IsNonnegOn h (Hypercube n))
    (m : ℕ) (hm : k₀ ≤ m) :
    HasQuarticBoxQMApproximationAt h B m
      (cubeSphereC6Norm n h * L₀) := by
  apply hasQuarticBoxQMApproximationAt_of_cubeSphereC6Norm_normalized
    hn hnonnegative
  intro hnormNe
  let M : ℝ := cubeSphereC6Norm n h
  have hMnonneg : 0 ≤ M :=
    sphereC6Norm_nonneg (by omega : 0 < 2 * n + 1) (cubeSphereLift n h)
  have hMpos : 0 < M := lt_of_le_of_ne hMnonneg (Ne.symm hnormNe)
  have hnormalizedNonnegative :
      IsNonnegOn (M⁻¹ • h) (Hypercube n) := by
    intro x hx
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
    exact mul_nonneg (inv_nonneg.mpr hMnonneg) (hnonnegative x hx)
  have hlift : cubeSphereLift n (M⁻¹ • h) =
      M⁻¹ • cubeSphereLift n h := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, cubeSphereLift_C]
  have hnormalizedNorm : cubeSphereC6Norm n (M⁻¹ • h) ≤ 1 := by
    unfold cubeSphereC6Norm
    rw [hlift, sphereC6Norm_smul (by omega : 0 < 2 * n + 1),
      abs_of_pos (inv_pos.mpr hMpos)]
    change M⁻¹ * M ≤ 1
    exact le_of_eq (inv_mul_cancel₀ hnormNe)
  exact hfamily (M⁻¹ • h) hnormalizedNonnegative hnormalizedNorm m hm

/-- A normalized quartic approximation family and a degree-linear repair
imply the explicit all-polynomial `O(r⁻⁴)` Putinar hierarchy rate.

The constants `A,c` are fixed before the polynomial, degree bound, and
canonical order, hence depend only on the fixed-dimensional input data. -/
theorem putinarExplicitRate_lasserreGap_of_normalizedApproximation
    {n Aq B k₀ : ℕ} {L₀ : ℝ} (hn : 0 < n)
    (hAq : 1 ≤ Aq) (hrepair : HasPutinarDegreeLinearRepair (n := n) Aq)
    (hB : 1 ≤ B) (hk₀ : 1 ≤ k₀) (hL₀ : 0 < L₀)
    (hfamily : HasNormalizedQuarticBoxQMApproximation n B k₀ L₀) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ ℓ : ℝ,
            lasserre_bound_box_qm p r = (ℓ : WithBot ℝ) ∧
              0 ≤ polyMin p - ℓ ∧
              polyMin p - ℓ ≤
                A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                  (polyMax p - polyMin p) / (r : ℝ) ^ 4 := by
  let q : ℕ := Aq * B
  let A : ℝ :=
    2 * (2 * (q : ℝ)) ^ 4 * L₀ * cubeSphereC6DimensionConstant n
  let c : ℕ := 2 * q * k₀
  have hq : 1 ≤ q := Nat.mul_le_mul hAq hB
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos (by positivity) hL₀)
      (cubeSphereC6DimensionConstant_pos n)
  have hc : 0 < c := by
    dsimp only [c]
    exact Nat.mul_pos (Nat.mul_pos (by omega) hq) (by omega)
  refine ⟨A, c, hA, hc, ?_⟩
  intro p d r hpDegree hr
  let e : ℕ := max d 1
  let h : MvPolynomial (Fin n) ℝ :=
    p - MvPolynomial.C (polyMin p)
  let M : ℝ := cubeSphereC6Norm n h
  let L : ℝ := M * L₀
  have hMnonneg : 0 ≤ M := by
    exact sphereC6Norm_nonneg (by omega : 0 < 2 * n + 1)
      (cubeSphereLift n h)
  have hL : 0 ≤ L := mul_nonneg hMnonneg hL₀.le
  have hthresholdCore : max d k₀ ≤ k₀ * e := by
    apply max_le
    · exact (le_max_left d 1).trans <| by
        simpa only [one_mul] using Nat.mul_le_mul_right e hk₀
    · calc
        k₀ = k₀ * 1 := by omega
        _ ≤ k₀ * e := Nat.mul_le_mul_left k₀ (le_max_right d 1)
  have hthreshold : 2 * (Aq * B) * max d k₀ ≤ r := by
    calc
      2 * (Aq * B) * max d k₀ ≤
          2 * (Aq * B) * (k₀ * e) :=
        Nat.mul_le_mul_left (2 * (Aq * B)) hthresholdCore
      _ = c * e := by
        dsimp only [c, q]
        ring
      _ ≤ r := by simpa only [e] using hr
  have hnonnegative : IsNonnegOn h (Hypercube n) := by
    simpa only [h] using centerAtPolyMin_nonnegative p
  have happrox : ∀ m, k₀ ≤ m →
      HasQuarticBoxQMApproximationAt h B m L := by
    intro m hm
    simpa only [L, M] using
      hfamily.approximation hn h hnonnegative m hm
  obtain ⟨ℓ, hℓ, hgapNonneg, hgap⟩ :=
    lasserre_bound_box_qm_gap_arbitrary_order hAq hrepair hB hk₀ hL
      hpDegree happrox hthreshold
  refine ⟨ℓ, hℓ, hgapNonneg, hgap.trans ?_⟩
  have hregularity :
      M ≤ cubeSphereC6DimensionConstant n * (e : ℝ) ^ 6 *
        (polyMax p - polyMin p) := by
    simpa only [M, h, e] using cubeSphereC6Norm_centered_le hn p hpDegree
  have hcoefficient :
      2 * (2 * (((Aq * B : ℕ) : ℝ))) ^ 4 * L ≤
        A * (e : ℝ) ^ 6 * (polyMax p - polyMin p) := by
    calc
      2 * (2 * (((Aq * B : ℕ) : ℝ))) ^ 4 * L =
          2 * (2 * (q : ℝ)) ^ 4 * (M * L₀) := by
        simp only [L, q]
      _ ≤ 2 * (2 * (q : ℝ)) ^ 4 *
          ((cubeSphereC6DimensionConstant n * (e : ℝ) ^ 6 *
            (polyMax p - polyMin p)) * L₀) := by
        gcongr
      _ = A * (e : ℝ) ^ 6 * (polyMax p - polyMin p) := by
        dsimp only [A]
        ring
  exact div_le_div_of_nonneg_right hcoefficient
    (pow_nonneg (Nat.cast_nonneg r) 4)

end QuarticConvergence
end OptimalConvergenceRates

end
