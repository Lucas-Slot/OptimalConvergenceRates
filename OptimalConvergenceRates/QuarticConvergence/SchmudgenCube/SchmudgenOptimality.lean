/-
  OptimalConvergenceRates/QuarticConvergence/SchmudgenCube/SchmudgenOptimality.lean

  Sharp fixed-objective lower bound for the Schmuedgen hierarchy.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.MainResults

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The first Choi--Lam zero direction lies in the hypercube. -/
theorem choiLamZeroDirection0_mem_hypercube : choiLamZeroDirection0 ∈ Hypercube 4 := by
  rw [Hypercube_mem_iff]
  intro i
  fin_cases i <;> simp [choiLamZeroDirection0] <;> norm_num

private theorem choiLamQuartic_not_mem_boxPreordering (r : ℕ) :
    choiLamQuartic ∉ BoxPreordering 4 r := by
  intro hmem
  let c := schmInteriorLowerBoundConst4
  let a : ℝ := c / (r + 1 : ℕ)
  let epsilon : ℝ := a ^ 4
  have hc : 0 < c := schmInteriorLowerBoundConst4_pos
  have hr1 : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have ha : 0 < a := div_pos hc hr1
  have hepsilon : 0 < epsilon := pow_pos ha _
  have hepsilonRpow : epsilon ^ (-(1 : ℝ) / 4) = a⁻¹ := by
    dsimp [epsilon]
    rw [← Real.rpow_natCast a 4, ← Real.rpow_mul ha.le]
    convert Real.rpow_neg_one a using 1 <;> norm_num
  have hcMul : c * epsilon ^ (-(1 : ℝ) / 4) = (r + 1 : ℕ) := by
    rw [hepsilonRpow]
    dsimp [a]
    field_simp
  let epsilon' : ℝ := min epsilon (schmInteriorEpsilon0 / 2)
  have hepsilon' : 0 < epsilon' := lt_min hepsilon (half_pos schmInteriorEpsilon0_pos)
  have hepsilon'0 : epsilon' ≤ schmInteriorEpsilon0 := by
    exact (min_le_right _ _).trans (half_le_self schmInteriorEpsilon0_pos.le)
  have hrpowMono : epsilon ^ (-(1 : ℝ) / 4) ≤
      epsilon' ^ (-(1 : ℝ) / 4) := by
    exact Real.rpow_le_rpow_of_nonpos hepsilon' (min_le_left _ _) (by norm_num)
  have hconst : MvPolynomial.C epsilon' ∈ BoxPreordering 4 r :=
    positive_const_in_box_preordering hepsilon' 4 r
  have hpert : choiLamPerturbed epsilon' ∈ BoxPreordering 4 r := by
    rw [choiLamPerturbed_eq]
    exact BoxPreordering_add hmem hconst
  have hdegree := lowerBoundMembershipBoxPreoChoiLam_quarter
    epsilon' hepsilon' hepsilon'0 r hpert
  have hstrict : (r : ℝ) < c * epsilon' ^ (-(1 : ℝ) / 4) := by
    calc
      (r : ℝ) < (r + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self r
      _ = c * epsilon ^ (-(1 : ℝ) / 4) := hcMul.symm
      _ ≤ c * epsilon' ^ (-(1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hrpowMono hc.le
  exact (not_lt_of_ge hdegree) hstrict

/-- The Choi--Lam perturbation obstruction gives a quartic lower bound for
the box-preordering hierarchy in dimension four. -/
theorem schmudgenCubeQuarticGapLower_of_small (r : ℕ) (hr : 0 < r)
    (hsmall : (schmInteriorLowerBoundConst4 / (r : ℝ)) ^ 4 ≤
      schmInteriorEpsilon0) :
    lasserre_bound_box_preo choiLamQuartic r ≤
      ↑(-(schmInteriorLowerBoundConst4 / (r : ℝ)) ^ 4) := by
  have hrPos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hcPos : 0 < schmInteriorLowerBoundConst4 := schmInteriorLowerBoundConst4_pos
  suffices key : ∀ l : ℝ, (choiLamQuartic - MvPolynomial.C l) ∈ BoxPreordering 4 r →
      l ≤ -(schmInteriorLowerBoundConst4 / (r : ℝ)) ^ 4 by
    unfold lasserre_bound_box_preo
    split_ifs with hne
    · exact WithBot.coe_le_coe.mpr (csSup_le hne fun l hl ↦ key l hl)
    · exact bot_le
  intro l hl
  have hfl : choiLamQuartic - MvPolynomial.C l = choiLamPerturbed (-l) := by
    simp [choiLamPerturbed, map_neg]
    ring
  rw [hfl] at hl
  have hlNonneg : 0 ≤ -l := by
    have h := box_preordering_subset_nonneg hl choiLamZeroDirection0
      choiLamZeroDirection0_mem_hypercube
    have hz : MvPolynomial.eval choiLamZeroDirection0 choiLamQuartic = 0 := by
      simpa [choiLamZeroDirection] using choiLamQuartic_zero_on_direction (0 : Fin 4)
    rw [choiLamPerturbed_eq, map_add, eval_C, hz] at h
    simpa using h
  by_cases hlZero : l = 0
  · subst hlZero
    exfalso
    apply choiLamQuartic_not_mem_boxPreordering r
    simpa [choiLamPerturbed] using hl
  have hlPos : 0 < -l := lt_of_le_of_ne hlNonneg fun h ↦ hlZero (by linarith)
  by_cases hlSmall : -l ≤ schmInteriorEpsilon0
  · have hdegree := lowerBoundMembershipBoxPreoChoiLam_quarter (-l) hlPos hlSmall r hl
    have hrootPos : 0 < (-l) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hlPos _
    have hratio : schmInteriorLowerBoundConst4 / (r : ℝ) ≤
        (-l) ^ ((1 : ℝ) / 4) := by
      rw [div_le_iff₀ hrPos]
      rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring,
        Real.rpow_neg hlPos.le] at hdegree
      rw [mul_inv_le_iff₀ hrootPos] at hdegree
      simpa [mul_comm] using hdegree
    have hpow := pow_le_pow_left₀ (div_nonneg hcPos.le hrPos.le) hratio 4
    have hrootPow : ((-l) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = -l := by
      rw [← Real.rpow_natCast ((-l) ^ ((1 : ℝ) / 4)) 4,
        ← Real.rpow_mul hlPos.le]
      norm_num
    rw [hrootPow] at hpow
    linarith
  · push Not at hlSmall
    linarith

end QuarticConvergence
end OptimalConvergenceRates

end
