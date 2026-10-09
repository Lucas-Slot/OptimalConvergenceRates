/-
  Summation bounds for the discrete Gaussian kernel in the moment
  obstruction.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.MomentFunctional
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.DiagonalDominance
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Logic.Equiv.Basic

import Mathlib.Data.Nat.Dist
import Mathlib.Data.Int.NatAbs
noncomputable section

open Finset

namespace OptimalConvergenceRates.GeneralArchimedean

/-- The bilateral geometric kernel on the integers. -/
def bilateralGeometric (q : ℝ) (z : ℤ) : ℝ :=
  q ^ z.natAbs

theorem hasSum_bilateralGeometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (bilateralGeometric q) ((1 + q) / (1 - q)) := by
  have hpos := hasSum_geometric_of_lt_one hq0 hq1
  have hneg :
      HasSum (fun n : ℕ ↦ q ^ (n + 1)) (q * (1 - q)⁻¹) := by
    simpa [pow_succ, mul_comm] using hpos.mul_left q
  have hint := hpos.int_rec hneg
  convert hint using 1
  · funext z
    cases z with
    | ofNat n => simp [bilateralGeometric]
    | negSucc n => simp [bilateralGeometric]
  · have hne : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_of_lt hq1).symm
    field_simp

theorem summable_bilateralGeometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (bilateralGeometric q) :=
  (hasSum_bilateralGeometric hq0 hq1).summable

theorem tsum_bilateralGeometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' z : ℤ, bilateralGeometric q z = (1 + q) / (1 - q) :=
  (hasSum_bilateralGeometric hq0 hq1).tsum_eq

/-- The product bilateral kernel on the integer lattice. -/
def bilateralGeometric₂ (q : ℝ) (z : ℤ × ℤ) : ℝ :=
  bilateralGeometric q z.1 * bilateralGeometric q z.2

theorem summable_bilateralGeometric₂ {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (bilateralGeometric₂ q) := by
  exact (summable_bilateralGeometric hq0 hq1).mul_of_nonneg
    (summable_bilateralGeometric hq0 hq1)
    (fun z ↦ pow_nonneg hq0 _) (fun z ↦ pow_nonneg hq0 _)

theorem tsum_bilateralGeometric₂ {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' z : ℤ × ℤ, bilateralGeometric₂ q z =
      ((1 + q) / (1 - q)) ^ 2 := by
  have h := (summable_bilateralGeometric hq0 hq1).tsum_mul_tsum
    (summable_bilateralGeometric hq0 hq1)
    (summable_bilateralGeometric₂ hq0 hq1)
  rw [tsum_bilateralGeometric hq0 hq1] at h
  simpa [bilateralGeometric₂, pow_two] using h.symm

/-- The integer lattice with its origin removed. -/
abbrev PuncturedIntLattice :=
  {z : ℤ × ℤ // z ∉ ({(0, 0)} : Finset (ℤ × ℤ))}

theorem tsum_punctured_bilateralGeometric₂
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' z : PuncturedIntLattice, bilateralGeometric₂ q z.1 =
      ((1 + q) / (1 - q)) ^ 2 - 1 := by
  let f : ℤ × ℤ → ℝ := bilateralGeometric₂ q
  have hf : Summable f := summable_bilateralGeometric₂ hq0 hq1
  have hsplit := hf.sum_add_tsum_subtype_compl ({(0, 0)} : Finset (ℤ × ℤ))
  have hzero : f (0, 0) = 1 := by simp [f, bilateralGeometric₂, bilateralGeometric]
  have htotal : ∑' z : ℤ × ℤ, f z = ((1 + q) / (1 - q)) ^ 2 :=
    tsum_bilateralGeometric₂ hq0 hq1
  rw [Finset.sum_singleton, hzero, htotal] at hsplit
  linarith


theorem exp_neg_four_pos : 0 < Real.exp (-4) :=
  Real.exp_pos _

theorem exp_neg_four_lt_one_sixteen :
    Real.exp (-4) < (1 : ℝ) / 16 := by
  have he : 2 < Real.exp 1 := by
    convert Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0) using 1;
      norm_num
  have he2 : (4 : ℝ) < Real.exp 1 * Real.exp 1 := by
    have hprod : 0 < (Real.exp 1 - 2) * (Real.exp 1 + 2) :=
      mul_pos (sub_pos.mpr he) (by positivity)
    nlinarith
  have he4 : (16 : ℝ) < Real.exp 4 := by
    rw [show (4 : ℝ) = 1 + 1 + 1 + 1 by norm_num,
      Real.exp_add, Real.exp_add, Real.exp_add]
    have he4' :
        (16 : ℝ) <
          (Real.exp 1 * Real.exp 1) * (Real.exp 1 * Real.exp 1) :=
      by
        have hprod : 0 < (Real.exp 1 * Real.exp 1 - 4) *
            (Real.exp 1 * Real.exp 1 + 4) := mul_pos (sub_pos.mpr he2) (by positivity)
        nlinarith
    nlinarith
  rw [Real.exp_neg]
  simpa [one_div] using
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 16) he4)

theorem punctured_bilateralGeometric₂_exp_neg_four_lt_one :
    (∑' z : PuncturedIntLattice,
        bilateralGeometric₂ (Real.exp (-4)) z.1) < 1 := by
  let q := Real.exp (-4)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  rw [tsum_punctured_bilateralGeometric₂ hq0 hq1]
  have hq : q < (1 : ℝ) / 16 := exp_neg_four_lt_one_sixteen
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  rw [div_pow]
  apply sub_lt_iff_lt_add.mpr
  apply (div_lt_iff₀ (sq_pos_of_pos hd)).2
  nlinarith [sq_nonneg q]


/-- The explicit lattice estimate has enough slack for quantitative
diagonal-dominance comparisons. -/
theorem punctured_bilateralGeometric₂_exp_neg_four_lt_half :
    (∑' z : PuncturedIntLattice,
        bilateralGeometric₂ (Real.exp (-4)) z.1) < (1 : ℝ) / 2 := by
  let q := Real.exp (-4)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  rw [tsum_punctured_bilateralGeometric₂ hq0 hq1]
  have hq : q < (1 : ℝ) / 16 := exp_neg_four_lt_one_sixteen
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  rw [div_pow]
  apply sub_lt_iff_lt_add.mpr
  apply (div_lt_iff₀ (sq_pos_of_pos hd)).2
  nlinarith [sq_nonneg q]
/-- An integral distance is at most its square after casting to the reals. -/
theorem natDist_cast_le_sq_sub (i k : ℕ) :
    (Nat.dist i k : ℝ) ≤ ((i : ℝ) - k) ^ 2 := by
  have habs : |(i : ℝ) - k| = (Nat.dist i k : ℝ) := by
    by_cases hki : k ≤ i
    · have hkiR : (k : ℝ) ≤ i := by exact_mod_cast hki
      rw [Nat.dist_eq_sub_of_le_right hki, Nat.cast_sub hki,
        abs_of_nonneg (sub_nonneg.mpr hkiR)]
    · have hik : i ≤ k := le_of_not_ge hki
      have hikR : (i : ℝ) ≤ k := by exact_mod_cast hik
      rw [Nat.dist_eq_sub_of_le hik, Nat.cast_sub hik,
        abs_of_nonpos (sub_nonpos.mpr hikR)]
      ring
  have hsq :
      ((i : ℝ) - k) ^ 2 = (Nat.dist i k : ℝ) ^ 2 := by
    rw [← sq_abs, habs]
  rw [hsq]
  by_cases hzero : Nat.dist i k = 0
  · simp [hzero]
  · have hone : (1 : ℝ) ≤ (Nat.dist i k : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hzero)
    have hnonneg : (0 : ℝ) ≤ (Nat.dist i k : ℝ) := by positivity
    nlinarith

/-- The discrete Gaussian is bounded by the bilateral geometric kernel
with ratio `exp (-4)`. -/
theorem gaussian_le_bilateralGeometric₂ (i j k l : ℕ) :
    Real.exp (-4 * (((i : ℝ) - k) ^ 2 + ((j : ℝ) - l) ^ 2)) ≤
      bilateralGeometric₂ (Real.exp (-4))
        ((i : ℤ) - k, (j : ℤ) - l) := by
  have hnatAbs (a b : ℕ) :
      ((a : ℤ) - b).natAbs = Nat.dist a b := by
    by_cases hba : b ≤ a
    · rw [Int.natAbs_natCast_sub_natCast_of_ge hba,
        Nat.dist_eq_sub_of_le_right hba]
    · have hab : a ≤ b := le_of_not_ge hba
      rw [Int.natAbs_natCast_sub_natCast_of_le hab,
        Nat.dist_eq_sub_of_le hab]
  have hdist :
      (Nat.dist i k : ℝ) + (Nat.dist j l : ℝ) ≤
        ((i : ℝ) - k) ^ 2 + ((j : ℝ) - l) ^ 2 :=
    add_le_add (natDist_cast_le_sq_sub i k) (natDist_cast_le_sq_sub j l)
  have harg :
      -4 * (((i : ℝ) - k) ^ 2 + ((j : ℝ) - l) ^ 2) ≤
        -4 * ((Nat.dist i k : ℝ) + (Nat.dist j l : ℝ)) :=
    mul_le_mul_of_nonpos_left hdist (by norm_num)
  have hright :
      bilateralGeometric₂ (Real.exp (-4))
          ((i : ℤ) - k, (j : ℤ) - l) =
        Real.exp
          (-4 * ((Nat.dist i k : ℝ) + (Nat.dist j l : ℝ))) := by
    unfold bilateralGeometric₂ bilateralGeometric
    rw [hnatAbs i k, hnatAbs j l]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hright]
  exact Real.exp_le_exp.mpr harg
/-- The normalized Gaussian entry associated to two bivariate exponent
pairs. -/
def bivarGaussianKernel (u v : ℕ × ℕ) : ℝ :=
  Real.exp (-4 * (((u.1 : ℝ) - v.1) ^ 2 + ((u.2 : ℝ) - v.2) ^ 2))

theorem bivarGaussianKernel_nonneg (u v : ℕ × ℕ) :
    0 ≤ bivarGaussianKernel u v :=
  (Real.exp_pos _).le

theorem bivarGaussianKernel_self (u : ℕ × ℕ) :
    bivarGaussianKernel u u = 1 := by
  simp [bivarGaussianKernel]

theorem bivarGaussianKernel_comm (u v : ℕ × ℕ) :
    bivarGaussianKernel u v = bivarGaussianKernel v u := by
  unfold bivarGaussianKernel
  congr 2; ring

/-- Every finite injectively indexed family of bivariate monomials has
normalized off-diagonal Gaussian row sum strictly below one. -/
theorem bivarGaussianKernel_offDiagonal_sum_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ × ℕ) (he : Function.Injective e) (a : ι) :
    (∑ b : ι, if a = b then 0 else bivarGaussianKernel (e a) (e b)) < 1 := by
  let J := {b : ι // b ≠ a}
  let source : J → ℝ := fun b ↦ bivarGaussianKernel (e a) (e b.1)
  let target : PuncturedIntLattice → ℝ :=
    fun z ↦ bilateralGeometric₂ (Real.exp (-4)) z.1
  let shift : J → PuncturedIntLattice := fun b ↦
    ⟨(((e a).1 : ℤ) - (e b.1).1, ((e a).2 : ℤ) - (e b.1).2), by
      simp only [Finset.mem_singleton]
      intro hz
      have hfst :
          ((e a).1 : ℤ) - (e b.1).1 = 0 :=
        congrArg Prod.fst hz
      have hsnd :
          ((e a).2 : ℤ) - (e b.1).2 = 0 :=
        congrArg Prod.snd hz
      have h1 : (e a).1 = (e b.1).1 := by exact_mod_cast (sub_eq_zero.mp hfst)
      have h2 : (e a).2 = (e b.1).2 := by exact_mod_cast (sub_eq_zero.mp hsnd)
      exact b.2 (he (Prod.ext h1 h2)).symm⟩
  have hshift : Function.Injective shift := by
    intro b c hbc
    have hfst :
        ((e a).1 : ℤ) - (e b.1).1 =
          ((e a).1 : ℤ) - (e c.1).1 :=
      congrArg (fun z : PuncturedIntLattice ↦ z.1.1) hbc
    have hsnd :
        ((e a).2 : ℤ) - (e b.1).2 =
          ((e a).2 : ℤ) - (e c.1).2 :=
      congrArg (fun z : PuncturedIntLattice ↦ z.1.2) hbc
    have h1 : (e b.1).1 = (e c.1).1 := by omega
    have h2 : (e b.1).2 = (e c.1).2 := by omega
    exact Subtype.ext (he (Prod.ext h1 h2))
  have hsource : Summable source := by
    apply summable_of_finite_support
    exact Set.toFinite _
  have htarget : Summable target := by
    exact (summable_bilateralGeometric₂ (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by norm_num))).subtype _
  have hpoint (b : J) : source b ≤ target (shift b) := by
    exact gaussian_le_bilateralGeometric₂
      (e a).1 (e a).2 (e b.1).1 (e b.1).2
  have hcompare :
      (∑' b : J, source b) ≤ ∑' z : PuncturedIntLattice, target z :=
    hsource.tsum_le_tsum_of_inj shift hshift
      (fun _ _ ↦ by unfold target bilateralGeometric₂ bilateralGeometric; positivity)
      hpoint htarget
  have hrewrite :
      (∑ b : ι, if a = b then 0 else bivarGaussianKernel (e a) (e b)) =
        ∑' b : J, source b := by
    rw [tsum_fintype]
    change
      (∑ b : ι, if a = b then 0 else bivarGaussianKernel (e a) (e b)) =
        ∑ b : J, bivarGaussianKernel (e a) (e b.1)
    calc
      (∑ b : ι, if a = b then 0 else bivarGaussianKernel (e a) (e b)) =
          ∑ b ∈ (Finset.univ.filter fun b : ι ↦ b ≠ a),
            bivarGaussianKernel (e a) (e b) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro b _hb
              by_cases hab : a = b
              · simp [hab]
              · simp [hab, Ne.symm hab]
      _ = ∑ b : J, bivarGaussianKernel (e a) (e b.1) := by
        symm
        simpa [J] using (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset ι)) (p := fun b : ι ↦ b ≠ a)
          (fun b ↦ bivarGaussianKernel (e a) (e b)))
  rw [hrewrite]
  exact hcompare.trans_lt punctured_bilateralGeometric₂_exp_neg_four_lt_one


/-- Quantitative version of the Gaussian row estimate. -/
theorem bivarGaussianKernel_offDiagonal_sum_lt_half
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ × ℕ) (he : Function.Injective e) (a : ι) :
    (∑ b : ι, if a = b then 0 else bivarGaussianKernel (e a) (e b)) <
      (1 : ℝ) / 2 := by
  let J := {b : ι // b ≠ a}
  let source : J → ℝ := fun b ↦ bivarGaussianKernel (e a) (e b.1)
  let target : PuncturedIntLattice → ℝ :=
    fun z ↦ bilateralGeometric₂ (Real.exp (-4)) z.1
  let shift : J → PuncturedIntLattice := fun b ↦
    ⟨(((e a).1 : ℤ) - (e b.1).1, ((e a).2 : ℤ) - (e b.1).2), by
      simp only [Finset.mem_singleton]
      intro hz
      have hfst := congrArg Prod.fst hz
      have hsnd := congrArg Prod.snd hz
      have h1 : (e a).1 = (e b.1).1 := by exact_mod_cast (sub_eq_zero.mp hfst)
      have h2 : (e a).2 = (e b.1).2 := by exact_mod_cast (sub_eq_zero.mp hsnd)
      exact b.2 (he (Prod.ext h1 h2)).symm⟩
  have hshift : Function.Injective shift := by
    intro b c hbc
    have hfst :
        ((e a).1 : ℤ) - (e b.1).1 = ((e a).1 : ℤ) - (e c.1).1 :=
      congrArg (fun z : PuncturedIntLattice ↦ z.1.1) hbc
    have hsnd :
        ((e a).2 : ℤ) - (e b.1).2 = ((e a).2 : ℤ) - (e c.1).2 :=
      congrArg (fun z : PuncturedIntLattice ↦ z.1.2) hbc
    have h1 : (e b.1).1 = (e c.1).1 := by omega
    have h2 : (e b.1).2 = (e c.1).2 := by omega
    exact Subtype.ext (he (Prod.ext h1 h2))
  have hsource : Summable source := summable_of_finite_support (Set.toFinite _)
  have htarget : Summable target :=
    (summable_bilateralGeometric₂ (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by norm_num))).subtype _
  have hcompare : (∑' b : J, source b) ≤ ∑' z : PuncturedIntLattice, target z :=
    hsource.tsum_le_tsum_of_inj shift hshift
      (fun _ _ ↦ by unfold target bilateralGeometric₂ bilateralGeometric; positivity)
      (fun b ↦ gaussian_le_bilateralGeometric₂
        (e a).1 (e a).2 (e b.1).1 (e b.1).2) htarget
  have hrewrite :
      (∑ b : ι, if a = b then 0 else bivarGaussianKernel (e a) (e b)) =
        ∑' b : J, source b := by
    rw [tsum_fintype]
    change (∑ b : ι, if a = b then 0 else bivarGaussianKernel (e a) (e b)) =
      ∑ b : J, bivarGaussianKernel (e a) (e b.1)
    calc
      _ = ∑ b ∈ (Finset.univ.filter fun b : ι ↦ b ≠ a),
          bivarGaussianKernel (e a) (e b) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro b _hb
            by_cases hab : a = b
            · simp [hab]
            · simp [hab, Ne.symm hab]
      _ = _ := by
        symm
        simpa [J] using (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset ι)) (p := fun b : ι ↦ b ≠ a)
          (fun b ↦ bivarGaussianKernel (e a) (e b)))
  rw [hrewrite]
  exact hcompare.trans_lt punctured_bilateralGeometric₂_exp_neg_four_lt_half
end OptimalConvergenceRates.GeneralArchimedean

end
