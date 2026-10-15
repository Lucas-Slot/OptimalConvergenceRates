/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/ChoiLam.lean

  Choi-Lam zero directions, nonnegativity, and non-SOS obstruction lemmas.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.Defs
import OptimalConvergenceRates.ExamplePolynomials.ChoiLam
import OptimalConvergenceRates.BasicNotions.SOS
import OptimalConvergenceRates.BasicNotions.SoSConeClosed
import Mathlib.Analysis.MeanInequalities

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

local macro "legacyCoeff" α:term:max p:term:max : term => `(($p).coeff $α)

/-! ## The quartic obstruction -/

/-- First zero direction for the Choi-Lam quartic. -/
def choiLamZeroDirection0 : Fin 4 → ℝ := ![1 / 2, 1 / 2, 1 / 2, 1 / 2]

/-- Second zero direction for the Choi-Lam quartic. -/
def choiLamZeroDirection1 : Fin 4 → ℝ := ![1 / 2, 1 / 2, -1 / 2, -1 / 2]

/-- Third zero direction for the Choi-Lam quartic. -/
def choiLamZeroDirection2 : Fin 4 → ℝ := ![1 / 2, -1 / 2, 1 / 2, -1 / 2]

/-- Fourth zero direction for the Choi-Lam quartic. -/
def choiLamZeroDirection3 : Fin 4 → ℝ := ![1 / 2, -1 / 2, -1 / 2, 1 / 2]

/-- The four orthonormal zero directions used in the local jet argument. -/
def choiLamZeroDirection : Fin 4 → Fin 4 → ℝ
  | 0 => choiLamZeroDirection0
  | 1 => choiLamZeroDirection1
  | 2 => choiLamZeroDirection2
  | 3 => choiLamZeroDirection3

theorem choiLamQuartic_zero_on_direction (i : Fin 4) :
    MvPolynomial.eval (choiLamZeroDirection i) choiLamQuartic = 0 := by
  fin_cases i <;>
    simp [choiLamZeroDirection, choiLamZeroDirection0, choiLamZeroDirection1,
      choiLamZeroDirection2, choiLamZeroDirection3, choiLamQuartic_eval] <;>
    norm_num

theorem choiLamQuartic_zero_on_direction_line (i : Fin 4) (t : ℝ) :
    MvPolynomial.eval (fun j => t * choiLamZeroDirection i j) choiLamQuartic = 0 := by
  fin_cases i <;>
    simp [choiLamZeroDirection, choiLamZeroDirection0, choiLamZeroDirection1,
      choiLamZeroDirection2, choiLamZeroDirection3, choiLamQuartic_eval] <;>
    ring


/-- Euclidean dot product in the four-variable space. -/
def interiorDot4 (u v : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, u i * v i

/-- The four Choi-Lam zero directions form an orthonormal basis. -/
theorem choiLamZeroDirection_orthonormal (i j : Fin 4) :
    interiorDot4 (choiLamZeroDirection i) (choiLamZeroDirection j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [interiorDot4, choiLamZeroDirection, choiLamZeroDirection0, choiLamZeroDirection1,
      choiLamZeroDirection2, choiLamZeroDirection3, Fin.sum_univ_four] <;>
    norm_num

/-- Each Choi-Lam zero direction has Euclidean squared norm one. -/
theorem choiLamZeroDirection_sqNorm (i : Fin 4) :
    interiorVecSqNorm (choiLamZeroDirection i) = 1 := by
  have h := choiLamZeroDirection_orthonormal i i
  simpa [interiorDot4, interiorVecSqNorm, pow_two] using h

/-! ## Choi-Lam positivity input -/

private theorem fourth_root_fourth (a : ℝ) : (a ^ 4) ^ (1 / 4 : ℝ) = |a| := by
  have hnon1 : 0 ≤ (a ^ 4) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hnon2 : 0 ≤ |a| := abs_nonneg a
  have hpoweq : ((a ^ 4) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = |a| ^ (4 : ℝ) := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ a ^ 4)]
    norm_num
    rw [← abs_pow]
    rw [abs_of_nonneg (by positivity : 0 ≤ a ^ 4)]
  apply le_antisymm
  · exact (Real.rpow_le_rpow_iff hnon1 hnon2 (by norm_num : (0 : ℝ) < 4)).mp
      (le_of_eq hpoweq)
  · exact (Real.rpow_le_rpow_iff hnon2 hnon1 (by norm_num : (0 : ℝ) < 4)).mp
      (le_of_eq hpoweq.symm)

private theorem four_mul_abs_mul_le_choiLam_terms (a b c d : ℝ) :
    4 * |a * b * c * d| ≤
      a ^ 4 + b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + d ^ 2 * b ^ 2 := by
  let f : Fin 4 → ℝ := ![a ^ 4, b ^ 2 * c ^ 2, c ^ 2 * d ^ 2, d ^ 2 * b ^ 2]
  have h := Real.geom_mean_le_arith_mean4_weighted
    (by norm_num : 0 ≤ (1 / 4 : ℝ)) (by norm_num : 0 ≤ (1 / 4 : ℝ))
    (by norm_num : 0 ≤ (1 / 4 : ℝ)) (by norm_num : 0 ≤ (1 / 4 : ℝ))
    (by dsimp [f]; positivity : 0 ≤ f 0) (by dsimp [f]; positivity : 0 ≤ f 1)
    (by dsimp [f]; positivity : 0 ≤ f 2) (by dsimp [f]; positivity : 0 ≤ f 3)
    (by norm_num : (1 / 4 : ℝ) + 1 / 4 + 1 / 4 + 1 / 4 = 1)
  dsimp [f] at h
  have h4 :
      4 * ((a ^ 4) ^ (1 / 4 : ℝ) * ((b ^ 2 * c ^ 2) ^ (1 / 4 : ℝ)) *
        ((c ^ 2 * d ^ 2) ^ (1 / 4 : ℝ)) * ((d ^ 2 * b ^ 2) ^ (1 / 4 : ℝ))) ≤
        a ^ 4 + b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + d ^ 2 * b ^ 2 := by
    nlinarith
  have hroot :
      (a ^ 4) ^ (1 / 4 : ℝ) * ((b ^ 2 * c ^ 2) ^ (1 / 4 : ℝ)) *
        ((c ^ 2 * d ^ 2) ^ (1 / 4 : ℝ)) * ((d ^ 2 * b ^ 2) ^ (1 / 4 : ℝ)) =
        |a * b * c * d| := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ a ^ 4) (by positivity : 0 ≤ b ^ 2 * c ^ 2)]
    rw [← Real.mul_rpow (by positivity : 0 ≤ a ^ 4 * (b ^ 2 * c ^ 2))
      (by positivity : 0 ≤ c ^ 2 * d ^ 2)]
    rw [← Real.mul_rpow
      (by positivity : 0 ≤ a ^ 4 * (b ^ 2 * c ^ 2) * (c ^ 2 * d ^ 2))
      (by positivity : 0 ≤ d ^ 2 * b ^ 2)]
    rw [show a ^ 4 * (b ^ 2 * c ^ 2) * (c ^ 2 * d ^ 2) * (d ^ 2 * b ^ 2) =
      (a * b * c * d) ^ 4 by ring]
    exact fourth_root_fourth (a * b * c * d)
  rw [hroot] at h4
  exact h4

/-- The Choi-Lam quartic is globally nonnegative. -/
theorem choiLamQuartic_nonneg_global :
    ∀ v : Fin 4 → ℝ, 0 ≤ MvPolynomial.eval v choiLamQuartic := by
  intro v
  rw [choiLamQuartic_eval]
  have hamgm := four_mul_abs_mul_le_choiLam_terms (v 0) (v 1) (v 2) (v 3)
  have hsign : 4 * v 0 * v 1 * v 2 * v 3 ≤ 4 * |v 0 * v 1 * v 2 * v 3| := by
    nlinarith [le_abs_self (v 0 * v 1 * v 2 * v 3)]
  nlinarith

/-- The Choi-Lam quartic has total degree at most four. -/
theorem choiLamQuartic_totalDegree_le_four : choiLamQuartic.totalDegree ≤ 4 := by
  unfold choiLamQuartic
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
      · refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
        · rw [MvPolynomial.totalDegree_X_pow]
        · calc ((X 1 : MvPolynomial (Fin 4) ℝ) ^ 2 * X 2 ^ 2).totalDegree
            ≤ ((X 1 : MvPolynomial (Fin 4) ℝ) ^ 2).totalDegree +
                ((X 2 : MvPolynomial (Fin 4) ℝ) ^ 2).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
            _ = 4 := by simp [MvPolynomial.totalDegree_X_pow]
      · calc ((X 2 : MvPolynomial (Fin 4) ℝ) ^ 2 * X 3 ^ 2).totalDegree
          ≤ ((X 2 : MvPolynomial (Fin 4) ℝ) ^ 2).totalDegree +
              ((X 3 : MvPolynomial (Fin 4) ℝ) ^ 2).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ = 4 := by simp [MvPolynomial.totalDegree_X_pow]
    · calc ((X 3 : MvPolynomial (Fin 4) ℝ) ^ 2 * X 1 ^ 2).totalDegree
        ≤ ((X 3 : MvPolynomial (Fin 4) ℝ) ^ 2).totalDegree +
            ((X 1 : MvPolynomial (Fin 4) ℝ) ^ 2).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ = 4 := by simp [MvPolynomial.totalDegree_X_pow]
  · calc (4 * X 0 * X 1 * X 2 * X 3 : MvPolynomial (Fin 4) ℝ).totalDegree
        ≤ (4 * X 0 * X 1 * X 2 : MvPolynomial (Fin 4) ℝ).totalDegree +
            (X 3 : MvPolynomial (Fin 4) ℝ).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ ((4 * X 0 * X 1 : MvPolynomial (Fin 4) ℝ).totalDegree +
            (X 2 : MvPolynomial (Fin 4) ℝ).totalDegree) +
            (X 3 : MvPolynomial (Fin 4) ℝ).totalDegree := by
          gcongr
          exact MvPolynomial.totalDegree_mul _ _
      _ ≤ (((4 * X 0 : MvPolynomial (Fin 4) ℝ).totalDegree +
            (X 1 : MvPolynomial (Fin 4) ℝ).totalDegree) +
            (X 2 : MvPolynomial (Fin 4) ℝ).totalDegree) +
            (X 3 : MvPolynomial (Fin 4) ℝ).totalDegree := by
          gcongr
          exact MvPolynomial.totalDegree_mul _ _
      _ ≤ ((((C (4 : ℝ) : MvPolynomial (Fin 4) ℝ).totalDegree +
            (X 0 : MvPolynomial (Fin 4) ℝ).totalDegree) +
            (X 1 : MvPolynomial (Fin 4) ℝ).totalDegree) +
            (X 2 : MvPolynomial (Fin 4) ℝ).totalDegree) +
            (X 3 : MvPolynomial (Fin 4) ℝ).totalDegree := by
          gcongr
          exact MvPolynomial.totalDegree_mul _ _
      _ = 4 := by simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]

/-- In any SOS representation of the Choi-Lam quartic, every square-root summand
has total degree at most two. -/
theorem choiLam_sos_summand_totalDegree_le_two
    {N : ℕ} {P : Fin N → MvPolynomial (Fin 4) ℝ}
    (hP : choiLamQuartic = ∑ i : Fin N, (P i) ^ 2) :
    ∀ i, (P i).totalDegree ≤ 2 := by
  exact sos_summand_totalDegree_le_of_sum_sq_totalDegree hP choiLamQuartic_totalDegree_le_four

private lemma finsupp_coord_le_sum (a : Fin 4 →₀ ℕ) (j : Fin 4) :
    a j ≤ a.sum (fun _ e => e) := by
  by_cases hj : a j = 0
  · simp [hj]
  · have hmem : j ∈ a.support := by
      rw [Finsupp.mem_support_iff]
      exact hj
    calc
      a j = ∑ x ∈ ({j} : Finset (Fin 4)), a x := by simp
      _ ≤ ∑ x ∈ a.support, a x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          have hxj : x = j := by simpa using hx
          subst x
          exact hmem
        · intro x _hx _hnot
          exact Nat.zero_le _
      _ = a.sum (fun _ e => e) := rfl

private lemma antidiagonal_single_four_degree_two_eq {j : Fin 4} {a b : Fin 4 →₀ ℕ}
    (hab : (a, b) ∈ Finset.antidiagonal (Finsupp.single j 4))
    (ha : (a.sum fun _ e => e) ≤ 2) (hb : (b.sum fun _ e => e) ≤ 2) :
    a = Finsupp.single j 2 ∧ b = Finsupp.single j 2 := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
  have hsum : (a.sum fun _ e => e) + (b.sum fun _ e => e) = 4 := by
    calc
      (a.sum fun _ e => e) + (b.sum fun _ e => e)
          = ((a + b).sum fun _ e => e) := by
            rw [Finsupp.sum_add_index]
            · simp
            · intro x
              simp
      _ = ((Finsupp.single j 4).sum fun _ e => e) := by rw [hab]
      _ = 4 := by simp
  have haeq : (a.sum fun _ e => e) = 2 := by omega
  have hbeq : (b.sum fun _ e => e) = 2 := by omega
  constructor
  · apply Finsupp.ext
    intro k
    by_cases hkj : k = j
    · subst k
      have hcoord := (Finsupp.ext_iff.mp hab) j
      simp at hcoord ⊢
      have hle := finsupp_coord_le_sum a j
      have hble := finsupp_coord_le_sum b j
      omega
    · have hcoord := (Finsupp.ext_iff.mp hab) k
      simp [hkj] at hcoord ⊢
      omega
  · apply Finsupp.ext
    intro k
    by_cases hkj : k = j
    · subst k
      have hcoord := (Finsupp.ext_iff.mp hab) j
      simp at hcoord ⊢
      have hle := finsupp_coord_le_sum a j
      have hble := finsupp_coord_le_sum b j
      omega
    · have hcoord := (Finsupp.ext_iff.mp hab) k
      simp [hkj] at hcoord ⊢
      omega

private lemma coeff_eq_zero_of_totalDegree_lt {p : MvPolynomial (Fin 4) ℝ} {m : Fin 4 →₀ ℕ}
    {d : ℕ} (hp : p.totalDegree ≤ d) (hm : d < m.sum fun _ e => e) :
    legacyCoeff m p = 0 := by
  by_contra hcoeff
  have hmem : m ∈ p.support := by
    rw [MvPolynomial.mem_support_iff]
    exact hcoeff
  have hmle := MvPolynomial.le_totalDegree hmem
  omega

private lemma single_two_add_single_two (j : Fin 4) :
    Finsupp.single j 2 + Finsupp.single j 2 = Finsupp.single j 4 := by
  apply Finsupp.ext
  intro k
  by_cases hkj : k = j
  · subst k
    simp
  · simp [hkj]

private lemma coeff_single_four_sq_of_totalDegree_le_two {j : Fin 4}
    {p : MvPolynomial (Fin 4) ℝ} (hp : p.totalDegree ≤ 2) :
    legacyCoeff (Finsupp.single j 4) (p ^ 2) =
      legacyCoeff (Finsupp.single j 2) p ^ 2 := by
  rw [pow_two, MvPolynomial.coeff_mul]
  rw [Finset.sum_eq_single (Finsupp.single j 2, Finsupp.single j 2)]
  · ring
  · intro x hx hne
    have hxmem := hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hleft : (x.1.sum fun _ e => e) ≤ 2
    · by_cases hright : (x.2.sum fun _ e => e) ≤ 2
      · have hpair := antidiagonal_single_four_degree_two_eq
          (j := j) (a := x.1) (b := x.2) hxmem hleft hright
        exfalso
        apply hne
        ext <;> simp [hpair.1, hpair.2]
      · have hzero : legacyCoeff x.2 p = 0 := by
          apply coeff_eq_zero_of_totalDegree_lt hp
          omega
        simp [hzero]
    · have hzero : legacyCoeff x.1 p = 0 := by
        apply coeff_eq_zero_of_totalDegree_lt hp
        omega
      simp [hzero]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    exact single_two_add_single_two j


private lemma finsupp_degree_eq_univ_sum (a : Fin 4 →₀ ℕ) :
    a.sum (fun _ e => e) = ∑ i : Fin 4, a i := by
  rw [Finsupp.sum_fintype]
  intro i
  rfl

private lemma degree_two_of_add_degree_four {a b m : Fin 4 →₀ ℕ}
    (hab : a + b = m) (hm : m.sum (fun _ e => e) = 4)
    (ha : (a.sum fun _ e => e) ≤ 2) (hb : (b.sum fun _ e => e) ≤ 2) :
    (a.sum fun _ e => e) = 2 ∧ (b.sum fun _ e => e) = 2 := by
  have hsum : (a.sum fun _ e => e) + (b.sum fun _ e => e) = 4 := by
    calc
      (a.sum fun _ e => e) + (b.sum fun _ e => e) = ((a + b).sum fun _ e => e) := by
        rw [Finsupp.sum_add_index]
        · simp
        · intro x; simp
      _ = 4 := by rw [hab, hm]
  omega

private lemma antidiagonal_two_two_cases {j : Fin 4} (hj : j ≠ 0) {a b : Fin 4 →₀ ℕ}
    (hab : a + b = Finsupp.single (0 : Fin 4) 2 + Finsupp.single j 2)
    (ha : (a.sum fun _ e => e) ≤ 2) (hb : (b.sum fun _ e => e) ≤ 2) :
    (a = Finsupp.single (0 : Fin 4) 2 ∧ b = Finsupp.single j 2) ∨
    (a = Finsupp.single j 2 ∧ b = Finsupp.single (0 : Fin 4) 2) ∨
    (a = Finsupp.single (0 : Fin 4) 1 + Finsupp.single j 1 ∧
      b = Finsupp.single (0 : Fin 4) 1 + Finsupp.single j 1) := by
  fin_cases j
  · contradiction
  · have hm :
        (Finsupp.single (0 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2).sum
            (fun _ e => e) = 4 := by
      rw [finsupp_degree_eq_univ_sum]
      simp [Fin.sum_univ_four]
    have hdeg := degree_two_of_add_degree_four hab hm ha hb
    rw [finsupp_degree_eq_univ_sum] at hdeg
    simp [Fin.sum_univ_four] at hdeg
    have h0 := Finsupp.ext_iff.mp hab (0 : Fin 4)
    have h1 := Finsupp.ext_iff.mp hab (1 : Fin 4)
    have h2 := Finsupp.ext_iff.mp hab (2 : Fin 4)
    have h3 := Finsupp.ext_iff.mp hab (3 : Fin 4)
    simp at h0 h1 h2 h3
    have ha0le : a 0 ≤ 2 := by omega
    interval_cases h : a 0
    · right; left; constructor <;> ext k <;> fin_cases k <;> simp [h] <;> omega
    · right; right; constructor <;> ext k <;> fin_cases k <;> simp [h] <;> omega
    · left; constructor <;> ext k <;> fin_cases k <;> simp [h] <;> omega
  · have hm :
        (Finsupp.single (0 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2).sum
            (fun _ e => e) = 4 := by
      rw [finsupp_degree_eq_univ_sum]
      simp [Fin.sum_univ_four]
    have hdeg := degree_two_of_add_degree_four hab hm ha hb
    rw [finsupp_degree_eq_univ_sum] at hdeg
    simp [Fin.sum_univ_four] at hdeg
    have h0 := Finsupp.ext_iff.mp hab (0 : Fin 4)
    have h1 := Finsupp.ext_iff.mp hab (1 : Fin 4)
    have h2 := Finsupp.ext_iff.mp hab (2 : Fin 4)
    have h3 := Finsupp.ext_iff.mp hab (3 : Fin 4)
    simp at h0 h1 h2 h3
    have ha0le : a 0 ≤ 2 := by omega
    interval_cases h : a 0
    · right; left; constructor <;> ext k <;> fin_cases k <;> simp [h] <;> omega
    · right; right; constructor <;> ext k <;> fin_cases k <;> simp [h] <;> omega
    · left; constructor <;> ext k <;> fin_cases k <;> simp [h] <;> omega
  · have hm :
        (Finsupp.single (0 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2).sum
            (fun _ e => e) = 4 := by
      rw [finsupp_degree_eq_univ_sum]
      simp [Fin.sum_univ_four]
    have hdeg := degree_two_of_add_degree_four hab hm ha hb
    rw [finsupp_degree_eq_univ_sum] at hdeg
    simp [Fin.sum_univ_four] at hdeg
    have h0 := Finsupp.ext_iff.mp hab (0 : Fin 4)
    have h1 := Finsupp.ext_iff.mp hab (1 : Fin 4)
    have h2 := Finsupp.ext_iff.mp hab (2 : Fin 4)
    have h3 := Finsupp.ext_iff.mp hab (3 : Fin 4)
    simp at h0 h1 h2 h3
    have ha0le : a 0 ≤ 2 := by omega
    interval_cases h : a 0
    · right; left; constructor <;> ext k <;> fin_cases k <;> simp [h] <;> omega
    · right; right; constructor <;> ext k <;> fin_cases k <;> simp [h] <;> omega
    · left; constructor <;> ext k <;> fin_cases k <;> simp [h] <;> omega

private lemma X_pow_eq_monomial (i : Fin 4) (k : ℕ) :
    ((X i : MvPolynomial (Fin 4) ℝ) ^ k) = monomial (Finsupp.single i k) 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih]
      change (monomial (Finsupp.single i k)) (1 : ℝ) *
          (monomial (Finsupp.single i 1)) (1 : ℝ) = _
      rw [MvPolynomial.monomial_mul_monomial]
      congr
      · ext j
        by_cases h : j = i <;> simp [h]
      · norm_num

private lemma X_pow_mul_X_pow_eq_monomial (i j : Fin 4) (a b : ℕ) :
    ((X i : MvPolynomial (Fin 4) ℝ) ^ a * X j ^ b) =
      monomial (Finsupp.single i a + Finsupp.single j b) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial]
  norm_num

private lemma four_X_prod_eq_monomial :
    (4 * X (0 : Fin 4) * X (1 : Fin 4) * X (2 : Fin 4) * X (3 : Fin 4) :
      MvPolynomial (Fin 4) ℝ) =
      monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1) 4 := by
  change (monomial 0 (4 : ℝ) * monomial (Finsupp.single (0 : Fin 4) 1) 1 *
      monomial (Finsupp.single (1 : Fin 4) 1) 1 *
      monomial (Finsupp.single (2 : Fin 4) 1) 1 *
      monomial (Finsupp.single (3 : Fin 4) 1) 1) = _
  repeat rw [MvPolynomial.monomial_mul_monomial]
  congr
  · ext j; fin_cases j <;> norm_num
  · norm_num

private lemma choiLamQuartic_coeff_single_four_one :
    legacyCoeff (Finsupp.single (1 : Fin 4) 4) choiLamQuartic = 0 := by
  unfold choiLamQuartic
  rw [X_pow_eq_monomial]
  rw [X_pow_mul_X_pow_eq_monomial, X_pow_mul_X_pow_eq_monomial,
    X_pow_mul_X_pow_eq_monomial, four_X_prod_eq_monomial]
  have h1 : Finsupp.single (0 : Fin 4) 4 ≠ Finsupp.single (1 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h2 : Finsupp.single (1 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 ≠
      Finsupp.single (1 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (2 : Fin 4); simp at this
  have h3 : Finsupp.single (2 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 ≠
      Finsupp.single (1 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (2 : Fin 4); simp at this
  have h4 : Finsupp.single (3 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 ≠
      Finsupp.single (1 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (3 : Fin 4); simp at this
  have h5 : Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 ≠
      Finsupp.single (1 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  simp [MvPolynomial.coeff_monomial, h1, h2, h3, h4, h5]


private lemma choiLamQuartic_coeff_single_four_two :
    legacyCoeff (Finsupp.single (2 : Fin 4) 4) choiLamQuartic = 0 := by
  unfold choiLamQuartic
  rw [X_pow_eq_monomial]
  rw [X_pow_mul_X_pow_eq_monomial, X_pow_mul_X_pow_eq_monomial,
    X_pow_mul_X_pow_eq_monomial, four_X_prod_eq_monomial]
  have h1 : Finsupp.single (0 : Fin 4) 4 ≠ Finsupp.single (2 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h2 : Finsupp.single (1 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 ≠
      Finsupp.single (2 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (1 : Fin 4); simp at this
  have h3 : Finsupp.single (2 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 ≠
      Finsupp.single (2 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (3 : Fin 4); simp at this
  have h4 : Finsupp.single (3 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 ≠
      Finsupp.single (2 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (3 : Fin 4); simp at this
  have h5 : Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 ≠
      Finsupp.single (2 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  simp [MvPolynomial.coeff_monomial, h1, h2, h3, h4, h5]

private lemma choiLamQuartic_coeff_single_four_three :
    legacyCoeff (Finsupp.single (3 : Fin 4) 4) choiLamQuartic = 0 := by
  unfold choiLamQuartic
  rw [X_pow_eq_monomial]
  rw [X_pow_mul_X_pow_eq_monomial, X_pow_mul_X_pow_eq_monomial,
    X_pow_mul_X_pow_eq_monomial, four_X_prod_eq_monomial]
  have h1 : Finsupp.single (0 : Fin 4) 4 ≠ Finsupp.single (3 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h2 : Finsupp.single (1 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 ≠
      Finsupp.single (3 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (1 : Fin 4); simp at this
  have h3 : Finsupp.single (2 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 ≠
      Finsupp.single (3 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (2 : Fin 4); simp at this
  have h4 : Finsupp.single (3 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 ≠
      Finsupp.single (3 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (1 : Fin 4); simp at this
  have h5 : Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 ≠
      Finsupp.single (3 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  simp [MvPolynomial.coeff_monomial, h1, h2, h3, h4, h5]

private lemma choiLamQuartic_coeff_single_four_of_ne_zero {j : Fin 4} (hj : j ≠ 0) :
    legacyCoeff (Finsupp.single j 4) choiLamQuartic = 0 := by
  fin_cases j
  · contradiction
  · exact choiLamQuartic_coeff_single_four_one
  · exact choiLamQuartic_coeff_single_four_two
  · exact choiLamQuartic_coeff_single_four_three


private lemma coeff_single_four_sum_sq_of_totalDegree_le_two
    {N : ℕ} {P : Fin N → MvPolynomial (Fin 4) ℝ}
    (hdeg : ∀ i, (P i).totalDegree ≤ 2) (j : Fin 4) :
    legacyCoeff (Finsupp.single j 4) (∑ i : Fin N, (P i) ^ 2) =
      ∑ i : Fin N, (legacyCoeff (Finsupp.single j 2) (P i)) ^ 2 := by
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact coeff_single_four_sq_of_totalDegree_le_two (j := j) (p := P i) (hdeg i)

private lemma coeff_single_two_eq_zero_of_sos_choiLam
    {N : ℕ} {P : Fin N → MvPolynomial (Fin 4) ℝ}
    (hP : choiLamQuartic = ∑ i : Fin N, (P i) ^ 2) (hdeg : ∀ i, (P i).totalDegree ≤ 2)
    {j : Fin 4} (hj : j ≠ 0) (i : Fin N) :
    legacyCoeff (Finsupp.single j 2) (P i) = 0 := by
  have hcoeff : ∑ i : Fin N, (legacyCoeff (Finsupp.single j 2) (P i)) ^ 2 = 0 := by
    rw [← coeff_single_four_sum_sq_of_totalDegree_le_two hdeg j]
    rw [← hP]
    exact choiLamQuartic_coeff_single_four_of_ne_zero hj
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun i _ => sq_nonneg (legacyCoeff (Finsupp.single j 2) (P i)))).mp hcoeff
  exact sq_eq_zero_iff.mp (hall i (Finset.mem_univ i))


private lemma coeff_zero_two_sq_of_totalDegree_le_two {j : Fin 4} (hj : j ≠ 0)
    {p : MvPolynomial (Fin 4) ℝ} (hp : p.totalDegree ≤ 2)
    (hj2 : legacyCoeff (Finsupp.single j 2) p = 0) :
    legacyCoeff (Finsupp.single (0 : Fin 4) 2 + Finsupp.single j 2) (p ^ 2) =
      legacyCoeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single j 1) p ^ 2 := by
  rw [pow_two, MvPolynomial.coeff_mul]
  rw [Finset.sum_eq_single
    (Finsupp.single (0 : Fin 4) 1 + Finsupp.single j 1,
      Finsupp.single (0 : Fin 4) 1 + Finsupp.single j 1)]
  · ring
  · intro x hx hne
    have hxmem := hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hleft : (x.1.sum fun _ e => e) ≤ 2
    · by_cases hright : (x.2.sum fun _ e => e) ≤ 2
      · have hcases := antidiagonal_two_two_cases (j := j) hj hx hleft hright
        rcases hcases with hcase | hcase | hcase
        · rcases hcase with ⟨hx1, hx2⟩
          simp [hx2, hj2]
        · rcases hcase with ⟨hx1, hx2⟩
          simp [hx1, hj2]
        · rcases hcase with ⟨hx1, hx2⟩
          exfalso
          apply hne
          ext k <;> simp [hx1, hx2]
      · have hzero : legacyCoeff x.2 p = 0 := by
          apply coeff_eq_zero_of_totalDegree_lt hp
          omega
        simp [hzero]
    · have hzero : legacyCoeff x.1 p = 0 := by
        apply coeff_eq_zero_of_totalDegree_lt hp
        omega
      simp [hzero]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    ext k
    by_cases hk0 : k = (0 : Fin 4)
    · subst k; simp [hj]
    · by_cases hkj : k = j
      · subst k; simp [hj]
      · simp [hk0, hkj]


private lemma choiLamQuartic_coeff_zero_two_1 :
    legacyCoeff (Finsupp.single (0 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2)
      choiLamQuartic = 0 := by
  unfold choiLamQuartic
  rw [X_pow_eq_monomial]
  rw [X_pow_mul_X_pow_eq_monomial, X_pow_mul_X_pow_eq_monomial,
    X_pow_mul_X_pow_eq_monomial, four_X_prod_eq_monomial]
  have h1 : Finsupp.single (0 : Fin 4) 4 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h2 : Finsupp.single (1 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h3 : Finsupp.single (2 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h4 : Finsupp.single (3 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h5 : Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  simp [MvPolynomial.coeff_monomial, h1, h2, h3, h4, h5]

private lemma choiLamQuartic_coeff_zero_two_2 :
    legacyCoeff (Finsupp.single (0 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2)
      choiLamQuartic = 0 := by
  unfold choiLamQuartic
  rw [X_pow_eq_monomial]
  rw [X_pow_mul_X_pow_eq_monomial, X_pow_mul_X_pow_eq_monomial,
    X_pow_mul_X_pow_eq_monomial, four_X_prod_eq_monomial]
  have h1 : Finsupp.single (0 : Fin 4) 4 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h2 : Finsupp.single (1 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h3 : Finsupp.single (2 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h4 : Finsupp.single (3 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h5 : Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  simp [MvPolynomial.coeff_monomial, h1, h2, h3, h4, h5]

private lemma choiLamQuartic_coeff_zero_two_3 :
    legacyCoeff (Finsupp.single (0 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2)
      choiLamQuartic = 0 := by
  unfold choiLamQuartic
  rw [X_pow_eq_monomial]
  rw [X_pow_mul_X_pow_eq_monomial, X_pow_mul_X_pow_eq_monomial,
    X_pow_mul_X_pow_eq_monomial, four_X_prod_eq_monomial]
  have h1 : Finsupp.single (0 : Fin 4) 4 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h2 : Finsupp.single (1 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h3 : Finsupp.single (2 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h4 : Finsupp.single (3 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h5 : Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 ≠
      Finsupp.single (0 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  simp [MvPolynomial.coeff_monomial, h1, h2, h3, h4, h5]

private lemma choiLamQuartic_coeff_zero_two_of_ne_zero {j : Fin 4} (hj : j ≠ 0) :
    legacyCoeff (Finsupp.single (0 : Fin 4) 2 + Finsupp.single j 2)
      choiLamQuartic = 0 := by
  fin_cases j
  · contradiction
  · exact choiLamQuartic_coeff_zero_two_1
  · exact choiLamQuartic_coeff_zero_two_2
  · exact choiLamQuartic_coeff_zero_two_3


private lemma coeff_zero_two_sum_sq_of_totalDegree_le_two
    {N : ℕ} {P : Fin N → MvPolynomial (Fin 4) ℝ}
    (hdeg : ∀ i, (P i).totalDegree ≤ 2) {j : Fin 4} (hj : j ≠ 0)
    (hj2 : ∀ i, legacyCoeff (Finsupp.single j 2) (P i) = 0) :
    legacyCoeff (Finsupp.single (0 : Fin 4) 2 + Finsupp.single j 2)
        (∑ i : Fin N, (P i) ^ 2) =
      ∑ i : Fin N,
        (legacyCoeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single j 1) (P i)) ^ 2 := by
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact coeff_zero_two_sq_of_totalDegree_le_two (j := j) hj (p := P i) (hdeg i) (hj2 i)

private lemma coeff_zero_one_eq_zero_of_sos_choiLam
    {N : ℕ} {P : Fin N → MvPolynomial (Fin 4) ℝ}
    (hP : choiLamQuartic = ∑ i : Fin N, (P i) ^ 2) (hdeg : ∀ i, (P i).totalDegree ≤ 2)
    {j : Fin 4} (hj : j ≠ 0) (i : Fin N) :
    legacyCoeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single j 1) (P i) = 0 := by
  have hj2 : ∀ i, legacyCoeff (Finsupp.single j 2) (P i) = 0 := by
    intro i
    exact coeff_single_two_eq_zero_of_sos_choiLam hP hdeg hj i
  have hcoeff :
      ∑ i : Fin N,
          (legacyCoeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single j 1)
            (P i)) ^ 2 = 0 := by
    rw [← coeff_zero_two_sum_sq_of_totalDegree_le_two hdeg hj hj2]
    rw [← hP]
    exact choiLamQuartic_coeff_zero_two_of_ne_zero hj
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (fun i _ => sq_nonneg
      (legacyCoeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single j 1) (P i)))).mp
      hcoeff
  exact sq_eq_zero_iff.mp (hall i (Finset.mem_univ i))


private lemma antidiagonal_mixed_has_zero_pair {a b : Fin 4 →₀ ℕ}
    (hab : a + b = Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
      Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1)
    (ha : (a.sum fun _ e => e) ≤ 2) (hb : (b.sum fun _ e => e) ≤ 2) :
    a = Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 ∨
    a = Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1 ∨
    a = Finsupp.single (0 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 ∨
    b = Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 ∨
    b = Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1 ∨
    b = Finsupp.single (0 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 := by
  have hm : (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
      Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1).sum (fun _ e => e) = 4 := by
    rw [finsupp_degree_eq_univ_sum]
    simp [Fin.sum_univ_four]
  have hdeg := degree_two_of_add_degree_four hab hm ha hb
  rw [finsupp_degree_eq_univ_sum] at hdeg
  simp [Fin.sum_univ_four] at hdeg
  have h0 := Finsupp.ext_iff.mp hab (0 : Fin 4)
  have h1 := Finsupp.ext_iff.mp hab (1 : Fin 4)
  have h2 := Finsupp.ext_iff.mp hab (2 : Fin 4)
  have h3 := Finsupp.ext_iff.mp hab (3 : Fin 4)
  simp at h0 h1 h2 h3
  have ha0le : a 0 ≤ 1 := by omega
  have ha1le : a 1 ≤ 1 := by omega
  have ha2le : a 2 ≤ 1 := by omega
  interval_cases h0a : a 0
  · have hb0 : b 0 = 1 := by omega
    have hb1le : b 1 ≤ 1 := by omega
    have hb2le : b 2 ≤ 1 := by omega
    interval_cases h1b : b 1
    · interval_cases h2b : b 2
      · right; right; right; right; right
        ext k
        fin_cases k
        all_goals simp [hb0, h1b, h2b]
        all_goals omega
      · right; right; right; right; left
        ext k
        fin_cases k
        all_goals simp [hb0, h1b, h2b]
        all_goals omega
    · right; right; right; left
      ext k
      fin_cases k
      all_goals simp [hb0, h1b]
      all_goals omega
  · interval_cases h1a : a 1
    · interval_cases h2a : a 2
      · right; right; left
        ext k
        fin_cases k
        all_goals simp [h0a, h1a, h2a]
        all_goals omega
      · right; left
        ext k
        fin_cases k
        all_goals simp [h0a, h1a, h2a]
        all_goals omega
    · left
      ext k
      fin_cases k
      all_goals simp [h0a, h1a]
      all_goals omega

private lemma coeff_mixed_sq_zero_of_totalDegree_le_two
    {p : MvPolynomial (Fin 4) ℝ} (hp : p.totalDegree ≤ 2)
    (h01 : legacyCoeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1) p = 0)
    (h02 : legacyCoeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (2 : Fin 4) 1) p = 0)
    (h03 : legacyCoeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1) p = 0) :
    legacyCoeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
      Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1) (p ^ 2) = 0 := by
  rw [pow_two, MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases hleft : (x.1.sum fun _ e => e) ≤ 2
  · by_cases hright : (x.2.sum fun _ e => e) ≤ 2
    · have hcases := antidiagonal_mixed_has_zero_pair hx hleft hright
      rcases hcases with hcase | hcase | hcase | hcase | hcase | hcase
      · simp [hcase, h01]
      · simp [hcase, h02]
      · simp [hcase, h03]
      · simp [hcase, h01]
      · simp [hcase, h02]
      · simp [hcase, h03]
    · have hzero : legacyCoeff x.2 p = 0 := by
        apply coeff_eq_zero_of_totalDegree_lt hp
        omega
      simp [hzero]
  · have hzero : legacyCoeff x.1 p = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt hp
      omega
    simp [hzero]


private lemma choiLamQuartic_coeff_mixed :
    legacyCoeff (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
      Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1) choiLamQuartic = -4 := by
  unfold choiLamQuartic
  rw [X_pow_eq_monomial]
  rw [X_pow_mul_X_pow_eq_monomial, X_pow_mul_X_pow_eq_monomial,
    X_pow_mul_X_pow_eq_monomial, four_X_prod_eq_monomial]
  have h1 : Finsupp.single (0 : Fin 4) 4 ≠
      Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h2 : Finsupp.single (1 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h3 : Finsupp.single (2 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  have h4 : Finsupp.single (3 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 := by
    intro h; have := Finsupp.ext_iff.mp h (0 : Fin 4); simp at this
  simp [MvPolynomial.coeff_monomial, h1, h2, h3, h4]

/-- The Choi-Lam quartic is not a sum of squares. -/
theorem choiLamQuartic_not_sos :
    ¬ IsSOS choiLamQuartic := by
  rintro ⟨N, P, hP⟩
  have hdeg : ∀ i, (P i).totalDegree ≤ 2 := choiLam_sos_summand_totalDegree_le_two hP
  let m : Fin 4 →₀ ℕ := Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
    Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1
  have hm_zero : legacyCoeff m (∑ i : Fin N, (P i) ^ 2) = 0 := by
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro i _
    exact coeff_mixed_sq_zero_of_totalDegree_le_two (p := P i) (hdeg i)
      (coeff_zero_one_eq_zero_of_sos_choiLam hP hdeg (by decide : (1 : Fin 4) ≠ 0) i)
      (coeff_zero_one_eq_zero_of_sos_choiLam hP hdeg (by decide : (2 : Fin 4) ≠ 0) i)
      (coeff_zero_one_eq_zero_of_sos_choiLam hP hdeg (by decide : (3 : Fin 4) ≠ 0) i)
  have hm_neg : legacyCoeff m (∑ i : Fin N, (P i) ^ 2) = -4 := by
    rw [← hP]
    exact choiLamQuartic_coeff_mixed
  nlinarith

/-- Coefficient `L¹` distance between two four-variable polynomials. -/
def coeffL1Distance4 (P S : MvPolynomial (Fin 4) ℝ) : ℝ :=
  ∑ α ∈ (P - S).support, |legacyCoeff α (P - S)|

/-- Coefficient `L¹` distance from `choiLamQuartic` to a candidate SOS polynomial. -/
def choiLamCoeffDistanceToSOS (S : MvPolynomial (Fin 4) ℝ) : ℝ :=
  coeffL1Distance4 choiLamQuartic S

theorem coeffL1Distance4_nonneg (P S : MvPolynomial (Fin 4) ℝ) :
    0 ≤ coeffL1Distance4 P S := by
  unfold coeffL1Distance4
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem choiLamCoeffDistanceToSOS_nonneg (S : MvPolynomial (Fin 4) ℝ) :
    0 ≤ choiLamCoeffDistanceToSOS S := by
  unfold choiLamCoeffDistanceToSOS
  exact coeffL1Distance4_nonneg choiLamQuartic S

/-- An SOS polynomial of total degree at most four has square-root summands of
degree at most two.  This packages the no-cancellation degree lemma for the
quartic cone. -/
theorem degreeBoundedSOS_of_isSOS_totalDegree_le_four
    {S : MvPolynomial (Fin 4) ℝ}
    (hS : IsSOS S) (hdeg : S.totalDegree ≤ 4) :
    Nonempty (DegreeBoundedSOS S 2) := by
  rcases hS with ⟨N, P, hP⟩
  refine ⟨⟨N, P, hP, ?_⟩⟩
  have hdeg' : S.totalDegree ≤ 2 * 2 := by simpa using hdeg
  exact sos_summand_totalDegree_le_of_sum_sq_totalDegree hP hdeg'

/-- All coefficient distances from `choiLamQuartic` to a degree-four SOS
polynomial, represented by square roots of degree at most two. -/
def choiLamSosDistanceSet : Set ℝ :=
  {d | ∃ S : MvPolynomial (Fin 4) ℝ,
    Nonempty (DegreeBoundedSOS S 2) ∧ d = choiLamCoeffDistanceToSOS S}

theorem choiLamSosDistanceSet_nonempty : choiLamSosDistanceSet.Nonempty := by
  refine ⟨choiLamCoeffDistanceToSOS 0, ?_⟩
  refine ⟨0, ?_, rfl⟩
  refine ⟨⟨0, ?_, ?_, ?_⟩⟩
  · intro i
    exact Fin.elim0 i
  · simp
  · intro i
    exact Fin.elim0 i

theorem choiLamSosDistanceSet_bddBelow : BddBelow choiLamSosDistanceSet := by
  refine ⟨0, ?_⟩
  intro d hd
  rcases hd with ⟨S, _hS, rfl⟩
  exact choiLamCoeffDistanceToSOS_nonneg S

/-- The coefficient-distance from `choiLamQuartic` to the degree-four SOS cone. -/
noncomputable def choiLamSosDistance : ℝ :=
  sInf choiLamSosDistanceSet

theorem choiLamSosDistance_nonneg : 0 ≤ choiLamSosDistance := by
  unfold choiLamSosDistance
  exact le_csInf choiLamSosDistanceSet_nonempty
    (by
      intro d hd
      rcases hd with ⟨S, _hS, rfl⟩
      exact choiLamCoeffDistanceToSOS_nonneg S)

/-- Closedness of the degree-four SOS cone in four variables for the coefficient
`L¹` topology.  Equivalently, if a degree-at-most-four polynomial has zero
distance to degree-four SOS polynomials, then it is itself degree-four SOS. -/
theorem degreeFourSOSCone_closed_coeffL1
    {P : MvPolynomial (Fin 4) ℝ}
    (hPdeg : P.totalDegree ≤ 4)
    (hdist : sInf {d | ∃ S : MvPolynomial (Fin 4) ℝ,
      Nonempty (DegreeBoundedSOS S 2) ∧ d = coeffL1Distance4 P S} = 0) :
    Nonempty (DegreeBoundedSOS P 2) := by
  apply degreeBoundedSOSCone_closed_coeffL1 (n := 4) (r := 2)
  · simpa using hPdeg
  · simpa [coeffL1Distance4, coeffL1Distance] using hdist

/-- The Choi-Lam quartic has positive coefficient distance from the degree-four
SOS cone. -/
theorem choiLamSosDistance_pos : 0 < choiLamSosDistance := by
  by_contra hnot
  have hle : choiLamSosDistance ≤ 0 := le_of_not_gt hnot
  have hzero : choiLamSosDistance = 0 := le_antisymm hle choiLamSosDistance_nonneg
  rcases degreeFourSOSCone_closed_coeffL1 choiLamQuartic_totalDegree_le_four (by
      simpa [choiLamSosDistance, choiLamSosDistanceSet, choiLamCoeffDistanceToSOS]
        using hzero) with ⟨hbounded⟩
  exact choiLamQuartic_not_sos hbounded.toIsSOS

theorem choiLamSosDistance_le_distance_to_sos {S : MvPolynomial (Fin 4) ℝ}
    (hS : IsSOS S) (hdeg : S.totalDegree ≤ 4) :
    choiLamSosDistance ≤ choiLamCoeffDistanceToSOS S := by
  unfold choiLamSosDistance
  exact csInf_le choiLamSosDistanceSet_bddBelow
    ⟨S, degreeBoundedSOS_of_isSOS_totalDegree_le_four hS hdeg, rfl⟩

end OptimalConvergenceRates

end
