/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/Motzkin/UpperBound.lean

  Matching Schmuedgen upper-bound certificate for the perturbed Motzkin sextic.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.MainProof
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.ChoiLamTight

open MvPolynomial Finset Polynomial

noncomputable section

namespace OptimalConvergenceRates
namespace Motzkin

/-! ## Fixed Motzkin polynomials -/

/-- The quadratic `a = x^2 + z^2` used in the explicit Motzkin certificate. -/
def motzkinA : MvPolynomial (Fin 3) ℝ :=
  X (0 : Fin 3) ^ 2 + X (2 : Fin 3) ^ 2

/-- Substitute a univariate polynomial in `a = x^2 + z^2`. -/
def polynomialInMotzkinA (p : Polynomial ℝ) : MvPolynomial (Fin 3) ℝ :=
  Polynomial.aeval motzkinA p

@[simp] theorem polynomialInMotzkinA_X :
    polynomialInMotzkinA Polynomial.X = motzkinA := by
  simp [polynomialInMotzkinA]

@[simp] theorem polynomialInMotzkinA_C (c : ℝ) :
    polynomialInMotzkinA (Polynomial.C c) = MvPolynomial.C c := by
  simp [polynomialInMotzkinA]

@[simp] theorem polynomialInMotzkinA_add (p q : Polynomial ℝ) :
    polynomialInMotzkinA (p + q) = polynomialInMotzkinA p + polynomialInMotzkinA q := by
  simp [polynomialInMotzkinA]

@[simp] theorem polynomialInMotzkinA_mul (p q : Polynomial ℝ) :
    polynomialInMotzkinA (p * q) = polynomialInMotzkinA p * polynomialInMotzkinA q := by
  simp [polynomialInMotzkinA]

@[simp] theorem polynomialInMotzkinA_pow (p : Polynomial ℝ) (k : ℕ) :
    polynomialInMotzkinA (p ^ k) = polynomialInMotzkinA p ^ k := by
  simp [polynomialInMotzkinA]

/-- The fixed SOS identity `a * Mtz = SOS`. -/
theorem motzkinA_mul_motzkinSextic_isSOS :
    IsSOS (motzkinA * motzkinSextic) := by
  let q0 : MvPolynomial (Fin 3) ℝ := X (2 : Fin 3) ^ 4 - X (0 : Fin 3) ^ 2 * X 1 ^ 2
  let q1 : MvPolynomial (Fin 3) ℝ := X 0 * X 2 * (X 2 ^ 2 - X 1 ^ 2)
  let q2 : MvPolynomial (Fin 3) ℝ := X 0 * X 1 * (X 2 ^ 2 - X 0 ^ 2)
  have hsos : IsSOS (q0 ^ 2 + q1 ^ 2 + q2 ^ 2) :=
    IsSOS_add (IsSOS_add (IsSOS_sq q0) (IsSOS_sq q1)) (IsSOS_sq q2)
  convert hsos using 1
  simp [q0, q1, q2, motzkinA, motzkinSextic]
  ring

/-- The fixed SOS identity `Mtz + a^3 = SOS`. -/
theorem motzkinSextic_add_motzkinA_cube_isSOS :
    IsSOS (motzkinSextic + motzkinA ^ 3) := by
  let q0 : MvPolynomial (Fin 3) ℝ := X (0 : Fin 3) ^ 3
  let q1 : MvPolynomial (Fin 3) ℝ := X 0 ^ 2 * X 1
  let q2 : MvPolynomial (Fin 3) ℝ :=
    X 0 * X 1 ^ 2 - MvPolynomial.C (3 / 2) * X 0 * X 2 ^ 2
  let q3 : MvPolynomial (Fin 3) ℝ := MvPolynomial.C (1 / 2) * X 0 * X 2 ^ 2
  let q4 : MvPolynomial (Fin 3) ℝ := X 0 ^ 2 * X 2
  let q5 : MvPolynomial (Fin 3) ℝ := X 2 ^ 3
  have hsos : IsSOS
      (q0 ^ 2 + q1 ^ 2 + q2 ^ 2 + q3 ^ 2 + q3 ^ 2 + q3 ^ 2 +
        q4 ^ 2 + q4 ^ 2 + q4 ^ 2 + q5 ^ 2 + q5 ^ 2) := by
    repeat first | apply IsSOS_add | apply IsSOS_sq
  convert hsos using 1
  have hthreehalf_two : ∀ p : MvPolynomial (Fin 3) ℝ,
      p * MvPolynomial.C (3 / 2 : ℝ) * 2 = p * 3 := by
    intro p
    change p * MvPolynomial.C (3 / 2 : ℝ) * MvPolynomial.C (2 : ℝ) =
      p * MvPolynomial.C (3 : ℝ)
    rw [mul_assoc, ← MvPolynomial.C_mul]
    norm_num
  have hthreehalf_sq : ∀ p : MvPolynomial (Fin 3) ℝ,
      p * MvPolynomial.C (3 / 2 : ℝ) ^ 2 = p * MvPolynomial.C (9 / 4 : ℝ) := by
    intro p
    rw [← MvPolynomial.C_pow]
    norm_num
  simp [q0, q1, q2, q3, q4, q5, motzkinA, motzkinSextic]
  ring_nf
  simp [hthreehalf_two, hthreehalf_sq]
  ring_nf
  have hhalf_sq_Cthree (p : MvPolynomial (Fin 3) ℝ) :
      p * MvPolynomial.C (1 / 2 : ℝ) ^ 2 * MvPolynomial.C (3 : ℝ) =
        p * MvPolynomial.C (3 / 4 : ℝ) := by
    rw [mul_assoc, ← MvPolynomial.C_pow, ← MvPolynomial.C_mul]
    norm_num
  have hcoeff (p : MvPolynomial (Fin 3) ℝ) :
      p * 3 = p * MvPolynomial.C (9 / 4 : ℝ) +
        p * MvPolynomial.C (1 / 2 : ℝ) ^ 2 * 3 := by
    change p * MvPolynomial.C (3 : ℝ) =
      p * MvPolynomial.C (9 / 4 : ℝ) +
        p * MvPolynomial.C (1 / 2 : ℝ) ^ 2 * MvPolynomial.C (3 : ℝ)
    rw [hhalf_sq_Cthree p, ← mul_add, ← MvPolynomial.C_add]
    norm_num
  linear_combination hcoeff (X (0 : Fin 3) ^ 2 * X (2 : Fin 3) ^ 4)

theorem motzkinA_totalDegree_le_two : motzkinA.totalDegree ≤ 2 := by
  calc
    motzkinA.totalDegree ≤
        max ((X (0 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).totalDegree)
          ((X (2 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).totalDegree) := by
      exact MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := by
      rw [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X_pow]
      norm_num

theorem polynomialInMotzkinA_totalDegree_le (p : Polynomial ℝ) :
    (polynomialInMotzkinA p).totalDegree ≤ 2 * p.natDegree := by
  unfold polynomialInMotzkinA
  rw [Polynomial.aeval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  calc
    (p.coeff k • motzkinA ^ k).totalDegree ≤ (motzkinA ^ k).totalDegree :=
      MvPolynomial.totalDegree_smul_le _ _
    _ ≤ k * motzkinA.totalDegree := MvPolynomial.totalDegree_pow _ _
    _ ≤ k * 2 := Nat.mul_le_mul_left k motzkinA_totalDegree_le_two
    _ ≤ p.natDegree * 2 := by
      rw [Finset.mem_range] at hk
      exact Nat.mul_le_mul_right 2 (by omega)
    _ = 2 * p.natDegree := by omega

theorem motzkinA_mul_motzkinSextic_totalDegree_le_eight :
    (motzkinA * motzkinSextic).totalDegree ≤ 8 := by
  calc
    (motzkinA * motzkinSextic).totalDegree ≤
        motzkinA.totalDegree + motzkinSextic.totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 2 + 6 := Nat.add_le_add motzkinA_totalDegree_le_two
      motzkinSextic_totalDegree_le_six
    _ = 8 := by norm_num

theorem motzkinSextic_add_motzkinA_cube_totalDegree_le_six :
    (motzkinSextic + motzkinA ^ 3).totalDegree ≤ 6 := by
  calc
    (motzkinSextic + motzkinA ^ 3).totalDegree ≤
        max motzkinSextic.totalDegree (motzkinA ^ 3).totalDegree :=
      MvPolynomial.totalDegree_add _ _
    _ ≤ 6 := by
      apply max_le motzkinSextic_totalDegree_le_six
      calc
        (motzkinA ^ 3).totalDegree ≤ 3 * motzkinA.totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ ≤ 3 * 2 := Nat.mul_le_mul_left 3 motzkinA_totalDegree_le_two
        _ = 6 := by norm_num


/-! ## Cubic Chebyshev cutoff -/

/-- The cubic cutoff `R_m = F_m^3`. -/
def motzkinCutoffR (m : ℕ) : Polynomial ℝ :=
  choiLamCutoffF m ^ 3

/-- The quotient polynomial `P_m = (1 - R_m) / X`. -/
def motzkinCutoffP (m : ℕ) : Polynomial ℝ :=
  (1 - motzkinCutoffR m) /ₘ Polynomial.X

/-- The residual polynomial `H_m(t) = epsilon - t^3 R_m(t)`. -/
def motzkinCutoffH (epsilon : ℝ) (m : ℕ) : Polynomial ℝ :=
  Polynomial.C epsilon - Polynomial.X ^ 3 * motzkinCutoffR m

theorem motzkinCutoffR_eval_zero (m : ℕ) (hm : m ≠ 0) :
    (motzkinCutoffR m).eval 0 = 1 := by
  simp [motzkinCutoffR, choiLamCutoffF_eval_zero m hm]

theorem motzkinCutoffX_mul_P_add_R (m : ℕ) (hm : m ≠ 0) :
    Polynomial.X * motzkinCutoffP m + motzkinCutoffR m = 1 := by
  have hroot : Polynomial.IsRoot (1 - motzkinCutoffR m : Polynomial ℝ) 0 := by
    rw [Polynomial.IsRoot.def]
    simp [motzkinCutoffR_eval_zero m hm]
  have hmul : Polynomial.X * motzkinCutoffP m = 1 - motzkinCutoffR m := by
    unfold motzkinCutoffP
    simpa using (Polynomial.mul_divByMonic_eq_iff_isRoot
      (p := (1 - motzkinCutoffR m : Polynomial ℝ)) (a := 0)).mpr hroot
  rw [hmul]
  ring

theorem motzkinCutoffR_natDegree_le (m : ℕ) (hm : 1 ≤ m) :
    (motzkinCutoffR m).natDegree ≤ 3 * m - 3 := by
  unfold motzkinCutoffR
  calc
    (choiLamCutoffF m ^ 3).natDegree ≤ 3 * (choiLamCutoffF m).natDegree :=
      Polynomial.natDegree_pow_le
    _ ≤ 3 * (m - 1) := Nat.mul_le_mul_left 3 (choiLamCutoffF_natDegree_le m hm)
    _ = 3 * m - 3 := by omega

theorem motzkinCutoffP_natDegree_le (m : ℕ) (hm : 2 ≤ m) :
    (motzkinCutoffP m).natDegree ≤ 3 * m - 4 := by
  unfold motzkinCutoffP
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  calc
    ((1 - motzkinCutoffR m) /ₘ Polynomial.X).natDegree
        ≤ (1 - motzkinCutoffR m : Polynomial ℝ).natDegree -
            Polynomial.X.natDegree := by
      rw [Polynomial.natDegree_divByMonic
        (1 - motzkinCutoffR m : Polynomial ℝ) Polynomial.monic_X]
    _ ≤ (3 * m - 3) - 1 := by
      have hsub : (1 - motzkinCutoffR m : Polynomial ℝ).natDegree ≤ 3 * m - 3 := by
        calc
          (1 - motzkinCutoffR m : Polynomial ℝ).natDegree
              ≤ max (1 : Polynomial ℝ).natDegree (motzkinCutoffR m).natDegree :=
            Polynomial.natDegree_sub_le _ _
          _ ≤ 3 * m - 3 := by
            apply max_le
            · simp
            · exact motzkinCutoffR_natDegree_le m hm1
      simpa using Nat.sub_le_sub_right hsub 1
    _ = 3 * m - 4 := by omega

theorem motzkinCutoffH_natDegree_le (epsilon : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    (motzkinCutoffH epsilon m).natDegree ≤ 3 * m := by
  unfold motzkinCutoffH
  calc
    (Polynomial.C epsilon - Polynomial.X ^ 3 * motzkinCutoffR m).natDegree
        ≤ max (Polynomial.C epsilon).natDegree
          (Polynomial.X ^ 3 * motzkinCutoffR m).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ 3 * m := by
      apply max_le
      · simp
      · calc
          (Polynomial.X ^ 3 * motzkinCutoffR m).natDegree
              ≤ (Polynomial.X ^ 3 : Polynomial ℝ).natDegree +
                  (motzkinCutoffR m).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 3 + (3 * m - 3) := by
            exact Nat.add_le_add (by simp) (motzkinCutoffR_natDegree_le m hm)
          _ = 3 * m := by omega

theorem choiLamCutoffF_nonneg_on_Icc (m : ℕ) (hm : 1 ≤ m) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 2 → 0 ≤ (choiLamCutoffF m).eval t := by
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0
    rw [choiLamCutoffF_eval_zero m (by omega)]
    norm_num
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hT := chebyshevT_abs_le_one m (1 - t) (by linarith [ht.2]) (by linarith [ht.1])
    have hTone : (chebyshevT m).eval (1 - t) ≤ 1 := (abs_le.mp hT).2
    have htf := choiLamCutoff_t_mul_F_eval m t
    have hprod : 0 ≤ t * (choiLamCutoffF m).eval t := by
      rw [htf]
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hTone)
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hprod) htpos

theorem motzkinCutoffR_mem_Icc (m : ℕ) (hm : 1 ≤ m) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 2 →
      (motzkinCutoffR m).eval t ∈ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  let x := (choiLamCutoffF m).eval t
  have hx0 : 0 ≤ x := choiLamCutoffF_nonneg_on_Icc m hm t ht
  have hxabs := choiLamCutoffF_abs_le_one_on_Icc m hm t ht
  have hx1 : x ≤ 1 := (le_abs_self x).trans hxabs
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have hx3 : x ^ 3 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]
  unfold motzkinCutoffR
  simp only [Polynomial.eval_pow]
  exact ⟨by positivity, hx3.trans hx2⟩

theorem motzkinCutoffP_nonneg_on_Icc (m : ℕ) (hm : 1 ≤ m) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 2 → 0 ≤ (motzkinCutoffP m).eval t := by
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0
    exact polynomial_eval_zero_nonneg_of_right_nonneg (motzkinCutoffP m) (by
      intro u hu hu2
      have huI : u ∈ Set.Icc (0 : ℝ) 2 := ⟨hu.le, hu2⟩
      have hR := (motzkinCutoffR_mem_Icc m hm u huI).2
      have hPR :=
        congrArg (Polynomial.eval u) (motzkinCutoffX_mul_P_add_R m (by omega))
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_one] at hPR
      have huP : u * (motzkinCutoffP m).eval u = 1 - (motzkinCutoffR m).eval u := by
        linarith
      rw [← mul_nonneg_iff_of_pos_left hu]
      rw [huP]
      exact sub_nonneg.mpr hR)
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hR := (motzkinCutoffR_mem_Icc m hm t ht).2
    have hPR :=
      congrArg (Polynomial.eval t) (motzkinCutoffX_mul_P_add_R m (by omega))
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_one] at hPR
    have htP : t * (motzkinCutoffP m).eval t = 1 - (motzkinCutoffR m).eval t := by
      linarith
    rw [← mul_nonneg_iff_of_pos_left htpos]
    rw [htP]
    exact sub_nonneg.mpr hR

theorem motzkinCutoffH_nonneg_on_Icc
    (epsilon : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (heps_bound : 8 / (m : ℝ) ^ 6 ≤ epsilon) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 2 → 0 ≤ (motzkinCutoffH epsilon m).eval t := by
  intro t ht
  have hT := chebyshevT_abs_le_one m (1 - t) (by linarith [ht.2]) (by linarith [ht.1])
  let N : ℝ := 1 - (chebyshevT m).eval (1 - t)
  have hN0 : 0 ≤ N := by
    dsimp [N]
    linarith [(abs_le.mp hT).2]
  have hN2 : N ≤ 2 := by
    dsimp [N]
    linarith [(abs_le.mp hT).1]
  have hNsq : N ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hN2)]
  have hNcube : N ^ 3 ≤ 8 := by
    nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.mpr hN2)]
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have htf := choiLamCutoff_t_mul_F_eval m t
  have hmain : t ^ 3 * (choiLamCutoffF m).eval t ^ 3 ≤ 8 / (m : ℝ) ^ 6 := by
    have hcube :
        (t * (choiLamCutoffF m).eval t) ^ 3 =
          ((m : ℝ) ^ 2)⁻¹ ^ 3 * N ^ 3 := by
      rw [htf]
      dsimp [N]
      ring
    have hscale : 0 ≤ ((m : ℝ) ^ 2)⁻¹ ^ 3 := by positivity
    calc
      t ^ 3 * (choiLamCutoffF m).eval t ^ 3 =
          (t * (choiLamCutoffF m).eval t) ^ 3 := by ring
      _ = ((m : ℝ) ^ 2)⁻¹ ^ 3 * N ^ 3 := hcube
      _ ≤ ((m : ℝ) ^ 2)⁻¹ ^ 3 * 8 :=
        mul_le_mul_of_nonneg_left hNcube hscale
      _ = 8 / (m : ℝ) ^ 6 := by
        field_simp [ne_of_gt hmpos]
  unfold motzkinCutoffH motzkinCutoffR
  simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
  linarith


/-! ## Interval-to-box lifting -/

private theorem interval_nonneg_comp_motzkinA_mul_sos_mem_box_qm
    (h : Polynomial ℝ) (S : MvPolynomial (Fin 3) ℝ) (D E r : ℕ)
    (h_nonneg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 2 → 0 ≤ h.eval t)
    (hdeg : h.natDegree ≤ D)
    (hS : IsSOS S) (hSdeg : S.totalDegree ≤ E)
    (hr : 2 * (D + 1) + E ≤ r) :
    polynomialInMotzkinA h * S ∈ BoxQuadraticModule 3 r := by
  classical
  let q : Polynomial ℝ := h.comp (Polynomial.X + 1)
  have hqdeg : q.natDegree ≤ D := by
    dsimp [q]
    calc
      (h.comp (Polynomial.X + 1)).natDegree
          ≤ h.natDegree * (Polynomial.X + 1 : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ D * 1 := by
        have hlin : (Polynomial.X + 1 : Polynomial ℝ).natDegree ≤ 1 :=
          (Polynomial.natDegree_add_le _ _).trans (by simp)
        exact Nat.mul_le_mul hdeg hlin
      _ = D := by simp
  have hqnonneg : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ q.eval x := by
    intro x hx
    have hx02 : x + 1 ∈ Set.Icc (0 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa [q, Polynomial.eval_comp, add_comm] using h_nonneg (x + 1) hx02
  obtain ⟨s0, s1, hsos0, hsos1, hdeg0, hdeg1, hqeq⟩ :=
    markov_lukacz q hqdeg hqnonneg
  let shift : Polynomial ℝ → MvPolynomial (Fin 3) ℝ := fun p =>
    Polynomial.aeval (motzkinA - 1) p
  let tau0 : MvPolynomial (Fin 3) ℝ := shift s0 * S
  let tau : MvPolynomial (Fin 3) ℝ := shift s1 * motzkinA * S
  let sigma : Fin 3 → MvPolynomial (Fin 3) ℝ := fun i =>
    if i = 0 ∨ i = 2 then tau else 0
  have hshift_sos0 : IsSOS (shift s0) := by
    obtain ⟨N, w, hw⟩ := hsos0
    refine ⟨N, fun i ↦ shift (w i), ?_⟩
    dsimp [shift]
    rw [hw]
    simp [map_sum, map_pow]
  have hshift_sos1 : IsSOS (shift s1) := by
    obtain ⟨N, w, hw⟩ := hsos1
    refine ⟨N, fun i ↦ shift (w i), ?_⟩
    dsimp [shift]
    rw [hw]
    simp [map_sum, map_pow]
  have htau0sos : IsSOS tau0 := IsSOS_mul hshift_sos0 hS
  have htausos : IsSOS tau := IsSOS_mul (IsSOS_mul hshift_sos1 (by
    refine ⟨2, fun i ↦ if i = 0 then X (0 : Fin 3) else X (2 : Fin 3), ?_⟩
    rw [Fin.sum_univ_two]
    simp [motzkinA])) hS
  have hshift_deg_le : ∀ p : Polynomial ℝ, (shift p).totalDegree ≤ 2 * p.natDegree := by
    intro p
    dsimp [shift]
    rw [Polynomial.aeval_eq_sum_range]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    have hbase : (motzkinA - 1 : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 2 := by
      calc
        (motzkinA - 1 : MvPolynomial (Fin 3) ℝ).totalDegree
            ≤ max motzkinA.totalDegree (1 : MvPolynomial (Fin 3) ℝ).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
        _ ≤ 2 := max_le motzkinA_totalDegree_le_two (by simp)
    calc
      (p.coeff k • (motzkinA - 1 : MvPolynomial (Fin 3) ℝ) ^ k).totalDegree
          ≤ ((motzkinA - 1 : MvPolynomial (Fin 3) ℝ) ^ k).totalDegree :=
        MvPolynomial.totalDegree_smul_le _ _
      _ ≤ k * (motzkinA - 1 : MvPolynomial (Fin 3) ℝ).totalDegree :=
        MvPolynomial.totalDegree_pow _ _
      _ ≤ k * 2 := Nat.mul_le_mul_left k hbase
      _ ≤ p.natDegree * 2 := by
        rw [Finset.mem_range] at hk
        exact Nat.mul_le_mul_right 2 (by omega)
      _ = 2 * p.natDegree := by omega
  have hs1_nat_of_ne_zero : s1 ≠ 0 → s1.natDegree + 2 ≤ D + 1 := by
    intro hs1
    have hone : (1 - Polynomial.X ^ 2 : Polynomial ℝ) ≠ 0 := by
      intro hz
      have hz0 := congrArg (Polynomial.eval (0 : ℝ)) hz
      norm_num at hz0
    have hprod :
        (s1 * (1 - Polynomial.X ^ 2 : Polynomial ℝ)).natDegree = s1.natDegree + 2 := by
      rw [Polynomial.natDegree_mul hs1 hone, natDegree_one_sub_X_sq_real]
    rw [← hprod]
    exact hdeg1
  have hdeg_tau0 : tau0.totalDegree ≤ r := by
    calc
      tau0.totalDegree ≤ (shift s0).totalDegree + S.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * s0.natDegree + E := by
        have hs := hshift_deg_le s0
        omega
      _ ≤ 2 * (D + 1) + E := by omega
      _ ≤ r := hr
  have hgenerator_deg (i : Fin 3) :
      (BoxSemialgebraicGenerator i).totalDegree ≤ 2 := by
    unfold BoxSemialgebraicGenerator
    calc
      (1 - X i ^ 2 : MvPolynomial (Fin 3) ℝ).totalDegree
          ≤ max (1 : MvPolynomial (Fin 3) ℝ).totalDegree (X i ^ 2).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
      _ ≤ 2 := by
        rw [MvPolynomial.totalDegree_X_pow]
        simp
  have hdeg_tau_generator (i : Fin 3) :
      (tau * BoxSemialgebraicGenerator i).totalDegree ≤ r := by
    by_cases hs1 : s1 = 0
    · subst hs1
      simp [tau, shift]
    · have hs1deg := hs1_nat_of_ne_zero hs1
      calc
        (tau * BoxSemialgebraicGenerator i).totalDegree
            ≤ tau.totalDegree + (BoxSemialgebraicGenerator i).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ (2 * s1.natDegree + 2 + E) + 2 := by
          have htau : tau.totalDegree ≤ 2 * s1.natDegree + 2 + E := by
            dsimp [tau]
            calc
              (shift s1 * motzkinA * S).totalDegree
                  ≤ (shift s1 * motzkinA).totalDegree + S.totalDegree :=
                MvPolynomial.totalDegree_mul _ _
              _ ≤ ((shift s1).totalDegree + motzkinA.totalDegree) + S.totalDegree := by
                exact Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
              _ ≤ (2 * s1.natDegree + 2) + E := by
                have hs := hshift_deg_le s1
                have ha := motzkinA_totalDegree_le_two
                omega
              _ = 2 * s1.natDegree + 2 + E := by omega
          exact Nat.add_le_add htau (hgenerator_deg i)
        _ ≤ 2 * (D + 1) + E := by omega
        _ ≤ r := hr
  refine ⟨tau0, sigma, htau0sos, ?_, hdeg_tau0, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [sigma] using htausos
    · change IsSOS 0
      exact IsSOS_zero
    · simpa [sigma] using htausos
  · intro i
    fin_cases i
    · simpa [sigma] using hdeg_tau_generator (0 : Fin 3)
    · simp [sigma]
    · simpa [sigma] using hdeg_tau_generator (2 : Fin 3)
  · have hsubst : Polynomial.aeval (motzkinA - 1) q = polynomialInMotzkinA h := by
      dsimp [q, polynomialInMotzkinA]
      rw [Polynomial.aeval_comp]
      simp
    have hqsub := congrArg (Polynomial.aeval (motzkinA - 1)) hqeq
    rw [hsubst] at hqsub
    dsimp [tau0, tau, shift]
    rw [hqsub]
    simp [sigma, tau, shift, Fin.sum_univ_three, BoxSemialgebraicGenerator, motzkinA]
    ring


/-! ## Explicit certificate -/

theorem motzkin_tight_identity (epsilon : ℝ) (m : ℕ) (hm : m ≠ 0) :
    motzkinPerturbed epsilon =
      polynomialInMotzkinA (motzkinCutoffP m) * (motzkinA * motzkinSextic)
        + polynomialInMotzkinA (motzkinCutoffR m) * (motzkinSextic + motzkinA ^ 3)
        + polynomialInMotzkinA (motzkinCutoffH epsilon m) := by
  have hPR := congrArg polynomialInMotzkinA (motzkinCutoffX_mul_P_add_R m hm)
  simp [polynomialInMotzkinA] at hPR
  unfold motzkinPerturbed motzkinCutoffH
  simp [polynomialInMotzkinA]
  ring_nf
  nth_rewrite 1 [show motzkinSextic =
      (motzkinA * (Polynomial.aeval motzkinA) (motzkinCutoffP m) +
        (Polynomial.aeval motzkinA) (motzkinCutoffR m)) * motzkinSextic by
    rw [hPR]
    ring]
  ring

theorem motzkin_tight_term1_mem_box_qm (m : ℕ) (hm : 2 ≤ m) :
    polynomialInMotzkinA (motzkinCutoffP m) * (motzkinA * motzkinSextic) ∈
      BoxQuadraticModule 3 (6 * m + 2) := by
  refine interval_nonneg_comp_motzkinA_mul_sos_mem_box_qm
    (motzkinCutoffP m) (motzkinA * motzkinSextic) (3 * m - 4) 8
    (6 * m + 2) (motzkinCutoffP_nonneg_on_Icc m (by omega))
    (motzkinCutoffP_natDegree_le m hm) motzkinA_mul_motzkinSextic_isSOS
    motzkinA_mul_motzkinSextic_totalDegree_le_eight ?_
  omega

theorem motzkin_tight_term2_mem_box_qm (m : ℕ) (hm : 1 ≤ m) :
    polynomialInMotzkinA (motzkinCutoffR m) * (motzkinSextic + motzkinA ^ 3) ∈
      BoxQuadraticModule 3 (6 * m + 2) := by
  refine interval_nonneg_comp_motzkinA_mul_sos_mem_box_qm
    (motzkinCutoffR m) (motzkinSextic + motzkinA ^ 3) (3 * m - 3) 6
    (6 * m + 2) (fun t ht ↦ (motzkinCutoffR_mem_Icc m hm t ht).1)
    (motzkinCutoffR_natDegree_le m hm) motzkinSextic_add_motzkinA_cube_isSOS
    motzkinSextic_add_motzkinA_cube_totalDegree_le_six ?_
  omega

theorem motzkin_tight_term3_mem_box_qm
    (epsilon : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (heps_bound : 8 / (m : ℝ) ^ 6 ≤ epsilon) :
    polynomialInMotzkinA (motzkinCutoffH epsilon m) ∈
      BoxQuadraticModule 3 (6 * m + 2) := by
  have hS : IsSOS (1 : MvPolynomial (Fin 3) ℝ) :=
    ⟨1, fun _ ↦ 1, by simp⟩
  simpa [mul_one] using
    interval_nonneg_comp_motzkinA_mul_sos_mem_box_qm
      (motzkinCutoffH epsilon m) 1 (3 * m) 0 (6 * m + 2)
      (motzkinCutoffH_nonneg_on_Icc epsilon m hm heps_bound)
      (motzkinCutoffH_natDegree_le epsilon m hm) hS (by simp) (by omega)

/-- Explicit Motzkin quadratic-module certificate with sixth-root cutoff parameter `m`. -/
theorem motzkinPerturbed_mem_BoxQuadraticModule_tight_of_m
    (epsilon : ℝ) (heps : 0 < epsilon)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (8 / epsilon) ^ ((1 : ℝ) / 6) ≤ (m : ℝ)) :
    motzkinPerturbed epsilon ∈ BoxQuadraticModule 3 (6 * m + 2) := by
  have heps_bound : 8 / (m : ℝ) ^ 6 ≤ epsilon := by
    have hbase_nonneg : 0 ≤ 8 / epsilon := by positivity
    have hroot_nonneg : 0 ≤ (8 / epsilon) ^ ((1 : ℝ) / 6) := by positivity
    have hpow := Real.rpow_le_rpow hroot_nonneg hm_eps (show 0 ≤ (6 : ℝ) by norm_num)
    have hleft : ((8 / epsilon) ^ ((1 : ℝ) / 6)) ^ (6 : ℝ) = 8 / epsilon := by
      rw [← Real.rpow_mul hbase_nonneg]
      norm_num
    have hsix_div : 8 / epsilon ≤ (m : ℝ) ^ 6 := by
      have hsixth : ((1 : ℝ) / 6) = (6 : ℝ)⁻¹ := by norm_num
      rw [← hleft]
      simpa [hsixth] using hpow
    have hmpos : 0 < (m : ℝ) ^ 6 := by positivity
    have hcross : 8 ≤ (m : ℝ) ^ 6 * epsilon := (div_le_iff₀ heps).mp hsix_div
    rw [div_le_iff₀ hmpos]
    nlinarith
  rw [motzkin_tight_identity epsilon m (by omega)]
  exact BoxQuadraticModule_add
    (BoxQuadraticModule_add
      (motzkin_tight_term1_mem_box_qm m hm)
      (motzkin_tight_term2_mem_box_qm m (by omega)))
    (motzkin_tight_term3_mem_box_qm epsilon m (by omega) heps_bound)

/-- The explicit Motzkin quadratic-module certificate is also a box-preordering
certificate at the same weighted degree. -/
theorem motzkinPerturbed_mem_BoxPreordering_tight_of_m
    (epsilon : ℝ) (heps : 0 < epsilon)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (8 / epsilon) ^ ((1 : ℝ) / 6) ≤ (m : ℝ)) :
    motzkinPerturbed epsilon ∈ BoxPreordering 3 (6 * m + 2) :=
  BoxQuadraticModule_subset_BoxPreordering
    (motzkinPerturbed_mem_BoxQuadraticModule_tight_of_m epsilon heps m hm hm_eps)

/-- Motzkin perturbations admit box-preordering certificates of weighted degree
`O(epsilon^(-1/6))`. -/
theorem motzkinPerturbed_mem_BoxPreordering_tight
    (epsilon : ℝ) (heps : 0 < epsilon) (heps8 : epsilon ≤ 8) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 28 * epsilon ^ (-(1 : ℝ) / 6) ∧
        motzkinPerturbed epsilon ∈ BoxPreordering 3 r := by
  let x : ℝ := epsilon ^ (-(1 : ℝ) / 6)
  let A : ℝ := (8 / epsilon) ^ ((1 : ℝ) / 6)
  let m : ℕ := max 2 (Nat.ceil A)
  refine ⟨6 * m + 2, ?_, ?_⟩
  · have hx_nonneg : 0 ≤ x := by positivity
    have hconst : (8 : ℝ) ^ ((1 : ℝ) / 6) ≤ 2 := by
      have hpow6 := Real.rpow_le_rpow (by norm_num : 0 ≤ (8 : ℝ))
        (by norm_num : (8 : ℝ) ≤ 2 ^ 6) (by norm_num : 0 ≤ (1 : ℝ) / 6)
      norm_num at hpow6
      exact hpow6
    have hx_ge_half : (1 / 2 : ℝ) ≤ x := by
      have hroot_le : epsilon ^ ((1 : ℝ) / 6) ≤ 2 := by
        have hpow := Real.rpow_le_rpow heps.le heps8
          (by norm_num : 0 ≤ (1 : ℝ) / 6)
        exact hpow.trans hconst
      have hroot_pos : 0 < epsilon ^ ((1 : ℝ) / 6) := by positivity
      have htmp : (1 / 2 : ℝ) ≤ 1 / epsilon ^ ((1 : ℝ) / 6) :=
        one_div_le_one_div_of_le hroot_pos hroot_le
      dsimp [x]
      rw [show (-(1 : ℝ) / 6) = -((1 : ℝ) / 6) by ring, Real.rpow_neg heps.le]
      simpa [one_div] using htmp
    have hA_le : A ≤ 2 * x := by
      dsimp [A, x]
      rw [Real.div_rpow (by norm_num : 0 ≤ (8 : ℝ)) heps.le]
      rw [show (-(1 : ℝ) / 6) = -((1 : ℝ) / 6) by ring, Real.rpow_neg heps.le]
      have hinv_nonneg : 0 ≤ (epsilon ^ ((1 : ℝ) / 6))⁻¹ := by positivity
      have hmul := mul_le_mul_of_nonneg_right hconst hinv_nonneg
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hceil_lt : (Nat.ceil A : ℝ) < A + 1 := Nat.ceil_lt_add_one (by positivity)
    have hceil_le : (Nat.ceil A : ℝ) ≤ 4 * x := by
      have : (Nat.ceil A : ℝ) < 4 * x := by nlinarith
      exact this.le
    have htwo_le : (2 : ℝ) ≤ 4 * x := by nlinarith
    have hm_le : (m : ℝ) ≤ 4 * x := by
      dsimp [m]
      rw [Nat.cast_max]
      exact max_le htwo_le hceil_le
    calc
      ((6 * m + 2 : ℕ) : ℝ) = 6 * (m : ℝ) + 2 := by norm_num
      _ ≤ 28 * x := by nlinarith
      _ = 28 * epsilon ^ (-(1 : ℝ) / 6) := by simp [x]
  · apply motzkinPerturbed_mem_BoxPreordering_tight_of_m
    · exact heps
    · simp [m]
    · have hceil : A ≤ (Nat.ceil A : ℝ) := Nat.le_ceil A
      have hceil_m : (Nat.ceil A : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.le_max_right 2 (Nat.ceil A)
      exact hceil.trans hceil_m

end Motzkin
end OptimalConvergenceRates

end
