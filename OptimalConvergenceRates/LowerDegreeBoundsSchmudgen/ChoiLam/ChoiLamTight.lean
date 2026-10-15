/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/ChoiLamTight.lean

  Matching Schmuedgen upper-bound certificate for the perturbed Choi-Lam quartic.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.MainProof
import OptimalConvergenceRates.MarkovLukacz.MarkovLukacz
import OptimalConvergenceRates.Chebyshev.ChebyshevGrowth
import Mathlib.Analysis.Calculus.MeanValue

open MvPolynomial Finset Polynomial

noncomputable section

namespace OptimalConvergenceRates

/-! ## Fixed Choi-Lam polynomials -/

/-- The quadratic `a = y^2 + z^2` used in the explicit Choi-Lam certificate. -/
def choiLamA : MvPolynomial (Fin 4) ℝ :=
  X (2 : Fin 4) ^ 2 + X (3 : Fin 4) ^ 2

/-- Substitute a univariate polynomial in the Choi-Lam auxiliary polynomial
`a = y^2 + z^2`. -/
def polynomialInChoiLamA (p : Polynomial ℝ) : MvPolynomial (Fin 4) ℝ :=
  Polynomial.aeval choiLamA p

@[simp] theorem polynomialInChoiLamA_X :
    polynomialInChoiLamA Polynomial.X = choiLamA := by
  simp [polynomialInChoiLamA]

@[simp] theorem polynomialInChoiLamA_C (c : ℝ) :
    polynomialInChoiLamA (Polynomial.C c) = MvPolynomial.C c := by
  simp [polynomialInChoiLamA]

@[simp] theorem polynomialInChoiLamA_add (p q : Polynomial ℝ) :
    polynomialInChoiLamA (p + q) = polynomialInChoiLamA p + polynomialInChoiLamA q := by
  simp [polynomialInChoiLamA]

@[simp] theorem polynomialInChoiLamA_mul (p q : Polynomial ℝ) :
    polynomialInChoiLamA (p * q) = polynomialInChoiLamA p * polynomialInChoiLamA q := by
  simp [polynomialInChoiLamA]

@[simp] theorem polynomialInChoiLamA_pow (p : Polynomial ℝ) (k : ℕ) :
    polynomialInChoiLamA (p ^ k) = polynomialInChoiLamA p ^ k := by
  simp [polynomialInChoiLamA]

/-- The fixed SOS identity `a C = SOS`. -/
theorem choiLamA_mul_choiLamQuartic_isSOS :
    IsSOS (choiLamA * choiLamQuartic) := by
  let q0 : MvPolynomial (Fin 4) ℝ := choiLamA * X (1 : Fin 4)
    - 2 * X (0 : Fin 4) * X (2 : Fin 4) * X (3 : Fin 4)
  let q1 : MvPolynomial (Fin 4) ℝ :=
    X (3 : Fin 4) * (X (0 : Fin 4) ^ 2 - X (2 : Fin 4) ^ 2)
  let q2 : MvPolynomial (Fin 4) ℝ :=
    X (2 : Fin 4) * (X (0 : Fin 4) ^ 2 - X (3 : Fin 4) ^ 2)
  have hsos : IsSOS (q0 ^ 2 + q1 ^ 2 + q2 ^ 2) :=
    IsSOS_add (IsSOS_add (IsSOS_sq q0) (IsSOS_sq q1)) (IsSOS_sq q2)
  have h : choiLamA * choiLamQuartic = q0 ^ 2 + q1 ^ 2 + q2 ^ 2 := by
    simp [q0, q1, q2, choiLamA, choiLamQuartic]
    ring_nf
  rw [h]
  exact hsos

/-- The fixed SOS identity `C + a^2 = SOS`. -/
theorem choiLamQuartic_add_choiLamA_sq_isSOS :
    IsSOS (choiLamQuartic + choiLamA ^ 2) := by
  let q0 : MvPolynomial (Fin 4) ℝ :=
    X (1 : Fin 4) * X (2 : Fin 4) - X (0 : Fin 4) * X (3 : Fin 4)
  let q1 : MvPolynomial (Fin 4) ℝ :=
    X (1 : Fin 4) * X (3 : Fin 4) - X (0 : Fin 4) * X (2 : Fin 4)
  let q2 : MvPolynomial (Fin 4) ℝ :=
    X (0 : Fin 4) ^ 2 - MvPolynomial.C (1 / 2 : ℝ) * choiLamA
  let q3 : MvPolynomial (Fin 4) ℝ := MvPolynomial.C (1 / 2 : ℝ) * choiLamA
  let q6 : MvPolynomial (Fin 4) ℝ := X (2 : Fin 4) * X (3 : Fin 4)
  have hsos : IsSOS (q0 ^ 2 + q1 ^ 2 + q2 ^ 2 + q3 ^ 2 + q3 ^ 2 + q3 ^ 2 + q6 ^ 2) := by
    repeat first | apply IsSOS_add | apply IsSOS_sq
  convert hsos using 1
  have hhalf_two : ∀ p : MvPolynomial (Fin 4) ℝ, p * MvPolynomial.C (2⁻¹ : ℝ) * 2 = p := by
    intro p
    change p * MvPolynomial.C (2⁻¹ : ℝ) * MvPolynomial.C (2 : ℝ) = p
    rw [mul_assoc, ← MvPolynomial.C_mul]
    norm_num
  have hhalf_sq_four : ∀ p : MvPolynomial (Fin 4) ℝ,
      p * MvPolynomial.C (2⁻¹ : ℝ) ^ 2 * 4 = p := by
    intro p
    change p * MvPolynomial.C (2⁻¹ : ℝ) ^ 2 * MvPolynomial.C (4 : ℝ) = p
    rw [mul_assoc, ← MvPolynomial.C_pow, ← MvPolynomial.C_mul]
    norm_num
  have hhalf_sq_eight : ∀ p : MvPolynomial (Fin 4) ℝ,
      p * MvPolynomial.C (2⁻¹ : ℝ) ^ 2 * 8 = p * 2 := by
    intro p
    change p * MvPolynomial.C (2⁻¹ : ℝ) ^ 2 * MvPolynomial.C (8 : ℝ) =
      p * MvPolynomial.C (2 : ℝ)
    rw [mul_assoc, ← MvPolynomial.C_pow, ← MvPolynomial.C_mul]
    norm_num
  simp [q0, q1, q2, q3, q6, choiLamA, choiLamQuartic]
  ring_nf
  simp [hhalf_two, hhalf_sq_four, hhalf_sq_eight]
  ring_nf

/-! ## Chebyshev cutoff polynomials -/

/-- Numerator of the Chebyshev cutoff before division by `m^2 X`. -/
def choiLamCutoffNumerator (m : ℕ) : Polynomial ℝ :=
  1 - (chebyshevT m).comp (1 - Polynomial.X)

/-- The cutoff polynomial `F_m(t) = (1 - T_m(1-t))/(m^2 t)`. -/
def choiLamCutoffF (m : ℕ) : Polynomial ℝ :=
  Polynomial.C ((m : ℝ) ^ 2)⁻¹ * (choiLamCutoffNumerator m /ₘ Polynomial.X)

/-- The square cutoff `R_m = F_m^2`. -/
def choiLamCutoffR (m : ℕ) : Polynomial ℝ :=
  choiLamCutoffF m ^ 2

/-- The quotient polynomial `P_m = (1 - R_m)/t`. -/
def choiLamCutoffP (m : ℕ) : Polynomial ℝ :=
  (1 - choiLamCutoffR m) /ₘ Polynomial.X

/-- The nonnegative residual `H_m(t) = epsilon - t^2 R_m(t)`. -/
def choiLamCutoffH (epsilon : ℝ) (m : ℕ) : Polynomial ℝ :=
  Polynomial.C epsilon - Polynomial.X ^ 2 * choiLamCutoffR m


/-- The endpoint derivative identity `T_m'(1) = m^2` for the local Chebyshev
normalization. -/
theorem chebyshevT_derivative_eval_one (m : ℕ) :
    (Polynomial.derivative (chebyshevT m)).eval 1 = (m : ℝ) ^ 2 := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => simp [chebyshevT_zero]
    | 1 => simp [chebyshevT_one]
    | n + 2 =>
      rw [chebyshevT_succ_succ]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X,
        Polynomial.derivative_ofNat, zero_mul, Polynomial.eval_sub,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
      rw [chebyshevT_eval_one, ih (n + 1) (by omega), ih n (by omega)]
      norm_num
      ring

/-! ## Certificate infrastructure and cutoff properties -/
theorem choiLamCutoffNumerator_eval_zero (m : ℕ) :
    (choiLamCutoffNumerator m).eval 0 = 0 := by
  simp [choiLamCutoffNumerator, chebyshevT_eval_one]

theorem choiLamCutoffNumerator_derivative_eval_zero (m : ℕ) :
    (Polynomial.derivative (choiLamCutoffNumerator m)).eval 0 = (m : ℝ) ^ 2 := by
  unfold choiLamCutoffNumerator
  rw [Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_comp_one_sub_X]
  simp [chebyshevT_derivative_eval_one]


theorem choiLamCutoffF_eval_zero (m : ℕ) (hm : m ≠ 0) :
    (choiLamCutoffF m).eval 0 = 1 := by
  have hroot : Polynomial.IsRoot (choiLamCutoffNumerator m) 0 := by
    rw [Polynomial.IsRoot.def, choiLamCutoffNumerator_eval_zero]
  have hmul : Polynomial.X * (choiLamCutoffNumerator m /ₘ Polynomial.X) =
      choiLamCutoffNumerator m := by
    simpa using (Polynomial.mul_divByMonic_eq_iff_isRoot (p := choiLamCutoffNumerator m)
      (a := 0)).mpr hroot
  have hderiv := congrArg Polynomial.derivative hmul
  have heval := congrArg (Polynomial.eval (0 : ℝ)) hderiv
  have hquot : (choiLamCutoffNumerator m /ₘ Polynomial.X).eval 0 = (m : ℝ) ^ 2 := by
    simpa [Polynomial.derivative_mul, choiLamCutoffNumerator_derivative_eval_zero] using heval
  unfold choiLamCutoffF
  simp [hquot, hm]



theorem choiLamCutoffX_mul_F (m : ℕ) :
    Polynomial.X * choiLamCutoffF m =
      Polynomial.C ((m : ℝ) ^ 2)⁻¹ * choiLamCutoffNumerator m := by
  have hroot : Polynomial.IsRoot (choiLamCutoffNumerator m) 0 := by
    rw [Polynomial.IsRoot.def, choiLamCutoffNumerator_eval_zero]
  have hmul : Polynomial.X * (choiLamCutoffNumerator m /ₘ Polynomial.X) =
      choiLamCutoffNumerator m := by
    simpa using (Polynomial.mul_divByMonic_eq_iff_isRoot (p := choiLamCutoffNumerator m)
      (a := 0)).mpr hroot
  have hmul' : (choiLamCutoffNumerator m /ₘ Polynomial.X) * Polynomial.X =
      choiLamCutoffNumerator m := by
    simpa [mul_comm] using hmul
  unfold choiLamCutoffF
  rw [mul_comm Polynomial.X, mul_assoc, hmul']

theorem choiLamCutoff_t_mul_F_eval (m : ℕ) (t : ℝ) :
    t * (choiLamCutoffF m).eval t =
      ((m : ℝ) ^ 2)⁻¹ * (1 - (chebyshevT m).eval (1 - t)) := by
  have h := congrArg (Polynomial.eval t) (choiLamCutoffX_mul_F m)
  simpa [choiLamCutoffNumerator, Polynomial.eval_comp, mul_comm, mul_left_comm, mul_assoc]
    using h

theorem choiLamCutoffR_eval_zero (m : ℕ) (hm : m ≠ 0) :
    (choiLamCutoffR m).eval 0 = 1 := by
  simp [choiLamCutoffR, choiLamCutoffF_eval_zero m hm]

theorem choiLamCutoffX_mul_P_add_R (m : ℕ) (hm : m ≠ 0) :
    Polynomial.X * choiLamCutoffP m + choiLamCutoffR m = 1 := by
  have hroot : Polynomial.IsRoot (1 - choiLamCutoffR m : Polynomial ℝ) 0 := by
    rw [Polynomial.IsRoot.def]
    simp [choiLamCutoffR_eval_zero m hm]
  have hmul : Polynomial.X * choiLamCutoffP m = 1 - choiLamCutoffR m := by
    unfold choiLamCutoffP
    simpa using (Polynomial.mul_divByMonic_eq_iff_isRoot
      (p := (1 - choiLamCutoffR m : Polynomial ℝ)) (a := 0)).mpr hroot
  rw [hmul]
  ring

theorem IsSOS_polynomialInChoiLamA_of_IsSOSUni {p : Polynomial ℝ} (hp : IsSOSUni p) :
    IsSOS (polynomialInChoiLamA p) := by
  obtain ⟨m, q, rfl⟩ := hp
  refine ⟨m, fun i => polynomialInChoiLamA (q i), ?_⟩
  simp [polynomialInChoiLamA, map_sum, map_pow]

theorem choiLamA_isSOS : IsSOS choiLamA := by
  refine ⟨2, fun i => if i = 0 then X (2 : Fin 4) else X (3 : Fin 4), ?_⟩
  rw [Fin.sum_univ_two]
  simp [choiLamA]

theorem choiLamA_totalDegree_le_two : choiLamA.totalDegree ≤ 2 := by
  calc choiLamA.totalDegree
      ≤ max ((X (2 : Fin 4) ^ 2 : MvPolynomial (Fin 4) ℝ).totalDegree)
          ((X (3 : Fin 4) ^ 2 : MvPolynomial (Fin 4) ℝ).totalDegree) := by
            unfold choiLamA
            exact MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := by
      rw [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X_pow]
      norm_num

theorem polynomialInChoiLamA_totalDegree_le (p : Polynomial ℝ) :
    (polynomialInChoiLamA p).totalDegree ≤ 2 * p.natDegree := by
  unfold polynomialInChoiLamA
  rw [Polynomial.aeval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  calc (p.coeff k • choiLamA ^ k).totalDegree
      ≤ (choiLamA ^ k).totalDegree := MvPolynomial.totalDegree_smul_le _ _
    _ ≤ k * choiLamA.totalDegree := MvPolynomial.totalDegree_pow _ _
    _ ≤ k * 2 := Nat.mul_le_mul_left k choiLamA_totalDegree_le_two
    _ ≤ p.natDegree * 2 := by
      rw [Finset.mem_range] at hk
      exact Nat.mul_le_mul_right 2 (by omega)
    _ = 2 * p.natDegree := by omega

theorem choiLamQuartic_add_choiLamA_sq_totalDegree_le_four :
    (choiLamQuartic + choiLamA ^ 2).totalDegree ≤ 4 := by
  calc (choiLamQuartic + choiLamA ^ 2).totalDegree
      ≤ max choiLamQuartic.totalDegree (choiLamA ^ 2).totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 4 := by
      have hC : choiLamQuartic.totalDegree ≤ 4 := choiLamQuartic_totalDegree_le_four
      have ha2 : (choiLamA ^ 2).totalDegree ≤ 4 := by
        calc (choiLamA ^ 2).totalDegree
            ≤ 2 * choiLamA.totalDegree := MvPolynomial.totalDegree_pow _ _
          _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 choiLamA_totalDegree_le_two
          _ = 4 := by norm_num
      exact max_le hC ha2

/-- A single SOS multiplier times a preordering generator product is a preordering term. -/
theorem IsSOS_mul_generatorProd_in_BoxPreordering_public (J : Finset (Fin 4))
    (σ : MvPolynomial (Fin 4) ℝ) (r : ℕ)
    (hsos : IsSOS σ) (hdeg : (σ * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) :
    σ * BoxSemialgebraicGeneratorProd J ∈ BoxPreordering 4 r := by
  have hJ_mem : J ∈ (Finset.univ : Finset (Fin 4)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ J)
  refine ⟨Function.update 0 J σ, ?_, ?_, ?_⟩
  · intro K
    by_cases hK : K = J
    · subst hK
      rwa [Function.update_self]
    · rw [Function.update_of_ne hK, Pi.zero_apply]
      exact IsSOS_zero
  · intro K
    by_cases hK : K = J
    · subst hK
      rwa [Function.update_self]
    · rw [Function.update_of_ne hK, Pi.zero_apply, zero_mul]
      exact Nat.zero_le _
  · rw [Finset.sum_eq_single J
      (fun K _ hK => by rw [Function.update_of_ne hK, Pi.zero_apply, zero_mul])
      (fun h => absurd hJ_mem h)]
    rw [Function.update_self]


theorem natDegree_one_sub_X_sq_real :
    (1 - Polynomial.X ^ 2 : Polynomial ℝ).natDegree = 2 := by
  have h : (1 - Polynomial.X ^ 2 : Polynomial ℝ) =
      Polynomial.C (-1) * Polynomial.X ^ 2 + Polynomial.C 1 := by
    simp only [map_neg, map_one]
    ring
  rw [h, Polynomial.natDegree_add_eq_left_of_degree_lt,
    Polynomial.natDegree_C_mul_X_pow _ _ (by norm_num : (-1 : ℝ) ≠ 0)]
  rw [Polynomial.degree_C (by norm_num : (1 : ℝ) ≠ 0),
    Polynomial.degree_C_mul_X_pow _ (by norm_num : (-1 : ℝ) ≠ 0)]
  exact WithBot.coe_lt_coe.mpr (by norm_num)

/-- Polynomials nonnegative on `[0,2]`, after substituting `a = y^2 + z^2` and
multiplying by an SOS polynomial, have a preordering certificate using only the
`y` and `z` box generators. -/
theorem interval_nonneg_comp_choiLamA_mul_sos_mem_box_preordering
    (h : Polynomial ℝ) (S : MvPolynomial (Fin 4) ℝ) (D E r : ℕ)
    (h_nonneg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 2 → 0 ≤ h.eval t)
    (hdeg : h.natDegree ≤ D)
    (hS : IsSOS S) (hSdeg : S.totalDegree ≤ E)
    (hr : 2 * (D + 1) + E ≤ r) :
    polynomialInChoiLamA h * S ∈ BoxPreordering 4 r := by
  classical
  let q : Polynomial ℝ := h.comp (Polynomial.X + 1)
  have hqdeg : q.natDegree ≤ D := by
    dsimp [q]
    calc (h.comp (Polynomial.X + 1)).natDegree
        ≤ h.natDegree * (Polynomial.X + 1 : Polynomial ℝ).natDegree :=
          Polynomial.natDegree_comp_le
      _ ≤ D * 1 := by
        have hlin : (Polynomial.X + 1 : Polynomial ℝ).natDegree ≤ 1 := by
          exact (Polynomial.natDegree_add_le _ _).trans (by simp)
        exact Nat.mul_le_mul hdeg hlin
      _ = D := by simp
  have hqnonneg : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ q.eval x := by
    intro x hx
    have hx01 : x + 1 ∈ Set.Icc (0 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa [q, Polynomial.eval_comp, add_comm] using h_nonneg (x + 1) hx01
  obtain ⟨σ0, σ1, hsos0, hsos1, hdeg0, hdeg1, hqeq⟩ :=
    markov_lukacz q hqdeg hqnonneg
  let shift : Polynomial ℝ → MvPolynomial (Fin 4) ℝ := fun p =>
    Polynomial.aeval (choiLamA - 1) p
  let τ0 : MvPolynomial (Fin 4) ℝ := shift σ0 * S
  let τ : MvPolynomial (Fin 4) ℝ := shift σ1 * choiLamA * S
  have hshift_sos0 : IsSOS (shift σ0) := by
    obtain ⟨N, w, hw⟩ := hsos0
    refine ⟨N, fun i => shift (w i), ?_⟩
    dsimp [shift]
    rw [hw]
    simp [map_sum, map_pow]
  have hshift_sos1 : IsSOS (shift σ1) := by
    obtain ⟨N, w, hw⟩ := hsos1
    refine ⟨N, fun i => shift (w i), ?_⟩
    dsimp [shift]
    rw [hw]
    simp [map_sum, map_pow]
  have hτ0sos : IsSOS τ0 := IsSOS_mul hshift_sos0 hS
  have hτsos : IsSOS τ := IsSOS_mul (IsSOS_mul hshift_sos1 choiLamA_isSOS) hS
  have hshift_deg_le : ∀ p : Polynomial ℝ, (shift p).totalDegree ≤ 2 * p.natDegree := by
    intro p
    dsimp [shift]
    rw [Polynomial.aeval_eq_sum_range]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    have hbase : (choiLamA - 1 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 2 := by
      calc (choiLamA - 1 : MvPolynomial (Fin 4) ℝ).totalDegree
          ≤ max choiLamA.totalDegree (1 : MvPolynomial (Fin 4) ℝ).totalDegree :=
            MvPolynomial.totalDegree_sub _ _
        _ ≤ 2 := by
          exact max_le choiLamA_totalDegree_le_two (by simp)
    calc (p.coeff k • (choiLamA - 1 : MvPolynomial (Fin 4) ℝ) ^ k).totalDegree
        ≤ ((choiLamA - 1 : MvPolynomial (Fin 4) ℝ) ^ k).totalDegree :=
          MvPolynomial.totalDegree_smul_le _ _
      _ ≤ k * (choiLamA - 1 : MvPolynomial (Fin 4) ℝ).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
      _ ≤ k * 2 := Nat.mul_le_mul_left k hbase
      _ ≤ p.natDegree * 2 := by
        rw [Finset.mem_range] at hk
        exact Nat.mul_le_mul_right 2 (by omega)
      _ = 2 * p.natDegree := by omega
  have hσ1_nat_of_ne_zero : σ1 ≠ 0 → σ1.natDegree + 2 ≤ D + 1 := by
    intro hzero
    have hone : (1 - Polynomial.X ^ 2 : Polynomial ℝ) ≠ 0 := by
      intro hz
      have hz0 := congrArg (Polynomial.eval (0 : ℝ)) hz
      norm_num at hz0
    have hdegprod : (σ1 * (1 - Polynomial.X ^ 2 : Polynomial ℝ)).natDegree =
        σ1.natDegree + 2 := by
      rw [Polynomial.natDegree_mul hzero hone, natDegree_one_sub_X_sq_real]
    rw [← hdegprod]
    exact hdeg1
  have hdegτ0 : (τ0 * BoxSemialgebraicGeneratorProd (∅ : Finset (Fin 4))).totalDegree ≤ r := by
    rw [BoxSemialgebraicGeneratorProd_empty, mul_one]
    calc τ0.totalDegree
        ≤ (shift σ0).totalDegree + S.totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * σ0.natDegree + E := by
        have h0 := hshift_deg_le σ0
        omega
      _ ≤ 2 * (D + 1) + E := by omega
      _ ≤ r := hr
  have hdegτ2 :
    (τ * BoxSemialgebraicGeneratorProd ({(2 : Fin 4)} : Finset (Fin 4))).totalDegree ≤
      r := by
    by_cases hzero : σ1 = 0
    · subst hzero
      dsimp [τ, shift]
      simp
    · have hσ1_nat := hσ1_nat_of_ne_zero hzero
      calc (τ * BoxSemialgebraicGeneratorProd ({(2 : Fin 4)} : Finset (Fin 4))).totalDegree
          ≤ τ.totalDegree +
              (BoxSemialgebraicGeneratorProd ({(2 : Fin 4)} : Finset (Fin 4))).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
        _ ≤ (2 * σ1.natDegree + 2 + E) + 2 := by
          have hτdeg : τ.totalDegree ≤ 2 * σ1.natDegree + 2 + E := by
            dsimp [τ]
            calc (shift σ1 * choiLamA * S).totalDegree
                ≤ (shift σ1 * choiLamA).totalDegree + S.totalDegree :=
                  MvPolynomial.totalDegree_mul _ _
              _ ≤ ((shift σ1).totalDegree + choiLamA.totalDegree) + S.totalDegree := by
                exact Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
              _ ≤ (2 * σ1.natDegree + 2) + E := by
                have hsdeg := hshift_deg_le σ1
                have ha_deg := choiLamA_totalDegree_le_two
                have hS_deg := hSdeg
                omega
              _ = 2 * σ1.natDegree + 2 + E := by omega
          have hgdeg :
              (BoxSemialgebraicGeneratorProd ({(2 : Fin 4)} : Finset (Fin 4))).totalDegree ≤
                2 := by
            rw [BoxSemialgebraicGeneratorProd_singleton]
            unfold BoxSemialgebraicGenerator
            calc (1 - X (2 : Fin 4) ^ 2 : MvPolynomial (Fin 4) ℝ).totalDegree
                ≤ max (1 : MvPolynomial (Fin 4) ℝ).totalDegree
                    (X (2 : Fin 4) ^ 2).totalDegree :=
                  MvPolynomial.totalDegree_sub _ _
              _ ≤ 2 := by
                rw [MvPolynomial.totalDegree_X_pow]
                simp
          omega
        _ ≤ 2 * (D + 1) + E := by omega
        _ ≤ r := hr
  have hdegτ3 :
    (τ * BoxSemialgebraicGeneratorProd ({(3 : Fin 4)} : Finset (Fin 4))).totalDegree ≤
      r := by
    by_cases hzero : σ1 = 0
    · subst hzero
      dsimp [τ, shift]
      simp
    · have hσ1_nat := hσ1_nat_of_ne_zero hzero
      calc (τ * BoxSemialgebraicGeneratorProd ({(3 : Fin 4)} : Finset (Fin 4))).totalDegree
          ≤ τ.totalDegree +
              (BoxSemialgebraicGeneratorProd ({(3 : Fin 4)} : Finset (Fin 4))).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
        _ ≤ (2 * σ1.natDegree + 2 + E) + 2 := by
          have hτdeg : τ.totalDegree ≤ 2 * σ1.natDegree + 2 + E := by
            dsimp [τ]
            calc (shift σ1 * choiLamA * S).totalDegree
                ≤ (shift σ1 * choiLamA).totalDegree + S.totalDegree :=
                  MvPolynomial.totalDegree_mul _ _
              _ ≤ ((shift σ1).totalDegree + choiLamA.totalDegree) + S.totalDegree := by
                exact Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
              _ ≤ (2 * σ1.natDegree + 2) + E := by
                have hsdeg := hshift_deg_le σ1
                have ha_deg := choiLamA_totalDegree_le_two
                have hS_deg := hSdeg
                omega
              _ = 2 * σ1.natDegree + 2 + E := by omega
          have hgdeg :
              (BoxSemialgebraicGeneratorProd ({(3 : Fin 4)} : Finset (Fin 4))).totalDegree ≤
                2 := by
            rw [BoxSemialgebraicGeneratorProd_singleton]
            unfold BoxSemialgebraicGenerator
            calc (1 - X (3 : Fin 4) ^ 2 : MvPolynomial (Fin 4) ℝ).totalDegree
                ≤ max (1 : MvPolynomial (Fin 4) ℝ).totalDegree
                    (X (3 : Fin 4) ^ 2).totalDegree :=
                  MvPolynomial.totalDegree_sub _ _
              _ ≤ 2 := by
                rw [MvPolynomial.totalDegree_X_pow]
                simp
          omega
        _ ≤ 2 * (D + 1) + E := by omega
        _ ≤ r := hr
  have hmem0 :
      τ0 * BoxSemialgebraicGeneratorProd (∅ : Finset (Fin 4)) ∈ BoxPreordering 4 r :=
    IsSOS_mul_generatorProd_in_BoxPreordering_public ∅ τ0 r hτ0sos hdegτ0
  have hmem2 : τ * BoxSemialgebraicGeneratorProd ({(2 : Fin 4)} : Finset (Fin 4)) ∈
      BoxPreordering 4 r :=
    IsSOS_mul_generatorProd_in_BoxPreordering_public
      ({(2 : Fin 4)} : Finset (Fin 4)) τ r hτsos hdegτ2
  have hmem3 : τ * BoxSemialgebraicGeneratorProd ({(3 : Fin 4)} : Finset (Fin 4)) ∈
      BoxPreordering 4 r :=
    IsSOS_mul_generatorProd_in_BoxPreordering_public
      ({(3 : Fin 4)} : Finset (Fin 4)) τ r hτsos hdegτ3
  have hsum_mem := BoxPreordering_add (BoxPreordering_add hmem0 hmem2) hmem3
  convert hsum_mem using 1
  dsimp [τ0, τ, shift]
  rw [BoxSemialgebraicGeneratorProd_empty, BoxSemialgebraicGeneratorProd_singleton,
    BoxSemialgebraicGeneratorProd_singleton]
  have hsubst : Polynomial.aeval (choiLamA - 1) q = polynomialInChoiLamA h := by
    dsimp [q, polynomialInChoiLamA]
    rw [Polynomial.aeval_comp]
    simp
  have hqsub := congrArg (Polynomial.aeval (choiLamA - 1)) hqeq
  rw [hsubst] at hqsub
  rw [hqsub]
  simp [BoxSemialgebraicGenerator, choiLamA]
  ring

theorem choiLamCutoffR_isSOSUni (m : ℕ) : IsSOSUni (choiLamCutoffR m) := by
  unfold choiLamCutoffR
  exact IsSOSUni_sq (choiLamCutoffF m)

theorem choiLamCutoffNumerator_natDegree_le (m : ℕ) :
    (choiLamCutoffNumerator m).natDegree ≤ m := by
  unfold choiLamCutoffNumerator
  calc (1 - (chebyshevT m).comp (1 - Polynomial.X)).natDegree
      ≤ max (1 : Polynomial ℝ).natDegree ((chebyshevT m).comp (1 - Polynomial.X)).natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ m := by
      have h1 : (1 : Polynomial ℝ).natDegree ≤ m := by simp
      have hcomp : ((chebyshevT m).comp (1 - Polynomial.X)).natDegree ≤ m := by
        have hcheb : (chebyshevT m).natDegree ≤ m := (natDegree_chebyshevT m).le
        have hlin : (1 - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
          exact (Polynomial.natDegree_sub_le (1 : Polynomial ℝ) Polynomial.X).trans (by simp)
        calc ((chebyshevT m).comp (1 - Polynomial.X)).natDegree
            ≤ (chebyshevT m).natDegree * (1 - Polynomial.X : Polynomial ℝ).natDegree :=
              Polynomial.natDegree_comp_le
          _ ≤ m * 1 := Nat.mul_le_mul hcheb hlin
          _ = m := by simp
      exact max_le h1 hcomp

theorem choiLamCutoffF_natDegree_le (m : ℕ) (_hm : 1 ≤ m) :
    (choiLamCutoffF m).natDegree ≤ m - 1 := by
  unfold choiLamCutoffF
  calc (Polynomial.C ((m : ℝ) ^ 2)⁻¹ * (choiLamCutoffNumerator m /ₘ Polynomial.X)).natDegree
      ≤ (choiLamCutoffNumerator m /ₘ Polynomial.X).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
    _ ≤ (choiLamCutoffNumerator m).natDegree - Polynomial.X.natDegree := by
      rw [Polynomial.natDegree_divByMonic (choiLamCutoffNumerator m) Polynomial.monic_X]
    _ ≤ m - 1 := by
      simpa using Nat.sub_le_sub_right (choiLamCutoffNumerator_natDegree_le m) 1

theorem choiLamCutoffR_natDegree_le (m : ℕ) (hm : 1 ≤ m) :
    (choiLamCutoffR m).natDegree ≤ 2 * m - 2 := by
  unfold choiLamCutoffR
  calc (choiLamCutoffF m ^ 2).natDegree
      ≤ 2 * (choiLamCutoffF m).natDegree := Polynomial.natDegree_pow_le
    _ ≤ 2 * (m - 1) := Nat.mul_le_mul_left 2 (choiLamCutoffF_natDegree_le m hm)
    _ = 2 * m - 2 := by omega

theorem choiLamCutoffP_natDegree_le (m : ℕ) (hm : 2 ≤ m) :
    (choiLamCutoffP m).natDegree ≤ 2 * m - 3 := by
  unfold choiLamCutoffP
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  calc ((1 - choiLamCutoffR m) /ₘ Polynomial.X).natDegree
      ≤ (1 - choiLamCutoffR m : Polynomial ℝ).natDegree -
          Polynomial.X.natDegree := by
        rw [Polynomial.natDegree_divByMonic
          (1 - choiLamCutoffR m : Polynomial ℝ) Polynomial.monic_X]
    _ ≤ (2 * m - 2) - 1 := by
      have hsub : (1 - choiLamCutoffR m : Polynomial ℝ).natDegree ≤ 2 * m - 2 := by
        calc (1 - choiLamCutoffR m : Polynomial ℝ).natDegree
            ≤ max (1 : Polynomial ℝ).natDegree (choiLamCutoffR m).natDegree :=
              Polynomial.natDegree_sub_le _ _
          _ ≤ 2 * m - 2 := by
            have h1 : (1 : Polynomial ℝ).natDegree ≤ 2 * m - 2 := by
              simp
            exact max_le h1 (choiLamCutoffR_natDegree_le m hm1)
      simpa using Nat.sub_le_sub_right hsub 1
    _ = 2 * m - 3 := by omega


theorem deriv_polynomial_eval (p : Polynomial ℝ) :
    deriv p.eval = (Polynomial.derivative p).eval := by
  funext x
  have h := Polynomial.deriv_aeval (𝕜 := ℝ) p (x := x)
  simp only [Polynomial.coe_aeval_eq_eval] at h
  exact h

theorem chebyshevT_lipschitz_on_Icc (m : ℕ) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |(chebyshevT m).eval y - (chebyshevT m).eval x| ≤ (m : ℝ) ^ 2 * |y - x| := by
  intro x hx y hy
  let f : ℝ → ℝ := fun z => (chebyshevT m).eval z
  have hf : ∀ z ∈ Set.Icc (-1 : ℝ) 1, DifferentiableAt ℝ f z := by
    intro z hz
    exact Polynomial.differentiableAt _
  have hbound : ∀ z ∈ Set.Icc (-1 : ℝ) 1, ‖deriv f z‖ ≤ (m : ℝ) ^ 2 := by
    intro z hz
    have hderiv := chebyshevT_deriv_bound_k1 m z hz.1 hz.2
    simpa [f, deriv_polynomial_eval, Real.norm_eq_abs] using hderiv
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (-1 : ℝ) 1) hf hbound (convex_Icc (-1 : ℝ) 1) hx hy
  simpa [f, Real.norm_eq_abs] using h


theorem polynomial_eval_zero_nonneg_of_right_nonneg (p : Polynomial ℝ)
    (hp : ∀ t : ℝ, 0 < t → t ≤ 2 → 0 ≤ p.eval t) : 0 ≤ p.eval 0 := by
  by_contra hneg
  push Not at hneg
  have hcont : Continuous (fun t : ℝ => p.eval t) := Polynomial.continuous_aeval p
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont.continuousAt
    (-(p.eval 0) / 2) (by linarith)
  let y : ℝ := min (δ / 2) 1
  have hypos : 0 < y := lt_min (by linarith) (by norm_num)
  have hy2 : y ≤ 2 := by
    calc y ≤ 1 := min_le_right _ _
      _ ≤ 2 := by norm_num
  have hydist : dist y 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hypos]
    calc y ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  have hnear := hδ hydist
  rw [Real.dist_eq] at hnear
  have hyneg : p.eval y < 0 := by
    have hupper : p.eval y - p.eval 0 < -(p.eval 0) / 2 := lt_of_le_of_lt (le_abs_self _) hnear
    linarith
  exact not_le_of_gt hyneg (hp y hypos hy2)

theorem choiLamCutoffF_abs_le_one_on_Icc (m : ℕ) (hm : 1 ≤ m) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 2 → |(choiLamCutoffF m).eval t| ≤ 1 := by
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0
    rw [choiLamCutoffF_eval_zero m (by omega)]
    simp
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hy1 : 1 - t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hy2 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
    have hlip := chebyshevT_lipschitz_on_Icc m 1 hy2 (1 - t) hy1
    have hTone : (chebyshevT m).eval 1 = 1 := chebyshevT_eval_one m
    have hN_abs : |1 - (chebyshevT m).eval (1 - t)| ≤ (m : ℝ) ^ 2 * t := by
      have ht_abs : |(1 - t) - 1| = t := by
        rw [show (1 - t) - 1 = -t by ring, abs_neg, abs_of_nonneg ht.1]
      rw [hTone, ht_abs] at hlip
      rw [abs_sub_comm]
      exact hlip
    have hmpos : 0 < (m : ℝ) ^ 2 := by positivity
    have htf := choiLamCutoff_t_mul_F_eval m t
    have htF_abs : |t * (choiLamCutoffF m).eval t| ≤ t := by
      rw [htf, abs_mul]
      have hscale : |((m : ℝ) ^ 2)⁻¹| = ((m : ℝ) ^ 2)⁻¹ := abs_of_nonneg (by positivity)
      rw [hscale]
      calc ((m : ℝ) ^ 2)⁻¹ * |1 - (chebyshevT m).eval (1 - t)|
          ≤ ((m : ℝ) ^ 2)⁻¹ * ((m : ℝ) ^ 2 * t) :=
            mul_le_mul_of_nonneg_left hN_abs (by positivity)
        _ = t := by field_simp [ne_of_gt hmpos]
    rw [abs_mul, abs_of_pos htpos] at htF_abs
    exact (mul_le_iff_le_one_right htpos).mp htF_abs

theorem choiLamCutoffP_nonneg_on_Icc (m : ℕ) (hm : 1 ≤ m) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 2 → 0 ≤ (choiLamCutoffP m).eval t := by
  refine fun t ht => ?_
  by_cases ht0 : t = 0
  · subst ht0
    exact polynomial_eval_zero_nonneg_of_right_nonneg (choiLamCutoffP m) (by
      intro u hu hule
      have huI : u ∈ Set.Icc (0 : ℝ) 2 := ⟨le_of_lt hu, hule⟩
      have hF := choiLamCutoffF_abs_le_one_on_Icc m hm u huI
      have hFsq : (choiLamCutoffF m).eval u ^ 2 ≤ 1 := by
        have hF' : |(choiLamCutoffF m).eval u| ≤ |(1 : ℝ)| := by simpa using hF
        have hsq := sq_le_sq.mpr hF'
        simpa using hsq
      have hRle : (choiLamCutoffR m).eval u ≤ 1 := by
        unfold choiLamCutoffR
        simpa [Polynomial.eval_pow] using hFsq
      have hPR :=
        congrArg (Polynomial.eval u) (choiLamCutoffX_mul_P_add_R m (by omega))
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_one] at hPR
      have huP : u * (choiLamCutoffP m).eval u = 1 - (choiLamCutoffR m).eval u := by
        linarith
      have hnon : 0 ≤ 1 - (choiLamCutoffR m).eval u := sub_nonneg.mpr hRle
      have hmul_nonneg : 0 ≤ (choiLamCutoffP m).eval u * u := by
        rw [mul_comm, huP]
        exact hnon
      exact nonneg_of_mul_nonneg_left hmul_nonneg hu)
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hF := choiLamCutoffF_abs_le_one_on_Icc m hm t ht
    have hFsq : (choiLamCutoffF m).eval t ^ 2 ≤ 1 := by
      have hF' : |(choiLamCutoffF m).eval t| ≤ |(1 : ℝ)| := by simpa using hF
      have hsq := sq_le_sq.mpr hF'
      simpa using hsq
    have hRle : (choiLamCutoffR m).eval t ≤ 1 := by
      unfold choiLamCutoffR
      simpa [Polynomial.eval_pow] using hFsq
    have hPR :=
      congrArg (Polynomial.eval t) (choiLamCutoffX_mul_P_add_R m (by omega))
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_one] at hPR
    have htP : t * (choiLamCutoffP m).eval t = 1 - (choiLamCutoffR m).eval t := by
      linarith
    have hnon : 0 ≤ 1 - (choiLamCutoffR m).eval t := sub_nonneg.mpr hRle
    have hmul_nonneg : 0 ≤ (choiLamCutoffP m).eval t * t := by
      rw [mul_comm, htP]
      exact hnon
    exact nonneg_of_mul_nonneg_left hmul_nonneg htpos

theorem choiLamCutoffH_natDegree_le (epsilon : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    (choiLamCutoffH epsilon m).natDegree ≤ 2 * m := by
  unfold choiLamCutoffH
  calc (Polynomial.C epsilon - Polynomial.X ^ 2 * choiLamCutoffR m).natDegree
      ≤ max (Polynomial.C epsilon).natDegree (Polynomial.X ^ 2 * choiLamCutoffR m).natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ 2 * m := by
      have hC : (Polynomial.C epsilon).natDegree ≤ 2 * m := by simp
      have hmul : (Polynomial.X ^ 2 * choiLamCutoffR m).natDegree ≤ 2 * m := by
        calc (Polynomial.X ^ 2 * choiLamCutoffR m).natDegree
            ≤ (Polynomial.X ^ 2 : Polynomial ℝ).natDegree + (choiLamCutoffR m).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 2 + (2 * m - 2) := by
            have hx : (Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by simp
            exact Nat.add_le_add hx (choiLamCutoffR_natDegree_le m hm)
          _ = 2 * m := by omega
      exact max_le hC hmul

theorem choiLamCutoffH_nonneg_on_Icc
    (epsilon : ℝ) (m : ℕ) (hm : 1 ≤ m) (heps_bound : 4 / (m : ℝ) ^ 4 ≤ epsilon) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 2 → 0 ≤ (choiLamCutoffH epsilon m).eval t := by
  intro t ht
  have hy1 : -1 ≤ 1 - t := by linarith [ht.2]
  have hy2 : 1 - t ≤ 1 := by linarith [ht.1]
  have hT := chebyshevT_abs_le_one m (1 - t) hy1 hy2
  have hN_abs : |1 - (chebyshevT m).eval (1 - t)| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hT).1, (abs_le.mp hT).2]
  have hN_sq : (1 - (chebyshevT m).eval (1 - t)) ^ 2 ≤ 4 := by
    have hN_abs' : |1 - (chebyshevT m).eval (1 - t)| ≤ |(2 : ℝ)| := by
      simpa using hN_abs
    have hsq := sq_le_sq.mpr hN_abs'
    norm_num at hsq
    exact hsq
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have htf := choiLamCutoff_t_mul_F_eval m t
  have hmain : t ^ 2 * (choiLamCutoffF m).eval t ^ 2 ≤ 4 / (m : ℝ) ^ 4 := by
    have hsq : (t * (choiLamCutoffF m).eval t) ^ 2 =
        ((m : ℝ) ^ 2)⁻¹ ^ 2 * (1 - (chebyshevT m).eval (1 - t)) ^ 2 := by
      rw [htf]
      ring
    have hnon : 0 ≤ ((m : ℝ) ^ 2)⁻¹ ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hN_sq hnon
    rw [← hsq] at hmul
    have hden : (((m : ℝ) ^ 2) ^ 2)⁻¹ * 4 = 4 / (m : ℝ) ^ 4 := by
      field_simp [ne_of_gt hmpos]
    have hleft : t ^ 2 * (choiLamCutoffF m).eval t ^ 2 =
        (t * (choiLamCutoffF m).eval t) ^ 2 := by
      ring
    simpa [hleft, hden, mul_comm, mul_left_comm, mul_assoc] using hmul
  unfold choiLamCutoffH
  simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, choiLamCutoffR]
  linarith

/-! ## Assembly of the explicit certificate -/

theorem choiLam_tight_identity (epsilon : ℝ) (m : ℕ) (hm : m ≠ 0) :
    choiLamPerturbed epsilon =
      polynomialInChoiLamA (choiLamCutoffP m) * (choiLamA * choiLamQuartic)
        + polynomialInChoiLamA (choiLamCutoffR m) * (choiLamQuartic + choiLamA ^ 2)
        + polynomialInChoiLamA (choiLamCutoffH epsilon m) := by
  have hPR := congrArg polynomialInChoiLamA (choiLamCutoffX_mul_P_add_R m hm)
  simp [polynomialInChoiLamA] at hPR
  unfold choiLamPerturbed choiLamCutoffH
  simp [polynomialInChoiLamA]
  ring_nf
  nth_rewrite 1 [show choiLamQuartic =
      (choiLamA * (Polynomial.aeval choiLamA) (choiLamCutoffP m) +
        (Polynomial.aeval choiLamA) (choiLamCutoffR m)) * choiLamQuartic by
    rw [hPR]
    ring]
  ring

theorem choiLam_tight_term1_mem_box_preordering (m : ℕ) (hm : 2 ≤ m) :
    polynomialInChoiLamA (choiLamCutoffP m) * (choiLamA * choiLamQuartic) ∈
      BoxPreordering 4 (4 * (m + 1)) := by
  refine interval_nonneg_comp_choiLamA_mul_sos_mem_box_preordering
    (choiLamCutoffP m) (choiLamA * choiLamQuartic) (2 * m - 3) 6 (4 * (m + 1))
    (choiLamCutoffP_nonneg_on_Icc m (le_trans (by norm_num) hm))
    (choiLamCutoffP_natDegree_le m hm)
    choiLamA_mul_choiLamQuartic_isSOS ?_ ?_
  · calc
      (choiLamA * choiLamQuartic).totalDegree ≤
          choiLamA.totalDegree + choiLamQuartic.totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 + 4 := by
        have ha : choiLamA.totalDegree ≤ 2 := by
          calc choiLamA.totalDegree
              ≤ max ((X (2 : Fin 4) ^ 2 : MvPolynomial (Fin 4) ℝ).totalDegree)
                  ((X (3 : Fin 4) ^ 2 : MvPolynomial (Fin 4) ℝ).totalDegree) := by
                    unfold choiLamA
                    exact MvPolynomial.totalDegree_add _ _
            _ ≤ 2 := by
              rw [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X_pow]
              norm_num
        have hc : choiLamQuartic.totalDegree ≤ 4 := choiLamQuartic_totalDegree_le_four
        omega
      _ = 6 := by norm_num
  · omega

theorem choiLam_tight_term2_mem_box_preordering (m : ℕ) (hm : 1 ≤ m) :
    polynomialInChoiLamA (choiLamCutoffR m) * (choiLamQuartic + choiLamA ^ 2) ∈
      BoxPreordering 4 (4 * (m + 1)) := by
  have hR : IsSOS (polynomialInChoiLamA (choiLamCutoffR m)) :=
    IsSOS_polynomialInChoiLamA_of_IsSOSUni (choiLamCutoffR_isSOSUni m)
  have hSOS : IsSOS (polynomialInChoiLamA (choiLamCutoffR m) *
      (choiLamQuartic + choiLamA ^ 2)) :=
    IsSOS_mul hR choiLamQuartic_add_choiLamA_sq_isSOS
  rw [show polynomialInChoiLamA (choiLamCutoffR m) * (choiLamQuartic + choiLamA ^ 2) =
      (polynomialInChoiLamA (choiLamCutoffR m) * (choiLamQuartic + choiLamA ^ 2)) *
        BoxSemialgebraicGeneratorProd (∅ : Finset (Fin 4)) by
    rw [BoxSemialgebraicGeneratorProd_empty, mul_one]]
  apply IsSOS_mul_generatorProd_in_BoxPreordering_public (J := ∅)
  · exact hSOS
  · rw [BoxSemialgebraicGeneratorProd_empty, mul_one]
    calc (polynomialInChoiLamA (choiLamCutoffR m) *
          (choiLamQuartic + choiLamA ^ 2)).totalDegree
        ≤ (polynomialInChoiLamA (choiLamCutoffR m)).totalDegree +
            (choiLamQuartic + choiLamA ^ 2).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * (2 * m - 2) + 4 := by
        have hRdeg := polynomialInChoiLamA_totalDegree_le (choiLamCutoffR m)
        have hRnat := choiLamCutoffR_natDegree_le m hm
        have hRmv : (polynomialInChoiLamA (choiLamCutoffR m)).totalDegree ≤
            2 * (2 * m - 2) := by
          exact le_trans hRdeg (Nat.mul_le_mul_left 2 hRnat)
        have hCdeg := choiLamQuartic_add_choiLamA_sq_totalDegree_le_four
        omega
      _ ≤ 4 * m := by omega
      _ ≤ 4 * (m + 1) := by
        exact Nat.mul_le_mul_left 4 (Nat.le_succ m)

theorem choiLam_tight_term3_mem_box_preordering
    (epsilon : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (heps_bound : 4 / (m : ℝ) ^ 4 ≤ epsilon) :
    polynomialInChoiLamA (choiLamCutoffH epsilon m) ∈ BoxPreordering 4 (4 * (m + 1)) := by
  have hS : IsSOS (1 : MvPolynomial (Fin 4) ℝ) := by
    exact ⟨1, fun _ => 1, by simp⟩
  have hSdeg : (1 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 0 := by simp
  simpa [mul_one] using
    interval_nonneg_comp_choiLamA_mul_sos_mem_box_preordering
      (choiLamCutoffH epsilon m) 1 (2 * m) 0 (4 * (m + 1))
      (choiLamCutoffH_nonneg_on_Icc epsilon m hm heps_bound)
      (choiLamCutoffH_natDegree_le epsilon m hm) hS hSdeg (by omega)

/-- Explicit tight upper certificate at level `4*m`. -/
theorem choiLamPerturbed_mem_BoxPreordering_tight_of_m
    (epsilon : ℝ) (_heps : 0 < epsilon) (_heps4 : epsilon ≤ 4)
    (m : ℕ) (hm : 2 ≤ m)
    (hm_eps : (4 / epsilon) ^ ((1 : ℝ) / 4) ≤ (m : ℝ)) :
    choiLamPerturbed epsilon ∈ BoxPreordering 4 (4 * (m + 1)) := by
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  have heps_bound : 4 / (m : ℝ) ^ 4 ≤ epsilon := by
    have hbase_nonneg : 0 ≤ 4 / epsilon := by positivity
    have hroot_nonneg : 0 ≤ (4 / epsilon) ^ ((1 : ℝ) / 4) := by positivity
    have hpow := Real.rpow_le_rpow hroot_nonneg hm_eps (show 0 ≤ (4 : ℝ) by norm_num)
    have hleft : ((4 / epsilon) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) = 4 / epsilon := by
      rw [← Real.rpow_mul hbase_nonneg]
      norm_num
    have hfour_div : 4 / epsilon ≤ (m : ℝ) ^ 4 := by
      have hquarter : ((1 : ℝ) / 4) = (4 : ℝ)⁻¹ := by norm_num
      rw [← hleft]
      simpa [hquarter] using hpow
    have hmpos : 0 < (m : ℝ) ^ 4 := by positivity
    have hcross : 4 ≤ (m : ℝ) ^ 4 * epsilon := (div_le_iff₀ _heps).mp hfour_div
    rw [div_le_iff₀ hmpos]
    nlinarith
  rw [choiLam_tight_identity epsilon m (by omega)]
  exact BoxPreordering_add
    (BoxPreordering_add
      (choiLam_tight_term1_mem_box_preordering m hm)
      (choiLam_tight_term2_mem_box_preordering m hm1))
    (choiLam_tight_term3_mem_box_preordering epsilon m hm1 heps_bound)

/-- Public tightness corollary: Choi-Lam perturbations have degree
`O(epsilon^(-1/4))` Schmuedgen/preordering certificates. -/
theorem choiLamPerturbed_mem_BoxPreordering_tight
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 24 * epsilon ^ (-(1 : ℝ) / 4) ∧
        choiLamPerturbed epsilon ∈ BoxPreordering 4 r := by
  let x : ℝ := epsilon ^ (-(1 : ℝ) / 4)
  let A : ℝ := (4 / epsilon) ^ ((1 : ℝ) / 4)
  let m : ℕ := max 2 (Nat.ceil A)
  refine ⟨4 * (m + 1), ?_, ?_⟩
  · have hx_nonneg : 0 ≤ x := by positivity
    have hconst : (4 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
      have hpow4 := Real.rpow_le_rpow (by norm_num : 0 ≤ (4 : ℝ))
        (by norm_num : (4 : ℝ) ≤ 2 ^ 4) (by norm_num : 0 ≤ (1 : ℝ) / 4)
      norm_num at hpow4
      exact hpow4
    have hx_ge_half : (1 / 2 : ℝ) ≤ x := by
      have hroot_le : epsilon ^ ((1 : ℝ) / 4) ≤ 2 := by
        have hpow := Real.rpow_le_rpow (le_of_lt heps) heps4
          (by norm_num : 0 ≤ (1 : ℝ) / 4)
        exact le_trans hpow hconst
      have hroot_pos : 0 < epsilon ^ ((1 : ℝ) / 4) := by positivity
      have htmp : (1 / 2 : ℝ) ≤ 1 / epsilon ^ ((1 : ℝ) / 4) :=
        one_div_le_one_div_of_le hroot_pos hroot_le
      dsimp [x]
      rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring, Real.rpow_neg (le_of_lt heps)]
      simpa [one_div] using htmp
    have hA_le : A ≤ 2 * x := by
      dsimp [A, x]
      rw [Real.div_rpow (by norm_num : 0 ≤ (4 : ℝ)) (le_of_lt heps)]
      rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring, Real.rpow_neg (le_of_lt heps)]
      have hinv_nonneg : 0 ≤ (epsilon ^ ((1 : ℝ) / 4))⁻¹ := by positivity
      have hmul := mul_le_mul_of_nonneg_right hconst hinv_nonneg
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hceil_lt : (Nat.ceil A : ℝ) < A + 1 := Nat.ceil_lt_add_one (by positivity)
    have hceil_le : (Nat.ceil A : ℝ) ≤ 4 * x := by
      have : (Nat.ceil A : ℝ) < 4 * x := by nlinarith
      exact le_of_lt this
    have htwo_le : (2 : ℝ) ≤ 4 * x := by nlinarith
    have hm_le : (m : ℝ) ≤ 4 * x := by
      dsimp [m]
      rw [Nat.cast_max]
      exact max_le htwo_le hceil_le
    calc ((4 * (m + 1) : ℕ) : ℝ)
        = 4 * ((m : ℝ) + 1) := by norm_num
      _ ≤ 4 * (6 * x) := by
        have hone_le : (1 : ℝ) ≤ 2 * x := by linarith
        nlinarith
      _ = 24 * epsilon ^ (-(1 : ℝ) / 4) := by simp [x]; ring
  · apply choiLamPerturbed_mem_BoxPreordering_tight_of_m
    · exact heps
    · exact heps4
    · simp [m]
    · have hceil : A ≤ (Nat.ceil A : ℝ) := Nat.le_ceil A
      have hceil_m : (Nat.ceil A : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.le_max_right 2 (Nat.ceil A)
      exact le_trans hceil hceil_m

end OptimalConvergenceRates

end
