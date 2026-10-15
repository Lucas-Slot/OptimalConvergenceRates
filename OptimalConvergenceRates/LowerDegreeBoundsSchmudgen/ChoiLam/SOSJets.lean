/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/SOSJets.lean

  Local control of SOS vectors extracted from four-variable box-preordering certificates.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.HomogeneousJets

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-- Extract the defining data of a four-variable preordering certificate. -/
theorem box_preordering_decomp_n4 (p : MvPolynomial (Fin 4) ℝ) (r : ℕ)
    (hp : p ∈ BoxPreordering 4 r) :
    ∃ (σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ),
      (∀ J, IsSOS (σ J)) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      p = ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J := by
  exact hp


/-- Extract preordering data together with explicit SOS vectors for every coefficient. -/
theorem box_preordering_decomp_with_sos_vectors (p : MvPolynomial (Fin 4) ℝ) (r : ℕ)
    (hp : p ∈ BoxPreordering 4 r) :
    ∃ (σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ),
      (∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 4) ℝ), σ J = sosVectorSq4 Q) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      p = ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J := by
  obtain ⟨σ, hsos, hdeg, hsum⟩ := hp
  refine ⟨σ, ?_, hdeg, hsum⟩
  intro J
  obtain ⟨N, Q, hQ⟩ := hsos J
  exact ⟨N, Q, hQ⟩

/-- Evaluation of an extracted SOS vector. -/
theorem interior_sos_eval_eq_vecSqNorm {N : ℕ} (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (x : Fin 4 → ℝ) :
    MvPolynomial.eval x (sosVectorSq4 Q) =
      interiorVecSqNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) := by
  unfold sosVectorSq4 interiorVecSqNorm
  simp [map_sum, map_pow]

/-- Local positivity of all preordering weights near the origin.

Equivalently, `g_I(x) >= alpha0` whenever `|x_i| <= s`. -/
theorem generatorProd_eval_ge_alpha0 (J : Finset (Fin 4)) (x : Fin 4 → ℝ)
    (hx : boxSmall x) :
    schmInteriorAlpha0 ≤
      MvPolynomial.eval x (BoxSemialgebraicGeneratorProd J) := by
  have hpoint : ∀ i : Fin 4,
      (15 / 16 : ℝ) ≤ MvPolynomial.eval x (BoxSemialgebraicGenerator i) := by
    intro i
    rw [BoxSemialgebraicGenerator_eval]
    have hsq : x i ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      have hi := hx i
      rw [← sq_abs, ← sq_abs (1 / 4 : ℝ)]
      simpa [schmInteriorS] using pow_le_pow_left₀ (abs_nonneg (x i)) hi 2
    norm_num at hsq ⊢
    nlinarith
  have hprod :
      (∏ i ∈ J, (15 / 16 : ℝ)) ≤
        ∏ i ∈ J, MvPolynomial.eval x (BoxSemialgebraicGenerator i) := by
    exact Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun i _ => hpoint i)
  have hcard : J.card ≤ 4 := by
    simpa [Fintype.card_fin] using (Finset.card_le_univ J)
  have hpow : (15 / 16 : ℝ) ^ 4 ≤ (15 / 16 : ℝ) ^ J.card := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
  unfold BoxSemialgebraicGeneratorProd
  rw [map_prod]
  rw [Finset.prod_const] at hprod
  unfold schmInteriorAlpha0 schmInteriorS
  norm_num at hpow
  norm_num
  exact hpow.trans hprod

/-- Termwise local control of each SOS coefficient in a concrete preordering certificate.

Positivity of each preordering weight near the origin bounds every individual
SOS coefficient by the whole left-hand side divided by `alpha0`. -/
theorem box_preordering_sos_coeff_eval_bound
    {epsilon : ℝ} {σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ}
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : choiLamQuartic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 4)) (x : Fin 4 → ℝ) (hx : boxSmall x) :
    MvPolynomial.eval x (σ J) ≤
      (MvPolynomial.eval x choiLamQuartic + epsilon) / schmInteriorAlpha0 := by
  have hsig_non : ∀ K, 0 ≤ MvPolynomial.eval x (σ K) := by
    intro K
    exact IsSOS_nonneg (σ K) (hsos K) x (Set.mem_univ _)
  have hterm_ge :
      schmInteriorAlpha0 * MvPolynomial.eval x (σ J) ≤
        MvPolynomial.eval x (σ J * BoxSemialgebraicGeneratorProd J) := by
    rw [map_mul]
    nlinarith
      [mul_le_mul_of_nonneg_right (generatorProd_eval_ge_alpha0 J x hx) (hsig_non J)]
  have hsum_non : ∀ K ∈ Finset.univ.powerset,
      0 ≤ MvPolynomial.eval x (σ K * BoxSemialgebraicGeneratorProd K) := by
    intro K _
    rw [map_mul]
    have hg := generatorProd_eval_ge_alpha0 K x hx
    nlinarith [schmInteriorAlpha0_pos, hsig_non K]
  have hsingle :
      MvPolynomial.eval x (σ J * BoxSemialgebraicGeneratorProd J) ≤
        ∑ K ∈ Finset.univ.powerset,
          MvPolynomial.eval x (σ K * BoxSemialgebraicGeneratorProd K) := by
    exact Finset.single_le_sum hsum_non (by simp)
  have htotal :
      MvPolynomial.eval x choiLamQuartic + epsilon =
        ∑ K ∈ Finset.univ.powerset,
          MvPolynomial.eval x (σ K * BoxSemialgebraicGeneratorProd K) := by
    calc
      MvPolynomial.eval x choiLamQuartic + epsilon =
          MvPolynomial.eval x (choiLamQuartic + MvPolynomial.C epsilon) := by simp
      _ = MvPolynomial.eval x (∑ K ∈ Finset.univ.powerset,
          σ K * BoxSemialgebraicGeneratorProd K) := by rw [hcert]
      _ = ∑ K ∈ Finset.univ.powerset,
          MvPolynomial.eval x (σ K * BoxSemialgebraicGeneratorProd K) := by simp [map_sum]
  have hmul_le :
      schmInteriorAlpha0 * MvPolynomial.eval x (σ J) ≤
        MvPolynomial.eval x choiLamQuartic + epsilon := by
    rw [htotal]
    exact hterm_ge.trans hsingle
  rw [le_div_iff₀ schmInteriorAlpha0_pos]
  nlinarith

/-- Termwise local control after replacing the Choi-Lam quartic by its
`5 * ||x||^4` local homogeneous bound. -/
theorem box_preordering_sos_coeff_eval_bound_by_norm
    {epsilon : ℝ} {σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ}
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : choiLamQuartic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 4)) (x : Fin 4 → ℝ) (hx : boxSmall x) :
    MvPolynomial.eval x (σ J) ≤ (5 * localSqNorm x ^ 2 + epsilon) / schmInteriorAlpha0 := by
  have hmain := box_preordering_sos_coeff_eval_bound hsos hcert J x hx
  have hnum :
      MvPolynomial.eval x choiLamQuartic + epsilon ≤ 5 * localSqNorm x ^ 2 + epsilon := by
    nlinarith [choiLamQuartic_le_five_localSqNorm_sq x]
  exact hmain.trans (div_le_div_of_nonneg_right hnum schmInteriorAlpha0_pos.le)

/-- Vector-square form of the local control when an SOS coefficient is already
presented as `||Q_J||^2`. -/
theorem box_preordering_sos_vector_sq_eval_bound_by_norm
    {N : ℕ} {epsilon : ℝ} {σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ}
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : choiLamQuartic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 4)) (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hσJ : σ J = sosVectorSq4 Q)
    (x : Fin 4 → ℝ) (hx : boxSmall x) :
    interiorVecSqNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
      (5 * localSqNorm x ^ 2 + epsilon) / schmInteriorAlpha0 := by
  rw [← interior_sos_eval_eq_vecSqNorm Q x, ← hσJ]
  exact box_preordering_sos_coeff_eval_bound_by_norm hsos hcert J x hx


/-- Square-root form of the coarse local control. -/
theorem sqrt_local_control_bound {epsilon u : ℝ} (heps : 0 ≤ epsilon) (hu : 0 ≤ u) :
    Real.sqrt ((5 * u ^ 2 + epsilon) / schmInteriorAlpha0) ≤
      schmInteriorLocalControlConst * (Real.sqrt epsilon + u) := by
  rw [Real.sqrt_le_iff]
  constructor
  · nlinarith [schmInteriorLocalControlConst_pos, Real.sqrt_nonneg epsilon, hu]
  have hnum_non : 0 ≤ 5 * u ^ 2 + epsilon := by positivity
  have hdiv : (5 * u ^ 2 + epsilon) / schmInteriorAlpha0 ≤ 2 * (5 * u ^ 2 + epsilon) := by
    rw [div_le_iff₀ schmInteriorAlpha0_pos]
    nlinarith [mul_le_mul_of_nonneg_right one_half_le_schmInteriorAlpha0 hnum_non]
  have hsqrt_sq : (Real.sqrt epsilon) ^ 2 = epsilon := Real.sq_sqrt heps
  have hbig :
      2 * (5 * u ^ 2 + epsilon) ≤
        (schmInteriorLocalControlConst * (Real.sqrt epsilon + u)) ^ 2 := by
    unfold schmInteriorLocalControlConst
    nlinarith [sq_nonneg (Real.sqrt epsilon + u), Real.sqrt_nonneg epsilon]
  exact hdiv.trans hbig

/-- Local control for an explicitly represented SOS coefficient. -/
theorem box_preordering_sos_vector_local_control_by_norm
    {N : ℕ} {epsilon : ℝ} {σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ}
    (heps : 0 ≤ epsilon)
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : choiLamQuartic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 4)) (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hσJ : σ J = sosVectorSq4 Q)
    (x : Fin 4 → ℝ) (hx : boxSmall x) :
    interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
      schmInteriorLocalControlConst * (Real.sqrt epsilon + localSqNorm x) := by
  unfold interiorVecNorm
  calc
    Real.sqrt (interiorVecSqNorm (fun i : Fin N => MvPolynomial.eval x (Q i)))
        ≤ Real.sqrt ((5 * localSqNorm x ^ 2 + epsilon) / schmInteriorAlpha0) :=
          Real.sqrt_le_sqrt
            (box_preordering_sos_vector_sq_eval_bound_by_norm hsos hcert J Q hσJ x hx)
    _ ≤ schmInteriorLocalControlConst * (Real.sqrt epsilon + localSqNorm x) :=
          sqrt_local_control_bound heps (localSqNorm_nonneg x)

/-- Points on every Choi-Lam zero line stay in the small coordinate box for `|t| <= s`. -/
theorem choiLam_zero_line_mem_boxSmall (zi : Fin 4) {t : ℝ} (ht : |t| ≤ schmInteriorS) :
    boxSmall (fun j => t * choiLamZeroDirection zi j) := by
  intro j
  have hz : |choiLamZeroDirection zi j| ≤ 1 := by
    fin_cases zi <;> fin_cases j <;>
      simp [choiLamZeroDirection, choiLamZeroDirection0, choiLamZeroDirection1,
        choiLamZeroDirection2, choiLamZeroDirection3] <;>
      norm_num
  calc
    |t * choiLamZeroDirection zi j| = |t| * |choiLamZeroDirection zi j| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hz (abs_nonneg t)
    _ ≤ schmInteriorS := by simpa using ht

/-- Sharper control along a Choi-Lam zero line. -/
theorem box_preordering_sos_vector_zero_line_control
    {N : ℕ} {epsilon : ℝ} {σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ}
    (heps : 0 ≤ epsilon)
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : choiLamQuartic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 4)) (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hσJ : σ J = sosVectorSq4 Q)
    (zi : Fin 4) (t : ℝ) (ht : |t| ≤ schmInteriorS) :
    interiorVecNorm
        (fun i : Fin N => MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
      ≤ schmInteriorLocalControlConst * Real.sqrt epsilon := by
  let x : Fin 4 → ℝ := fun j => t * choiLamZeroDirection zi j
  have hx : boxSmall x := choiLam_zero_line_mem_boxSmall zi ht
  have hsq : interiorVecSqNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
      epsilon / schmInteriorAlpha0 := by
    rw [← interior_sos_eval_eq_vecSqNorm Q x, ← hσJ]
    have hmain := box_preordering_sos_coeff_eval_bound hsos hcert J x hx
    rw [choiLamQuartic_zero_on_direction_line zi t] at hmain
    simpa using hmain
  unfold interiorVecNorm
  calc
    Real.sqrt (interiorVecSqNorm (fun i : Fin N => MvPolynomial.eval x (Q i)))
        ≤ Real.sqrt (epsilon / schmInteriorAlpha0) := Real.sqrt_le_sqrt hsq
    _ ≤ schmInteriorLocalControlConst * Real.sqrt epsilon := by
      rw [Real.sqrt_le_iff]
      constructor
      · nlinarith [schmInteriorLocalControlConst_pos, Real.sqrt_nonneg epsilon]
      have hdiv : epsilon / schmInteriorAlpha0 ≤ 2 * epsilon := by
        rw [div_le_iff₀ schmInteriorAlpha0_pos]
        nlinarith [mul_le_mul_of_nonneg_right one_half_le_schmInteriorAlpha0 heps]
      have hsqrt_sq : (Real.sqrt epsilon) ^ 2 = epsilon := Real.sq_sqrt heps
      have hbig : 2 * epsilon ≤ (schmInteriorLocalControlConst * Real.sqrt epsilon) ^ 2 := by
        unfold schmInteriorLocalControlConst
        nlinarith [Real.sqrt_nonneg epsilon]
      exact hdiv.trans hbig

/-- Certificate-level extraction of the local controls (5.3) and (5.4).

For every preordering coefficient, choose an SOS vector witness.  The extracted
vector satisfies the coarse local bound on the small box and the sharper bound
on each Choi-Lam zero line. -/
theorem box_preordering_certificate_sos_vectors_local_control
    {epsilon : ℝ} {r : ℕ} (heps : 0 ≤ epsilon)
    (hcert : choiLamQuartic + MvPolynomial.C epsilon ∈ BoxPreordering 4 r) :
    ∃ (σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ),
      (∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 4) ℝ),
        σ J = sosVectorSq4 Q ∧
        (∀ x, boxSmall x →
          interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
            schmInteriorLocalControlConst * (Real.sqrt epsilon + localSqNorm x)) ∧
        (∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
          interiorVecNorm
              (fun i : Fin N =>
                MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i)) ≤
            schmInteriorLocalControlConst * Real.sqrt epsilon)) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      choiLamQuartic + MvPolynomial.C epsilon =
        ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J := by
  obtain ⟨σ, hsos, hdeg, hsum⟩ := hcert
  refine ⟨σ, ?_, hdeg, hsum⟩
  intro J
  obtain ⟨N, Q, hQ⟩ := hsos J
  refine ⟨N, Q, hQ, ?_, ?_⟩
  · intro x hx
    exact box_preordering_sos_vector_local_control_by_norm heps hsos hsum J Q hQ x hx
  · intro zi t ht
    exact box_preordering_sos_vector_zero_line_control heps hsos hsum J Q hQ zi t ht

/-- Termwise local control of the SOS vectors extracted from a preordering certificate.

This is a compact public wrapper around
`box_preordering_certificate_sos_vectors_local_control`. -/
theorem box_preordering_sos_vector_local_bound
    {r : ℕ} {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (hcert : choiLamQuartic + MvPolynomial.C epsilon ∈ BoxPreordering 4 r) :
    ∃ (σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ),
      (∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 4) ℝ),
        σ J = sosVectorSq4 Q ∧
        (∀ x, boxSmall x →
          interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
            schmInteriorLocalControlConst * (Real.sqrt epsilon + localSqNorm x)) ∧
        (∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
          interiorVecNorm
              (fun i : Fin N =>
                MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i)) ≤
            schmInteriorLocalControlConst * Real.sqrt epsilon)) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      choiLamQuartic + MvPolynomial.C epsilon =
        ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J :=
  box_preordering_certificate_sos_vectors_local_control heps hcert

end OptimalConvergenceRates

end
