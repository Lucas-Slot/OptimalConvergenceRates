/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/Motzkin/LocalControl.lean

  Local control of SOS vectors extracted from three-variable box-preordering certificates.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.HomogeneousJets
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.CertificateExtraction

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin


/-- Coordinatewise small box used for local Motzkin estimates. -/
def motzkinBoxSmall (x : Fin 3 → ℝ) : Prop :=
  ∀ i, |x i| ≤ schmInteriorS

/-- The six projective zero directions of the Motzkin sextic. -/
def motzkinZeroDirection : Fin 6 → Fin 3 → ℝ
  | 0 => motzkinAxisX
  | 1 => motzkinAxisY
  | 2 => motzkinSignDirection 0 0
  | 3 => motzkinSignDirection 0 1
  | 4 => motzkinSignDirection 1 0
  | 5 => motzkinSignDirection 1 1

theorem motzkinSextic_zero_on_direction_line (i : Fin 6) (t : ℝ) :
    eval (fun j => t * motzkinZeroDirection i j) motzkinSextic = 0 := by
  fin_cases i <;> rw [motzkinSextic_eval] <;>
    simp [motzkinZeroDirection, motzkinAxisX, motzkinAxisY,
      motzkinSignDirection] <;> ring

/-- Extract the defining data of a three-variable preordering certificate. -/
theorem box_preordering_decomp_n3 (p : MvPolynomial (Fin 3) ℝ) (r : ℕ)
    (hp : p ∈ BoxPreordering 3 r) :
    ∃ (σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ),
      (∀ J, IsSOS (σ J)) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      p = ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J := by
  exact hp


/-- Extract preordering data together with explicit SOS vectors for every coefficient. -/
theorem box_preordering_decomp_with_sos_vectors (p : MvPolynomial (Fin 3) ℝ) (r : ℕ)
    (hp : p ∈ BoxPreordering 3 r) :
    ∃ (σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ),
      (∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 3) ℝ), σ J = sosVectorSq3 Q) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      p = ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J := by
  obtain ⟨σ, hsos, hdeg, hsum⟩ := hp
  refine ⟨σ, ?_, hdeg, hsum⟩
  intro J
  obtain ⟨N, Q, hQ⟩ := hsos J
  exact ⟨N, Q, hQ⟩

/-- Evaluation of an extracted SOS vector. -/
theorem interior_sos_eval_eq_vecSqNorm {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ)
    (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (sosVectorSq3 Q) =
      interiorVecSqNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) := by
  unfold sosVectorSq3 interiorVecSqNorm
  simp [map_sum, map_pow]

/-- Local positivity of all preordering weights near the origin.

Equivalently, `g_I(x) >= alpha0` whenever `|x_i| <= s`. -/
theorem generatorProd_eval_ge_alpha0 (J : Finset (Fin 3)) (x : Fin 3 → ℝ)
    (hx : motzkinBoxSmall x) :
    schmInteriorAlpha0 ≤
      MvPolynomial.eval x (BoxSemialgebraicGeneratorProd J) := by
  have hpoint : ∀ i : Fin 3,
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
    have h := Finset.card_le_univ J
    simp [Fintype.card_fin] at h
    omega
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
    {epsilon : ℝ} {σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ}
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : motzkinSextic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 3)) (x : Fin 3 → ℝ) (hx : motzkinBoxSmall x) :
    MvPolynomial.eval x (σ J) ≤
      (MvPolynomial.eval x motzkinSextic + epsilon) / schmInteriorAlpha0 := by
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
      MvPolynomial.eval x motzkinSextic + epsilon =
        ∑ K ∈ Finset.univ.powerset,
          MvPolynomial.eval x (σ K * BoxSemialgebraicGeneratorProd K) := by
    calc
      MvPolynomial.eval x motzkinSextic + epsilon =
          MvPolynomial.eval x (motzkinSextic + MvPolynomial.C epsilon) := by simp
      _ = MvPolynomial.eval x (∑ K ∈ Finset.univ.powerset,
          σ K * BoxSemialgebraicGeneratorProd K) := by rw [hcert]
      _ = ∑ K ∈ Finset.univ.powerset,
          MvPolynomial.eval x (σ K * BoxSemialgebraicGeneratorProd K) := by simp [map_sum]
  have hmul_le :
      schmInteriorAlpha0 * MvPolynomial.eval x (σ J) ≤
        MvPolynomial.eval x motzkinSextic + epsilon := by
    rw [htotal]
    exact hterm_ge.trans hsingle
  rw [le_div_iff₀ schmInteriorAlpha0_pos]
  nlinarith

/-- Termwise local control after replacing the Choi-Lam quartic by its
`5 * ||x||^4` local homogeneous bound. -/
theorem box_preordering_sos_coeff_eval_bound_by_norm
    {epsilon : ℝ} {σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ}
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : motzkinSextic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 3)) (x : Fin 3 → ℝ) (hx : motzkinBoxSmall x) :
    MvPolynomial.eval x (σ J) ≤ (3 * motzkinSqNorm x ^ 3 + epsilon) / schmInteriorAlpha0 := by
  have hmain := box_preordering_sos_coeff_eval_bound hsos hcert J x hx
  have hnum :
      MvPolynomial.eval x motzkinSextic + epsilon ≤ 3 * motzkinSqNorm x ^ 3 + epsilon := by
    nlinarith [motzkinSextic_eval_le_three_sqNorm_cube x]
  exact hmain.trans (div_le_div_of_nonneg_right hnum schmInteriorAlpha0_pos.le)

/-- Vector-square form of the local control when an SOS coefficient is already
presented as `||Q_J||^2`. -/
theorem box_preordering_sos_vector_sq_eval_bound_by_norm
    {N : ℕ} {epsilon : ℝ} {σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ}
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : motzkinSextic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 3)) (Q : Fin N → MvPolynomial (Fin 3) ℝ)
    (hσJ : σ J = sosVectorSq3 Q)
    (x : Fin 3 → ℝ) (hx : motzkinBoxSmall x) :
    interiorVecSqNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
      (3 * motzkinSqNorm x ^ 3 + epsilon) / schmInteriorAlpha0 := by
  rw [← interior_sos_eval_eq_vecSqNorm Q x, ← hσJ]
  exact box_preordering_sos_coeff_eval_bound_by_norm hsos hcert J x hx


/-- Square-root form of the coarse local control. -/
theorem sqrt_local_control_bound {epsilon u : ℝ} (heps : 0 ≤ epsilon)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.sqrt ((3 * u ^ 3 + epsilon) / schmInteriorAlpha0) ≤
      schmInteriorLocalControlConst * (Real.sqrt epsilon + u) := by
  rw [Real.sqrt_le_iff]
  constructor
  · nlinarith [schmInteriorLocalControlConst_pos, Real.sqrt_nonneg epsilon, hu]
  have hnum_non : 0 ≤ 3 * u ^ 3 + epsilon := by positivity
  have hdiv : (3 * u ^ 3 + epsilon) / schmInteriorAlpha0 ≤ 2 * (3 * u ^ 3 + epsilon) := by
    rw [div_le_iff₀ schmInteriorAlpha0_pos]
    nlinarith [mul_le_mul_of_nonneg_right one_half_le_schmInteriorAlpha0 hnum_non]
  have hu32 : u ^ 3 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
  have hsqrt_sq : (Real.sqrt epsilon) ^ 2 = epsilon := Real.sq_sqrt heps
  have hbig :
      2 * (3 * u ^ 3 + epsilon) ≤
        (schmInteriorLocalControlConst * (Real.sqrt epsilon + u)) ^ 2 := by
    unfold schmInteriorLocalControlConst
    nlinarith [sq_nonneg (Real.sqrt epsilon + u), Real.sqrt_nonneg epsilon]
  exact hdiv.trans hbig

/-- Local control for an explicitly represented SOS coefficient. -/
theorem box_preordering_sos_vector_local_control_by_norm
    {N : ℕ} {epsilon : ℝ} {σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ}
    (heps : 0 ≤ epsilon)
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : motzkinSextic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 3)) (Q : Fin N → MvPolynomial (Fin 3) ℝ)
    (hσJ : σ J = sosVectorSq3 Q)
    (x : Fin 3 → ℝ) (hx : motzkinBoxSmall x) :
    interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
      schmInteriorLocalControlConst * (Real.sqrt epsilon + motzkinSqNorm x) := by
  unfold interiorVecNorm
  calc
    Real.sqrt (interiorVecSqNorm (fun i : Fin N => MvPolynomial.eval x (Q i)))
        ≤ Real.sqrt ((3 * motzkinSqNorm x ^ 3 + epsilon) / schmInteriorAlpha0) :=
          Real.sqrt_le_sqrt
            (box_preordering_sos_vector_sq_eval_bound_by_norm hsos hcert J Q hσJ x hx)
    _ ≤ schmInteriorLocalControlConst * (Real.sqrt epsilon + motzkinSqNorm x) :=
          sqrt_local_control_bound heps (motzkinSqNorm_nonneg x) (by
            rw [motzkinSqNorm, Fin.sum_univ_three]
            have hsq (i : Fin 3) : x i ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
              have hi := hx i
              rw [← sq_abs, ← sq_abs (1 / 4 : ℝ)]
              simpa [schmInteriorS] using
                pow_le_pow_left₀ (abs_nonneg (x i)) hi 2
            nlinarith [hsq 0, hsq 1, hsq 2])

/-- Cubic-order local control along a unit direction. -/
theorem box_preordering_sos_vector_unit_line_cubic_control
    {N : ℕ} {epsilon : ℝ} {σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ}
    (heps : 0 ≤ epsilon)
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : motzkinSextic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 3)) (Q : Fin N → MvPolynomial (Fin 3) ℝ)
    (hσJ : σ J = sosVectorSq3 Q)
    (v : Fin 3 → ℝ) (hv : motzkinSqNorm v = 1)
    (t : ℝ) (ht : |t| ≤ schmInteriorS) :
    interiorVecNorm
        (fun i : Fin N => MvPolynomial.eval (fun j => t * v j) (Q i)) ≤
      schmInteriorLocalControlConst * (Real.sqrt epsilon + |t| ^ 3) := by
  let x : Fin 3 → ℝ := fun j => t * v j
  have hvcoord (j : Fin 3) : |v j| ≤ 1 := by
    have hj : v j ^ 2 ≤ motzkinSqNorm v := by
      unfold motzkinSqNorm
      exact Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ j)
    rw [hv] at hj
    nlinarith [sq_abs (v j), abs_nonneg (v j)]
  have hx : motzkinBoxSmall x := by
    intro j
    calc
      |x j| = |t| * |v j| := abs_mul _ _
      _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hvcoord j) (abs_nonneg t)
      _ ≤ schmInteriorS := by simpa using ht
  have hsq := box_preordering_sos_vector_sq_eval_bound_by_norm
    hsos hcert J Q hσJ x hx
  have hnorm : motzkinSqNorm x = t ^ 2 := by
    dsimp [x]
    rw [motzkinSqNorm_smul, hv, mul_one]
  rw [hnorm] at hsq
  unfold interiorVecNorm
  calc
    Real.sqrt (interiorVecSqNorm (fun i : Fin N => MvPolynomial.eval x (Q i))) ≤
        Real.sqrt ((3 * (t ^ 2) ^ 3 + epsilon) / schmInteriorAlpha0) :=
      Real.sqrt_le_sqrt hsq
    _ ≤ schmInteriorLocalControlConst * (Real.sqrt epsilon + |t| ^ 3) := by
      rw [Real.sqrt_le_iff]
      constructor
      · exact mul_nonneg schmInteriorLocalControlConst_pos.le
          (add_nonneg (Real.sqrt_nonneg epsilon) (pow_nonneg (abs_nonneg t) 3))
      have hnum : 0 ≤ 3 * (t ^ 2) ^ 3 + epsilon := by positivity
      have hdiv : (3 * (t ^ 2) ^ 3 + epsilon) / schmInteriorAlpha0 ≤
          2 * (3 * (t ^ 2) ^ 3 + epsilon) := by
        rw [div_le_iff₀ schmInteriorAlpha0_pos]
        nlinarith [mul_le_mul_of_nonneg_right one_half_le_schmInteriorAlpha0 hnum]
      have hsqrt : (Real.sqrt epsilon) ^ 2 = epsilon := Real.sq_sqrt heps
      have habs : (|t| ^ 3) ^ 2 = (t ^ 2) ^ 3 := by
        rw [← abs_pow, sq_abs]
        ring
      unfold schmInteriorLocalControlConst
      nlinarith [sq_nonneg (Real.sqrt epsilon + |t| ^ 3),
        Real.sqrt_nonneg epsilon, pow_nonneg (abs_nonneg t) 3]

/-- Points on every Choi-Lam zero line stay in the small coordinate box for `|t| <= s`. -/
theorem motzkin_zero_line_mem_motzkinBoxSmall (zi : Fin 6) {t : ℝ} (ht : |t| ≤ schmInteriorS) :
    motzkinBoxSmall (fun j => t * motzkinZeroDirection zi j) := by
  intro j
  have hz : |motzkinZeroDirection zi j| ≤ 1 := by
    fin_cases zi <;> fin_cases j <;>
      simp [motzkinZeroDirection, motzkinAxisX, motzkinAxisY, motzkinSignDirection]
  calc
    |t * motzkinZeroDirection zi j| = |t| * |motzkinZeroDirection zi j| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hz (abs_nonneg t)
    _ ≤ schmInteriorS := by simpa using ht

/-- Sharper control along a Motzkin zero line. -/
theorem box_preordering_sos_vector_zero_line_control
    {N : ℕ} {epsilon : ℝ} {σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ}
    (heps : 0 ≤ epsilon)
    (hsos : ∀ J, IsSOS (σ J))
    (hcert : motzkinSextic + MvPolynomial.C epsilon =
      ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J)
    (J : Finset (Fin 3)) (Q : Fin N → MvPolynomial (Fin 3) ℝ)
    (hσJ : σ J = sosVectorSq3 Q)
    (zi : Fin 6) (t : ℝ) (ht : |t| ≤ schmInteriorS) :
    interiorVecNorm
        (fun i : Fin N => MvPolynomial.eval (fun j => t * motzkinZeroDirection zi j) (Q i))
      ≤ schmInteriorLocalControlConst * Real.sqrt epsilon := by
  let x : Fin 3 → ℝ := fun j => t * motzkinZeroDirection zi j
  have hx : motzkinBoxSmall x := motzkin_zero_line_mem_motzkinBoxSmall zi ht
  have hsq : interiorVecSqNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
      epsilon / schmInteriorAlpha0 := by
    rw [← interior_sos_eval_eq_vecSqNorm Q x, ← hσJ]
    have hmain := box_preordering_sos_coeff_eval_bound hsos hcert J x hx
    rw [motzkinSextic_zero_on_direction_line zi t] at hmain
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
    (hcert : motzkinSextic + MvPolynomial.C epsilon ∈ BoxPreordering 3 r) :
    ∃ (σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ),
      (∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 3) ℝ),
        σ J = sosVectorSq3 Q ∧
        (∀ x, motzkinBoxSmall x →
          interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
            schmInteriorLocalControlConst * (Real.sqrt epsilon + motzkinSqNorm x)) ∧
        (∀ zi : Fin 6, ∀ t : ℝ, |t| ≤ schmInteriorS →
          interiorVecNorm
              (fun i : Fin N =>
                MvPolynomial.eval (fun j => t * motzkinZeroDirection zi j) (Q i)) ≤
            schmInteriorLocalControlConst * Real.sqrt epsilon)) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      motzkinSextic + MvPolynomial.C epsilon =
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

/-- Certificate-level extraction with both local and degree control. -/
theorem box_preordering_certificate_sos_vectors_local_control_with_degree
    {epsilon : ℝ} {r : ℕ} (heps : 0 ≤ epsilon)
    (hcert : motzkinSextic + MvPolynomial.C epsilon ∈ BoxPreordering 3 r) :
    ∃ (σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ),
      (∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 3) ℝ),
        σ J = sosVectorSq3 Q ∧
        (∀ i, (Q i).totalDegree ≤ r) ∧
        (∀ x, motzkinBoxSmall x →
          interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
            schmInteriorLocalControlConst * (Real.sqrt epsilon + motzkinSqNorm x)) ∧
        (∀ zi : Fin 6, ∀ t : ℝ, |t| ≤ schmInteriorS →
          interiorVecNorm
              (fun i : Fin N =>
                MvPolynomial.eval (fun j => t * motzkinZeroDirection zi j) (Q i)) ≤
            schmInteriorLocalControlConst * Real.sqrt epsilon)) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      motzkinSextic + MvPolynomial.C epsilon =
        ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J := by
  obtain ⟨σ, hsos, hdeg, hsum⟩ := hcert
  refine ⟨σ, ?_, hdeg, hsum⟩
  have hQdeg := boxPreorderingSOSWitnessDegreeBound_n3 hsos hdeg
  intro J
  obtain ⟨N, Q, hQ, hQdegJ⟩ := hQdeg J
  refine ⟨N, Q, hQ, hQdegJ, ?_, ?_⟩
  · intro x hx
    exact box_preordering_sos_vector_local_control_by_norm
      heps hsos hsum J Q hQ x hx
  · intro zi t ht
    exact box_preordering_sos_vector_zero_line_control
      heps hsos hsum J Q hQ zi t ht

/-- Degree-controlled SOS roots with both zero-line and cubic unit-line estimates. -/
theorem box_preordering_certificate_sos_vectors_cubic_with_degree
    {epsilon : ℝ} {r : ℕ} (heps : 0 ≤ epsilon)
    (hcert : motzkinSextic + MvPolynomial.C epsilon ∈ BoxPreordering 3 r) :
    ∃ (σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ),
      (∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 3) ℝ),
        σ J = sosVectorSq3 Q ∧
        (∀ i, (Q i).totalDegree ≤ r) ∧
        (∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
          ∀ t : ℝ, |t| ≤ schmInteriorS →
            interiorVecNorm (fun i : Fin N =>
              MvPolynomial.eval (fun j => t * v j) (Q i)) ≤
              schmInteriorLocalControlConst * (Real.sqrt epsilon + |t| ^ 3)) ∧
        (∀ zi : Fin 6, ∀ t : ℝ, |t| ≤ schmInteriorS →
          interiorVecNorm (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * motzkinZeroDirection zi j) (Q i)) ≤
            schmInteriorLocalControlConst * Real.sqrt epsilon)) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      motzkinSextic + MvPolynomial.C epsilon =
        ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J := by
  obtain ⟨σ, hsos, hdeg, hsum⟩ := hcert
  refine ⟨σ, ?_, hdeg, hsum⟩
  have hQdeg := boxPreorderingSOSWitnessDegreeBound_n3 hsos hdeg
  intro J
  obtain ⟨N, Q, hQ, hQdegJ⟩ := hQdeg J
  refine ⟨N, Q, hQ, hQdegJ, ?_, ?_⟩
  · intro v hv t ht
    exact box_preordering_sos_vector_unit_line_cubic_control
      heps hsos hsum J Q hQ v hv t ht
  · intro zi t ht
    exact box_preordering_sos_vector_zero_line_control
      heps hsos hsum J Q hQ zi t ht

/-- Termwise local control of the SOS vectors extracted from a preordering certificate.

This is a compact public wrapper around
`box_preordering_certificate_sos_vectors_local_control`. -/
theorem box_preordering_sos_vector_local_bound
    {r : ℕ} {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (hcert : motzkinSextic + MvPolynomial.C epsilon ∈ BoxPreordering 3 r) :
    ∃ (σ : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ),
      (∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 3) ℝ),
        σ J = sosVectorSq3 Q ∧
        (∀ x, motzkinBoxSmall x →
          interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
            schmInteriorLocalControlConst * (Real.sqrt epsilon + motzkinSqNorm x)) ∧
        (∀ zi : Fin 6, ∀ t : ℝ, |t| ≤ schmInteriorS →
          interiorVecNorm
              (fun i : Fin N =>
                MvPolynomial.eval (fun j => t * motzkinZeroDirection zi j) (Q i)) ≤
            schmInteriorLocalControlConst * Real.sqrt epsilon)) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      motzkinSextic + MvPolynomial.C epsilon =
        ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J :=
  box_preordering_certificate_sos_vectors_local_control heps hcert



private def qexp (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

@[simp] private lemma qexp_eq_qexp_iff (a b c d e f : ℕ) :
    qexp a b c = qexp d e f ↔ a = d ∧ b = e ∧ c = f := by
  constructor
  · intro h
    have h0 := congrArg (fun x : Fin 3 →₀ ℕ ↦ x 0) h
    have h1 := congrArg (fun x : Fin 3 →₀ ℕ ↦ x 1) h
    have h2 := congrArg (fun x : Fin 3 →₀ ℕ ↦ x 2) h
    simpa [qexp] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private lemma degree_two_coordinate_cases {d : Fin 3 →₀ ℕ} (hd : d.degree = 2) :
    (d 0 = 2 ∧ d 1 = 0 ∧ d 2 = 0) ∨
    (d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 0) ∨
    (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 1) ∨
    (d 0 = 0 ∧ d 1 = 2 ∧ d 2 = 0) ∨
    (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 1) ∨
    (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 2) := by
  have hdDegree := hd
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hd
  have h0 : d 0 ≤ 2 := (Finsupp.le_degree 0 d).trans_eq hdDegree
  have h1 : d 1 ≤ 2 := (Finsupp.le_degree 1 d).trans_eq hdDegree
  have h2 : d 2 ≤ 2 := (Finsupp.le_degree 2 d).trans_eq hdDegree
  interval_cases hd0 : d 0 <;> interval_cases hd1 : d 1 <;>
    interval_cases hd2 : d 2 <;> omega

private def quadraticNormalForm (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  monomial (qexp 2 0 0) (coeff (qexp 2 0 0) p) +
  monomial (qexp 1 1 0) (coeff (qexp 1 1 0) p) +
  monomial (qexp 1 0 1) (coeff (qexp 1 0 1) p) +
  monomial (qexp 0 2 0) (coeff (qexp 0 2 0) p) +
  monomial (qexp 0 1 1) (coeff (qexp 0 1 1) p) +
  monomial (qexp 0 0 2) (coeff (qexp 0 0 2) p)

private lemma eq_quadraticNormalForm {p : MvPolynomial (Fin 3) ℝ}
    (hp : homogeneousPart3 2 p = p) : p = quadraticNormalForm p := by
  ext d
  by_cases hd : d.degree = 2
  · rcases degree_two_coordinate_cases hd with h | h | h | h | h | h
    all_goals
      rcases h with ⟨h0, h1, h2⟩
      have hdexp : d = qexp (d 0) (d 1) (d 2) := by
        ext i
        fin_cases i <;> simp [qexp]
      simp only [h0, h1, h2] at hdexp
      subst d
      simp [quadraticNormalForm]
  · have hc : coeff d p = 0 :=
      (isHomogeneous_of_homogeneousPart3_eq hp).coeff_eq_zero hd
    have hne (a b c : ℕ) (hsum : a + b + c = 2) : qexp a b c ≠ d := by
      intro h
      apply hd
      rw [← h, Finsupp.degree_eq_sum, Fin.sum_univ_three]
      simp [qexp]
      omega
    change p.coeff d = 0 at hc
    rw [hc]
    simp [quadraticNormalForm, hne]

private lemma eval_quadratic_eq_coeffs {p : MvPolynomial (Fin 3) ℝ}
    (hp : homogeneousPart3 2 p = p) (x : Fin 3 → ℝ) :
    eval x p =
      coeff (Finsupp.single 0 2) p * x 0 ^ 2 +
      coeff (Finsupp.single 0 1 + Finsupp.single 1 1) p * x 0 * x 1 +
      coeff (Finsupp.single 0 1 + Finsupp.single 2 1) p * x 0 * x 2 +
      coeff (Finsupp.single 1 2) p * x 1 ^ 2 +
      coeff (Finsupp.single 1 1 + Finsupp.single 2 1) p * x 1 * x 2 +
      coeff (Finsupp.single 2 2) p * x 2 ^ 2 := by
  calc
    eval x p = eval x (quadraticNormalForm p) :=
      congrArg (eval x) (eq_quadraticNormalForm hp)
    _ = _ := by
      simp only [quadraticNormalForm, map_add]
      simp [MvPolynomial.eval_monomial, qexp, Fin.prod_univ_three]
      ring


private lemma interiorVecNorm_average_four_le
    {N : ℕ} {B : ℝ} (u0 u1 u2 u3 : Fin N → ℝ)
    (h0 : interiorVecNorm u0 ≤ B) (h1 : interiorVecNorm u1 ≤ B)
    (h2 : interiorVecNorm u2 ≤ B) (h3 : interiorVecNorm u3 ≤ B) :
    interiorVecNorm (fun i => (u0 i + u1 i + u2 i + u3 i) / 4) ≤ B := by
  have hsum :
      interiorVecNorm (fun i => u0 i + u1 i + u2 i + u3 i) ≤ 4 * B := by
    calc
      interiorVecNorm (fun i => u0 i + u1 i + u2 i + u3 i) ≤
          interiorVecNorm (fun i => u0 i + u1 i + u2 i) +
            interiorVecNorm u3 := by
        simpa [add_assoc] using interiorVecNorm_add_le
          (fun i => u0 i + u1 i + u2 i) u3
      _ ≤ (interiorVecNorm (fun i => u0 i + u1 i) + interiorVecNorm u2) +
            interiorVecNorm u3 := by
        gcongr
        exact interiorVecNorm_add_le _ _
      _ ≤ ((interiorVecNorm u0 + interiorVecNorm u1) + interiorVecNorm u2) +
            interiorVecNorm u3 := by
        gcongr
        exact interiorVecNorm_add_le _ _
      _ ≤ 4 * B := by linarith
  have hscale :
      interiorVecNorm (fun i => (u0 i + u1 i + u2 i + u3 i) / 4) =
        (1 / 4 : ℝ) * interiorVecNorm (fun i => u0 i + u1 i + u2 i + u3 i) := by
    have heq : (fun i => (u0 i + u1 i + u2 i + u3 i) / 4) =
        fun i => (1 / 4 : ℝ) * (u0 i + u1 i + u2 i + u3 i) := by
      funext i
      ring
    rw [heq]
    change vecNorm (fun i => (1 / 4 : ℝ) * (u0 i + u1 i + u2 i + u3 i)) =
      (1 / 4 : ℝ) * vecNorm (fun i => u0 i + u1 i + u2 i + u3 i)
    exact vecNorm_smul_nonneg (1 / 4) (by norm_num) _
  rw [hscale]
  nlinarith

/-- Evaluations on the six Motzkin zero directions control a homogeneous
linear polynomial vector. -/
theorem linear_unisolvence
    {N : ℕ} (H : Fin N → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ i, homogeneousPart3 1 (H i) = H i)
    {B : ℝ}
    (hEval : ∀ z : Fin 6,
      interiorVecNorm (fun i : Fin N => eval (motzkinZeroDirection z) (H i)) ≤ B) :
    motzkinVecCoeffNorm H ≤ 5 * B := by
  have hc0 : interiorVecNorm
      (fun i : Fin N => coeff (Finsupp.single (0 : Fin 3) 1) (H i)) ≤ B := by
    have heq :
        (fun i : Fin N => coeff (Finsupp.single (0 : Fin 3) 1) (H i)) =
          fun i : Fin N => eval (motzkinZeroDirection 0) (H i) := by
      funext i
      have h := eval_linear_eq_sum_coeff (hhom i) (motzkinZeroDirection 0)
      simp [motzkinZeroDirection, motzkinAxisX, Fin.sum_univ_three] at h
      change coeff (Finsupp.single (0 : Fin 3) 1) (H i) = eval motzkinAxisX (H i)
      simpa [coeff, motzkinAxisX] using h.symm
    rw [heq]
    exact hEval 0
  have hc1 : interiorVecNorm
      (fun i : Fin N => coeff (Finsupp.single (1 : Fin 3) 1) (H i)) ≤ B := by
    have heq :
        (fun i : Fin N => coeff (Finsupp.single (1 : Fin 3) 1) (H i)) =
          fun i : Fin N => eval (motzkinZeroDirection 1) (H i) := by
      funext i
      have h := eval_linear_eq_sum_coeff (hhom i) (motzkinZeroDirection 1)
      simp [motzkinZeroDirection, motzkinAxisY, Fin.sum_univ_three] at h
      change coeff (Finsupp.single (1 : Fin 3) 1) (H i) = eval motzkinAxisY (H i)
      simpa [coeff, motzkinAxisY] using h.symm
    rw [heq]
    exact hEval 1
  have hzEq :
      (fun i : Fin N => coeff (Finsupp.single (2 : Fin 3) 1) (H i)) =
        fun i : Fin N =>
          eval (motzkinZeroDirection 2) (H i) -
            coeff (Finsupp.single (0 : Fin 3) 1) (H i) -
            coeff (Finsupp.single (1 : Fin 3) 1) (H i) := by
    funext i
    have h := eval_linear_eq_sum_coeff (hhom i) (motzkinZeroDirection 2)
    simp [motzkinZeroDirection, motzkinSignDirection, Fin.sum_univ_three] at h
    change coeff (Finsupp.single (2 : Fin 3) 1) (H i) =
      eval (motzkinSignDirection 0 0) (H i) -
        coeff (Finsupp.single (0 : Fin 3) 1) (H i) -
        coeff (Finsupp.single (1 : Fin 3) 1) (H i)
    linarith
  have hc2 : interiorVecNorm
      (fun i : Fin N => coeff (Finsupp.single (2 : Fin 3) 1) (H i)) ≤ 3 * B := by
    rw [hzEq]
    calc
      interiorVecNorm (fun i : Fin N =>
          eval (motzkinZeroDirection 2) (H i) -
            coeff (Finsupp.single (0 : Fin 3) 1) (H i) -
            coeff (Finsupp.single (1 : Fin 3) 1) (H i)) ≤
          interiorVecNorm (fun i : Fin N =>
            eval (motzkinZeroDirection 2) (H i) -
              coeff (Finsupp.single (0 : Fin 3) 1) (H i)) +
          interiorVecNorm
            (fun i : Fin N => coeff (Finsupp.single (1 : Fin 3) 1) (H i)) := by
        simpa using interiorVecNorm_sub_le
          (fun i : Fin N =>
            eval (motzkinZeroDirection 2) (H i) -
              coeff (Finsupp.single (0 : Fin 3) 1) (H i))
          (fun i : Fin N => coeff (Finsupp.single (1 : Fin 3) 1) (H i))
      _ ≤ (interiorVecNorm
            (fun i : Fin N => eval (motzkinZeroDirection 2) (H i)) +
          interiorVecNorm
            (fun i : Fin N => coeff (Finsupp.single (0 : Fin 3) 1) (H i))) +
          interiorVecNorm
            (fun i : Fin N => coeff (Finsupp.single (1 : Fin 3) 1) (H i)) := by
        gcongr
        exact interiorVecNorm_sub_le _ _
      _ ≤ 3 * B := by nlinarith [hEval 2]
  calc
    motzkinVecCoeffNorm H ≤
        ∑ j : Fin 3, interiorVecNorm
          (fun i : Fin N => coeff (Finsupp.single j 1) (H i)) :=
      motzkinVecCoeffNorm_linear_le_sum_coeff_vectors H hhom
    _ = interiorVecNorm
          (fun i : Fin N => coeff (Finsupp.single (0 : Fin 3) 1) (H i)) +
        interiorVecNorm
          (fun i : Fin N => coeff (Finsupp.single (1 : Fin 3) 1) (H i)) +
        interiorVecNorm
          (fun i : Fin N => coeff (Finsupp.single (2 : Fin 3) 1) (H i)) := by
      rw [Fin.sum_univ_three]
    _ ≤ 5 * B := by nlinarith



@[simp] private lemma qsingle_one_add_self (i : Fin 3) :
    Finsupp.single i 1 + Finsupp.single i 1 = Finsupp.single i 2 := by
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

/-- Evaluations on the six Motzkin zero directions control a homogeneous
quadratic polynomial vector. -/
theorem quadratic_unisolvence
    {N : ℕ} (H : Fin N → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ i, homogeneousPart3 2 (H i) = H i)
    {B : ℝ}
    (hEval : ∀ z : Fin 6,
      interiorVecNorm (fun i : Fin N => eval (motzkinZeroDirection z) (H i)) ≤ B) :
    motzkinVecCoeffNorm H ≤ 100 * B := by
  let V : Fin 6 → Fin N → ℝ :=
    fun z i => eval (motzkinZeroDirection z) (H i)
  let A : Fin N → ℝ := fun i => coeff (Finsupp.single (0 : Fin 3) 2) (H i)
  let D : Fin N → ℝ := fun i => coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single 1 1) (H i)
  let E : Fin N → ℝ := fun i => coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single 2 1) (H i)
  let C : Fin N → ℝ := fun i => coeff (Finsupp.single (2 : Fin 3) 2) (H i)
  let F : Fin N → ℝ := fun i => coeff (Finsupp.single (1 : Fin 3) 1 + Finsupp.single 2 1) (H i)
  let Y : Fin N → ℝ := fun i => coeff (Finsupp.single (1 : Fin 3) 2) (H i)
  have hB : 0 ≤ B := (interiorVecNorm_nonneg (V 0)).trans (hEval 0)
  have hforms (i : Fin N) :
      V 2 i = A i + D i + E i + Y i + F i + C i ∧
      V 3 i = A i + D i - E i + Y i - F i + C i ∧
      V 4 i = A i - D i + E i + Y i - F i + C i ∧
      V 5 i = A i - D i - E i + Y i + F i + C i := by
    have h2 := eval_quadratic_eq_coeffs (hhom i) (motzkinZeroDirection 2)
    have h3 := eval_quadratic_eq_coeffs (hhom i) (motzkinZeroDirection 3)
    have h4 := eval_quadratic_eq_coeffs (hhom i) (motzkinZeroDirection 4)
    have h5 := eval_quadratic_eq_coeffs (hhom i) (motzkinZeroDirection 5)
    exact ⟨
      by simpa [V, A, D, E, C, F, Y, motzkinZeroDirection, motzkinSignDirection] using h2,
      by simpa [coeff, V, A, D, E, C, F, Y, sub_eq_add_neg, motzkinZeroDirection, motzkinSignDirection] using h3,
      by simpa [coeff, V, A, D, E, C, F, Y, sub_eq_add_neg, motzkinZeroDirection, motzkinSignDirection] using h4,
      by simpa [coeff, V, A, D, E, C, F, Y, sub_eq_add_neg, motzkinZeroDirection, motzkinSignDirection] using h5⟩
  have hAeq : A = V 0 := by
    funext i
    have h := eval_quadratic_eq_coeffs (hhom i) (motzkinZeroDirection 0)
    simpa [A, V, motzkinZeroDirection, motzkinAxisX] using h.symm
  have hYeq : Y = V 1 := by
    funext i
    have h := eval_quadratic_eq_coeffs (hhom i) (motzkinZeroDirection 1)
    simpa [Y, V, motzkinZeroDirection, motzkinAxisY] using h.symm
  have hCeq : C = fun i => (V 2 i + V 3 i + V 4 i + V 5 i) / 4 - A i - Y i := by
    funext i
    rcases hforms i with ⟨h2, h3, h4, h5⟩
    dsimp [C]
    linarith
  have hDeq : D = fun i => (V 2 i + V 3 i - V 4 i - V 5 i) / 4 := by
    funext i
    rcases hforms i with ⟨h2, h3, h4, h5⟩
    dsimp [D]
    linarith
  have hEeq : E = fun i => (V 2 i - V 3 i + V 4 i - V 5 i) / 4 := by
    funext i
    rcases hforms i with ⟨h2, h3, h4, h5⟩
    dsimp [E]
    linarith
  have hFeq : F = fun i => (V 2 i - V 3 i - V 4 i + V 5 i) / 4 := by
    funext i
    rcases hforms i with ⟨h2, h3, h4, h5⟩
    dsimp [F]
    linarith
  have hV (z : Fin 6) : interiorVecNorm (V z) ≤ B := hEval z
  have hA : interiorVecNorm A ≤ B := by rw [hAeq]; exact hV 0
  have hY : interiorVecNorm Y ≤ B := by rw [hYeq]; exact hV 1
  have hD : interiorVecNorm D ≤ B := by
    rw [hDeq]
    exact interiorVecNorm_average_four_le (V 2) (V 3)
      (fun i => -V 4 i) (fun i => -V 5 i) (hV 2) (hV 3)
      (by simpa using (interiorVecNorm_neg (V 4)).trans_le (hV 4))
      (by simpa using (interiorVecNorm_neg (V 5)).trans_le (hV 5))
  have hE : interiorVecNorm E ≤ B := by
    rw [hEeq]
    exact interiorVecNorm_average_four_le (V 2) (fun i => -V 3 i)
      (V 4) (fun i => -V 5 i) (hV 2)
      (by simpa using (interiorVecNorm_neg (V 3)).trans_le (hV 3))
      (hV 4) (by simpa using (interiorVecNorm_neg (V 5)).trans_le (hV 5))
  have hF : interiorVecNorm F ≤ B := by
    rw [hFeq]
    exact interiorVecNorm_average_four_le (V 2) (fun i => -V 3 i)
      (fun i => -V 4 i) (V 5) (hV 2)
      (by simpa using (interiorVecNorm_neg (V 3)).trans_le (hV 3))
      (by simpa using (interiorVecNorm_neg (V 4)).trans_le (hV 4)) (hV 5)
  have hC : interiorVecNorm C ≤ 3 * B := by
    rw [hCeq]
    calc
      interiorVecNorm (fun i => (V 2 i + V 3 i + V 4 i + V 5 i) / 4 - A i - Y i) ≤
          interiorVecNorm
            (fun i => (V 2 i + V 3 i + V 4 i + V 5 i) / 4 - A i) +
          interiorVecNorm Y := by
        simpa using interiorVecNorm_sub_le
          (fun i => (V 2 i + V 3 i + V 4 i + V 5 i) / 4 - A i) Y
      _ ≤ (interiorVecNorm
              (fun i => (V 2 i + V 3 i + V 4 i + V 5 i) / 4) +
            interiorVecNorm A) + interiorVecNorm Y := by
        gcongr
        exact interiorVecNorm_sub_le _ _
      _ ≤ 3 * B := by
        have havg := interiorVecNorm_average_four_le
          (V 2) (V 3) (V 4) (V 5) (hV 2) (hV 3) (hV 4) (hV 5)
        linarith
  have hA3 : interiorVecNorm A ≤ 3 * B := hA.trans (by linarith)
  have hD3 : interiorVecNorm D ≤ 3 * B := hD.trans (by linarith)
  have hE3 : interiorVecNorm E ≤ 3 * B := hE.trans (by linarith)
  have hY3 : interiorVecNorm Y ≤ 3 * B := hY.trans (by linarith)
  have hF3 : interiorVecNorm F ≤ 3 * B := hF.trans (by linarith)
  have hD01 : interiorVecNorm (fun i : Fin N =>
      coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single 1 1) (H i)) ≤ 3 * B := by
    change interiorVecNorm D ≤ 3 * B
    exact hD3
  have hD10 : interiorVecNorm (fun i : Fin N =>
      coeff (Finsupp.single (1 : Fin 3) 1 + Finsupp.single 0 1) (H i)) ≤ 3 * B := by
    simpa [add_comm] using hD01
  have hE02 : interiorVecNorm (fun i : Fin N =>
      coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single 2 1) (H i)) ≤ 3 * B := by
    change interiorVecNorm E ≤ 3 * B
    exact hE3
  have hE20 : interiorVecNorm (fun i : Fin N =>
      coeff (Finsupp.single (2 : Fin 3) 1 + Finsupp.single 0 1) (H i)) ≤ 3 * B := by
    simpa [add_comm] using hE02
  have hF12 : interiorVecNorm (fun i : Fin N =>
      coeff (Finsupp.single (1 : Fin 3) 1 + Finsupp.single 2 1) (H i)) ≤ 3 * B := by
    change interiorVecNorm F ≤ 3 * B
    exact hF3
  have hF21 : interiorVecNorm (fun i : Fin N =>
      coeff (Finsupp.single (2 : Fin 3) 1 + Finsupp.single 1 1) (H i)) ≤ 3 * B := by
    simpa [add_comm] using hF12
  have hordered (ab : Fin 3 × Fin 3) :
      interiorVecNorm (fun i : Fin N =>
        coeff (Finsupp.single ab.1 1 + Finsupp.single ab.2 1) (H i)) ≤ 3 * B := by
    rcases ab with ⟨a, b⟩
    fin_cases a <;> fin_cases b
    all_goals first
      | simpa [A, qsingle_one_add_self] using hA3
      | exact hD01
      | exact hE02
      | exact hD10
      | simpa [Y, qsingle_one_add_self] using hY3
      | exact hF12
      | exact hE20
      | exact hF21
      | simpa [C, qsingle_one_add_self] using hC
  calc
    motzkinVecCoeffNorm H ≤
        ∑ ab : Fin 3 × Fin 3, interiorVecNorm (fun i : Fin N =>
          coeff (Finsupp.single ab.1 1 + Finsupp.single ab.2 1) (H i)) :=
      motzkinVecCoeffNorm_quadratic_le_ordered_sum_coeff_vectors H hhom
    _ ≤ ∑ _ab : Fin 3 × Fin 3, 3 * B :=
      Finset.sum_le_sum (fun ab _ => hordered ab)
    _ = 27 * B := by simp; ring
    _ ≤ 100 * B := by nlinarith


end Motzkin

end OptimalConvergenceRates

end
