/- Schmuedgen degree lower bound for the perturbed Motzkin sextic. -/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.Constants

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

private theorem sqrt_mul_pow_three_le_of_sixth
    {epsilon c : ℝ} {r : ℕ}
    (heps : 0 < epsilon)
    (hsmall : (r : ℝ) ≤ c * epsilon ^ (-(1 : ℝ) / 6)) :
    Real.sqrt epsilon * (r : ℝ) ^ 3 ≤ c ^ 3 := by
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hpow := Real.rpow_le_rpow hr0 hsmall (by norm_num : (0 : ℝ) ≤ 3)
  have hpow' : (r : ℝ) ^ 3 ≤ (c * epsilon ^ (-(1 : ℝ) / 6)) ^ 3 := by
    simpa using hpow
  have hright : (c * epsilon ^ (-(1 : ℝ) / 6)) ^ 3 =
      c ^ 3 * epsilon ^ (-(1 : ℝ) / 2) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul heps.le]
    norm_num
  rw [hright] at hpow'
  rw [Real.sqrt_eq_rpow]
  calc
    epsilon ^ ((1 : ℝ) / 2) * (r : ℝ) ^ 3
        ≤ epsilon ^ ((1 : ℝ) / 2) *
            (c ^ 3 * epsilon ^ (-(1 : ℝ) / 2)) := by
          exact mul_le_mul_of_nonneg_left hpow'
            (Real.rpow_nonneg heps.le _)
    _ = c ^ 3 := by
      rw [show epsilon ^ ((1 : ℝ) / 2) *
          (c ^ 3 * epsilon ^ (-(1 : ℝ) / 2)) =
        c ^ 3 * (epsilon ^ ((1 : ℝ) / 2) *
          epsilon ^ (-(1 : ℝ) / 2)) by ring]
      rw [← Real.rpow_add heps]
      norm_num

private theorem motzkinPerturbed_totalDegree_ge_six
    (epsilon : ℝ) :
    6 ≤ (motzkinPerturbed epsilon).totalDegree := by
  have hMne : motzkinSextic ≠ 0 := by
    intro hzero
    let z : Fin 3 → ℝ := fun i ↦ if i = 2 then 1 else 0
    have heval : MvPolynomial.eval z motzkinSextic = 1 := by
      rw [motzkinSextic_eval]
      simp [z]
    rw [hzero, map_zero] at heval
    norm_num at heval
  by_contra hnot
  have hzero :
      MvPolynomial.homogeneousComponent 6 (motzkinPerturbed epsilon) = 0 :=
    MvPolynomial.homogeneousComponent_eq_zero 6 (motzkinPerturbed epsilon) (by omega)
  have hpart := homogeneousPart3_motzkinPerturbed epsilon
  rw [homogeneousPart3_eq_homogeneousComponent, hzero] at hpart
  exact hMne hpart.symm

private theorem motzkin_certificate_degree_ge_two
    {epsilon : ℝ} {r : ℕ}
    (hmem : motzkinPerturbed epsilon ∈ BoxPreordering 3 r) :
    2 ≤ r := by
  obtain ⟨sigma, _hsos, hdeg, hsum⟩ := hmem
  have htotal : (motzkinPerturbed epsilon).totalDegree ≤ r := by
    rw [hsum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro J _
    exact hdeg J
  have hge := motzkinPerturbed_totalDegree_ge_six epsilon
  omega

private theorem motzkin_sixth_root_facts
    {epsilon : ℝ} (heps : 0 < epsilon)
    (heps0 : epsilon ≤ motzkinEpsilon0) :
    let rho := epsilon ^ ((1 : ℝ) / 6)
    0 < rho ∧ rho ≤ 1 ∧
      Real.sqrt epsilon = rho ^ 3 ∧
      rho < schmInteriorS / 2 := by
  let rho := epsilon ^ ((1 : ℝ) / 6)
  have hrho : 0 < rho := Real.rpow_pos_of_pos heps _
  have hsqrt : Real.sqrt epsilon = rho ^ 3 := by
    rw [Real.sqrt_eq_rpow]
    dsimp [rho]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul heps.le]
    norm_num
  have hrho16 : rho ≤ 1 / 16 := by
    have hpow := Real.rpow_le_rpow heps.le heps0
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 6)
    dsimp [motzkinEpsilon0] at hpow
    calc
      rho ≤ ((1 / 16 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) := hpow
      _ = 1 / 16 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 16)]
        norm_num
  refine ⟨hrho, hrho16.trans (by norm_num), hsqrt, ?_⟩
  norm_num [schmInteriorS] at hrho16 ⊢
  linarith

private theorem motzkin_r_mul_sixth_root_le
    {epsilon : ℝ} {r : ℕ} (heps : 0 < epsilon)
    (hsmall : (r : ℝ) ≤
      motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6)) :
    (r : ℝ) * epsilon ^ ((1 : ℝ) / 6) ≤ 1 / 8 := by
  have hrho : 0 ≤ epsilon ^ ((1 : ℝ) / 6) := Real.rpow_nonneg heps.le _
  have hcancel :
      epsilon ^ (-(1 : ℝ) / 6) * epsilon ^ ((1 : ℝ) / 6) = 1 := by
    rw [← Real.rpow_add heps]
    norm_num
  calc
    (r : ℝ) * epsilon ^ ((1 : ℝ) / 6) ≤
        (motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6)) *
          epsilon ^ ((1 : ℝ) / 6) :=
      mul_le_mul_of_nonneg_right hsmall hrho
    _ = motzkinLowerBoundConst := by rw [mul_assoc, hcancel, mul_one]
    _ ≤ 1 / 8 := motzkinLowerBoundConst_le_eighth

private theorem motzkin_error_lt_distance
    {epsilon : ℝ} {r : ℕ} (heps : 0 < epsilon)
    (hsmall : (r : ℝ) ≤
      motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6)) :
    motzkinJetErrorConst * (r : ℝ) ^ 3 * Real.sqrt epsilon <
      motzkinSosDistance := by
  have hscale : Real.sqrt epsilon * (r : ℝ) ^ 3 ≤
      motzkinLowerBoundConst ^ 3 :=
    sqrt_mul_pow_three_le_of_sixth heps hsmall
  have herror :
      motzkinJetErrorConst * (Real.sqrt epsilon * (r : ℝ) ^ 3) ≤
        motzkinJetErrorConst * motzkinLowerBoundConst ^ 3 :=
    mul_le_mul_of_nonneg_left hscale motzkinJetErrorConst_pos.le
  have hhalf :
      motzkinJetErrorConst * motzkinLowerBoundConst ^ 3 ≤
        motzkinSosDistance / 2 := by
    calc
      motzkinJetErrorConst * motzkinLowerBoundConst ^ 3 ≤
          motzkinJetErrorConst *
            (motzkinSosDistance / (2 * motzkinJetErrorConst)) :=
        mul_le_mul_of_nonneg_left motzkinLowerBoundConst_cube_le_distance
          motzkinJetErrorConst_pos.le
      _ = motzkinSosDistance / 2 := by
        field_simp [motzkinJetErrorConst_pos.ne']
  calc
    motzkinJetErrorConst * (r : ℝ) ^ 3 * Real.sqrt epsilon =
        motzkinJetErrorConst * (Real.sqrt epsilon * (r : ℝ) ^ 3) := by ring
    _ ≤ motzkinJetErrorConst * motzkinLowerBoundConst ^ 3 := herror
    _ ≤ motzkinSosDistance / 2 := hhalf
    _ < motzkinSosDistance := by nlinarith [motzkinSosDistance_pos]

theorem box_preordering_motzkin_too_close_sixth
    {epsilon : ℝ} {r : ℕ}
    (heps : 0 < epsilon) (heps0 : epsilon ≤ motzkinEpsilon0)
    (hsmall : (r : ℝ) ≤
      motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6))
    (hmem : motzkinPerturbed epsilon ∈ BoxPreordering 3 r) :
    False := by
  classical
  have hr2 : 2 ≤ r := motzkin_certificate_degree_ge_two hmem
  let rho := epsilon ^ ((1 : ℝ) / 6)
  obtain ⟨hrho, hrhoOne, hsqrt, hrhoSmall⟩ :=
    motzkin_sixth_root_facts heps heps0
  have hrSmall : (r : ℝ) * rho ≤ 1 / 8 := by
    exact motzkin_r_mul_sixth_root_le heps hsmall
  obtain ⟨sigma, hroots, _hweightedDegree, hsum⟩ :=
    box_preordering_certificate_sos_vectors_cubic_with_degree heps.le hmem
  let N : Finset (Fin 3) → ℕ := fun J ↦ (hroots J).choose
  let Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ :=
    fun J ↦ (hroots J).choose_spec.choose
  have hQ (J : Finset (Fin 3)) :
      sigma J = sosVectorSq3 (Q J) ∧
      (∀ i, (Q J i).totalDegree ≤ r) ∧
      (∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
        ∀ t : ℝ, |t| ≤ schmInteriorS →
          interiorVecNorm (fun i : Fin (N J) =>
            MvPolynomial.eval (fun j ↦ t * v j) (Q J i)) ≤
            schmInteriorLocalControlConst * (Real.sqrt epsilon + |t| ^ 3)) ∧
      (∀ zi : Fin 6, ∀ t : ℝ, |t| ≤ schmInteriorS →
        interiorVecNorm (fun i : Fin (N J) =>
          MvPolynomial.eval (fun j ↦ t * motzkinZeroDirection zi j) (Q J i)) ≤
          schmInteriorLocalControlConst * Real.sqrt epsilon) :=
    (hroots J).choose_spec.choose_spec
  have herrRaw := motzkinDegreeSixError_coeffNorm_le hr2 heps hrho hrhoOne
    hsqrt hrhoSmall hrSmall Q sigma (fun J ↦ (hQ J).1) hsum
    (fun J ↦ (hQ J).2.1) (fun J ↦ (hQ J).2.2.1)
    (fun J ↦ (hQ J).2.2.2)
  have herr :
      motzkinCoeffNorm (motzkinDegreeSixError Q) ≤
        motzkinJetErrorConst * (r : ℝ) ^ 3 * Real.sqrt epsilon := by
    calc
      motzkinCoeffNorm (motzkinDegreeSixError Q) ≤
          motzkinDegreeSixNormConst *
            (27 * (2352 * motzkinPairErrorBound r epsilon)) := herrRaw
      _ = motzkinJetErrorConst * (r : ℝ) ^ 3 * Real.sqrt epsilon := by
        unfold motzkinJetErrorConst motzkinPairErrorBound
        ring
  have hS : Nonempty (DegreeBoundedSOS (motzkinCubicJetSOS Q) 3) :=
    motzkinCubicJetSOS_degreeBounded Q
  have hdistance := motzkinSosDistance_le hS
  have hdistanceError :
      motzkinSosDistance ≤ motzkinCoeffNorm (motzkinDegreeSixError Q) := by
    simpa [coeffL1Distance, motzkinCoeffNorm, motzkinDegreeSixError] using hdistance
  exact (not_lt_of_ge (hdistanceError.trans herr))
    (motzkin_error_lt_distance heps hsmall)

/-- Every sufficiently small positive perturbation requires degree
of order epsilon^(-1/6) in the ternary box preordering. -/
theorem schmuedgen_motzkin_lower_degree_bound_sixth
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ motzkinEpsilon0) (r : ℕ)
    (hmem : motzkinPerturbed epsilon ∈ BoxPreordering 3 r) :
    motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6) ≤ (r : ℝ) := by
  by_contra hcontra
  push Not at hcontra
  exact box_preordering_motzkin_too_close_sixth heps heps0
    (le_of_lt hcontra) hmem

theorem schmuedgen_motzkin_lower_degree_bound_sixth_contra
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ motzkinEpsilon0) (r : ℕ)
    (hr : (r : ℝ) <
      motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6)) :
    motzkinPerturbed epsilon ∉ BoxPreordering 3 r := by
  intro hmem
  have hle := schmuedgen_motzkin_lower_degree_bound_sixth
    epsilon heps heps0 r hmem
  linarith

end Motzkin

end OptimalConvergenceRates

end
