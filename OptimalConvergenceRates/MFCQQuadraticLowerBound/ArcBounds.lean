/-
  Uniform control of the extracted SOS roots on the three parabolic arcs.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.ArcRestrictions
import OptimalConvergenceRates.MFCQQuadraticLowerBound.WeightedMarkov

noncomputable section

open Finset MvPolynomial Polynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

variable {epsilon : ℝ} {r : ℕ}

/-- The perturbation in any certificate is nonnegative, by evaluation at
the common active point. -/
theorem ExtractedCertificate.epsilon_nonneg
    (certificate : ExtractedCertificate epsilon r) : 0 ≤ epsilon := by
  have hidentity := congrArg (MvPolynomial.eval origin) certificate.identity
  simp only [map_add, map_sum, map_mul, map_pow, map_zero, map_one,
    MvPolynomial.eval_C] at hidentity
  simp [objective, generators, ball, q₁, q₂, q₃, q₄, u, v, t,
    origin, Fin.sum_univ_five] at hidentity
  have hzero : 0 ≤ MvPolynomial.eval origin certificate.sigmaZero :=
    IsSOS_nonneg _ certificate.sosZero _ (Set.mem_univ _)
  have hball : 0 ≤ MvPolynomial.eval origin (certificate.sigma 4) :=
    IsSOS_nonneg _ (certificate.sos 4) _ (Set.mem_univ _)
  linarith

/-- The extracted root vector on one scaled arc. -/
def arcRootPolynomials (certificate : ExtractedCertificate epsilon r)
    (j : Fin 3) : Fin certificate.rootCount → Polynomial ℝ :=
  fun i ↦ restrictScaledArc j (certificate.roots i)

theorem arcRootPolynomials_natDegree_le
    (certificate : ExtractedCertificate epsilon r) (j : Fin 3) (i) :
    (arcRootPolynomials certificate j i).natDegree ≤ 2 * r := by
  exact (restrictScaledArc_natDegree_le j (certificate.roots i)).trans
    (Nat.mul_le_mul_left 2 (certificate.rootDegree i))

/-- On every scaled arc, the squared root norm is at most twice the
objective perturbation. -/
theorem arcRootPolynomials_sqNorm_le
    (certificate : ExtractedCertificate epsilon r) (j : Fin 3)
    {s : ℝ} (hs : |s| ≤ 1) :
    interiorVecSqNorm
        (fun i ↦ (arcRootPolynomials certificate j i).eval s) ≤
      2 * (s ^ 2 / 4 + epsilon) := by
  let z := scaledArcPoint j s
  have hsigma (i : Fin 5) :
      0 ≤ MvPolynomial.eval z (certificate.sigma i) :=
    IsSOS_nonneg _ (certificate.sos i) _ (Set.mem_univ _)
  have hgen (i : Fin 5) : 0 ≤ MvPolynomial.eval z (generators i) :=
    scaledArc_generators_nonneg j i hs
  have hterm (i : Fin 5) :
      0 ≤ MvPolynomial.eval z (certificate.sigma i) *
        MvPolynomial.eval z (generators i) :=
    mul_nonneg (hsigma i) (hgen i)
  have hzero : 0 ≤ MvPolynomial.eval z certificate.sigmaZero :=
    IsSOS_nonneg _ certificate.sosZero _ (Set.mem_univ _)
  have hball := scaledArc_ball_ge_half j hs
  have hballTerm :
      (1 / 2 : ℝ) * MvPolynomial.eval z (certificate.sigma 4) ≤
        MvPolynomial.eval z (certificate.sigma 4) *
          MvPolynomial.eval z ball := by
    nlinarith [mul_le_mul_of_nonneg_left hball (hsigma 4)]
  have hobjective : MvPolynomial.eval z objective = s ^ 2 / 4 := by
    rw [← restrictScaledArc_eval]
    simp [restrictScaledArc_objective]
    ring
  have hidentity := congrArg (MvPolynomial.eval z) certificate.identity
  simp only [map_add, map_sum, map_mul, MvPolynomial.eval_C] at hidentity
  rw [hobjective] at hidentity
  rw [Fin.sum_univ_five] at hidentity
  have hroot := congrArg (MvPolynomial.eval z) certificate.rootDecomp
  simp only [map_add, map_sum, map_pow] at hroot
  unfold interiorVecSqNorm arcRootPolynomials
  simp_rw [restrictScaledArc_eval]
  rw [← hroot]
  change
    MvPolynomial.eval z certificate.sigmaZero +
        MvPolynomial.eval z (certificate.sigma 4) ≤
      2 * (s ^ 2 / 4 + epsilon)
  have hterm4 :
      MvPolynomial.eval z (certificate.sigma 4) *
          MvPolynomial.eval z (generators 4) =
        MvPolynomial.eval z (certificate.sigma 4) *
          MvPolynomial.eval z ball := by
    simp [generators]
  rw [hterm4] at hidentity
  nlinarith [hterm 0, hterm 1, hterm 2, hterm 3]

/-- Rationalized form of the root-amplitude estimate used in the weighted
Markov lemma. -/
theorem arcRootPolynomials_norm_le
    (certificate : ExtractedCertificate epsilon r) (j : Fin 3)
    {s : ℝ} (hs : |s| ≤ 1) :
    interiorVecNorm
        (fun i ↦ (arcRootPolynomials certificate j i).eval s) ≤
      (3 / 4 : ℝ) * |s| + (3 / 2 : ℝ) * Real.sqrt epsilon := by
  have hepsilon := certificate.epsilon_nonneg
  have hsq := arcRootPolynomials_sqNorm_le certificate j hs
  let B : ℝ := (3 / 4 : ℝ) * |s| + (3 / 2 : ℝ) * Real.sqrt epsilon
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsqrt : (Real.sqrt epsilon) ^ 2 = epsilon := Real.sq_sqrt hepsilon
  have habs : |s| ^ 2 = s ^ 2 := sq_abs s
  have hsqB :
      interiorVecSqNorm
          (fun i ↦ (arcRootPolynomials certificate j i).eval s) ≤ B ^ 2 := by
    dsimp [B]
    nlinarith [mul_nonneg (abs_nonneg s) (Real.sqrt_nonneg epsilon)]
  simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm, B] using
    (vecNorm_le_of_vecSqNorm_le hB (by
      simpa [vecSqNorm, interiorVecSqNorm] using hsqB))

/-- Dimension-free second-derivative bound for the root vector on any one
of the three scaled arcs. -/
theorem arcRootPolynomials_secondDerivative_le
    (certificate : ExtractedCertificate epsilon r) (hr : 1 ≤ r)
    (j : Fin 3) :
    interiorVecNorm (fun i ↦
        (derivative (derivative (arcRootPolynomials certificate j i))).eval 0) ≤
      9 * (r : ℝ) + 72 * (r : ℝ) ^ 2 * Real.sqrt epsilon := by
  have hD : 2 ≤ 2 * r := by omega
  have hepsilon := certificate.epsilon_nonneg
  have hmarkov := secondDerivative_of_linear_growth
    (D := 2 * r) hD (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg epsilon))
    (arcRootPolynomials certificate j)
    (arcRootPolynomials_natDegree_le certificate j)
    (fun s hs ↦ arcRootPolynomials_norm_le certificate j hs)
  convert hmarkov using 1 <;> push_cast <;> ring

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
