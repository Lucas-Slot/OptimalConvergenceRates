/-
  Exact order-two coefficient identities behind the local SOS obstruction.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.ArcBounds

noncomputable section

open Finset MvPolynomial Polynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

variable {epsilon : ℝ} {r : ℕ}

def rootValueVector (certificate : ExtractedCertificate epsilon r) :
    Fin certificate.rootCount → ℝ :=
  fun i ↦ MvPolynomial.eval origin (certificate.roots i)

def rootCoeffOneVector (certificate : ExtractedCertificate epsilon r)
    (j : Fin 3) : Fin certificate.rootCount → ℝ :=
  fun i ↦ (arcRootPolynomials certificate j i).coeff 1

def rootCoeffTwoVector (certificate : ExtractedCertificate epsilon r)
    (j : Fin 3) : Fin certificate.rootCount → ℝ :=
  fun i ↦ (arcRootPolynomials certificate j i).coeff 2

def activeMultiplierSum (certificate : ExtractedCertificate epsilon r) : ℝ :=
  ∑ i : Fin 4, MvPolynomial.eval origin (certificate.sigma i.castSucc)

theorem certificate_value_at_origin
    (certificate : ExtractedCertificate epsilon r) :
    epsilon = MvPolynomial.eval origin certificate.sigmaZero +
      MvPolynomial.eval origin (certificate.sigma 4) := by
  have hidentity := congrArg (MvPolynomial.eval origin) certificate.identity
  simp only [map_add, map_sum, map_mul, MvPolynomial.eval_C] at hidentity
  simpa [objective, generators, ball, q₁, q₂, q₃, q₄, u, v, t,
    origin, Fin.sum_univ_five] using hidentity

theorem rootValue_sqNorm_eq
    (certificate : ExtractedCertificate epsilon r) :
    interiorVecSqNorm (rootValueVector certificate) = epsilon := by
  have hroot := congrArg (MvPolynomial.eval origin) certificate.rootDecomp
  simp only [map_add, map_sum, map_pow] at hroot
  unfold interiorVecSqNorm rootValueVector
  rw [← hroot]
  exact (certificate_value_at_origin certificate).symm

theorem rootValue_norm_eq
    (certificate : ExtractedCertificate epsilon r) :
    interiorVecNorm (rootValueVector certificate) = Real.sqrt epsilon := by
  unfold interiorVecNorm
  rw [rootValue_sqNorm_eq]

theorem ballMultiplier_value_le
    (certificate : ExtractedCertificate epsilon r) :
    MvPolynomial.eval origin (certificate.sigma 4) ≤ epsilon := by
  have hzero : 0 ≤ MvPolynomial.eval origin certificate.sigmaZero :=
    IsSOS_nonneg _ certificate.sosZero _ (Set.mem_univ _)
  calc
    MvPolynomial.eval origin (certificate.sigma 4) ≤
        MvPolynomial.eval origin certificate.sigmaZero +
          MvPolynomial.eval origin (certificate.sigma 4) := by linarith
    _ = epsilon := (certificate_value_at_origin certificate).symm

/-- Coefficient two of the restricted certificate, before specializing
the three fixed arc coefficient tables. -/
theorem restricted_certificate_coeff_two
    (certificate : ExtractedCertificate epsilon r) (j : Fin 3) :
    (1 / 4 : ℝ) =
      (restrictScaledArc j certificate.sigmaZero).coeff 2 +
        ∑ i : Fin 5,
          ((restrictScaledArc j (certificate.sigma i)).coeff 0 *
              arcGeneratorCoeffTwo j i +
            if i = 4 then
              (restrictScaledArc j (certificate.sigma i)).coeff 2
            else 0) := by
  have hidentity := congrArg
    (fun p : MvPolynomial (Fin 3) ℝ ↦ (restrictScaledArc j p).coeff 2)
    certificate.identity
  simp only [restrictScaledArc, map_add, map_sum, map_mul,
    MvPolynomial.aeval_C, Polynomial.coeff_add, Polynomial.finsetSum_coeff] at hidentity
  change
    (restrictScaledArc j objective).coeff 2 + (Polynomial.C epsilon).coeff 2 =
      (restrictScaledArc j certificate.sigmaZero).coeff 2 +
        ∑ b : Fin 5,
          (restrictScaledArc j (certificate.sigma b) *
            restrictScaledArc j (generators b)).coeff 2 at hidentity
  simp_rw [coeff_two_mul] at hidentity
  simp only [restrictScaledArc_generator_coeff_zero,
    restrictScaledArc_generator_coeff_one,
    restrictScaledArc_generator_coeff_two, mul_zero, add_zero] at hidentity
  simpa [restrictScaledArc_objective, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hidentity

/-- Coefficient two of the two surviving SOS terms, expressed through the
root-vector coefficients. -/
theorem root_sum_coeff_two
    (certificate : ExtractedCertificate epsilon r) (j : Fin 3) :
    (restrictScaledArc j
        (certificate.sigmaZero + certificate.sigma 4)).coeff 2 =
      2 * vecDot (rootValueVector certificate)
          (rootCoeffTwoVector certificate j) +
        interiorVecSqNorm (rootCoeffOneVector certificate j) := by
  have hroot := congrArg
    (fun p : MvPolynomial (Fin 3) ℝ ↦ (restrictScaledArc j p).coeff 2)
    certificate.rootDecomp
  simp only [restrictScaledArc, map_add, map_sum, map_pow,
    Polynomial.coeff_add, Polynomial.finsetSum_coeff] at hroot
  simp_rw [pow_two, coeff_two_mul] at hroot
  change
    (restrictScaledArc j certificate.sigmaZero).coeff 2 +
        (restrictScaledArc j (certificate.sigma 4)).coeff 2 =
      ∑ i : Fin certificate.rootCount,
        ((restrictScaledArc j (certificate.roots i)).coeff 0 *
            (restrictScaledArc j (certificate.roots i)).coeff 2 +
          (restrictScaledArc j (certificate.roots i)).coeff 1 *
            (restrictScaledArc j (certificate.roots i)).coeff 1 +
          (restrictScaledArc j (certificate.roots i)).coeff 2 *
            (restrictScaledArc j (certificate.roots i)).coeff 0) at hroot
  unfold vecDot interiorVecSqNorm rootValueVector rootCoeffOneVector
    rootCoeffTwoVector arcRootPolynomials
  simp_rw [restrictScaledArc_coeff_zero] at hroot
  rw [show restrictScaledArc j (certificate.sigmaZero + certificate.sigma 4) =
      restrictScaledArc j certificate.sigmaZero +
        restrictScaledArc j (certificate.sigma 4) by simp [restrictScaledArc],
    Polynomial.coeff_add, hroot]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem central_rootCoeffOne_zero
    (certificate : ExtractedCertificate epsilon r) :
    rootCoeffOneVector certificate 0 = 0 := by
  funext i
  exact restrictScaledArc_zero_coeff_one (certificate.roots i)

/-- The exact first jet identity from differentiating in `t`, written in
terms of the scaled central arc. -/
theorem first_jet_identity
    (certificate : ExtractedCertificate epsilon r) :
    1 = 8 * vecDot (rootValueVector certificate)
          (rootCoeffTwoVector certificate 0) +
        activeMultiplierSum certificate := by
  have hcoeff := restricted_certificate_coeff_two certificate 0
  have hroot := root_sum_coeff_two certificate 0
  rw [central_rootCoeffOne_zero] at hroot
  simp [interiorVecSqNorm] at hroot
  have hsum :
      (restrictScaledArc 0 certificate.sigmaZero).coeff 2 +
          (restrictScaledArc 0 (certificate.sigma 4)).coeff 2 =
        2 * vecDot (rootValueVector certificate)
          (rootCoeffTwoVector certificate 0) := by
    simpa [restrictScaledArc, map_add, Polynomial.coeff_add] using hroot
  simp [arcGeneratorCoeffTwo, Fin.sum_univ_five] at hcoeff
  simp [activeMultiplierSum, Fin.sum_univ_four]
  nlinarith

/-- The exact Laplacian-type jet identity obtained by combining the two
coordinate arcs and subtracting twice the central arc. -/
theorem second_jet_identity
    (certificate : ExtractedCertificate epsilon r) :
    0 =
      2 * vecDot (rootValueVector certificate)
        (fun i ↦ rootCoeffTwoVector certificate 1 i +
          rootCoeffTwoVector certificate 2 i -
          2 * rootCoeffTwoVector certificate 0 i) +
      interiorVecSqNorm (rootCoeffOneVector certificate 1) +
      interiorVecSqNorm (rootCoeffOneVector certificate 2) +
      (1 / 2 : ℝ) * activeMultiplierSum certificate -
      (1 / 2 : ℝ) * MvPolynomial.eval origin (certificate.sigma 4) := by
  have hcoeff0 := restricted_certificate_coeff_two certificate 0
  have hcoeff1 := restricted_certificate_coeff_two certificate 1
  have hcoeff2 := restricted_certificate_coeff_two certificate 2
  have hroot0 := root_sum_coeff_two certificate 0
  have hroot1 := root_sum_coeff_two certificate 1
  have hroot2 := root_sum_coeff_two certificate 2
  rw [central_rootCoeffOne_zero] at hroot0
  simp [interiorVecSqNorm] at hroot0
  have hsum0 :
      (restrictScaledArc 0 certificate.sigmaZero).coeff 2 +
          (restrictScaledArc 0 (certificate.sigma 4)).coeff 2 =
        2 * vecDot (rootValueVector certificate)
          (rootCoeffTwoVector certificate 0) := by
    simpa [restrictScaledArc, map_add, Polynomial.coeff_add] using hroot0
  have hsum1 :
      (restrictScaledArc 1 certificate.sigmaZero).coeff 2 +
          (restrictScaledArc 1 (certificate.sigma 4)).coeff 2 =
        2 * vecDot (rootValueVector certificate)
            (rootCoeffTwoVector certificate 1) +
          interiorVecSqNorm (rootCoeffOneVector certificate 1) := by
    simpa [restrictScaledArc, map_add, Polynomial.coeff_add] using hroot1
  have hsum2 :
      (restrictScaledArc 2 certificate.sigmaZero).coeff 2 +
          (restrictScaledArc 2 (certificate.sigma 4)).coeff 2 =
        2 * vecDot (rootValueVector certificate)
            (rootCoeffTwoVector certificate 2) +
          interiorVecSqNorm (rootCoeffOneVector certificate 2) := by
    simpa [restrictScaledArc, map_add, Polynomial.coeff_add] using hroot2
  simp [arcGeneratorCoeffTwo, Fin.sum_univ_five] at hcoeff0 hcoeff1 hcoeff2
  simp [activeMultiplierSum, Fin.sum_univ_four]
  unfold vecDot at hsum0 hsum1 hsum2 ⊢
  rw [show (∑ i, rootValueVector certificate i *
        (rootCoeffTwoVector certificate 1 i +
          rootCoeffTwoVector certificate 2 i -
          2 * rootCoeffTwoVector certificate 0 i)) =
      ∑ i, (rootValueVector certificate i * rootCoeffTwoVector certificate 1 i +
        rootValueVector certificate i * rootCoeffTwoVector certificate 2 i -
        2 * (rootValueVector certificate i * rootCoeffTwoVector certificate 0 i)) by
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
