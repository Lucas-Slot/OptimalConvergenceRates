/-
  Extract the two SOS root families that survive at the minimizer.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.Defs
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

/-- A quadratic-module certificate together with a single degree-controlled
vector of square roots for the free and ball SOS terms. -/
structure ExtractedCertificate (epsilon : ℝ) (r : ℕ) where
  sigmaZero : MvPolynomial (Fin 3) ℝ
  sigma : Fin 5 → MvPolynomial (Fin 3) ℝ
  sosZero : IsSOS sigmaZero
  sos : ∀ i, IsSOS (sigma i)
  degreeZero : sigmaZero.totalDegree ≤ 2 * r
  degree : ∀ i, (sigma i * generators i).totalDegree ≤ 2 * r
  identity : objective + C epsilon =
    sigmaZero + ∑ i : Fin 5, sigma i * generators i
  rootCount : ℕ
  roots : Fin rootCount → MvPolynomial (Fin 3) ℝ
  rootDegree : ∀ i, (roots i).totalDegree ≤ r
  rootDecomp : sigmaZero + sigma 4 = ∑ i : Fin rootCount, (roots i) ^ 2

theorem ball_ne_zero : ball ≠ (0 : MvPolynomial (Fin 3) ℝ) := by
  intro h
  have h' := congrArg (MvPolynomial.eval origin) h
  norm_num [origin, ball, u, v, t] at h'

/-- Expose a truncated certificate and merge the roots of `sigmaZero` and
the ball multiplier.  The root degree is the paper order `r`. -/
theorem extractedCertificate_of_mem
    {epsilon : ℝ} {r : ℕ}
    (hcertificate : objective + C epsilon ∈
      GenQuadraticModule generators (2 * r)) :
    Nonempty (ExtractedCertificate epsilon r) := by
  obtain ⟨sigmaZero, sigma, hsosZero, hsos, hdegreeZero, hdegree,
    hidentity⟩ := hcertificate
  have hsigmaBallDegree : (sigma 4).totalDegree ≤ 2 * r := by
    by_cases hzero : sigma 4 = 0
    · simp [hzero]
    · have hmul := MvPolynomial.totalDegree_mul_of_isDomain hzero ball_ne_zero
      have hterm : (sigma 4 * ball).totalDegree ≤ 2 * r := by
        simpa [generators] using hdegree 4
      rw [hmul] at hterm
      omega
  have hsosZero' := hsosZero
  obtain ⟨NZero, PZero, hPZero⟩ := hsosZero'
  obtain ⟨NBall, PBall, hPBall⟩ := hsos 4
  have hPZeroDegree : ∀ i, (PZero i).totalDegree ≤ r :=
    sos_summand_totalDegree_le_of_sum_sq_totalDegree hPZero hdegreeZero
  have hPBallDegree : ∀ i, (PBall i).totalDegree ≤ r :=
    sos_summand_totalDegree_le_of_sum_sq_totalDegree hPBall hsigmaBallDegree
  refine ⟨{
    sigmaZero := sigmaZero
    sigma := sigma
    sosZero := hsosZero
    sos := hsos
    degreeZero := hdegreeZero
    degree := hdegree
    identity := hidentity
    rootCount := NZero + NBall
    roots := Fin.append PZero PBall
    rootDegree := ?_
    rootDecomp := ?_ }⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [Fin.append] using hPZeroDegree j
    · intro j
      simpa [Fin.append] using hPBallDegree j
  · rw [hPZero, hPBall, Fin.sum_univ_add]
    simp [Fin.append]

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
