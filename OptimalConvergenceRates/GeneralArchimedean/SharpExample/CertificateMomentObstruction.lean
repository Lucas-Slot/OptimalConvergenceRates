import OptimalConvergenceRates.GeneralArchimedean.SharpExample.SlabCertificateBounds

noncomputable section
open Finset MvPolynomial
open OptimalConvergenceRates

namespace OptimalConvergenceRates.GeneralArchimedean

theorem sharpExplicitCertificate_moment_obstruction
    {eps t : Real} {r D : Nat} (hr : 2 <= r)
    (ht0 : 0 < t) (htsmall : t <= (1 : Real) / 64)
    (ht : t = 2 * eps)
    (sigma0 sigmaA sigmaB sigmaG sigmaBall : MvPolynomial (Fin 3) Real)
    (hsigma0 : IsSOS sigma0) (hsigmaA : IsSOS sigmaA)
    (hsigmaB : IsSOS sigmaB) (hsigmaG : IsSOS sigmaG)
    (hsigmaBall : IsSOS sigmaBall)
    (hdegree0 : sigma0.totalDegree <= r)
    (hdegreeA : sigmaA.totalDegree <= r)
    (hdegreeB : sigmaB.totalDegree <= r)
    (hdegreeG : sigmaG.totalDegree <= r)
    (hdegreeBall : sigmaBall.totalDegree <= r)
    (hcert : sharpArchimedeanObjective + MvPolynomial.C eps =
      sigma0 + sigmaA * sharpArchimedeanA +
        sigmaB * sharpArchimedeanB + sigmaG * sharpArchimedeanW +
        sigmaBall * sharpArchimedeanGenerators (3 : Fin 4))
    (hD : 1 <= D)
    (hsmall : ((t ^ 2) ^ 2) * Real.exp (32 * (D : Real) + 16) <=
      (1 : Real) / 12)
    (hbase : (8 : Real) * (r : Real) ^ 2 * (t ^ 2) <=
      Real.exp (-((32 : Real) * (D : Real) + 32))) :
    1 <= 24 * ((2 * D + 1 : Nat) : Real) ^ 2 *
      ((2 * r + 1 : Nat) : Real) ^ 2 * sharpRestrictedTauEnvelope t r *
        Real.exp (16 - 16 * (D : Real) ^ 2) := by
  have hdegreeTwo0 : sigma0.totalDegree <= 2*r := by omega
  have hdegreeTwoA : sigmaA.totalDegree <= 2*r := by omega
  have hdegreeTwoB : sigmaB.totalDegree <= 2*r := by omega
  have hdegreeTwoG : sigmaG.totalDegree <= 2*r := by omega
  have hdegreeTwoBall : sigmaBall.totalDegree <= 2*r := by omega
  obtain ⟨hdb0⟩ := nonempty_degreeBoundedSOS_of_isSOS_totalDegree_le
    hsigma0 hdegreeTwo0
  obtain ⟨hdbA⟩ := nonempty_degreeBoundedSOS_of_isSOS_totalDegree_le
    hsigmaA hdegreeTwoA
  obtain ⟨hdbB⟩ := nonempty_degreeBoundedSOS_of_isSOS_totalDegree_le
    hsigmaB hdegreeTwoB
  obtain ⟨hdbG⟩ := nonempty_degreeBoundedSOS_of_isSOS_totalDegree_le
    hsigmaG hdegreeTwoG
  obtain ⟨hdbBall⟩ := nonempty_degreeBoundedSOS_of_isSOS_totalDegree_le
    hsigmaBall hdegreeTwoBall
  let R := sharpTwoVariableRefutation_of_explicit_certificate
    (eps := eps) (t := t) (r := r) (by nlinarith [ht0]) ht
    sigma0 sigmaA sigmaB sigmaG sigmaBall hdb0 hdbA hdbB hdbG hdbBall hcert
  have hH : 0 <= sharpRestrictedTauEnvelope t r := by
    unfold sharpRestrictedTauEnvelope sharpNegativeSlabEnvelope sharpSlabEnvelope
    positivity
  have heta : 0 < t ^ 2 := sq_pos_of_pos ht0
  have hetaOne : t ^ 2 <= 1 := by
    have htOne : t <= 1 := htsmall.trans (by norm_num)
    nlinarith
  have hrho : (1 : Real) / 2 <= 1 - t ^ 2 := by
    nlinarith [sq_nonneg ((1 : Real) / 64 - t)]
  have hrhoOne : 1 - t ^ 2 <= 1 := by nlinarith [sq_nonneg t]
  let hbounds := fun {a b : Real} (ha0 : 0 <= a)
      (ha4 : a <= (1 : Real) / 4) (hb0 : 0 <= b)
      (hb4 : b <= (1 : Real) / 4) =>
    sharpCertificate_restricted_tau_bounds hr ht0 htsmall ht
      sigma0 sigmaA sigmaB sigmaG sigmaBall hsigma0 hsigmaA hsigmaB
      hsigmaG hsigmaBall hdegree0 hdegreeA hdegreeB hdegreeG hdegreeBall
      hcert ha0 ha4 hb0 hb4
  apply sosMomentObstruction_explicit heta hetaOne hrho hrhoOne hH hD
    hsmall hbase R.sos0 R.sos1 R.sos2 R.sos3 R.sos4
  · intro a b ha0 ha4 hb0 hb4
    change MvPolynomial.eval ![a,b]
      (MvPolynomial.C (2/t) * sharpRestrictZ (-t) sigma0) <=
        sharpRestrictedTauEnvelope t r
    exact (hbounds ha0 ha4 hb0 hb4).1
  · intro a b ha0 ha4 hb0 hb4
    change MvPolynomial.eval ![a,b]
      (MvPolynomial.C (2/t) * sharpRestrictZ (-t) sigmaA) <=
        sharpRestrictedTauEnvelope t r
    exact (hbounds ha0 ha4 hb0 hb4).2.1
  · intro a b ha0 ha4 hb0 hb4
    change MvPolynomial.eval ![a,b]
      (MvPolynomial.C (2/t) * sharpRestrictZ (-t) sigmaB) <=
        sharpRestrictedTauEnvelope t r
    exact (hbounds ha0 ha4 hb0 hb4).2.2.1
  · intro a b ha0 ha4 hb0 hb4
    change MvPolynomial.eval ![a,b]
      (MvPolynomial.C 2 * sharpRestrictZ (-t) sigmaG) <=
        sharpRestrictedTauEnvelope t r
    exact (hbounds ha0 ha4 hb0 hb4).2.2.2.1
  · intro a b ha0 ha4 hb0 hb4
    change MvPolynomial.eval ![a,b]
      (MvPolynomial.C (2/t) * sharpRestrictZ (-t) sigmaBall) <=
        sharpRestrictedTauEnvelope t r
    exact (hbounds ha0 ha4 hb0 hb4).2.2.2.2
  · exact R.identity


/-- A truncated certificate for the fixed three-variable example forces the
explicit signed-moment inequality after restriction to `z = -2 eps`. -/
theorem sharpCertificate_moment_obstruction
    {eps : Real} {r D : Nat} (hr : 2 <= r)
    (heps : 0 < eps) (htsmall : 2 * eps <= (1 : Real) / 64)
    (hcert : sharpArchimedeanObjective + MvPolynomial.C eps ∈
      GenQuadraticModule sharpArchimedeanGenerators r)
    (hD : 1 <= D)
    (hsmall : (((2 * eps) ^ 2) ^ 2) *
      Real.exp (32 * (D : Real) + 16) <= (1 : Real) / 12)
    (hbase : (8 : Real) * (r : Real) ^ 2 * ((2 * eps) ^ 2) <=
      Real.exp (-((32 : Real) * (D : Real) + 32))) :
    1 <= 24 * ((2 * D + 1 : Nat) : Real) ^ 2 *
      ((2 * r + 1 : Nat) : Real) ^ 2 *
        sharpRestrictedTauEnvelope (2 * eps) r *
          Real.exp (16 - 16 * (D : Real) ^ 2) := by
  obtain ⟨sigma0, sigma, hsigma0, hsigma, hdegree0, hdegree,
    hidentity⟩ := hcert
  have hsigmaDegree (i : Fin 4) : (sigma i).totalDegree <= r := by
    by_cases hzero : sigma i = 0
    · simp [hzero]
    · have hmul := MvPolynomial.totalDegree_mul_of_isDomain hzero
        (sharpArchimedeanGenerator_ne_zero i)
      have hi := hdegree i
      rw [hmul] at hi
      omega
  have hcertExplicit :
      sharpArchimedeanObjective + MvPolynomial.C eps =
        sigma0 + sigma 0 * sharpArchimedeanA +
          sigma 1 * sharpArchimedeanB + sigma 2 * sharpArchimedeanW +
          sigma 3 * sharpArchimedeanGenerators 3 := by
    calc
      sharpArchimedeanObjective + MvPolynomial.C eps = sigma0 +
          (sigma 0 * sharpArchimedeanA + sigma 1 * sharpArchimedeanB +
            sigma 2 * sharpArchimedeanW +
            sigma 3 * sharpArchimedeanGenerators 3) := by
        simpa [Fin.sum_univ_four, sharpArchimedeanGenerators,
        KrivineStengle.sharpSeedGenerators] using hidentity
      _ = _ := by ring
  exact sharpExplicitCertificate_moment_obstruction hr
    (by nlinarith [heps]) htsmall rfl
    sigma0 (sigma 0) (sigma 1) (sigma 2) (sigma 3)
    hsigma0 (hsigma 0) (hsigma 1) (hsigma 2) (hsigma 3)
    hdegree0 (hsigmaDegree 0) (hsigmaDegree 1) (hsigmaDegree 2)
    (hsigmaDegree 3) hcertExplicit hD hsmall hbase

end OptimalConvergenceRates.GeneralArchimedean

end
