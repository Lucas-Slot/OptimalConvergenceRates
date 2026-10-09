/-
  The signed-moment obstruction in terms of the repository's
  `DegreeBoundedSOS` witness type.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.GaussianDecay

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

private theorem degreeBoundedSOS_rootNorm_le_sqrt
    {tau : MvPolynomial (Fin 2) Real} {d : Nat}
    (htau : DegreeBoundedSOS tau d) {H : Real}
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      MvPolynomial.eval ![a, b] tau <= H) :
    forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (htau.P k)) <= Real.sqrt H := by
  intro a b ha0 ha1 hb0 hb1
  unfold OptimalConvergenceRates.interiorVecNorm
  apply Real.sqrt_le_sqrt
  have heval := hbound a b ha0 ha1 hb0 hb1
  rw [htau.eval_eq_vecSqNorm] at heval
  simpa [OptimalConvergenceRates.interiorVecSqNorm, OptimalConvergenceRates.vecSqNorm] using heval

/-- Explicit quantitative form of the two-variable moment obstruction.  The
SOS degree bound is a root-degree bound, matching `DegreeBoundedSOS`. -/
theorem sosMomentObstruction_explicit
    {tau0 tau1 tau2 tau3 tau4 : MvPolynomial (Fin 2) Real}
    {D d : Nat} {eta rho H : Real}
    (heta : 0 < eta) (hetaOne : eta <= 1)
    (hrho : (1 : Real) / 2 <= rho) (hrhoOne : rho <= 1)
    (hH : 0 <= H) (hD : 1 <= D)
    (hsmall : eta ^ 2 * Real.exp (32 * (D : Real) + 16) <=
      (1 : Real) / 12)
    (hbase : (8 : Real) * (d : Real) ^ 2 * eta <=
      Real.exp (-((32 : Real) * (D : Real) + 32)))
    (htau0 : DegreeBoundedSOS tau0 d)
    (htau1 : DegreeBoundedSOS tau1 d)
    (htau2 : DegreeBoundedSOS tau2 d)
    (htau3 : DegreeBoundedSOS tau3 d)
    (htau4 : DegreeBoundedSOS tau4 d)
    (hbound0 : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      MvPolynomial.eval ![a, b] tau0 <= H)
    (hbound1 : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      MvPolynomial.eval ![a, b] tau1 <= H)
    (hbound2 : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      MvPolynomial.eval ![a, b] tau2 <= H)
    (hbound3 : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      MvPolynomial.eval ![a, b] tau3 <= H)
    (hbound4 : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      MvPolynomial.eval ![a, b] tau4 <= H)
    (hrefute :
      (-1 : MvPolynomial (Fin 2) Real) =
        tau0 + obstructionA * tau1 + obstructionB * tau2 +
          (-(obstructionA * obstructionB + C (eta ^ 2))) * tau3 +
          (C rho - obstructionA ^ 2 - obstructionB ^ 2) * tau4) :
    1 <=
      24 * ((2 * D + 1 : Nat) : Real) ^ 2 *
        ((2 * d + 1 : Nat) : Real) ^ 2 * H *
          Real.exp (16 - 16 * (D : Real) ^ 2) := by
  have hdecay := sharpTailDecay_of_base_le heta.le hetaOne hbase
  have hrefuteRoots := hrefute
  rw [htau0.decomp, htau1.decomp, htau2.decomp, htau3.decomp,
    htau4.decomp] at hrefuteRoots
  have hcore := momentObstruction_of_root_bounds
    heta hetaOne hrho hrhoOne (Real.sqrt_nonneg H)
    (Real.exp_pos _).le hD hsmall hdecay
    htau0.P htau1.P htau2.P htau3.P htau4.P
    htau0.degree htau1.degree htau2.degree htau3.degree htau4.degree
    (degreeBoundedSOS_rootNorm_le_sqrt htau0 hbound0)
    (degreeBoundedSOS_rootNorm_le_sqrt htau1 hbound1)
    (degreeBoundedSOS_rootNorm_le_sqrt htau2 hbound2)
    (degreeBoundedSOS_rootNorm_le_sqrt htau3 hbound3)
    (degreeBoundedSOS_rootNorm_le_sqrt htau4 hbound4)
    hrefuteRoots
  rw [sharpTailPenalty, Real.sq_sqrt hH] at hcore
  nlinarith

end OptimalConvergenceRates.GeneralArchimedean

end
