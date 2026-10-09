/-
  OptimalConvergenceRates/KrivineStengle/HermiteIrreducible.lean

  Hermite's root-sign identity for all monic irreducible factors over a
  real-closed field.
-/
import OptimalConvergenceRates.KrivineStengle.HermiteQuadratic
import OptimalConvergenceRates.KrivineStengle.HermiteLinear

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- Hermite's root-sign identity for an arbitrary monic linear polynomial. -/
theorem hermiteSignature_eq_rootSignSum_monic_linear {p : R[X]}
    (hpMonic : p.Monic) (hpDegree : p.natDegree = 1) (h : R[X]) :
    hermiteSignature p h hpMonic = rootSignSum p h := by
  let a := -p.coeff 0
  have hp : p = X - C a := by
    simpa [a] using hpMonic.eq_X_add_C hpDegree
  simpa only [hp] using
    (hermiteSignature_eq_rootSignSum_X_sub_C a h)

/-- Hermite's root-sign identity for every monic irreducible over a real-closed field. -/
theorem hermiteSignature_eq_rootSignSum_irreducible {p : R[X]}
    (hpMonic : p.Monic) (hpIrr : Irreducible p) (h : R[X]) :
    hermiteSignature p h hpMonic = rootSignSum p h := by
  rcases irreducible_natDegree_eq_one_or_two hpIrr with hpDegree | hpDegree
  · exact hermiteSignature_eq_rootSignSum_monic_linear hpMonic hpDegree h
  · exact hermiteSignature_eq_rootSignSum_irreducible_quadratic
      hpMonic hpIrr hpDegree h

end OptimalConvergenceRates.KrivineStengle

end
