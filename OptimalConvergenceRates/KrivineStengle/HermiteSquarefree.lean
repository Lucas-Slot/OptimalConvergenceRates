/-
  OptimalConvergenceRates/KrivineStengle/HermiteSquarefree.lean

  Hermite's root-sign identity for squarefree products of monic irreducibles.
-/
import OptimalConvergenceRates.KrivineStengle.HermiteIrreducible
import OptimalConvergenceRates.KrivineStengle.HermiteIdentityFinset

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u v

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- Distinct monic irreducible polynomials are coprime. -/
theorem isCoprime_of_monic_irreducible_ne {p q : R[X]}
    (hpMonic : p.Monic) (hqMonic : q.Monic)
    (hpIrr : Irreducible p) (hqIrr : Irreducible q) (hne : p ≠ q) :
    IsCoprime p q := by
  rw [hpIrr.coprime_iff_not_dvd]
  intro hdvd
  exact hne (eq_of_monic_of_associated hpMonic hqMonic
    (hpIrr.associated_of_dvd hqIrr hdvd))

/-- Hermite's root-sign identity for a product of pairwise distinct monic
irreducible factors over a real-closed field. -/
theorem hermiteSignature_eq_rootSignSum_finset_prod_irreducible
    {I : Type v} (s : Finset I) (f : I → R[X])
    (hmonic : ∀ i ∈ s, (f i).Monic)
    (hirr : ∀ i ∈ s, Irreducible (f i))
    (hinj : Set.InjOn f s) :
    ∀ h : R[X],
      hermiteSignature (∏ i ∈ s, f i) h
          (monic_prod_of_monic s f hmonic) =
        rootSignSum (∏ i ∈ s, f i) h := by
  apply hermiteSignature_eq_rootSignSum_finset_prod s f hmonic
  · intro i hi j hj hij
    exact isCoprime_of_monic_irreducible_ne
      (hmonic i hi) (hmonic j hj) (hirr i hi) (hirr j hj)
      (fun h ↦ hij (hinj hi hj h))
  · intro i hi h
    exact hermiteSignature_eq_rootSignSum_irreducible
      (hmonic i hi) (hirr i hi) h

end OptimalConvergenceRates.KrivineStengle

end
