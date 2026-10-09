import OptimalConvergenceRates.KrivineStengle.HermiteSquarefree
import OptimalConvergenceRates.KrivineStengle.HermiteLinearPowerIdentity
import OptimalConvergenceRates.KrivineStengle.HermiteQuadraticPowerIdentity

noncomputable section

open Polynomial UniqueFactorizationMonoid

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- Hermite's root-sign identity for every monic polynomial over a real-closed
field, including arbitrary root multiplicities. -/
theorem hermiteSignature_eq_rootSignSum_monic (p h : R[X]) (hpMonic : p.Monic) :
    hermiteSignature p h hpMonic = rootSignSum p h := by
  classical
  let factors : Multiset R[X] := normalizedFactors p
  let support : Finset R[X] := factors.toFinset
  have hp0 : p ≠ 0 := hpMonic.ne_zero
  have hfactor {q : R[X]} (hq : q ∈ support) :
      Irreducible q ∧ q.Monic ∧ q ∣ p := by
    apply (Polynomial.mem_normalizedFactors_iff hp0).mp
    exact Multiset.mem_toFinset.mp hq
  have hcount {q : R[X]} (hq : q ∈ support) : 0 < factors.count q := by
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hq)
  have hproduct : ∏ q ∈ support, q ^ factors.count q = p := by
    rw [← Finset.prod_multiset_count factors]
    have hfac := leadingCoeff_mul_prod_normalizedFactors p
    rw [hpMonic.leadingCoeff, C_1, one_mul] at hfac
    exact hfac
  have hidentity := hermiteSignature_eq_rootSignSum_finset_prod support
    (fun q : R[X] ↦ q ^ factors.count q)
    (by
      intro q hq
      exact (hfactor hq).2.1.pow _)
    (by
      intro q hq r hr hqr
      exact (isCoprime_of_monic_irreducible_ne
        (hfactor hq).2.1 (hfactor hr).2.1
        (hfactor hq).1 (hfactor hr).1 hqr).pow)
    (by
      intro q hq weight
      rcases irreducible_natDegree_eq_one_or_two (hfactor hq).1 with hdegree | hdegree
      · exact hermiteSignature_eq_rootSignSum_monic_linear_pow
          (hfactor hq).2.1 hdegree weight (hcount hq)
      · exact hermiteSignature_eq_rootSignSum_irreducible_quadratic_pow
          (hfactor hq).2.1 (hfactor hq).1 hdegree weight (hcount hq)) h
  simpa only [hproduct] using hidentity

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- The Hermite signature sum counts distinct roots satisfying all strict
side inequalities, for every monic polynomial over a real-closed field. -/
theorem strictRootCount_eq_hermite_sum {s : ℕ}
    (f : R[X]) (hf : f.Monic) (g : Fin s → R[X]) :
    (2 : ℤ) ^ s * (strictRootCount f g : ℤ) =
      ∑ exponent : Fin s → Fin 2,
        hermiteSignature f (∏ i, (g i) ^ (exponent i).1.succ) hf :=
  strictRootCount_hermite_identity f hf g
    (fun h ↦ hermiteSignature_eq_rootSignSum_monic f h hf)

/-- A monic polynomial has a root satisfying all strict side inequalities
iff its finite Hermite signature sum is positive. -/
theorem exists_root_all_pos_iff_hermite_sum_pos_realClosed {s : ℕ}
    (f : R[X]) (hf : f.Monic) (g : Fin s → R[X]) :
    (∃ r ∈ f.roots.toFinset, ∀ i, 0 < (g i).eval r) ↔
      0 < ∑ exponent : Fin s → Fin 2,
        hermiteSignature f (∏ i, (g i) ^ (exponent i).1.succ) hf :=
  exists_root_all_pos_iff_hermite_sum_pos f hf g
    (fun h ↦ hermiteSignature_eq_rootSignSum_monic f h hf)

end OptimalConvergenceRates.KrivineStengle

end
