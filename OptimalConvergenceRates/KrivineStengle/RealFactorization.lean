import OptimalConvergenceRates.KrivineStengle.RealComplexAlgebraicClosed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.QuadraticDiscriminant

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- Every irreducible polynomial over a real-closed field has degree at most two. -/
theorem irreducible_natDegree_le_two {p : R[X]} (hp : Irreducible p) :
    p.natDegree ≤ 2 := by
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_aeval_eq_zero (RealComplex R) p
      (degree_pos_of_irreducible hp).ne'
  have hzInt : IsIntegral R z := Algebra.IsIntegral.isIntegral z
  have hminDvd : minpoly R z ∣ p := minpoly.dvd R z hz
  have hpDvd : p ∣ minpoly R z :=
    (minpoly.irreducible hzInt).dvd_symm hp hminDvd
  calc
    p.natDegree ≤ (minpoly R z).natDegree :=
      natDegree_le_of_dvd hpDvd (minpoly.ne_zero hzInt)
    _ ≤ Module.finrank R (RealComplex R) := minpoly.natDegree_le z
    _ = 2 := QuadraticAlgebra.finrank_eq_two (-1 : R) 0

/-- Irreducibles over a real-closed field are linear or quadratic. -/
theorem irreducible_natDegree_eq_one_or_two {p : R[X]} (hp : Irreducible p) :
    p.natDegree = 1 ∨ p.natDegree = 2 := by
  have hpos : 0 < p.natDegree := hp.natDegree_pos
  have hle : p.natDegree ≤ 2 := irreducible_natDegree_le_two hp
  omega

/-- Every factor in the canonical irreducible factorization is linear or quadratic. -/
theorem factor_natDegree_eq_one_or_two {p q : R[X]}
    (hq : q ∈ UniqueFactorizationMonoid.factors p) :
    q.natDegree = 1 ∨ q.natDegree = 2 :=
  irreducible_natDegree_eq_one_or_two
    (UniqueFactorizationMonoid.irreducible_of_factor q hq)

/-- Every nonzero polynomial over a real-closed field is, up to a unit, a product of
linear and quadratic irreducible polynomials. -/
theorem exists_linear_quadratic_factorization (p : R[X]) (hp : p ≠ 0) :
    ∃ factors : Multiset R[X],
      (∀ q ∈ factors, q.natDegree = 1 ∨ q.natDegree = 2) ∧
        Associated factors.prod p := by
  refine ⟨UniqueFactorizationMonoid.factors p, ?_,
    UniqueFactorizationMonoid.factors_prod hp⟩
  intro q hq
  exact factor_natDegree_eq_one_or_two hq

/-- A monic irreducible quadratic over a real-closed field is strictly positive everywhere. -/
theorem monic_irreducible_quadratic_eval_pos {p : R[X]}
    (hpMonic : p.Monic) (hpIrr : Irreducible p) (hpDegree : p.natDegree = 2)
    (x : R) : 0 < p.eval x := by
  have hcoeffTwo : p.coeff 2 = 1 := by
    rw [← hpDegree, coeff_natDegree, hpMonic.leadingCoeff]
  have hpoly :
      p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
    calc
      p = ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ i :=
        p.as_sum_range_C_mul_X_pow
      _ = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
        rw [hpDegree]
        norm_num [Finset.sum_range_succ]
        ring
  by_contra hpos
  have heval : x * x + p.coeff 1 * x + p.coeff 0 ≤ 0 := by
    have := le_of_not_gt hpos
    rw [hpoly] at this
    simpa [hcoeffTwo, pow_two] using this
  have hdisc : 0 ≤ discrim (1 : R) (p.coeff 1) (p.coeff 0) := by
    rw [discrim]
    nlinarith [sq_nonneg (2 * x + p.coeff 1)]
  obtain ⟨s, hs⟩ :=
    IsRealClosed.exists_eq_pow_of_nonneg hdisc (by decide : (2 : ℕ) ≠ 0)
  obtain ⟨r, hr⟩ :=
    exists_quadratic_eq_zero (one_ne_zero : (1 : R) ≠ 0)
      ⟨s, by simpa [pow_two] using hs⟩
  have hroot : p.IsRoot r := by
    rw [IsRoot, hpoly]
    simpa [hcoeffTwo, pow_two] using hr
  exact hpIrr.not_isRoot_of_natDegree_ne_one (by omega) hroot

end OptimalConvergenceRates.KrivineStengle

end
