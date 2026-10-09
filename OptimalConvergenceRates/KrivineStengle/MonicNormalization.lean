/-
  OptimalConvergenceRates/KrivineStengle/MonicNormalization.lean

  Specialization-safe monic normalization on an actual-degree branch.
-/
import OptimalConvergenceRates.KrivineStengle.DegreeBranchPartition
import Mathlib.Algebra.Polynomial.Roots

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Normalize a specialized polynomial by the coefficient selected by an
actual-degree branch. The accompanying theorem supplies monicity only when
the branch guard is known. -/
def monicNormalizeSpecialization {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) : F[X] :=
  let p := specializePolynomial coeff x f
  p * Polynomial.C (p.coeff d)⁻¹

/-- On an actual-degree branch, the chosen normalization is monic. -/
theorem monic_monicNormalizeSpecialization {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    (monicNormalizeSpecialization coeff x f d).Monic := by
  let p := specializePolynomial coeff x f
  have hpDegree : p.degree = d :=
    (actualDegreeCondition_iff_degree_eq coeff x f d).1 hdegree
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hpDegree
    simp at hpDegree
  have hnat : p.natDegree = d := natDegree_eq_of_degree_eq_some hpDegree
  have hlead : p.leadingCoeff = p.coeff d := by
    rw [leadingCoeff, hnat]
  simpa [monicNormalizeSpecialization, p, hlead] using
    monic_mul_leadingCoeff_inv hp0

/-- Monic normalization preserves the actual degree selected by the branch. -/
theorem natDegree_monicNormalizeSpecialization {n : ℕ} {F : Type*}
    [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    (monicNormalizeSpecialization coeff x f d).natDegree = d := by
  let p := specializePolynomial coeff x f
  have hpDegree : p.degree = d :=
    (actualDegreeCondition_iff_degree_eq coeff x f d).1 hdegree
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hpDegree
    simp at hpDegree
  have hnat : p.natDegree = d := natDegree_eq_of_degree_eq_some hpDegree
  have hlead : p.leadingCoeff = p.coeff d := by
    rw [leadingCoeff, hnat]
  calc
    (monicNormalizeSpecialization coeff x f d).natDegree = p.natDegree := by
      simpa [monicNormalizeSpecialization, p, hlead] using
        natDegree_mul_leadingCoeff_inv p hp0
    _ = d := hnat

/-- Monic normalization preserves the multiset of roots. -/
theorem roots_monicNormalizeSpecialization {n : ℕ} {F : Type*}
    [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    (monicNormalizeSpecialization coeff x f d).roots =
      (specializePolynomial coeff x f).roots := by
  let p := specializePolynomial coeff x f
  have hlead : p.coeff d ≠ 0 := hdegree.1
  rw [monicNormalizeSpecialization]
  rw [mul_comm, roots_C_mul p (inv_ne_zero hlead)]

/-- Each normalized coefficient is the guarded rational expression
`f_j / f_d` on the actual-degree branch. -/
def monicNormalizedCoefficient {n : ℕ}
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d j : ℕ) :
    GuardedRational n :=
  ⟨f.coeff j, f.coeff d⟩

theorem monicNormalizedCoefficient_valid {n : ℕ} {F : Type*}
    [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d j : ℕ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    (monicNormalizedCoefficient f d j).Valid coeff x := by
  simpa [monicNormalizedCoefficient, ActualDegreeCondition,
    specializePolynomial, Polynomial.coeff_map] using hdegree.1

theorem eval_monicNormalizedCoefficient {n : ℕ} {F : Type*}
    [Field F] (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d j : ℕ) :
    (monicNormalizedCoefficient f d j).eval coeff x =
      (specializePolynomial coeff x f).coeff j /
        (specializePolynomial coeff x f).coeff d := by
  simp [monicNormalizedCoefficient, GuardedRational.eval,
    specializePolynomial, Polynomial.coeff_map]

end OptimalConvergenceRates.KrivineStengle

end
