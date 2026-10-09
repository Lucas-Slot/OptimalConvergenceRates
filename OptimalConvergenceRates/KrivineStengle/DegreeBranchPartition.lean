/-
  OptimalConvergenceRates/KrivineStengle/DegreeBranchPartition.lean

  The exhaustive specialization partition into the zero-polynomial branch
  and actual-degree branches.
-/
import OptimalConvergenceRates.KrivineStengle.DegreeBranches

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- The branch on which every coefficient of the specialized polynomial
vanishes. Only coefficients up to the symbolic degree need to be tested. -/
def zeroPolynomialBranch {n : ℕ} (f : (MvPolynomial (Fin n) ℝ)[X]) :
    SignFormula n :=
  .all ((List.range (f.natDegree + 1)).map
    (fun j ↦ .eqZero (f.coeff j)))

/-- Correctness of the finite zero-polynomial branch. -/
theorem realizes_zeroPolynomialBranch_iff {n : ℕ} {F : Type*} [Field F]
    [LinearOrder F] [IsStrictOrderedRing F] (coeff : ℝ →+* F)
    (x : Fin n → F) (f : (MvPolynomial (Fin n) ℝ)[X]) :
    (zeroPolynomialBranch f).Realizes coeff x ↔
      specializePolynomial coeff x f = 0 := by
  rw [zeroPolynomialBranch, SignFormula.realizes_all]
  constructor
  · intro hzero
    ext j
    by_cases hj : j < f.natDegree + 1
    · have hmem : SignFormula.eqZero (f.coeff j) ∈
          (List.range (f.natDegree + 1)).map
            (fun k ↦ SignFormula.eqZero (f.coeff k)) := by
        exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
      have hjzero := hzero _ hmem
      simpa [specializePolynomial, Polynomial.coeff_map] using hjzero
    · have hcoeff : f.coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (Nat.le_of_not_gt hj)
      simp [specializePolynomial, Polynomial.coeff_map, hcoeff]
  · intro hzero formula hformula
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hformula
    have hjzero := congrArg (fun p : F[X] ↦ p.coeff j) hzero
    simpa [specializePolynomial, Polynomial.coeff_map] using hjzero

/-- Every specialization lies either on the zero-polynomial branch or on
an actual-degree branch within the symbolic degree bound. -/
theorem realizes_zero_or_degreeBranch {n : ℕ} {F : Type*} [Field F]
    [LinearOrder F] [IsStrictOrderedRing F] (coeff : ℝ →+* F)
    (x : Fin n → F) (f : (MvPolynomial (Fin n) ℝ)[X]) :
    (zeroPolynomialBranch f).Realizes coeff x ∨
      ∃ d ≤ f.natDegree, (degreeBranch f d).Realizes coeff x := by
  let p := specializePolynomial coeff x f
  by_cases hp : p = 0
  · exact Or.inl ((realizes_zeroPolynomialBranch_iff coeff x f).2 hp)
  · right
    refine ⟨p.natDegree, ?_, ?_⟩
    · dsimp only [p, specializePolynomial]
      exact natDegree_map_le
    · rw [realizes_degreeBranch_iff, actualDegreeCondition_iff_degree_eq]
      exact degree_eq_natDegree hp

/-- The zero-polynomial branch is disjoint from every actual-degree branch. -/
theorem zeroPolynomialBranch_disjoint_degreeBranch {n : ℕ} {F : Type*}
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hzero : (zeroPolynomialBranch f).Realizes coeff x)
    (hdegree : (degreeBranch f d).Realizes coeff x) : False := by
  have hpzero := (realizes_zeroPolynomialBranch_iff coeff x f).1 hzero
  have hactual := (realizes_degreeBranch_iff coeff x f d).1 hdegree
  exact hactual.1 (by rw [hpzero]; simp)

end OptimalConvergenceRates.KrivineStengle

end
