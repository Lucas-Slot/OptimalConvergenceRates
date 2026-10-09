/-
  OptimalConvergenceRates/KrivineStengle/DegreeBranches.lean

  Specialization-safe branches for the actual degree of a parameterized polynomial.
-/
import OptimalConvergenceRates.KrivineStengle.GuardedRational
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.MvPolynomial.Polynomial

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Specialize the parameter coefficients of a univariate polynomial. -/
def specializePolynomial {n : ℕ} {F : Type*} [CommRing F] (coeff : ℝ →+* F)
    (x : Fin n → F) (f : (MvPolynomial (Fin n) ℝ)[X]) : F[X] :=
  f.map (eval₂Hom coeff x)

/-- The semantic condition that a specialized polynomial is nonzero with actual degree `d`:
its `d`th coefficient is nonzero and every higher coefficient vanishes. -/
def ActualDegreeCondition {n : ℕ} {F : Type*} [CommRing F] (coeff : ℝ →+* F)
    (x : Fin n → F) (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) : Prop :=
  (specializePolynomial coeff x f).coeff d ≠ 0 ∧
    ∀ j, d < j → (specializePolynomial coeff x f).coeff j = 0

/-- A sign formula selecting the branch on which the parameterized polynomial has nonzero
leading coefficient at `d` and all higher coefficients vanish. Only the finitely many
coefficients up to the symbolic degree need to be tested. -/
def degreeBranch {n : ℕ} (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) :
    SignFormula n :=
  .conj (.neg (.eqZero (f.coeff d)))
    (.all (((List.range (f.natDegree + 1)).filter (fun j ↦ d < j)).map
      (fun j ↦ .eqZero (f.coeff j))))

/-- Correctness of the finite actual-degree branch under arbitrary coefficient specialization. -/
theorem realizes_degreeBranch_iff {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) :
    (degreeBranch f d).Realizes coeff x ↔ ActualDegreeCondition coeff x f d := by
  constructor
  · intro h
    rw [degreeBranch, SignFormula.realizes_conj, SignFormula.realizes_neg,
      SignFormula.realizes_eqZero, SignFormula.realizes_all] at h
    refine ⟨?_, ?_⟩
    · simpa [ActualDegreeCondition, specializePolynomial, Polynomial.coeff_map] using h.1
    · intro j hdj
      by_cases hj : j < f.natDegree + 1
      · have hmem : SignFormula.eqZero (f.coeff j) ∈
            ((List.range (f.natDegree + 1)).filter (fun k ↦ d < k)).map
              (fun k ↦ SignFormula.eqZero (f.coeff k)) := by
          apply List.mem_map.mpr
          exact ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj, by simpa using hdj⟩, rfl⟩
        have hjzero := h.2 _ hmem
        simpa [ActualDegreeCondition, specializePolynomial, Polynomial.coeff_map] using hjzero
      · have hcoeff : f.coeff j = 0 := by
          exact coeff_eq_zero_of_natDegree_lt (Nat.le_of_not_gt hj)
        simp [specializePolynomial, Polynomial.coeff_map, hcoeff]
  · rintro ⟨hlead, hhigh⟩
    rw [degreeBranch, SignFormula.realizes_conj, SignFormula.realizes_neg,
      SignFormula.realizes_eqZero, SignFormula.realizes_all]
    constructor
    · simpa [ActualDegreeCondition, specializePolynomial, Polynomial.coeff_map] using hlead
    · intro formula hformula
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hformula
      have hdj : d < j := by simpa using (List.mem_filter.mp hj).2
      have := hhigh j hdj
      simpa [ActualDegreeCondition, specializePolynomial, Polynomial.coeff_map] using this


/-- The semantic branch condition is exactly equality of the specialized polynomial degree.
Unlike `natDegree`, this formulation excludes the zero polynomial when `d = 0`. -/
theorem actualDegreeCondition_iff_degree_eq {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) :
    ActualDegreeCondition coeff x f d ↔
      (specializePolynomial coeff x f).degree = d := by
  let p := specializePolynomial coeff x f
  constructor
  · rintro ⟨hlead, hhigh⟩
    change p.coeff d ≠ 0 at hlead
    change ∀ j, d < j → p.coeff j = 0 at hhigh
    have hp0 : p ≠ 0 := by
      intro hp
      apply hlead
      rw [hp]
      simp
    have hnat : p.natDegree = d :=
      natDegree_eq_of_le_of_coeff_ne_zero
        (natDegree_le_iff_coeff_eq_zero.mpr hhigh) hlead
    rw [degree_eq_natDegree hp0, hnat]
  · intro hdegree
    change p.degree = d at hdegree
    have hp0 : p ≠ 0 := by
      intro hp
      rw [hp] at hdegree
      simp at hdegree
    have hnat : p.natDegree = d := natDegree_eq_of_degree_eq_some hdegree
    constructor
    · rw [← hnat, coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp0
    · intro j hdj
      exact coeff_eq_zero_of_natDegree_lt (hnat.trans_lt hdj)

/-- The degree branches are mutually exclusive. -/
theorem actualDegreeCondition_unique {n : ℕ} {F : Type*} [Field F]
    (coeff : ℝ →+* F) (x : Fin n → F) (f : (MvPolynomial (Fin n) ℝ)[X])
    {d e : ℕ} (hd : ActualDegreeCondition coeff x f d)
    (he : ActualDegreeCondition coeff x f e) : d = e := by
  rcases lt_trichotomy d e with hde | hde | hed
  · exact False.elim (he.1 (hd.2 e hde))
  · exact hde
  · exact False.elim (hd.1 (he.2 d hed))

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Reinterpret a polynomial in `n+1` variables as a univariate polynomial
in variable zero with coefficients in the remaining `n` variables. -/
def asUnivariate {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ) :
    (MvPolynomial (Fin n) ℝ)[X] :=
  MvPolynomial.finSuccEquiv ℝ n p

/-- Evaluating the specialized univariate polynomial is exactly evaluation
of the original multivariate polynomial at `Fin.cons y x`. -/
theorem eval_specialize_asUnivariate
    {n : ℕ} {F : Type*} [CommRing F]
    (coeff : ℝ →+* F) (x : Fin n → F) (y : F)
    (p : MvPolynomial (Fin (n + 1)) ℝ) :
    (specializePolynomial coeff x (asUnivariate p)).eval y =
      eval₂Hom coeff (Fin.cons y x) p := by
  let lhs : MvPolynomial (Fin (n + 1)) ℝ →+* F :=
    (Polynomial.evalRingHom y).comp
      ((Polynomial.mapRingHom (eval₂Hom coeff x)).comp
        (MvPolynomial.finSuccEquiv ℝ n).toRingEquiv.toRingHom)
  have hlhs : lhs = eval₂Hom coeff (Fin.cons y x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [lhs, MvPolynomial.finSuccEquiv_X_zero]
      · simp [lhs, MvPolynomial.finSuccEquiv_X_succ]
  change lhs p = eval₂Hom coeff (Fin.cons y x) p
  exact RingHom.congr_fun hlhs p

end OptimalConvergenceRates.KrivineStengle

end
