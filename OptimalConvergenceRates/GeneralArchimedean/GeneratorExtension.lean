/-
  Lifting quadratic-module certificates after adjoining one generator.
-/
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanGeometry
import OptimalConvergenceRates.KrivineStengle.Refutation
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- A truncated quadratic-module certificate remains valid after adjoining a generator. -/
theorem genQuadraticModule_lift_appendGenerator
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {h p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : p ∈ GenQuadraticModule g r) :
    p ∈ GenQuadraticModule (KrivineStengle.appendGenerator g h) r := by
  obtain ⟨σ₀, σ, hσ₀, hσ, hdegree₀, hdegree, hidentity⟩ := hp
  refine ⟨σ₀, Fin.snoc σ 0, hσ₀, ?_, hdegree₀, ?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp [IsSOS_zero]
    · simpa using hσ i
  · intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp
    · simpa [KrivineStengle.appendGenerator_castSucc] using hdegree i
  · rw [hidentity, Fin.sum_univ_castSucc]
    simp [KrivineStengle.appendGenerator_castSucc,
      KrivineStengle.appendGenerator_last]

/-- Untruncated module membership remains valid after adjoining a generator. -/
theorem QuadraticModuleMem.lift_appendGenerator
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {h p : MvPolynomial (Fin n) ℝ}
    (hp : QuadraticModuleMem g p) :
    QuadraticModuleMem (KrivineStengle.appendGenerator g h) p := by
  obtain ⟨r, hr⟩ := hp
  exact ⟨r, genQuadraticModule_lift_appendGenerator hr⟩

/-- Splitting a truncated refutation after adjoining one generator preserves
the truncation order on the old-module part and the complete new-generator
term. -/
theorem split_appendGenerator_refutation_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {h : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hrefute : (-1 : MvPolynomial (Fin n) ℝ) ∈
      GenQuadraticModule (KrivineStengle.appendGenerator g h) r) :
    ∃ s t : MvPolynomial (Fin n) ℝ,
      s ∈ GenQuadraticModule g r ∧
        IsSOS t ∧
        (t * h).totalDegree ≤ r ∧
        (-1 : MvPolynomial (Fin n) ℝ) = s + h * t := by
  obtain ⟨sigmaZero, sigma, hsigmaZero, hsigma,
    hdegreeZero, hdegree, hidentity⟩ := hrefute
  let s : MvPolynomial (Fin n) ℝ :=
    sigmaZero + ∑ i : Fin m, sigma i.castSucc * g i
  let t : MvPolynomial (Fin n) ℝ := sigma (Fin.last m)
  have hs : s ∈ GenQuadraticModule g r := by
    refine ⟨sigmaZero, fun i => sigma i.castSucc, hsigmaZero,
      fun i => hsigma i.castSucc, hdegreeZero, ?_, rfl⟩
    intro i
    simpa [KrivineStengle.appendGenerator_castSucc] using
      hdegree i.castSucc
  have hterm : (t * h).totalDegree ≤ r := by
    simpa [t, KrivineStengle.appendGenerator_last] using
      hdegree (Fin.last m)
  refine ⟨s, t, hs, hsigma (Fin.last m), hterm, ?_⟩
  calc
    (-1 : MvPolynomial (Fin n) ℝ) =
        sigmaZero +
          ∑ j : Fin (m + 1),
            sigma j * KrivineStengle.appendGenerator g h j :=
      hidentity
    _ = s + h * t := by
      rw [Fin.sum_univ_castSucc]
      simp only [KrivineStengle.appendGenerator_castSucc,
        KrivineStengle.appendGenerator_last]
      dsimp [s, t]
      ring

/-- If the appended generator is nonzero, its SOS multiplier in the split
refutation has total degree at most the original truncation order. -/
theorem split_appendGenerator_refutation_at_degree
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {h : MvPolynomial (Fin n) ℝ} {r : ℕ} (hh : h ≠ 0)
    (hrefute : (-1 : MvPolynomial (Fin n) ℝ) ∈
      GenQuadraticModule (KrivineStengle.appendGenerator g h) r) :
    ∃ s t : MvPolynomial (Fin n) ℝ,
      s ∈ GenQuadraticModule g r ∧ IsSOS t ∧ t.totalDegree ≤ r ∧
        (-1 : MvPolynomial (Fin n) ℝ) = s + h * t := by
  obtain ⟨s, t, hs, ht, hterm, hid⟩ :=
    split_appendGenerator_refutation_at hrefute
  refine ⟨s, t, hs, ht, ?_, hid⟩
  by_cases htzero : t = 0
  · simp [htzero]
  · rw [totalDegree_mul_of_isDomain htzero hh] at hterm
    omega
/-- Adjoining a generator preserves Archimedeanity. -/
theorem IsArchimedean.appendGenerator
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) (h : MvPolynomial (Fin n) ℝ) :
    IsArchimedean (KrivineStengle.appendGenerator g h) := by
  obtain ⟨R, r, hR, hcert⟩ := harch
  exact ⟨R, r, hR, genQuadraticModule_lift_appendGenerator hcert⟩

/-- The extended basic closed set is contained in the original one. -/
theorem basicClosedSet_appendGenerator_subset
    (g : Fin m → MvPolynomial (Fin n) ℝ) (h : MvPolynomial (Fin n) ℝ) :
    KrivineStengle.basicClosedSet (KrivineStengle.appendGenerator g h) ⊆
      KrivineStengle.basicClosedSet g := by
  intro x hx i
  simpa using hx i.castSucc

end OptimalConvergenceRates.GeneralArchimedean

end
