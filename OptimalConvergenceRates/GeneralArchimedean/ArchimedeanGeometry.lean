/-
  OptimalConvergenceRates/GeneralArchimedean/ArchimedeanGeometry.lean

  Compactness and minimum-attainment consequences of an Archimedean
  quadratic-module certificate.
-/
import OptimalConvergenceRates.GeneralArchimedean.Defs

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- Untruncated quadratic-module membership is closed under addition. -/
theorem QuadraticModuleMem.add
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ}
    (hp : QuadraticModuleMem g p) (hq : QuadraticModuleMem g q) :
    QuadraticModuleMem g (p + q) := by
  obtain ⟨r, hr⟩ := hp
  obtain ⟨s, hs⟩ := hq
  exact ⟨max r s, genQuadraticModule_add hr hs⟩

/-- Every SOS polynomial belongs to the untruncated quadratic module. -/
theorem QuadraticModuleMem.of_isSOS
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    {p : MvPolynomial (Fin n) ℝ} (hp : IsSOS p) :
    QuadraticModuleMem g p :=
  ⟨p.totalDegree, genQuadraticModule_sos g hp le_rfl⟩

/-- Multiplication by an SOS polynomial preserves untruncated membership. -/
theorem QuadraticModuleMem.sos_mul
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ}
    (hp : IsSOS p) (hq : QuadraticModuleMem g q) :
    QuadraticModuleMem g (p * q) := by
  obtain ⟨r, hr⟩ := hq
  exact ⟨r + p.totalDegree, genQuadraticModule_sos_mul hp hr⟩

/-- Quadratic-module elements are nonnegative on their basic closed set. -/
theorem QuadraticModuleMem.eval_nonneg
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} (hp : QuadraticModuleMem g p)
    {x : Fin n → ℝ} (hx : x ∈ KrivineStengle.basicClosedSet g) :
    0 ≤ eval x p := by
  obtain ⟨r, hr⟩ := hp
  exact GenQuadraticModule.eval_nonneg hr x hx

/-- A basic closed polynomial set is closed. -/
theorem basicClosedSet_isClosed
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    IsClosed (KrivineStengle.basicClosedSet g) := by
  rw [show KrivineStengle.basicClosedSet g =
      ⋂ i, {x | 0 ≤ eval x (g i)} by
    ext x
    simp [KrivineStengle.basicClosedSet]]
  exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_eval (g i))

/-- The defining Archimedean certificate bounds the sum of coordinate squares. -/
theorem IsArchimedean.sum_sq_le
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) {x : Fin n → ℝ}
    (hx : x ∈ KrivineStengle.basicClosedSet g) :
    ∃ R, 0 < R ∧ ∑ i, (x i) ^ 2 ≤ R := by
  obtain ⟨R, r, hR, hcert⟩ := harch
  refine ⟨R, hR, ?_⟩
  have hnonneg := GenQuadraticModule.eval_nonneg hcert x hx
  simpa using hnonneg

/-- An Archimedean basic closed set lies in a coordinate box. -/
theorem IsArchimedean.subset_scaledHypercube
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) :
    ∃ R, 0 < R ∧
      KrivineStengle.basicClosedSet g ⊆ ScaledHypercube (Real.sqrt R) n := by
  obtain ⟨R, r, hR, hcert⟩ := harch
  refine ⟨R, hR, ?_⟩
  intro x hx
  rw [ScaledHypercube_mem_abs _ (Real.sqrt_nonneg _) x]
  intro i
  have hsum : ∑ j, (x j) ^ 2 ≤ R := by
    have hnonneg := GenQuadraticModule.eval_nonneg hcert x hx
    simpa using hnonneg
  have hi : (x i) ^ 2 ≤ R :=
    le_trans (Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)) hsum
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hi

/-- Every Archimedean basic closed set is compact. -/
theorem IsArchimedean.isCompact_basicClosedSet
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) :
    IsCompact (KrivineStengle.basicClosedSet g) := by
  obtain ⟨R, hR, hsubset⟩ := harch.subset_scaledHypercube
  exact (ScaledHypercube_compact (n := n) (Real.sqrt R)).of_isClosed_subset
    (basicClosedSet_isClosed g) hsubset

/-- The polynomial image of a nonempty Archimedean feasible set is compact. -/
theorem IsArchimedean.image_isCompact
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ) :
    IsCompact ((fun x ↦ eval x f) '' KrivineStengle.basicClosedSet g) :=
  harch.isCompact_basicClosedSet.image (continuous_eval f)

/-- A polynomial attains its minimum on a nonempty Archimedean feasible set. -/
theorem polynomialMinimum_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ) :
    ∃ x ∈ KrivineStengle.basicClosedSet g, eval x f = polynomialMinimum g f := by
  have hc := harch.image_isCompact f
  have himage : ((fun x ↦ eval x f) '' KrivineStengle.basicClosedSet g).Nonempty :=
    hne.image _
  obtain ⟨x, hx, hfx⟩ := hc.sInf_mem himage
  exact ⟨x, hx, hfx⟩

/-- The attained minimum is a pointwise lower bound on the feasible set. -/
theorem polynomialMinimum_le_eval
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ)
    {x : Fin n → ℝ} (hx : x ∈ KrivineStengle.basicClosedSet g) :
    polynomialMinimum g f ≤ eval x f := by
  exact csInf_le (harch.image_isCompact f).bddBelow ⟨x, hx, rfl⟩

/-- Centering an objective at its minimum gives a nonnegative polynomial. -/
theorem centered_nonnegOn
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ) :
    IsNonnegOn (f - C (polynomialMinimum g f))
      (KrivineStengle.basicClosedSet g) := by
  intro x hx
  simp only [eval_sub, eval_C]
  exact sub_nonneg.mpr (polynomialMinimum_le_eval harch f hx)

end OptimalConvergenceRates.GeneralArchimedean

end
