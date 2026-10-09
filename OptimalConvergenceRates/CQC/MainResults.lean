import OptimalConvergenceRates.CQC.PublicProofs

/-!
# Putinar rates under CQC

This is the readable public statement layer. Definitions and proof calculations
live in the supporting files of this directory.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates

/-- A fixed nonnegative unit-cube polynomial controls the perturbed
certificates of every fixed nonnegative polynomial on an Archimedean CQC
system. A zero of the original polynomial produces a zero of the cube
polynomial. -/
theorem fixedInstanceTransfer
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : CQC g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ P : MvPolynomial (Fin (n + m)) ℝ,
      ∃ c Clog : ℝ,
        1 ≤ c ∧ 0 < Clog ∧
        IsNonnegOn P (Hypercube (n + m)) ∧
        (∀ {e d : ℕ}, 2 ≤ e →
          (∀ i, (g i).totalDegree ≤ e) → p.totalDegree ≤ d →
          P.totalDegree ≤ d + 4 * m * (e - 1)) ∧
        ((∃ x ∈ KrivineStengle.basicClosedSet g,
            MvPolynomial.eval x p = 0) →
          ∃ z ∈ Hypercube (n + m), MvPolynomial.eval z P = 0) ∧
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 → ∀ {r : ℕ},
          P + C (ε / c) ∈ BoxQuadraticModule (n + m) r →
          p + C ε ∈ GenQuadraticModule g
            ((max 1 (Finset.univ.sup fun i ↦ (g i).totalDegree)) * r +
              Nat.ceil (Clog * (1 + Real.log (1 / ε)))) :=
  CQCMainResultsProofs.fixedInstanceTransfer hn hm hne harch hcqc hp

/-- Every fixed nonnegative polynomial on an Archimedean CQC basic closed set
has Putinar certificates with perturbation of order `r⁻⁴`. -/
theorem putinarQuarticRate
    {n m : ℕ} (hn : 0 < n) (_hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : CQC g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r :=
  CQCMainResultsProofs.putinarQuarticRate hn hne harch hcqc hp

/-- Inverse form of the CQC quartic rate: every positive perturbation has a
certificate at a degree bounded by its inverse fourth root, up to the fixed
threshold and ceiling term. -/
theorem putinarQuarticDegreeBound
    {n m : ℕ} (hn : 0 < n) (_hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : CQC g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ r : ℕ,
          (r : ℝ) < (r₀ : ℝ) +
              (A / epsilon) ^ ((1 : ℝ) / 4) + 1 ∧
            p + C epsilon ∈ GenQuadraticModule g r :=
  CQCMainResultsProofs.putinarQuarticDegreeBound hn hne harch hcqc hp

/-- The generalized quadratic-module Lasserre hierarchy converges at the
fixed-instance rate `O(r⁻⁴)` under CQC. -/
theorem lasserreQuarticRate
    {n m : ℕ} (hn : 0 < n) (_hm : 0 < m)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (f : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : CQC g) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        ((GeneralArchimedean.polynomialMinimum g f -
            A / (r : ℝ) ^ 4 : ℝ) : WithBot ℝ) ≤
            GeneralArchimedean.genLasserreBoundQM g f r ∧
          GeneralArchimedean.genLasserreBoundQM g f r ≤
            (GeneralArchimedean.polynomialMinimum g f : WithBot ℝ) :=
  CQCMainResultsProofs.lasserreQuarticRate hn g f hne harch hcqc

end OptimalConvergenceRates

end
