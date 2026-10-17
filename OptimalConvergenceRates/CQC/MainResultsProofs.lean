import OptimalConvergenceRates.CQC.LasserreRate
import OptimalConvergenceRates.CQC.TransferOrder
import OptimalConvergenceRates.CQC.EqualityTransferAbsorption
import OptimalConvergenceRates.CQC.EqualityLasserreRate

/-! Proof delegates for the public CQC statements. -/

noncomputable section
open MvPolynomial
namespace OptimalConvergenceRates.CQCInternal
open GeneralArchimedean

variable {n m : ℕ}

theorem fixedInstanceTransfer_proof
    (hn : 0 < n) (hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : ActiveGradientIndependent g)
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
            (generatorDegree g * r + Nat.ceil
              (Clog * (1 + Real.log (1 / ε)))) :=
  fixedInstanceTransfer_internal hn hm hne harch hcqc hp

theorem fixedInstanceTransferOrder_proof
    (hn : 0 < n) (hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : ActiveGradientIndependent g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ P : MvPolynomial (Fin (n + m)) ℝ,
      ∃ c Clog : ℝ,
        1 ≤ c ∧ 0 < Clog ∧
        IsNonnegOn P (Hypercube (n + m)) ∧
        ((∃ x ∈ KrivineStengle.basicClosedSet g,
            MvPolynomial.eval x p = 0) →
          ∃ z ∈ Hypercube (n + m), MvPolynomial.eval z P = 0) ∧
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
          (∃ r, P + C (ε / c) ∈ BoxQuadraticModule (n + m) r) →
          perturbationOrder g p ε ≤
            generatorDegree g * boxPerturbationOrder P (ε / c) +
              Nat.ceil (Clog * (1 + Real.log (1 / ε))) :=
  fixedInstanceTransferOrder_internal hn hm hne harch hcqc hp

theorem putinarQuarticRate_proof
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : ActiveGradientIndependent g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r :=
  putinarQuarticRate_internal hn hne harch hcqc hp

theorem lasserreQuarticRate_proof
    (hn : 0 < n)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (f : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : ActiveGradientIndependent g) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        ((polynomialMinimum g f - A / (r : ℝ) ^ 4 : ℝ) : WithBot ℝ) ≤
            genLasserreBoundQM g f r ∧
          genLasserreBoundQM g f r ≤
            (polynomialMinimum g f : WithBot ℝ) :=
  lasserreQuarticRate_internal hn g f hne harch hcqc


theorem fixedInstanceTransferWithEqualities_proof
    (hn : 0 < n) (hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : CQCWithEqualities g)
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
            (generatorDegree g * r + Nat.ceil
              (Clog * (1 + Real.log (1 / ε)))) :=
  fixedInstanceTransferWithEqualities_internal hn hm hne harch hcqc hp

theorem putinarQuarticRateWithEqualities_proof
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : CQCWithEqualities g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r :=
  putinarQuarticRateWithEqualities_internal hn hne harch hcqc hp

theorem lasserreQuarticRateWithEqualities_proof
    (hn : 0 < n)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (f : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : CQCWithEqualities g) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        ((polynomialMinimum g f - A / (r : ℝ) ^ 4 : ℝ) : WithBot ℝ) ≤
            genLasserreBoundQM g f r ∧
          genLasserreBoundQM g f r ≤
            (polynomialMinimum g f : WithBot ℝ) :=
  lasserreQuarticRateWithEqualities_internal hn g f hne harch hcqc

end OptimalConvergenceRates.CQCInternal
end


