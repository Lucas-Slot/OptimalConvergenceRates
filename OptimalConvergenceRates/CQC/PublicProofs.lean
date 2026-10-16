import OptimalConvergenceRates.CQC.Defs
import OptimalConvergenceRates.CQC.MainResultsProofs
import OptimalConvergenceRates.BasicNotions.GeneralConeOps
import OptimalConvergenceRates.QuarticConvergence.InverseRate

/-! Proof adapters between the internal CQC formulation and the public statements. -/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.CQCMainResultsProofs

open GeneralArchimedean

variable {n m : ℕ}

theorem fixedInstanceTransfer
    (hn : 0 < n) (hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
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
              Nat.ceil (Clog * (1 + Real.log (1 / ε)))) := by
  simpa only [CQC, CQCInternal.ActiveGradientIndependent,
      CQCInternal.generatorDegree] using
    CQCInternal.fixedInstanceTransfer_proof hn hm hne harch hcqc hp

theorem putinarQuarticRate
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : CQC g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r := by
  simpa only [CQC, CQCInternal.ActiveGradientIndependent,
      CQCInternal.generatorDegree] using
    CQCInternal.putinarQuarticRate_proof hn hne harch hcqc hp

theorem putinarQuarticDegreeBound
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : CQC g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ r : ℕ,
          (r : ℝ) < (r₀ : ℝ) +
              (A / epsilon) ^ ((1 : ℝ) / 4) + 1 ∧
            p + C epsilon ∈ GenQuadraticModule g r := by
  obtain ⟨A, r₀, hA, hr₀, hcertificate⟩ :=
    putinarQuarticRate hn hne harch hcqc hp
  refine ⟨A, r₀, hA, hr₀, ?_⟩
  intro epsilon hepsilon
  let r := QuarticConvergence.quarticInverseOrder r₀ A epsilon
  have hscale : A / (r : ℝ) ^ 4 ≤ epsilon := by
    dsimp [r]
    exact QuarticConvergence.quarticScale_le_epsilon hr₀ hA.le hepsilon
  have hbase : p + C (A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r := by
    exact hcertificate r (QuarticConvergence.quarticInverseOrder_ge r₀ A epsilon)
  have hconstant : C (epsilon - A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r :=
    GenQuadraticModule_mono (Nat.zero_le r)
      (genQuadraticModule_C_nonneg g (sub_nonneg.mpr hscale))
  have hsum := GenQuadraticModule_add hbase hconstant
  refine ⟨r, ?_, ?_⟩
  · simpa only using QuarticConvergence.quarticInverseOrder_lt r₀ hA.le hepsilon
  · have heq :
        p + C (A / (r : ℝ) ^ 4) + C (epsilon - A / (r : ℝ) ^ 4) =
          p + C epsilon := by
      rw [map_sub]
      ring
    rw [← heq]
    exact hsum

theorem lasserreQuarticRate
    (hn : 0 < n)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (f : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : CQC g) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        ((polynomialMinimum g f - A / (r : ℝ) ^ 4 : ℝ) : WithBot ℝ) ≤
            genLasserreBoundQM g f r ∧
          genLasserreBoundQM g f r ≤
            (polynomialMinimum g f : WithBot ℝ) := by
  simpa only [CQC, CQCInternal.ActiveGradientIndependent,
      CQCInternal.generatorDegree] using
    CQCInternal.lasserreQuarticRate_proof hn g f hne harch hcqc


theorem fixedInstanceTransferWithEqualities
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
            ((max 1 (Finset.univ.sup fun i ↦ (g i).totalDegree)) * r +
              Nat.ceil (Clog * (1 + Real.log (1 / ε)))) := by
  simpa only [CQCInternal.generatorDegree] using
    CQCInternal.fixedInstanceTransferWithEqualities_proof
      hn hm hne harch hcqc hp

theorem putinarQuarticRateWithEqualities
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
  CQCInternal.putinarQuarticRateWithEqualities_proof
    hn hne harch hcqc hp

theorem putinarQuarticDegreeBoundWithEqualities
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : CQCWithEqualities g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ r : ℕ,
          (r : ℝ) < (r₀ : ℝ) +
              (A / epsilon) ^ ((1 : ℝ) / 4) + 1 ∧
            p + C epsilon ∈ GenQuadraticModule g r := by
  obtain ⟨A, r₀, hA, hr₀, hcertificate⟩ :=
    putinarQuarticRateWithEqualities hn hne harch hcqc hp
  refine ⟨A, r₀, hA, hr₀, ?_⟩
  intro epsilon hepsilon
  let r := QuarticConvergence.quarticInverseOrder r₀ A epsilon
  have hscale : A / (r : ℝ) ^ 4 ≤ epsilon := by
    dsimp [r]
    exact QuarticConvergence.quarticScale_le_epsilon hr₀ hA.le hepsilon
  have hbase : p + C (A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r := by
    exact hcertificate r
      (QuarticConvergence.quarticInverseOrder_ge r₀ A epsilon)
  have hconstant : C (epsilon - A / (r : ℝ) ^ 4) ∈
      GenQuadraticModule g r :=
    GenQuadraticModule_mono (Nat.zero_le r)
      (genQuadraticModule_C_nonneg g (sub_nonneg.mpr hscale))
  have hsum := GenQuadraticModule_add hbase hconstant
  refine ⟨r, ?_, ?_⟩
  · simpa only using
      QuarticConvergence.quarticInverseOrder_lt r₀ hA.le hepsilon
  · have heq :
        p + C (A / (r : ℝ) ^ 4) +
            C (epsilon - A / (r : ℝ) ^ 4) =
          p + C epsilon := by
      rw [map_sub]
      ring
    rw [← heq]
    exact hsum

theorem lasserreQuarticRateWithEqualities
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
  CQCInternal.lasserreQuarticRateWithEqualities_proof
    hn g f hne harch hcqc

end OptimalConvergenceRates.CQCMainResultsProofs

end
