import OptimalConvergenceRates.CQC.CertificateOrder
import OptimalConvergenceRates.CQC.TransferAbsorption

/-! # Least-order form of the fixed-instance CQC transfer -/

noncomputable section
open MvPolynomial
namespace OptimalConvergenceRates.CQCInternal
open GeneralArchimedean

variable {n m : ℕ}

/-- The certificate implication yields the corresponding inequality between
least certificate orders whenever the positive cube perturbation has a
certificate. -/
theorem fixedInstanceTransferOrder_internal
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
              Nat.ceil (Clog * (1 + Real.log (1 / ε))) := by
  obtain ⟨P, c, Clog, hc, hClog, hP, _hPdegree, hPzero, htransfer⟩ :=
    fixedInstanceTransfer_internal hn hm hne harch hcqc hp
  refine ⟨P, c, Clog, hc, hClog, hP, hPzero, ?_⟩
  intro ε hε hεhalf hboxExists
  apply quadraticModuleOrder_le
  exact htransfer hε hεhalf (boxQuadraticModuleOrder_mem hboxExists)

end OptimalConvergenceRates.CQCInternal
end


