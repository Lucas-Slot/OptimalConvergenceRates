import OptimalConvergenceRates.CQC.ModulePullback
import OptimalConvergenceRates.CQC.MultiplierRemovalTheorem
import OptimalConvergenceRates.CQC.LiftDegree
import OptimalConvergenceRates.CQC.ZeroMinimum

noncomputable section
open MvPolynomial
namespace OptimalConvergenceRates
namespace CQCInternal
open GeneralArchimedean
variable {n m : ℕ}

theorem exists_fixedInstanceTransfer_raw
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : ActiveGradientIndependent g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ P : MvPolynomial (Fin (n + m)) ℝ,
      ∃ a : MvPolynomial (Fin n) ℝ,
      ∃ c Clog : ℝ, ∃ s : ℕ,
        1 ≤ c ∧ 0 < Clog ∧
        IsNonnegOn P (Hypercube (n + m)) ∧
        (0 < m → ∀ {e d : ℕ}, 2 ≤ e →
          (∀ i, (g i).totalDegree ≤ e) → p.totalDegree ≤ d →
          P.totalDegree ≤ d + 4 * m * (e - 1)) ∧
        (∀ x ∈ KrivineStengle.basicClosedSet g,
          0 < MvPolynomial.eval x a) ∧
        ((∃ x ∈ KrivineStengle.basicClosedSet g,
            MvPolynomial.eval x p = 0) →
          ∃ z ∈ Hypercube (n + m), MvPolynomial.eval z P = 0) ∧
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 → ∀ {r : ℕ},
          P + C (ε / c) ∈ BoxQuadraticModule (n + m) r →
          p + C ε ∈ GenQuadraticModule g
            ((s + generatorDegree g * r) +
              Nat.ceil (Clog * (1 + Real.log (c / ε)))) := by
  obtain ⟨R, M, hR, -, hPbox, hbase, hslack, hpull, ha⟩ :=
    exists_descendedSlackObjective hn hne harch hcqc hp
  let Pdesc := descendedSlackObjective g p M
  let P := unitBoxLiftPolynomial R Pdesc
  let a := determinantMultiplier g
  have hPnonneg : IsNonnegOn P (Hypercube (n + m)) :=
    unitBoxLiftPolynomial_nonneg_on_hypercube hR hPbox
  have hPdegree : 0 < m → ∀ {e d : ℕ}, 2 ≤ e →
      (∀ i, (g i).totalDegree ≤ e) → p.totalDegree ≤ d →
      P.totalDegree ≤ d + 4 * m * (e - 1) := by
    intro hm e d he hg hpdegree
    exact totalDegree_unitBoxLiftPolynomial_descended_le
      hm he g p M R hg hpdegree
  have hPzero :
      (∃ x ∈ KrivineStengle.basicClosedSet g,
          MvPolynomial.eval x p = 0) →
        ∃ z ∈ Hypercube (n + m), MvPolynomial.eval z P = 0 := by
    intro hzero
    exact exists_cube_zero_of_exists_feasible_zero hR hbase hslack hzero
  obtain ⟨s, hmodule⟩ := unitCube_certificate_pullback
    hR g hne harch hbase hslack
  obtain ⟨c₀, Clog, hc₀, hClog, hremove⟩ :=
    removePositiveMultiplier_log g p a hne harch ha
  let c : ℝ := max c₀ 1
  have hc : 1 ≤ c := le_max_right _ _
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hc₀c : c₀ ≤ c := le_max_left _ _
  refine ⟨P, a, c, Clog, s, hc, hClog, hPnonneg, hPdegree, ha, hPzero, ?_⟩
  intro ε hε hεhalf r hbox
  let δ : ℝ := ε / c
  have hδ : 0 < δ := div_pos hε hcpos
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    calc
      ε / c ≤ ε := (div_le_iff₀ hcpos).2 (by nlinarith)
      _ ≤ 1 / 2 := hεhalf
  have hpulled := hmodule hbox
  have hweighted : a ^ 2 * p + C δ ∈
      GenQuadraticModule g (s + generatorDegree g * r) := by
    convert hpulled using 1
    simp only [P, Pdesc, map_add, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
    rw [unitCubePullback_unitBoxLiftPolynomial hR.ne' g,
      generatorSlackSubstitution_descendedSlackObjective]
  have hremoved := hremove hδ hδhalf hweighted
  have hgap : 0 ≤ ε - c₀ * δ := by
    dsimp [δ]
    have hratio : c₀ / c ≤ 1 := (div_le_one hcpos).2 hc₀c
    have hfactor : 0 ≤ 1 - c₀ / c := sub_nonneg.mpr hratio
    calc
      0 ≤ ε * (1 - c₀ / c) := mul_nonneg hε.le hfactor
      _ = ε - c₀ * (ε / c) := by field_simp
  have hconst := genQuadraticModule_C_nonneg g hgap
  have hsum := genQuadraticModule_add hremoved hconst
  have htarget : p + C ε ∈ GenQuadraticModule g
      (max ((s + generatorDegree g * r) + Nat.ceil
        (Clog * (1 + Real.log (1 / δ)))) 0) := by
    have hC : (C ε : MvPolynomial (Fin n) ℝ) =
        C (c₀ * δ) + C (ε - c₀ * δ) := by
      rw [← map_add]
      congr 1
      ring
    rw [hC]
    simpa only [add_assoc] using hsum
  have hlog : 1 / δ = c / ε := by
    dsimp [δ]
    field_simp
  simpa [hlog] using htarget

end CQCInternal
end OptimalConvergenceRates
end


