import OptimalConvergenceRates.CQC.Transfer

noncomputable section
open MvPolynomial
namespace OptimalConvergenceRates.CQCInternal
open GeneralArchimedean
variable {n m : ℕ}

theorem fixedInstanceTransfer_internal
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
              (Clog * (1 + Real.log (1 / ε)))) := by
  obtain ⟨P, a, c, C₀, s, hc, hC₀, hP, hPdegree, ha, hPzero, hraw⟩ :=
    exists_fixedInstanceTransfer_raw hn hne harch hcqc hp
  let Clog : ℝ := (s : ℝ) + 2 + C₀ * (1 + Real.log c)
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hClog : 0 < Clog := by
    dsimp [Clog]
    positivity
  refine ⟨P, c, Clog, hc, hClog, hP, hPdegree hm, hPzero, ?_⟩
  intro ε hε hεhalf r hbox
  have hrawCert := hraw hε hεhalf hbox
  have hinv : 1 ≤ 1 / ε := by
    rw [one_div]
    exact (one_le_inv₀ hε).2 (by linarith)
  have hloginv : 0 ≤ Real.log (1 / ε) := Real.log_nonneg hinv
  have hL : 1 ≤ 1 + Real.log (1 / ε) := by linarith
  have hlogFormula : Real.log (c / ε) =
      Real.log c + Real.log (1 / ε) := by
    rw [show c / ε = c * (1 / ε) by ring,
      Real.log_mul (zero_lt_one.trans_le hc).ne' (one_div_ne_zero hε.ne')]
  let A : ℝ := C₀ * (1 + Real.log (c / ε))
  have hA : 0 ≤ A := by
    dsimp [A]
    rw [hlogFormula]
    positivity
  have hceilA : (Nat.ceil A : ℝ) ≤ A + 1 :=
    (Nat.ceil_lt_add_one hA).le
  have hrealOrder : ((s + Nat.ceil A : ℕ) : ℝ) ≤
      Clog * (1 + Real.log (1 / ε)) := by
    push_cast
    calc
      (s : ℝ) + (Nat.ceil A : ℝ) ≤ (s : ℝ) + (A + 1) := by linarith
      _ ≤ Clog * (1 + Real.log (1 / ε)) := by
        dsimp [A, Clog]
        rw [hlogFormula]
        nlinarith [mul_nonneg hC₀.le hloginv]
  have hceilTarget : ((s + Nat.ceil A : ℕ) : ℝ) ≤
      (Nat.ceil (Clog * (1 + Real.log (1 / ε))) : ℝ) :=
    hrealOrder.trans (Nat.le_ceil _)
  have hnatOrder : s + Nat.ceil A ≤
      Nat.ceil (Clog * (1 + Real.log (1 / ε))) := by
    exact_mod_cast hceilTarget
  rw [hlogFormula] at hrawCert
  apply GenQuadraticModule_mono _ hrawCert
  dsimp [A] at hnatOrder
  rw [hlogFormula] at hnatOrder
  omega

end OptimalConvergenceRates.CQCInternal
end


