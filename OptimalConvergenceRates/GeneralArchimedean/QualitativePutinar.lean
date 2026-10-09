/-
  End-to-end qualitative Putinar theorem assembled from the conversion
  infrastructure; the quantitative modules retain truncation and coefficient bounds.
-/
import OptimalConvergenceRates.GeneralArchimedean.ChebyshevWeight
import OptimalConvergenceRates.GeneralArchimedean.GeneratorExtension
import OptimalConvergenceRates.GeneralArchimedean.RefutationConversion
import OptimalConvergenceRates.GeneralArchimedean.Stengle

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates
namespace GeneralArchimedean

variable {n m : ℕ}

/-- Split a quadratic-module refutation after adjoining one generator into
an old-module part and the SOS multiplier of the new generator. -/
theorem split_appendGenerator_refutation
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {h : MvPolynomial (Fin n) ℝ}
    (hrefute : QuadraticModuleMem
      (KrivineStengle.appendGenerator g h) (-1)) :
    ∃ s t : MvPolynomial (Fin n) ℝ,
      QuadraticModuleMem g s ∧ IsSOS t ∧
        (-1 : MvPolynomial (Fin n) ℝ) = s + h * t := by
  obtain ⟨r, sigmaZero, sigma, hsigmaZero, hsigma,
    hdegreeZero, hdegree, hidentity⟩ := hrefute
  let s : MvPolynomial (Fin n) ℝ :=
    sigmaZero + ∑ i : Fin m, sigma i.castSucc * g i
  let t : MvPolynomial (Fin n) ℝ := sigma (Fin.last m)
  have hzero : QuadraticModuleMem g sigmaZero :=
    QuadraticModuleMem.of_isSOS g hsigmaZero
  have hterms : ∀ i : Fin m,
      QuadraticModuleMem g (sigma i.castSucc * g i) := by
    intro i
    have hgen : QuadraticModuleMem g (g i) :=
      ⟨(g i).totalDegree, genQuadraticModule_generator g i⟩
    exact QuadraticModuleMem.sos_mul (hsigma i.castSucc) hgen
  have hsum : QuadraticModuleMem g
      (∑ i : Fin m, sigma i.castSucc * g i) := by
    exact QuadraticModuleMem.sum Finset.univ
      (fun i => sigma i.castSucc * g i)
      (fun i hi => hterms i)
  have hs : QuadraticModuleMem g s := hzero.add hsum
  refine ⟨s, t, hs, hsigma (Fin.last m), ?_⟩
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

/-- A positive perturbation of a polynomial nonnegative on an Archimedean
basic closed set belongs to the untruncated quadratic module. -/
theorem qualitative_putinar_two_mul
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (harch : IsArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    QuadraticModuleMem g (p + C (2 * epsilon)) := by
  let h := KrivineStengle.perturbationGenerator p epsilon
  let g' := KrivineStengle.appendGenerator g h
  obtain ⟨w⟩ := nonnegative_krivine_stengle_witness g p hp
  have hpre : KrivineStengle.PreorderingMem g' (-1) := by
    simpa [g', h] using w.perturbation_refutation hepsilon
  have harch' : IsArchimedean g' := harch.appendGenerator h
  have hmodule : QuadraticModuleMem g' (-1) :=
    archimedean_preordering_refutation_to_module harch' hpre
  obtain ⟨s, t, hs, ht, hrefute'⟩ :=
    split_appendGenerator_refutation (g := g) (h := h) hmodule
  have hrefute :
      (-1 : MvPolynomial (Fin n) ℝ) =
        s - (p + C epsilon) * t := by
    dsimp [h, KrivineStengle.perturbationGenerator] at hrefute'
    calc
      (-1 : MvPolynomial (Fin n) ℝ) = s + (-p - C epsilon) * t :=
        hrefute'
      _ = s - (p + C epsilon) * t := by ring
  obtain ⟨R, hR, hcoord⟩ :=
    harch.exists_coordinate_square_bound
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  let Czero : ℝ := 1 + weightedCoeffEnvelope R t
  have hCzero : 0 < Czero := by
    have henv := weightedCoeffEnvelope_nonneg hR0 t
    dsimp [Czero]
    linarith
  have hCzero_t : QuadraticModuleMem g (C Czero - t) := by
    have hbase := weightedCoeffEnvelope_minus_mem hR0 hcoord t
    have hone : QuadraticModuleMem g (C 1) :=
      QuadraticModuleMem.of_isSOS g
        (IsSOS_C_nonneg 1 zero_le_one)
    convert hbase.add hone using 1
    dsimp [Czero]
    rw [map_add, map_one]
    ring
  have hone_tau : QuadraticModuleMem g
      (1 - C Czero⁻¹ * t) := by
    have hinvSOS : IsSOS
        (C Czero⁻¹ : MvPolynomial (Fin n) ℝ) :=
      IsSOS_C_nonneg Czero⁻¹ (inv_nonneg.mpr hCzero.le)
    have hscaled :=
      QuadraticModuleMem.sos_mul hinvSOS hCzero_t
    rw [show (1 - C Czero⁻¹ * t) = C Czero⁻¹ * (C Czero - t) by
      rw [mul_sub, ← map_mul, inv_mul_cancel₀ hCzero.ne', map_one]]
    exact hscaled
  let q : MvPolynomial (Fin n) ℝ := p + C epsilon
  let U : ℝ := 1 + weightedCoeffEnvelope R q
  have hU : 0 < U := by
    have henv := weightedCoeffEnvelope_nonneg hR0 q
    dsimp [U]
    linarith
  have hUq : QuadraticModuleMem g (C U - q) := by
    have hbase := weightedCoeffEnvelope_minus_mem hR0 hcoord q
    have hone : QuadraticModuleMem g (C 1) :=
      QuadraticModuleMem.of_isSOS g
        (IsSOS_C_nonneg 1 zero_le_one)
    convert hbase.add hone using 1
    rw [map_add, map_one]
    ring
  have hc : 0 < Czero⁻¹ := inv_pos.mpr hCzero
  obtain ⟨W, hWdegree⟩ :=
    chebyshevEliminationWeight_exists hepsilon hc hU
  exact eliminate_refutation_of_weight p s t epsilon Czero U
    hCzero hepsilon.le hrefute hs ht hone_tau
    (by simpa [q] using hUq) W

/-- Standard qualitative Putinar form with an arbitrary positive
perturbation. -/
theorem qualitative_putinar
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (harch : IsArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    QuadraticModuleMem g (p + C epsilon) := by
  have hhalf : 0 < epsilon / 2 := by positivity
  have h := qualitative_putinar_two_mul g p harch hp hhalf
  convert h using 1
  congr 1
  congr 1
  linarith

end GeneralArchimedean
end OptimalConvergenceRates

end
