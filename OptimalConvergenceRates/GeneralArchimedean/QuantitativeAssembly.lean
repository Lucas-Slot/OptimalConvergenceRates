/-
  Degree-tracked assembly of Chebyshev elimination from a truncated
  quadratic-module refutation over one appended perturbation generator.
-/
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanEnvelopeDegree
import OptimalConvergenceRates.GeneralArchimedean.ChebyshevWeight
import OptimalConvergenceRates.GeneralArchimedean.GeneratorExtension
import OptimalConvergenceRates.GeneralArchimedean.Stengle
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeBridge

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- Common truncation order produced by the tracked elimination argument. -/
def perturbationEliminationOrder
    (degreeP refutationOrder envelopeOrder chebyshevOrder : ℕ) : ℕ :=
  max
    (refutationOrder + 2 * chebyshevOrder * degreeP)
    (max
      (envelopeOrder + 2 * refutationOrder +
        (1 + 2 * chebyshevOrder) * degreeP)
      (envelopeOrder + 2 * degreeP +
        2 * (1 + 2 * chebyshevOrder) * degreeP +
        refutationOrder))

/-- A truncated refutation over the appended constraint
`-p-epsilon` yields a certificate for `p+2*epsilon` at a completely
explicit order. This theorem retains exactly the data consumed by the
quantitative preordering-to-module conversion. -/
theorem putinar_of_truncated_perturbation_refutation
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g))
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {refutationOrder : ℕ}
    (hrefute : (-1 : MvPolynomial (Fin n) ℝ) ∈
      GenQuadraticModule
        (KrivineStengle.appendGenerator g
          (KrivineStengle.perturbationGenerator p epsilon))
        refutationOrder) :
    ∃ (B : ℝ) (envelopeOrder : ℕ) (Czero U : ℝ),
      1 ≤ B ∧ 0 < Czero ∧ 0 < U ∧
        p + C (2 * epsilon) ∈
          GenQuadraticModule g
            (perturbationEliminationOrder p.totalDegree refutationOrder
              envelopeOrder
              (chebyshevDegree epsilon Czero⁻¹ U)) := by
  let h := KrivineStengle.perturbationGenerator p epsilon
  have hh : h ≠ 0 := by
    exact perturbationGenerator_ne_zero g p hne hp hepsilon
  obtain ⟨s, t, hs, ht, htDegree, hrefuteSplit⟩ :=
    split_appendGenerator_refutation_at_degree hh
      (by simpa [h] using hrefute)
  have hrefuteNormalized :
      (-1 : MvPolynomial (Fin n) ℝ) =
        s - (p + C epsilon) * t := by
    calc
      (-1 : MvPolynomial (Fin n) ℝ) = s + h * t :=
        hrefuteSplit
      _ = s - (p + C epsilon) * t := by
        dsimp [h, KrivineStengle.perturbationGenerator]
        ring
  obtain ⟨B, envelopeOrder, hB, hcoord⟩ :=
    harch.exists_truncated_coordinate_square_bound
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  let Czero : ℝ := 1 + weightedCoeffEnvelope B t
  have hCzero : 0 < Czero := by
    have henv := weightedCoeffEnvelope_nonneg hB0 t
    dsimp [Czero]
    linarith
  have hCzero_t :
      C Czero - t ∈
        GenQuadraticModule g (envelopeOrder + 2 * refutationOrder) := by
    have hbase := weightedCoeffEnvelope_minus_mem_at hB0 hcoord t
    have hbase' :
        C (weightedCoeffEnvelope B t) - t ∈
          GenQuadraticModule g (envelopeOrder + 2 * refutationOrder) :=
      GenQuadraticModule_mono
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 htDegree) envelopeOrder)
        hbase
    have hone : C (1 : ℝ) ∈ GenQuadraticModule g 0 :=
      genQuadraticModule_C_nonneg g zero_le_one
    have hone' := GenQuadraticModule_mono
      (Nat.zero_le (envelopeOrder + 2 * refutationOrder)) hone
    have hsum := GenQuadraticModule_add hbase' hone'
    have hsum' :
        (C (weightedCoeffEnvelope B t) - t) + C (1 : ℝ) ∈
          GenQuadraticModule g (envelopeOrder + 2 * refutationOrder) := by
      simpa using hsum
    convert hsum' using 1
    dsimp [Czero]
    rw [map_add, map_one]
    ring
  have hone_tau :
      1 - C Czero⁻¹ * t ∈
        GenQuadraticModule g (envelopeOrder + 2 * refutationOrder) := by
    have hinvSOS : IsSOS
        (C Czero⁻¹ : MvPolynomial (Fin n) ℝ) :=
      IsSOS_C_nonneg Czero⁻¹ (inv_nonneg.mpr hCzero.le)
    have hscaled := genQuadraticModule_sos_mul hinvSOS hCzero_t
    have hscaled' :
        C Czero⁻¹ * (C Czero - t) ∈
          GenQuadraticModule g (envelopeOrder + 2 * refutationOrder) := by
      simpa using hscaled
    rw [show 1 - C Czero⁻¹ * t =
        C Czero⁻¹ * (C Czero - t) by
      rw [mul_sub, ← map_mul, inv_mul_cancel₀ hCzero.ne', map_one]]
    exact hscaled'
  let q : MvPolynomial (Fin n) ℝ := p + C epsilon
  have hqDegree : q.totalDegree ≤ p.totalDegree := by
    dsimp [q]
    exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  let U : ℝ := 1 + weightedCoeffEnvelope B q
  have hU : 0 < U := by
    have henv := weightedCoeffEnvelope_nonneg hB0 q
    dsimp [U]
    linarith
  have hUq :
      C U - q ∈
        GenQuadraticModule g (envelopeOrder + 2 * p.totalDegree) := by
    have hbase := weightedCoeffEnvelope_minus_mem_at hB0 hcoord q
    have hbase' :
        C (weightedCoeffEnvelope B q) - q ∈
          GenQuadraticModule g (envelopeOrder + 2 * p.totalDegree) :=
      GenQuadraticModule_mono
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hqDegree) envelopeOrder)
        hbase
    have hone : C (1 : ℝ) ∈ GenQuadraticModule g 0 :=
      genQuadraticModule_C_nonneg g zero_le_one
    have hone' := GenQuadraticModule_mono
      (Nat.zero_le (envelopeOrder + 2 * p.totalDegree)) hone
    have hsum := GenQuadraticModule_add hbase' hone'
    have hsum' :
        (C (weightedCoeffEnvelope B q) - q) + C (1 : ℝ) ∈
          GenQuadraticModule g (envelopeOrder + 2 * p.totalDegree) := by
      simpa using hsum
    convert hsum' using 1
    dsimp [U]
    rw [map_add, map_one]
    ring
  obtain ⟨W, hWDegree⟩ :=
    chebyshevEliminationWeight_exists hepsilon (inv_pos.mpr hCzero) hU
  have hcert := eliminate_refutation_of_weight_at_bound
    p s t epsilon Czero U hCzero hepsilon.le hrefuteNormalized hs ht
    hone_tau (by simpa [q] using hUq) W hWDegree hqDegree htDegree
  refine ⟨B, envelopeOrder, Czero, U, hB, hCzero, hU, ?_⟩
  simpa [perturbationEliminationOrder] using hcert

/-- An explicit upper envelope for the appended-generator multiplier of a
bounded refutation certificate. -/
def boundedMultiplierEnvelope (n r : ℕ) (B H : ℝ) : ℝ :=
  1 + polynomialEnvelopeBound n r B H

/-- An epsilon-uniform upper envelope for `p + epsilon` when
`0 < epsilon ≤ 1`. -/
def boundedObjectiveEnvelope
    (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (B : ℝ) : ℝ :=
  1 + polynomialEnvelopeBound n p.totalDegree B (coeffL1Norm p + 1)

/-- A bounded appended-generator refutation gives Chebyshev elimination with
all quantities affecting the output order explicit. -/
theorem putinar_of_bounded_perturbation_refutation_of_coordinate_bounds
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g))
    {B : ℝ} {envelopeOrder : ℕ}
    (hB : 1 ≤ B)
    (hcoord : ∀ i : Fin n,
      C B - X i ^ 2 ∈ GenQuadraticModule g envelopeOrder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    {refutationOrder : ℕ} {H : ℝ}
    (hrefute : BoundedQuadraticModuleCertificate
      (KrivineStengle.appendGenerator g
        (KrivineStengle.perturbationGenerator p epsilon))
      (-1 : MvPolynomial (Fin n) ℝ) refutationOrder H) :
    p + C (2 * epsilon) ∈
      GenQuadraticModule g
        (perturbationEliminationOrder p.totalDegree refutationOrder
          envelopeOrder
          (chebyshevDegree epsilon
            (boundedMultiplierEnvelope n refutationOrder B H)⁻¹
            (boundedObjectiveEnvelope n p B))) := by
  let h := KrivineStengle.perturbationGenerator p epsilon
  have hh : h ≠ 0 :=
    perturbationGenerator_ne_zero g p hne hp hepsilon
  obtain ⟨s, t, hs, ht, htDegree, htNorm, hrefuteSplit⟩ :=
    hrefute.split_appendGenerator_refutation_at_degree hh
  have hrefuteNormalized :
      (-1 : MvPolynomial (Fin n) ℝ) =
        s - (p + C epsilon) * t := by
    calc
      (-1 : MvPolynomial (Fin n) ℝ) = s + h * t :=
        hrefuteSplit
      _ = s - (p + C epsilon) * t := by
        dsimp [h, KrivineStengle.perturbationGenerator]
        ring
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hH : 0 ≤ H := hrefute.bound_nonneg
  let Czero := boundedMultiplierEnvelope n refutationOrder B H
  have hCzero : 0 < Czero := by
    dsimp [Czero, boundedMultiplierEnvelope, polynomialEnvelopeBound]
    positivity
  have henvT :
      weightedCoeffEnvelope B t ≤
        polynomialEnvelopeBound n refutationOrder B H :=
    weightedCoeffEnvelope_le_polynomialEnvelopeBound
      hB hH t htDegree htNorm
  have hCzero_t :
      C Czero - t ∈
        GenQuadraticModule g (envelopeOrder + 2 * refutationOrder) := by
    have hbase : ModuleLEAt g
        (envelopeOrder + 2 * t.totalDegree) t
        (C (weightedCoeffEnvelope B t)) := by
      change C (weightedCoeffEnvelope B t) - t ∈
        GenQuadraticModule g (envelopeOrder + 2 * t.totalDegree)
      exact weightedCoeffEnvelope_minus_mem_at hB0 hcoord t
    have hbase' :
        ModuleLEAt g (envelopeOrder + 2 * refutationOrder) t
          (C (weightedCoeffEnvelope B t)) := by
      apply hbase.mono
      exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 htDegree)
        envelopeOrder
    have hupper : ModuleLEAt g 0
        (C (weightedCoeffEnvelope B t))
        (C (polynomialEnvelopeBound n refutationOrder B H)) :=
      ModuleLEAt.constant henvT
    have hle : ModuleLEAt g (envelopeOrder + 2 * refutationOrder) t
        (C (polynomialEnvelopeBound n refutationOrder B H)) := by
      simpa using hbase'.trans hupper
    have hone : C (1 : ℝ) ∈ GenQuadraticModule g 0 :=
      genQuadraticModule_C_nonneg g zero_le_one
    have hsum := GenQuadraticModule_add hle
      (GenQuadraticModule_mono
        (Nat.zero_le (envelopeOrder + 2 * refutationOrder)) hone)
    convert hsum using 1
    dsimp [Czero, boundedMultiplierEnvelope, ModuleLEAt]
    rw [map_add, map_one]
    ring
  have hone_tau :
      1 - C Czero⁻¹ * t ∈
        GenQuadraticModule g (envelopeOrder + 2 * refutationOrder) := by
    have hinvSOS : IsSOS
        (C Czero⁻¹ : MvPolynomial (Fin n) ℝ) :=
      IsSOS_C_nonneg Czero⁻¹ (inv_nonneg.mpr hCzero.le)
    have hscaled := genQuadraticModule_sos_mul hinvSOS hCzero_t
    rw [show 1 - C Czero⁻¹ * t =
        C Czero⁻¹ * (C Czero - t) by
      rw [mul_sub, ← map_mul, inv_mul_cancel₀ hCzero.ne', map_one]]
    simpa using hscaled
  let q : MvPolynomial (Fin n) ℝ := p + C epsilon
  have hqDegree : q.totalDegree ≤ p.totalDegree := by
    dsimp [q]
    exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  have hqNorm : coeffL1Norm q ≤ coeffL1Norm p + 1 := by
    calc
      coeffL1Norm q ≤ coeffL1Norm p + coeffL1Norm
          (C epsilon : MvPolynomial (Fin n) ℝ) := by
        simpa [q] using coeffL1Norm_add_le p
          (C epsilon : MvPolynomial (Fin n) ℝ)
      _ ≤ coeffL1Norm p + |epsilon| :=
        add_le_add_right (coeffL1Norm_C_le (n := n) epsilon) _
      _ ≤ coeffL1Norm p + 1 := by
        rw [abs_of_pos hepsilon]
        linarith
  let U := boundedObjectiveEnvelope n p B
  have hU : 0 < U := by
    dsimp [U, boundedObjectiveEnvelope, polynomialEnvelopeBound]
    positivity
  have henvQ :
      weightedCoeffEnvelope B q ≤
        polynomialEnvelopeBound n p.totalDegree B (coeffL1Norm p + 1) :=
    weightedCoeffEnvelope_le_polynomialEnvelopeBound
      hB (by linarith [coeffL1Norm_nonneg p]) q hqDegree hqNorm
  have hUq :
      C U - q ∈
        GenQuadraticModule g (envelopeOrder + 2 * p.totalDegree) := by
    have hbase : ModuleLEAt g
        (envelopeOrder + 2 * q.totalDegree) q
        (C (weightedCoeffEnvelope B q)) := by
      change C (weightedCoeffEnvelope B q) - q ∈
        GenQuadraticModule g (envelopeOrder + 2 * q.totalDegree)
      exact weightedCoeffEnvelope_minus_mem_at hB0 hcoord q
    have hbase' :
        ModuleLEAt g (envelopeOrder + 2 * p.totalDegree) q
          (C (weightedCoeffEnvelope B q)) := by
      apply hbase.mono
      exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hqDegree)
        envelopeOrder
    have hupper : ModuleLEAt g 0
        (C (weightedCoeffEnvelope B q))
        (C (polynomialEnvelopeBound n p.totalDegree B
          (coeffL1Norm p + 1))) :=
      ModuleLEAt.constant henvQ
    have hle : ModuleLEAt g (envelopeOrder + 2 * p.totalDegree) q
        (C (polynomialEnvelopeBound n p.totalDegree B
          (coeffL1Norm p + 1))) := by
      simpa using hbase'.trans hupper
    have hone : C (1 : ℝ) ∈ GenQuadraticModule g 0 :=
      genQuadraticModule_C_nonneg g zero_le_one
    have hsum := GenQuadraticModule_add hle
      (GenQuadraticModule_mono
        (Nat.zero_le (envelopeOrder + 2 * p.totalDegree)) hone)
    convert hsum using 1
    dsimp [U, boundedObjectiveEnvelope, ModuleLEAt]
    rw [map_add, map_one]
    ring
  obtain ⟨W, hWDegree⟩ :=
    chebyshevEliminationWeight_exists hepsilon (inv_pos.mpr hCzero) hU
  have hcert := eliminate_refutation_of_weight_at_bound
    p s t epsilon Czero U hCzero hepsilon.le hrefuteNormalized hs ht
    hone_tau (by simpa [q] using hUq) W hWDegree hqDegree htDegree
  simpa [perturbationEliminationOrder, Czero, U] using hcert

/-- Archimedean wrapper around the fixed-coordinate bounded elimination
theorem. -/
theorem putinar_of_bounded_perturbation_refutation
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    {refutationOrder : ℕ} {H : ℝ}
    (hrefute : BoundedQuadraticModuleCertificate
      (KrivineStengle.appendGenerator g
        (KrivineStengle.perturbationGenerator p epsilon))
      (-1 : MvPolynomial (Fin n) ℝ) refutationOrder H) :
    ∃ (B : ℝ) (envelopeOrder : ℕ),
      1 ≤ B ∧
        p + C (2 * epsilon) ∈
          GenQuadraticModule g
            (perturbationEliminationOrder p.totalDegree refutationOrder
              envelopeOrder
              (chebyshevDegree epsilon
                (boundedMultiplierEnvelope n refutationOrder B H)⁻¹
                (boundedObjectiveEnvelope n p B))) := by
  obtain ⟨B, envelopeOrder, hB, hcoord⟩ :=
    harch.exists_truncated_coordinate_square_bound
  exact ⟨B, envelopeOrder, hB,
    putinar_of_bounded_perturbation_refutation_of_coordinate_bounds
      g p hne hp hB hcoord hepsilon hepsilon1 hrefute⟩



end OptimalConvergenceRates.GeneralArchimedean

end
