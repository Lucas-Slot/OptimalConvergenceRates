/-
  OptimalConvergenceRates/KrivineStengle/PositiveHermiteSignatureFormula.lean

  A finite sign formula for positivity of a sum of Hermite signatures.
-/
import OptimalConvergenceRates.KrivineStengle.HermiteSignatureListFormula

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- All positive totals attainable by a list of `count` signatures of
`d`-dimensional matrices. -/
def positiveSignatureTotals (d count : ℕ) : List ℤ :=
  (Finset.Icc (1 : ℤ) ((d : ℤ) * (count : ℤ))).toList

@[simp] theorem mem_positiveSignatureTotals_iff (d count : ℕ) (s : ℤ) :
    s ∈ positiveSignatureTotals d count ↔
      0 < s ∧ s ≤ (d : ℤ) * (count : ℤ) := by
  simp only [positiveSignatureTotals, Finset.mem_toList, Finset.mem_Icc]
  omega

theorem hermiteSignatureList_sum_le
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hs : List ((MvPolynomial (Fin n) ℝ)[X]))
    (hdegree : ActualDegreeCondition coeff x f d) :
    (hs.map fun h ↦
      hermiteSignature
        (monicNormalizeSpecialization coeff x f d)
        (specializePolynomial coeff x h)
        (monic_monicNormalizeSpecialization coeff x f d hdegree)).sum ≤
      (d : ℤ) * (hs.length : ℤ) := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
      let p := monicNormalizeSpecialization coeff x f d
      let q := specializePolynomial coeff x h
      let hp := monic_monicNormalizeSpecialization coeff x f d hdegree
      have hpDegree : p.natDegree = d := by
        exact natDegree_monicNormalizeSpecialization coeff x f d hdegree
      have hhead : hermiteSignature p q hp ≤ (d : ℤ) := by
        simpa [hermiteSignature, hpDegree] using
          (matrixSignature_bounds (hermiteTraceMatrix p q hp)).2
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      change hermiteSignature p q hp + _ ≤ (d : ℤ) * ((hs.length : ℤ) + 1)
      nlinarith

/-- Formula saying that the finite sum of Hermite signatures attached to
`hs` is strictly positive. -/
def positiveHermiteSignatureListFormula {n : ℕ}
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hs : List ((MvPolynomial (Fin n) ℝ)[X])) : SignFormula n :=
  SignFormula.any ((positiveSignatureTotals d hs.length).map fun total ↦
    hermiteSignatureListSumFormula f d hs total)

/-- Correctness of the positive Hermite-signature sum formula. -/
theorem realizes_positiveHermiteSignatureListFormula_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hs : List ((MvPolynomial (Fin n) ℝ)[X]))
    (hdegree : ActualDegreeCondition coeff x f d) :
    (positiveHermiteSignatureListFormula f d hs).Realizes coeff x ↔
      0 < (hs.map fun h ↦
        hermiteSignature
          (monicNormalizeSpecialization coeff x f d)
          (specializePolynomial coeff x h)
          (monic_monicNormalizeSpecialization coeff x f d hdegree)).sum := by
  rw [positiveHermiteSignatureListFormula, SignFormula.realizes_any]
  constructor
  · rintro ⟨formula, hformula, hrealizes⟩
    obtain ⟨total, htotal, rfl⟩ := List.mem_map.mp hformula
    have hsum := (realizes_hermiteSignatureListSumFormula_iff
      coeff x f d hs total hdegree).1 hrealizes
    have hpos := (mem_positiveSignatureTotals_iff d hs.length total).1 htotal
    omega
  · intro hpos
    let total := (hs.map fun h ↦
      hermiteSignature
        (monicNormalizeSpecialization coeff x f d)
        (specializePolynomial coeff x h)
        (monic_monicNormalizeSpecialization coeff x f d hdegree)).sum
    have hupper : total ≤ (d : ℤ) * (hs.length : ℤ) := by
      exact hermiteSignatureList_sum_le coeff x f d hs hdegree
    have hmem : total ∈ positiveSignatureTotals d hs.length :=
      (mem_positiveSignatureTotals_iff d hs.length total).2 ⟨hpos, hupper⟩
    refine ⟨_, List.mem_map.mpr ⟨total, hmem, rfl⟩, ?_⟩
    apply (realizes_hermiteSignatureListSumFormula_iff
      coeff x f d hs total hdegree).2
    rfl

end OptimalConvergenceRates.KrivineStengle

end
