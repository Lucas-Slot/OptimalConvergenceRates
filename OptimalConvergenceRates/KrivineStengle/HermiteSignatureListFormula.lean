/-
  OptimalConvergenceRates/KrivineStengle/HermiteSignatureListFormula.lean

  Finite formulas for exact sums of specialized Hermite signatures.
-/
import OptimalConvergenceRates.KrivineStengle.HermiteSignatureFormula
import OptimalConvergenceRates.KrivineStengle.MatrixSignature

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- Every integer that can occur as the signature of a `d`-dimensional
matrix. -/
def signatureValues (d : ℕ) : List ℤ :=
  (Finset.Icc (-(d : ℤ)) (d : ℤ)).toList

@[simp] theorem mem_signatureValues_iff (d : ℕ) (s : ℤ) :
    s ∈ signatureValues d ↔ -(d : ℤ) ≤ s ∧ s ≤ (d : ℤ) := by
  simp [signatureValues]

/-- Formula saying that the sum of the Hermite signatures associated to
the list `hs` is exactly `total`. Each recursive branch enumerates only
the finite interval of possible `d`-dimensional signatures. -/
def hermiteSignatureListSumFormula {n : ℕ}
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ) :
    List ((MvPolynomial (Fin n) ℝ)[X]) → ℤ → SignFormula n
  | [], total => if total = 0 then trueSignFormula n else falseSignFormula n
  | h :: hs, total =>
      SignFormula.any ((signatureValues d).map fun s ↦
        .conj (guardedHermiteSignatureFormula f h d s)
          (hermiteSignatureListSumFormula f d hs (total - s)))

/-- Correctness of the exact finite Hermite-signature sum formula. -/
theorem realizes_hermiteSignatureListSumFormula_iff
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (f : (MvPolynomial (Fin n) ℝ)[X]) (d : ℕ)
    (hs : List ((MvPolynomial (Fin n) ℝ)[X])) (total : ℤ)
    (hdegree : ActualDegreeCondition coeff x f d) :
    (hermiteSignatureListSumFormula f d hs total).Realizes coeff x ↔
      (hs.map fun h ↦
        hermiteSignature
          (monicNormalizeSpecialization coeff x f d)
          (specializePolynomial coeff x h)
          (monic_monicNormalizeSpecialization coeff x f d hdegree)).sum = total := by
  induction hs generalizing total with
  | nil =>
      by_cases htotal : total = 0
      · simp [hermiteSignatureListSumFormula, htotal, trueSignFormula]
      · have hzero : (0 : ℤ) ≠ total := fun h ↦ htotal h.symm
        simp [hermiteSignatureListSumFormula, htotal, hzero, falseSignFormula]
  | cons h hs ih =>
      rw [hermiteSignatureListSumFormula, SignFormula.realizes_any]
      constructor
      · rintro ⟨formula, hformula, hrealizes⟩
        obtain ⟨s, hsMem, rfl⟩ := List.mem_map.mp hformula
        rw [SignFormula.realizes_conj,
          realizes_guardedHermiteSignatureFormula_iff
            coeff x f h d s hdegree,
          ih (total - s)] at hrealizes
        simp only [List.map_cons, List.sum_cons]
        omega
      · intro hsum
        let p := monicNormalizeSpecialization coeff x f d
        let hp := monic_monicNormalizeSpecialization coeff x f d hdegree
        let q := specializePolynomial coeff x h
        let s := hermiteSignature p q hp
        have hpDegree : p.natDegree = d := by
          exact natDegree_monicNormalizeSpecialization coeff x f d hdegree
        have hsBounds : -(d : ℤ) ≤ s ∧ s ≤ (d : ℤ) := by
          simpa [s, hermiteSignature, hpDegree] using
            matrixSignature_bounds (hermiteTraceMatrix p q hp)
        have hsMem : s ∈ signatureValues d :=
          (mem_signatureValues_iff d s).2 hsBounds
        refine ⟨_, List.mem_map.mpr ⟨s, hsMem, rfl⟩, ?_⟩
        rw [SignFormula.realizes_conj,
          realizes_guardedHermiteSignatureFormula_iff
            coeff x f h d s hdegree,
          ih (total - s)]
        constructor
        · rfl
        · simp only [List.map_cons, List.sum_cons] at hsum
          change s + _ = total at hsum
          omega

end OptimalConvergenceRates.KrivineStengle

end
