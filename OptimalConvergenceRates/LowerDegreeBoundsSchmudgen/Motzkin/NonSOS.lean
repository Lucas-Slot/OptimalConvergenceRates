/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/Motzkin/NonSOS.lean

  The Motzkin sextic is not a sum of squares.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.HomogeneousJets

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

private lemma degree_eq_sum_n3 (a : Fin 3 →₀ ℕ) :
    a.degree = a.sum (fun _ e ↦ e) := rfl

private lemma coeff_homogeneousPart3_degree (m : ℕ)
    (q : MvPolynomial (Fin 3) ℝ) (a : Fin 3 →₀ ℕ) :
    coeff a (homogeneousPart3 m q) = if a.degree = m then coeff a q else 0 := by
  simpa only [degree_eq_sum_n3] using coeff_homogeneousPart3 m q a

/-- At degree six, the square of a polynomial of degree at most three only sees
its homogeneous cubic part. -/
lemma homogeneousPart3_sq_six_of_totalDegree_le_three
    (q : MvPolynomial (Fin 3) ℝ) (hq : q.totalDegree ≤ 3) :
    homogeneousPart3 6 (q ^ 2) = homogeneousPart3 3 q ^ 2 := by
  ext a
  rw [coeff_homogeneousPart3_degree]
  by_cases ha6 : a.degree = 6
  · rw [if_pos ha6]
    simp only [pow_two, MvPolynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro bc hbc
    rw [Finset.mem_antidiagonal] at hbc
    by_cases hb : coeff bc.1 q = 0
    · simp [coeff_homogeneousPart3_degree, hb]
    by_cases hc : coeff bc.2 q = 0
    · simp [coeff_homogeneousPart3_degree, hc]
    have hbmem : bc.1 ∈ q.support := MvPolynomial.mem_support_iff.mpr hb
    have hcmem : bc.2 ∈ q.support := MvPolynomial.mem_support_iff.mpr hc
    have hbdeg : bc.1.degree ≤ 3 := (MvPolynomial.le_totalDegree hbmem).trans hq
    have hcdeg : bc.2.degree ≤ 3 := (MvPolynomial.le_totalDegree hcmem).trans hq
    have hsum : bc.1.degree + bc.2.degree = 6 := by
      rw [← map_add, hbc, ha6]
    have hb3 : bc.1.degree = 3 := by omega
    have hc3 : bc.2.degree = 3 := by omega
    simp [coeff_homogeneousPart3_degree, hb3, hc3]
  · rw [if_neg ha6, pow_two, MvPolynomial.coeff_mul]
    symm
    apply Finset.sum_eq_zero
    intro bc hbc
    rw [Finset.mem_antidiagonal] at hbc
    rw [coeff_homogeneousPart3_degree, coeff_homogeneousPart3_degree]
    by_cases hb3 : bc.1.degree = 3 <;> by_cases hc3 : bc.2.degree = 3
    · exfalso
      apply ha6
      rw [← hbc, map_add, hb3, hc3]
    · simp [hc3]
    · simp [hb3]
    · simp [hb3, hc3]
/-- Taking degree six in an SOS representation of the Motzkin sextic gives an
SOS representation by homogeneous cubic forms. -/
lemma motzkinSextic_eq_cubicParts_sq
    {N : ℕ} {Q : Fin N → MvPolynomial (Fin 3) ℝ}
    (hQ : motzkinSextic = ∑ i : Fin N, (Q i) ^ 2) :
    motzkinSextic = ∑ i : Fin N, (homogeneousPart3 3 (Q i)) ^ 2 := by
  have hdeg := motzkinSosSummand_totalDegree_le_three hQ
  have hhomM : homogeneousPart3 6 motzkinSextic = motzkinSextic := by
    rw [homogeneousPart3_eq_homogeneousComponent]
    have hmotzkin : motzkinSextic.IsHomogeneous 6 := by
      have hx2 : (X (0 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 :=
        MvPolynomial.isHomogeneous_X_pow _ _
      have hx4 : (X (0 : Fin 3) ^ 4 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 4 :=
        MvPolynomial.isHomogeneous_X_pow _ _
      have hy2 : (X (1 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 :=
        MvPolynomial.isHomogeneous_X_pow _ _
      have hy4 : (X (1 : Fin 3) ^ 4 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 4 :=
        MvPolynomial.isHomogeneous_X_pow _ _
      have hz2 : (X (2 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 :=
        MvPolynomial.isHomogeneous_X_pow _ _
      have hz6 : (X (2 : Fin 3) ^ 6 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 6 :=
        MvPolynomial.isHomogeneous_X_pow _ _
      have hneg :
          (3 * X (0 : Fin 3) ^ 2 * X (1 : Fin 3) ^ 2 * X (2 : Fin 3) ^ 2 :
            MvPolynomial (Fin 3) ℝ).IsHomogeneous 6 := by
        simpa [Nat.add_assoc] using (((hx2.C_mul 3).mul hy2).mul hz2)
      simpa [motzkinSextic, Nat.add_assoc] using
        (((hx4.mul hy2).add (hx2.mul hy4)).add hz6).sub hneg
    simpa using (MvPolynomial.homogeneousComponent_of_mem (m := 6) hmotzkin)
  calc
    motzkinSextic = homogeneousPart3 6 motzkinSextic := hhomM.symm
    _ = homogeneousPart3 6 (∑ i : Fin N, (Q i) ^ 2) := by rw [hQ]
    _ = ∑ i : Fin N, homogeneousPart3 6 ((Q i) ^ 2) := by
      simpa using homogeneousPart3_sum 6 Finset.univ (fun i ↦ (Q i) ^ 2)
    _ = ∑ i : Fin N, (homogeneousPart3 3 (Q i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact homogeneousPart3_sq_six_of_totalDegree_le_three (Q i) (hdeg i)

end Motzkin

end OptimalConvergenceRates

end
