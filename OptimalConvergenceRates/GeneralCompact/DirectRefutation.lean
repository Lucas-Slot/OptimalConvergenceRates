/-
  Direct fixed-order preordering refutations from Krivine--Stengle.
-/
import OptimalConvergenceRates.GeneralCompact.Envelope
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeRefutation

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralCompact

variable {n m : ℕ}

private def oldSubset (J : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter fun i => i.castSucc ∈ J

private def oldGeneratorProduct
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (J : Finset (Fin (m + 1))) : MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin m, if i.castSucc ∈ J then g i else 1

private theorem oldGeneratorProduct_eq
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (J : Finset (Fin (m + 1))) :
    oldGeneratorProduct g J = ∏ i ∈ oldSubset J, g i := by
  classical
  unfold oldGeneratorProduct oldSubset
  rw [Finset.prod_filter]

private theorem appendGenerator_product_eq
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (h : MvPolynomial (Fin n) ℝ)
    (J : Finset (Fin (m + 1))) :
    (∏ j ∈ J, KrivineStengle.appendGenerator g h j) =
      oldGeneratorProduct g J *
        (if Fin.last m ∈ J then h else 1) := by
  classical
  calc
    (∏ j ∈ J, KrivineStengle.appendGenerator g h j) =
        ∏ j : Fin (m + 1),
          if j ∈ J then KrivineStengle.appendGenerator g h j else 1 := by
            simp
    _ = (∏ i : Fin m,
          if i.castSucc ∈ J then g i else 1) *
          (if Fin.last m ∈ J then h else 1) := by
            rw [Fin.prod_univ_castSucc]
            simp
    _ = _ := rfl

private theorem perturbationGenerator_ne_zero
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g))
    {ε : ℝ} (hε : 0 < ε) :
    KrivineStengle.perturbationGenerator p ε ≠ 0 := by
  intro hzero
  obtain ⟨x, hx⟩ := hne
  have heval := congrArg (MvPolynomial.eval x) hzero
  have hp0 := hp x hx
  simp [KrivineStengle.perturbationGenerator] at heval
  linarith

/-- The fixed loss which converts a coefficient bound for an appended
preordering certificate into a coefficient bound for its odd part. -/
def splitCoefficientFactor
    (g : Fin m → MvPolynomial (Fin n) ℝ) : ℝ :=
  ∑ J ∈ (Finset.univ : Finset (Fin (m + 1))).powerset,
    coeffL1Norm (oldGeneratorProduct g J)

theorem splitCoefficientFactor_nonneg
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    0 ≤ splitCoefficientFactor g := by
  exact Finset.sum_nonneg fun _ _ ↦ coeffL1Norm_nonneg _

/-- One SOS multiplier times one squarefree generator product is a
truncated preordering certificate at the degree of that complete term. -/
private theorem singleTerm_mem
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin m)) (σ : MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hσ : IsSOS σ) (hdegree : (σ * ∏ i ∈ I, g i).totalDegree ≤ r) :
    σ * ∏ i ∈ I, g i ∈ GenPreordering g r := by
  classical
  refine ⟨Function.update 0 I σ, ?_, ?_, ?_⟩
  · intro J
    by_cases hJI : J = I
    · subst J
      simpa using hσ
    · simp [Function.update_of_ne hJI, IsSOS_zero]
  · intro J
    by_cases hJI : J = I
    · subst J
      simpa using hdegree
    · simp [Function.update_of_ne hJI]
  · rw [Finset.sum_eq_single I]
    · simp
    · intro J _ hJI
      simp [Function.update_of_ne hJI]
    · simp

/-- Split a bounded appended-preordering refutation into its even and odd
parts. Both parts remain in the original preordering at the same order. -/
theorem split_bounded_appendGenerator_refutation
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (h : MvPolynomial (Fin n) ℝ) {r : ℕ} {H : ℝ}
    (hh : h ≠ 0)
    (c : GeneralArchimedean.BoundedPreorderingCertificate
      (KrivineStengle.appendGenerator g h) (-1) r H) :
    ∃ s t : MvPolynomial (Fin n) ℝ,
      s ∈ GenPreordering g r ∧ t ∈ GenPreordering g r ∧
      coeffL1Norm t ≤ H * splitCoefficientFactor g ∧
      (-1 : MvPolynomial (Fin n) ℝ) = s + h * t := by
  classical
  let subsets := (Finset.univ : Finset (Fin (m + 1))).powerset
  let base : Finset (Fin (m + 1)) → MvPolynomial (Fin n) ℝ :=
    fun J ↦ c.certificate.sigma J * oldGeneratorProduct g J
  let hasLast : Finset (Fin (m + 1)) → Prop :=
    fun J ↦ Fin.last m ∈ J
  let s := ∑ J ∈ subsets.filter (fun J ↦ ¬ hasLast J), base J
  let t := ∑ J ∈ subsets.filter hasLast, base J
  have hbaseDegree (J : Finset (Fin (m + 1))) :
      (base J).totalDegree ≤ r := by
    have hdegree := c.certificate.degree_le J
    rw [appendGenerator_product_eq] at hdegree
    by_cases hJ : hasLast J
    · simp only [hasLast] at hJ
      rw [if_pos hJ] at hdegree
      by_cases hbase0 : base J = 0
      · simp [hbase0]
      have hmul : (base J * h).totalDegree ≤ r := by
        simpa only [base, mul_assoc] using hdegree
      rw [MvPolynomial.totalDegree_mul_of_isDomain hbase0 hh] at hmul
      omega
    · simp only [hasLast] at hJ ⊢
      rw [if_neg hJ] at hdegree
      simpa only [base, mul_one] using hdegree
  have hbaseMem (J : Finset (Fin (m + 1))) :
      base J ∈ GenPreordering g r := by
    change c.certificate.sigma J * oldGeneratorProduct g J ∈ GenPreordering g r
    rw [oldGeneratorProduct_eq]
    exact singleTerm_mem g (oldSubset J) (c.certificate.sigma J)
      (c.certificate.isSOS J)
      (by simpa [base, oldGeneratorProduct_eq] using hbaseDegree J)
  have hs : s ∈ GenPreordering g r := by
    exact genPreordering_sum (subsets.filter fun J ↦ ¬ hasLast J) base
      (fun J _ ↦ hbaseMem J)
  have ht : t ∈ GenPreordering g r := by
    exact genPreordering_sum (subsets.filter hasLast) base
      (fun J _ ↦ hbaseMem J)
  have htNorm : coeffL1Norm t ≤ H * splitCoefficientFactor g := by
    calc
      coeffL1Norm t ≤
          ∑ J ∈ subsets.filter hasLast, coeffL1Norm (base J) := by
        simpa only [t] using
          coeffL1Norm_sum_le (subsets.filter hasLast) base
      _ ≤ ∑ J ∈ subsets.filter hasLast,
          H * coeffL1Norm (oldGeneratorProduct g J) := by
        apply Finset.sum_le_sum
        intro J hJ
        calc
          coeffL1Norm (base J) ≤
              coeffL1Norm (c.certificate.sigma J) *
                coeffL1Norm (oldGeneratorProduct g J) := by
            exact coeffL1Norm_mul_le _ _
          _ ≤ H * coeffL1Norm (oldGeneratorProduct g J) := by
            exact mul_le_mul_of_nonneg_right (c.coeff_le J)
              (coeffL1Norm_nonneg _)
      _ ≤ ∑ J ∈ subsets,
          H * coeffL1Norm (oldGeneratorProduct g J) := by
        calc
          (∑ J ∈ subsets.filter hasLast,
              H * coeffL1Norm (oldGeneratorProduct g J)) ≤
              (∑ J ∈ subsets.filter hasLast,
                H * coeffL1Norm (oldGeneratorProduct g J)) +
              ∑ J ∈ subsets.filter (fun J ↦ ¬ hasLast J),
                H * coeffL1Norm (oldGeneratorProduct g J) :=
            le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦
              mul_nonneg c.bound_nonneg (coeffL1Norm_nonneg _))
          _ = _ := Finset.sum_filter_add_sum_filter_not subsets hasLast _
      _ = H * splitCoefficientFactor g := by
        simp only [splitCoefficientFactor, subsets, Finset.mul_sum]
  have hid : (-1 : MvPolynomial (Fin n) ℝ) = s + h * t := by
    calc
      (-1 : MvPolynomial (Fin n) ℝ) =
          ∑ J ∈ subsets,
            c.certificate.sigma J *
              ∏ j ∈ J, KrivineStengle.appendGenerator g h j :=
        c.certificate.identity
      _ = (∑ J ∈ subsets.filter hasLast,
              c.certificate.sigma J *
                ∏ j ∈ J, KrivineStengle.appendGenerator g h j) +
            ∑ J ∈ subsets.filter (fun J ↦ ¬ hasLast J),
              c.certificate.sigma J *
                ∏ j ∈ J, KrivineStengle.appendGenerator g h j := by
        symm
        exact Finset.sum_filter_add_sum_filter_not subsets hasLast _
      _ = h * t + s := by
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro J hJ
          have hlast : Fin.last m ∈ J := by
            exact (Finset.mem_filter.mp hJ).2
          rw [appendGenerator_product_eq, if_pos hlast]
          simp only [base]
          ring
        · apply Finset.sum_congr rfl
          intro J hJ
          have hlast : Fin.last m ∉ J := by
            exact (Finset.mem_filter.mp hJ).2
          rw [appendGenerator_product_eq, if_neg hlast]
          simp only [base]
          ring
      _ = s + h * t := by ring
  exact ⟨s, t, hs, ht, htNorm, hid⟩

/-- Nonnegativity gives a fixed-order direct preordering refutation. Its
odd multiplier has only power-law coefficient growth. -/
theorem exists_direct_power_bounded_refutation
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ k r A, 1 ≤ k ∧ 0 ≤ A ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∃ s t : MvPolynomial (Fin n) ℝ,
          s ∈ GenPreordering g r ∧ t ∈ GenPreordering g r ∧
          coeffL1Norm t ≤ (ε ^ (2 * k))⁻¹ * A ∧
          (-1 : MvPolynomial (Fin n) ℝ) = s - (p + C ε) * t := by
  obtain ⟨k, r, A₀, hk, hA₀, hrefute⟩ :=
    GeneralArchimedean.exists_power_bounded_perturbation_refutation g p hp
  let A := A₀ * splitCoefficientFactor g
  refine ⟨k, r, A, hk, mul_nonneg hA₀ (splitCoefficientFactor_nonneg g), ?_⟩
  intro ε hε hε1
  obtain ⟨c⟩ := hrefute hε hε1
  have hh := perturbationGenerator_ne_zero g p hne hp hε
  obtain ⟨s, t, hs, ht, htNorm, hid⟩ :=
    split_bounded_appendGenerator_refutation g
      (KrivineStengle.perturbationGenerator p ε) hh c
  refine ⟨s, t, hs, ht, ?_, ?_⟩
  · simpa only [A, mul_assoc] using htNorm
  · calc
      (-1 : MvPolynomial (Fin n) ℝ) = s + (-p - C ε) * t := by
        simpa [KrivineStengle.perturbationGenerator] using hid
      _ = s - (p + C ε) * t := by ring

end OptimalConvergenceRates.GeneralCompact

end
