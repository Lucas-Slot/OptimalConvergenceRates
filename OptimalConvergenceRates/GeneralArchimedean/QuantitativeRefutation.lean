/-
  Quantitative coefficient bookkeeping for the fixed Krivine--Stengle
  perturbation refutation.
-/
import OptimalConvergenceRates.GeneralArchimedean.Certificates
import OptimalConvergenceRates.GeneralArchimedean.Stengle

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- A purely numerical envelope for the generator factors introduced by
multiplication of squarefree preordering terms. -/
def preorderingMulFactorEnvelope (e : Fin m → ℝ) : ℝ :=
  let subsets := (Finset.univ : Finset (Fin m)).powerset
  let pairs := subsets.product subsets
  ∑ K ∈ subsets,
    ∑ IJ ∈ pairs.filter
        (fun IJ => KrivineStengle.subsetParity IJ.1 IJ.2 = K),
      (∏ i ∈ IJ.1 ∩ IJ.2, e i) ^ 2

theorem mulFactor_le_preorderingMulFactorEnvelope
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    PreorderingCertificate.mulFactor g ≤
      preorderingMulFactorEnvelope (fun i => coeffL1Norm (g i)) := by
  classical
  unfold PreorderingCertificate.mulFactor preorderingMulFactorEnvelope
  apply Finset.sum_le_sum
  intro K hK
  apply Finset.sum_le_sum
  intro IJ hIJ
  let u := ∏ i ∈ IJ.1 ∩ IJ.2, g i
  have hprod :
      coeffL1Norm u ≤
        ∏ i ∈ IJ.1 ∩ IJ.2, coeffL1Norm (g i) := by
    exact coeffL1Norm_prod_le (IJ.1 ∩ IJ.2) g
  have hu0 : 0 ≤ coeffL1Norm u := coeffL1Norm_nonneg u
  have hprod0 :
      0 ≤ ∏ i ∈ IJ.1 ∩ IJ.2, coeffL1Norm (g i) :=
    Finset.prod_nonneg fun i hi => coeffL1Norm_nonneg (g i)
  calc
    coeffL1Norm ((∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2) =
        coeffL1Norm (u ^ 2) := rfl
    _ ≤ coeffL1Norm u ^ 2 := coeffL1Norm_pow_le u 2
    _ ≤ (∏ i ∈ IJ.1 ∩ IJ.2, coeffL1Norm (g i)) ^ 2 := by
      nlinarith

theorem preorderingMulFactorEnvelope_mono
    {e f : Fin m → ℝ}
    (he : ∀ i, 0 ≤ e i) (hef : ∀ i, e i ≤ f i) :
    preorderingMulFactorEnvelope e ≤ preorderingMulFactorEnvelope f := by
  classical
  unfold preorderingMulFactorEnvelope
  apply Finset.sum_le_sum
  intro K hK
  apply Finset.sum_le_sum
  intro IJ hIJ
  have hprod :
      (∏ i ∈ IJ.1 ∩ IJ.2, e i) ≤
        ∏ i ∈ IJ.1 ∩ IJ.2, f i := by
    apply Finset.prod_le_prod
    · intro i hi
      exact he i
    · intro i hi
      exact hef i
  have heprod : 0 ≤ ∏ i ∈ IJ.1 ∩ IJ.2, e i :=
    Finset.prod_nonneg fun i hi => he i
  have hfprod : 0 ≤ ∏ i ∈ IJ.1 ∩ IJ.2, f i :=
    Finset.prod_nonneg fun i hi => (he i).trans (hef i)
  nlinarith

/-- Coefficient envelopes for the old generators and the appended
perturbation generator. -/
def perturbationGeneratorCoeffEnvelope
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    Fin (m + 1) → ℝ :=
  Fin.lastCases (coeffL1Norm p + 1) (fun i => coeffL1Norm (g i))

theorem perturbationGeneratorCoeffEnvelope_nonneg
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    ∀ i, 0 ≤ perturbationGeneratorCoeffEnvelope g p i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [perturbationGeneratorCoeffEnvelope, Fin.lastCases_last]
    linarith [coeffL1Norm_nonneg p]
  · simp [perturbationGeneratorCoeffEnvelope, coeffL1Norm_nonneg]

theorem appendPerturbation_coeffL1Norm_le
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∀ i,
      coeffL1Norm
          (KrivineStengle.appendGenerator g
            (KrivineStengle.perturbationGenerator p epsilon) i) ≤
        perturbationGeneratorCoeffEnvelope g p i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [KrivineStengle.appendGenerator_last,
      KrivineStengle.perturbationGenerator,
      perturbationGeneratorCoeffEnvelope, Fin.lastCases_last]
    calc
      coeffL1Norm (-p - C epsilon) ≤
          coeffL1Norm (-p) + coeffL1Norm (C epsilon) :=
        coeffL1Norm_sub_le _ _
      _ ≤ coeffL1Norm p + |epsilon| := by
        rw [coeffL1Norm_neg]
        exact add_le_add le_rfl (coeffL1Norm_C_le (n := n) epsilon)
      _ ≤ coeffL1Norm p + 1 := by
        exact add_le_add le_rfl
          (by simpa [abs_of_nonneg hepsilon0] using hepsilon1)
  · simp [perturbationGeneratorCoeffEnvelope]

/-- A fixed bound for multiplication in every appended perturbation
preordering with the perturbation parameter in [0,1]. -/
def perturbationMulFactorBound
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  preorderingMulFactorEnvelope (perturbationGeneratorCoeffEnvelope g p)

theorem perturbation_mulFactor_le
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    PreorderingCertificate.mulFactor
        (KrivineStengle.appendGenerator g
          (KrivineStengle.perturbationGenerator p epsilon)) ≤
      perturbationMulFactorBound g p := by
  exact (mulFactor_le_preorderingMulFactorEnvelope
    (KrivineStengle.appendGenerator g
      (KrivineStengle.perturbationGenerator p epsilon))).trans
    (preorderingMulFactorEnvelope_mono
      (fun i => coeffL1Norm_nonneg _)
      (appendPerturbation_coeffL1Norm_le g p hepsilon0 hepsilon1))

theorem perturbationMulFactorBound_nonneg
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    0 ≤ perturbationMulFactorBound g p := by
  exact PreorderingCertificate.mulFactor_nonneg
    (KrivineStengle.appendGenerator g
      (KrivineStengle.perturbationGenerator p 0)) |>.trans
    (perturbation_mulFactor_le g p (le_refl 0) zero_le_one)

/-- Coefficient bound obtained by repeated multiplication with a common
upper bound for the preordering multiplication factor. -/
def certificatePowerBound (F H : ℝ) : ℕ → ℝ
  | 0 => 1
  | N + 1 => certificatePowerBound F H N * H * F

theorem certificatePowerBound_nonneg
    {F H : ℝ} (hF : 0 ≤ F) (hH : 0 ≤ H) :
    ∀ N, 0 ≤ certificatePowerBound F H N
  | 0 => by simp [certificatePowerBound]
  | N + 1 => by
      simp only [certificatePowerBound]
      exact mul_nonneg
        (mul_nonneg (certificatePowerBound_nonneg hF hH N) hH) hF

/-- A bounded certificate can be raised to a power while retaining an
explicit recursive coefficient bound. -/
def boundedPower
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ} {H F : ℝ}
    (hfactor : PreorderingCertificate.mulFactor g ≤ F)
    (c : BoundedPreorderingCertificate g p r H) :
    ∀ N, BoundedPreorderingCertificate g (p ^ N) (N * r)
      (certificatePowerBound F H N)
  | 0 => by
      simpa [certificatePowerBound] using
        BoundedPreorderingCertificate.constantNonneg g 1 zero_le_one
  | N + 1 => by
      simpa [certificatePowerBound, pow_succ, Nat.succ_mul] using
        (boundedPower hfactor c N).mulOfFactorLe c hfactor

/-- Recursive size bound for
`(c+h)^N-c^N`, using the subtraction-free identity at the successor
step. -/
def powerDifferenceBound (F Hc Hh : ℝ) : ℕ → ℝ
  | 0 => 0
  | N + 1 =>
      (Hc + Hh) * powerDifferenceBound F Hc Hh N * F +
        Hh * certificatePowerBound F Hc N * F

theorem powerDifferenceBound_nonneg
    {F Hc Hh : ℝ} (hF : 0 ≤ F) (hHc : 0 ≤ Hc) (hHh : 0 ≤ Hh) :
    ∀ N, 0 ≤ powerDifferenceBound F Hc Hh N
  | 0 => by simp [powerDifferenceBound]
  | N + 1 => by
      simp only [powerDifferenceBound]
      have hp := powerDifferenceBound_nonneg hF hHc hHh N
      have hc := certificatePowerBound_nonneg hF hHc N
      positivity

/-- Degree- and coefficient-controlled subtraction-free certificate for a
power difference. -/
def boundedAddPowSubPow
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {c h : MvPolynomial (Fin n) ℝ} {d : ℕ}
    {Hc Hh F : ℝ}
    (hfactor : PreorderingCertificate.mulFactor g ≤ F)
    (cc : BoundedPreorderingCertificate g c 0 Hc)
    (ch : BoundedPreorderingCertificate g h d Hh) :
    ∀ N, BoundedPreorderingCertificate g ((c + h) ^ N - c ^ N)
      (N * d) (powerDifferenceBound F Hc Hh N)
  | 0 => by
      convert BoundedPreorderingCertificate.constantNonneg g 0 le_rfl using 1 <;>
        simp
  | N + 1 => by
      let cplus := cc.add ch
      let previous := boundedAddPowSubPow hfactor cc ch N
      let left := cplus.mulOfFactorLe previous hfactor
      let cpow := boundedPower hfactor cc N
      let right := ch.mulOfFactorLe cpow hfactor
      let raw : BoundedPreorderingCertificate g
          ((c + h) * ((c + h) ^ N - c ^ N) + h * c ^ N)
          (max (max 0 d + N * d) (d + N * 0))
          ((Hc + Hh) * powerDifferenceBound F Hc Hh N * F +
            Hh * certificatePowerBound F Hc N * F) :=
        left.add right
      have horder :
          max (max 0 d + N * d) (d + N * 0) ≤ (N + 1) * d := by
        simp only [max_eq_right (Nat.zero_le d), Nat.mul_zero, Nat.add_zero,
          Nat.succ_mul]
        omega
      have raised := raw.mono horder
      have hpoly :
          (c + h) ^ (N + 1) - c ^ (N + 1) =
            (c + h) * ((c + h) ^ N - c ^ N) + h * c ^ N := by
        ring
      rw [hpoly]
      simpa only [powerDifferenceBound] using raised


/-- A fixed Krivine--Stengle witness supplies a uniformly bounded-degree
perturbation refutation whose coefficient size grows by only the fixed
power epsilon^(-2k). -/
theorem bounded_perturbation_refutation_of_ksWitness
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (w : KrivineStengle.KSWitness g p) :
    ∃ (r : ℕ) (A : ℝ), 0 ≤ A ∧
      ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
        Nonempty
          (BoundedPreorderingCertificate
            (KrivineStengle.appendGenerator g
              (KrivineStengle.perturbationGenerator p epsilon))
            (-1) r ((epsilon ^ (2 * w.k))⁻¹ * A)) := by
  classical
  obtain ⟨rS, hS⟩ := w.hS
  obtain ⟨rT, hT⟩ := w.hT
  obtain ⟨HS, ⟨cS⟩⟩ :=
    BoundedPreorderingCertificate.exists_of_mem hS
  obtain ⟨HT, ⟨cT⟩⟩ :=
    BoundedPreorderingCertificate.exists_of_mem hT
  let L : ℝ :=
    (((Finset.univ : Finset (Fin (m + 1))).powerset.card : ℕ) : ℝ)
  let F : ℝ := perturbationMulFactorBound g p
  let N : ℕ := 2 * w.k
  let r : ℕ :=
    max (max rT (max 0 p.totalDegree + rS)) (N * p.totalDegree)
  let A : ℝ :=
    (L * HT + (1 + 1) * (L * HS) * F) +
      powerDifferenceBound F 1 1 N
  have hL : 0 ≤ L := by positivity
  have hF : 0 ≤ F := perturbationMulFactorBound_nonneg g p
  have hA : 0 ≤ A := by
    dsimp [A]
    have hHS : 0 ≤ HS := cS.bound_nonneg
    have hHT : 0 ≤ HT := cT.bound_nonneg
    have hdiff : 0 ≤ powerDifferenceBound F 1 1 N :=
      powerDifferenceBound_nonneg hF zero_le_one zero_le_one N
    positivity
  refine ⟨r, A, hA, ?_⟩
  intro epsilon hepsilon hepsilon1
  let h := KrivineStengle.perturbationGenerator p epsilon
  let g' := KrivineStengle.appendGenerator g h
  have hfactor : PreorderingCertificate.mulFactor g' ≤ F := by
    dsimp [g', h, F]
    exact perturbation_mulFactor_le g p hepsilon.le hepsilon1
  let cS' : BoundedPreorderingCertificate g' w.S rS (L * HS) := by
    simpa [g', h, L] using cS.liftAppendGenerator h
  let cT' : BoundedPreorderingCertificate g' w.T rT (L * HT) := by
    simpa [g', h, L] using cT.liftAppendGenerator h
  let cepsilon0 :=
    BoundedPreorderingCertificate.constantNonneg g' epsilon hepsilon.le
  let cepsilon : BoundedPreorderingCertificate g' (C epsilon) 0 1 :=
    cepsilon0.weakenBound hepsilon1
  let ch0 := BoundedPreorderingCertificate.generator g' (Fin.last m)
  have hhDegree : h.totalDegree ≤ p.totalDegree := by
    dsimp [h]
    exact KrivineStengle.perturbationGenerator_totalDegree_le p epsilon
  let chBase : BoundedPreorderingCertificate g' h h.totalDegree 1 := by
    simpa [g'] using ch0
  let ch : BoundedPreorderingCertificate g' h p.totalDegree 1 :=
    chBase.mono hhDegree
  let cplus := cepsilon.add ch
  let cprod : BoundedPreorderingCertificate g'
      ((C epsilon + h) * w.S) (max 0 p.totalDegree + rS)
      ((1 + 1) * (L * HS) * F) :=
    cplus.mulOfFactorLe cS' hfactor
  let cdiff : BoundedPreorderingCertificate g'
      ((C epsilon + h) ^ N - (C epsilon) ^ N)
      (N * p.totalDegree) (powerDifferenceBound F 1 1 N) :=
    boundedAddPowSubPow hfactor cepsilon ch N
  let rhs : BoundedPreorderingCertificate g'
      (w.T + (C epsilon + h) * w.S +
        ((C epsilon + h) ^ N - (C epsilon) ^ N))
      r A := by
    exact (cT'.add cprod).add cdiff
  have hidentity :
      -(C (epsilon ^ N)) =
        w.T + (C epsilon + h) * w.S +
          ((C epsilon + h) ^ N - (C epsilon) ^ N) := by
    simpa [h, N, C_pow] using w.perturbation_identity epsilon
  let negCert : BoundedPreorderingCertificate g'
      (-(C (epsilon ^ N))) r A := by
    rw [hidentity]
    exact rhs
  have hepsilonPow0 : 0 ≤ epsilon ^ N := pow_nonneg hepsilon.le N
  have hepsilonPowNe : epsilon ^ N ≠ 0 := pow_ne_zero N hepsilon.ne'
  let scaled := negCert.scaleNonneg
    (epsilon ^ N)⁻¹ (inv_nonneg.mpr hepsilonPow0)
  have hscaled :
      C (epsilon ^ N)⁻¹ * (-(C (epsilon ^ N))) =
        (-1 : MvPolynomial (Fin n) ℝ) := by
    rw [← C_neg, ← C_mul]
    field_simp
    simp
  refine ⟨?_⟩
  rw [← hscaled]
  simpa [N] using scaled

/-- Nonnegativity supplies a fixed-order perturbation refutation with a
fixed power-law coefficient bound. -/
theorem exists_power_bounded_perturbation_refutation
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ (k r : ℕ) (A : ℝ), 1 ≤ k ∧ 0 ≤ A ∧
      ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
        Nonempty
          (BoundedPreorderingCertificate
            (KrivineStengle.appendGenerator g
              (KrivineStengle.perturbationGenerator p epsilon))
            (-1) r ((epsilon ^ (2 * k))⁻¹ * A)) := by
  obtain ⟨w⟩ := nonnegative_krivine_stengle_witness g p hp
  obtain ⟨r, A, hA, hrefute⟩ :=
    bounded_perturbation_refutation_of_ksWitness w
  exact ⟨w.k, r, A, w.k_pos, hA, hrefute⟩
end OptimalConvergenceRates.GeneralArchimedean

end
