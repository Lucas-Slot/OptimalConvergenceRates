/-
  Degree-controlled bridge from named bounded preordering certificates to the
  quantitative preordering-to-quadratic-module conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeConversion
import OptimalConvergenceRates.GeneralArchimedean.Certificates
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeRefutation
import OptimalConvergenceRates.GeneralArchimedean.GeneratorExtension
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m s : ℕ}

/-- Coefficients attached to a zero generator product do not contribute to a
preordering identity.  Removing them is what lets a bound on complete
preordering terms control the degrees of the individual SOS multipliers. -/
def activePreorderingCoefficient
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) : MvPolynomial (Fin n) ℝ :=
  if ∏ i ∈ I, a i = 0 then 0 else sigma I

theorem activePreorderingCoefficient_isSOS
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I)) (I : Finset (Fin s)) :
    IsSOS (activePreorderingCoefficient a sigma I) := by
  by_cases hI : ∏ i ∈ I, a i = 0
  · simp [activePreorderingCoefficient, hI, IsSOS_zero]
  · simp [activePreorderingCoefficient, hI, hsigma I]

theorem activePreorderingCoefficient_mul
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) :
    activePreorderingCoefficient a sigma I * ∏ i ∈ I, a i =
      sigma I * ∏ i ∈ I, a i := by
  by_cases hI : ∏ i ∈ I, a i = 0
  · simp [activePreorderingCoefficient, hI]
  · simp [activePreorderingCoefficient, hI]

theorem activePreorderingCoefficient_identity
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    {p : MvPolynomial (Fin n) ℝ}
    (hidentity : p =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i) :
    p = ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
      activePreorderingCoefficient a sigma I * ∏ i ∈ I, a i := by
  rw [hidentity]
  apply Finset.sum_congr rfl
  intro I hI
  exact (activePreorderingCoefficient_mul a sigma I).symm

theorem activePreorderingCoefficient_totalDegree_le
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (c : PreorderingCertificate a p r)
    (I : Finset (Fin s)) :
    (activePreorderingCoefficient a c.sigma I).totalDegree ≤ r := by
  by_cases hprod : ∏ i ∈ I, a i = 0
  · simp [activePreorderingCoefficient, hprod]
  · by_cases hsigma : c.sigma I = 0
    · simp [activePreorderingCoefficient, hprod, hsigma]
    · rw [activePreorderingCoefficient, if_neg hprod]
      have hdegree := c.degree_le I
      rw [totalDegree_mul_of_isDomain hsigma hprod] at hdegree
      exact (Nat.le_add_right _ _).trans hdegree

theorem activePreorderingCoefficient_coeffL1Norm_le
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (c : BoundedPreorderingCertificate a p r H)
    (I : Finset (Fin s)) :
    coeffL1Norm (activePreorderingCoefficient a c.certificate.sigma I) ≤ H := by
  by_cases hprod : ∏ i ∈ I, a i = 0
  · simpa [activePreorderingCoefficient, hprod] using c.bound_nonneg
  · simpa [activePreorderingCoefficient, hprod] using c.coeff_le I
/-- Degree-tracked version of the common Archimedean envelope for one member
of a finite polynomial family. -/
theorem family_member_le_finiteFamilyEnvelope_at
    {ι : Type*} [DecidableEq ι]
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {R : ℝ} {t d : ℕ} (hR : 0 ≤ R)
    (hcoord : ∀ i : Fin n,
      C R - X i ^ 2 ∈ GenQuadraticModule g t)
    (S : Finset ι) (q : ι → MvPolynomial (Fin n) ℝ)
    (hqDegree : ∀ i ∈ S, (q i).totalDegree ≤ d)
    {i : ι} (hi : i ∈ S) :
    ModuleLEAt g (t + 2 * d) (q i)
      (C (finiteFamilyEnvelope R S q)) := by
  let e : ι → ℝ := fun j => weightedCoeffEnvelope R (q j)
  have hbase : ModuleLEAt g (t + 2 * (q i).totalDegree)
      (q i) (C (e i)) := by
    change C (e i) - q i ∈
      GenQuadraticModule g (t + 2 * (q i).totalDegree)
    exact weightedCoeffEnvelope_minus_mem_at hR hcoord (q i)
  have hbase' := hbase.mono <|
    Nat.add_le_add_left (Nat.mul_le_mul_left 2 (hqDegree i hi)) t
  have hei : e i ≤ finiteFamilyEnvelope R S q := by
    have hsingle : e i ≤ ∑ j ∈ S, e j :=
      Finset.single_le_sum
        (fun j _ => weightedCoeffEnvelope_nonneg hR (q j)) hi
    dsimp [finiteFamilyEnvelope]
    linarith
  have hconst : ModuleLEAt g 0 (C (e i))
      (C (finiteFamilyEnvelope R S q)) :=
    ModuleLEAt.constant hei
  have htrans := hbase'.trans hconst
  simpa using htrans

/-- Number of monomials in a fixed number of variables of total degree at
most a fixed bound.  The set is finite by the standard bounded-degree theorem
for finitely supported functions. -/
def boundedMonomialCount (n d : ℕ) : ℕ :=
  Set.ncard {alpha : Fin n →₀ ℕ | alpha.degree ≤ d}

/-- The number of monomials of total degree at most `d` is at most the
number of exponent vectors with every coordinate at most `d`. -/
theorem boundedMonomialCount_le_pow (n d : ℕ) :
    boundedMonomialCount n d ≤ (d + 1) ^ n := by
  let S : Set (Fin n →₀ ℕ) := {alpha | alpha.degree ≤ d}
  let encode : S → (Fin n → Fin (d + 1)) := fun alpha i =>
    ⟨alpha.1 i, lt_of_le_of_lt (Finsupp.le_degree i alpha.1)
      (Nat.lt_succ_of_le alpha.2)⟩
  have hencode : Function.Injective encode := by
    intro alpha beta hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg (fun z => (z i).val) hab
  have hrange : Set.range (fun alpha : S => alpha.1) = S := by
    ext alpha
    simp
  calc
    boundedMonomialCount n d = S.ncard := rfl
    _ = (Set.range (fun alpha : S => alpha.1)).ncard := by rw [hrange]
    _ = Nat.card S := Set.ncard_range_of_injective Subtype.val_injective
    _ ≤ Nat.card (Fin n → Fin (d + 1)) :=
      Nat.card_le_card_of_injective encode hencode
    _ = (d + 1) ^ n := by
      rw [Nat.card_fun]
      simp

theorem support_card_le_boundedMonomialCount
    (q : MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hq : q.totalDegree ≤ d) :
    q.support.card ≤ boundedMonomialCount n d := by
  have hfinite :
      ({alpha : Fin n →₀ ℕ | alpha.degree ≤ d} : Set (Fin n →₀ ℕ)).Finite :=
    Finsupp.finite_of_degree_le d
  have hsubset :
      (q.support : Set (Fin n →₀ ℕ)) ⊆
        {alpha : Fin n →₀ ℕ | alpha.degree ≤ d} := by
    intro alpha halpha
    exact (MvPolynomial.le_totalDegree halpha).trans hq
  simpa [boundedMonomialCount] using
    Set.ncard_le_ncard hsubset hfinite

/-- A numerical upper bound for the Archimedean coefficient envelope of a
polynomial with bounded degree and coefficient norm. -/
def polynomialEnvelopeBound (n d : ℕ) (B H : ℝ) : ℝ :=
  (boundedMonomialCount n d : ℝ) * ((H / 2) ^ 2 * B ^ d + 1)

theorem weightedCoeffEnvelope_le_polynomialEnvelopeBound
    {B H : ℝ} {d : ℕ} (hB : 1 ≤ B) (hH : 0 ≤ H)
    (q : MvPolynomial (Fin n) ℝ)
    (hqDegree : q.totalDegree ≤ d)
    (hqNorm : coeffL1Norm q ≤ H) :
    weightedCoeffEnvelope B q ≤ polynomialEnvelopeBound n d B H := by
  have hnorm0 : 0 ≤ coeffL1Norm q := coeffL1Norm_nonneg q
  have hsquare :
      (coeffL1Norm q / 2) ^ 2 ≤ (H / 2) ^ 2 := by
    nlinarith [sq_nonneg (H / 2 - coeffL1Norm q / 2)]
  have hpow : B ^ q.totalDegree ≤ B ^ d :=
    pow_le_pow_right₀ hB hqDegree
  have hinside :
      (coeffL1Norm q / 2) ^ 2 * B ^ q.totalDegree + 1 ≤
        (H / 2) ^ 2 * B ^ d + 1 := by
    gcongr
  have hcardNat :=
    support_card_le_boundedMonomialCount q hqDegree
  have hcard :
      (q.support.card : ℝ) ≤ (boundedMonomialCount n d : ℝ) := by
    exact_mod_cast hcardNat
  calc
    weightedCoeffEnvelope B q ≤
        q.support.card *
          ((coeffL1Norm q / 2) ^ 2 * B ^ q.totalDegree + 1) :=
      weightedCoeffEnvelope_le hB q
    _ ≤ (boundedMonomialCount n d : ℝ) *
          ((H / 2) ^ 2 * B ^ d + 1) := by
      exact mul_le_mul hcard hinside (by positivity) (by positivity)
    _ = polynomialEnvelopeBound n d B H := rfl

/-- Uniform bound for the common envelope of a finite family. -/
def finiteFamilyEnvelopeBound
    (familyCard n d : ℕ) (B H : ℝ) : ℝ :=
  1 + (familyCard : ℝ) * polynomialEnvelopeBound n d B H

theorem finiteFamilyEnvelope_le_finiteFamilyEnvelopeBound
    {ι : Type*} {B H : ℝ} {d : ℕ}
    (hB : 1 ≤ B) (hH : 0 ≤ H)
    (S : Finset ι) (q : ι → MvPolynomial (Fin n) ℝ)
    (hqDegree : ∀ i ∈ S, (q i).totalDegree ≤ d)
    (hqNorm : ∀ i ∈ S, coeffL1Norm (q i) ≤ H) :
    finiteFamilyEnvelope B S q ≤
      finiteFamilyEnvelopeBound S.card n d B H := by
  unfold finiteFamilyEnvelope finiteFamilyEnvelopeBound
  gcongr
  calc
    ∑ i ∈ S, weightedCoeffEnvelope B (q i) ≤
        ∑ _i ∈ S, polynomialEnvelopeBound n d B H := by
      exact Finset.sum_le_sum fun i hi =>
        weightedCoeffEnvelope_le_polynomialEnvelopeBound
          hB hH (q i) (hqDegree i hi) (hqNorm i hi)
    _ = (S.card : ℝ) * polynomialEnvelopeBound n d B H := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Quantitative conversion of a named bounded preordering refutation in an
Archimedean module.  Every order and scalar fed to the conversion is explicit,
and the selected rational package retains its logarithmic parameter bounds. -/
theorem archimedean_bounded_preordering_refutation_to_module_at
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (harch : IsArchimedean a)
    {r : ℕ} {H : ℝ}
    (c : BoundedPreorderingCertificate a
      (-1 : MvPolynomial (Fin n) ℝ) r H) :
    ∃ (R : ℝ) (t d : ℕ) (B Hconvert : ℝ),
      1 ≤ R ∧
      d = r + ∑ i : Fin s, (a i).totalDegree ∧
      B = finiteFamilyEnvelope R Finset.univ a ∧
      Hconvert =
        finiteFamilyEnvelopeBound
          ((Finset.univ : Finset (Finset (Fin s))).card)
          n d R H ∧
      let Bprime : ℝ := 2 * (B + 1)
      let eta : ℝ := absorptionScale s Hconvert Bprime
      ∃ pkg : Package eta B eta,
        (pkg.ell : ℝ) ≤
            Real.log (eta / 4) / Real.log (1 / 9) + 1 ∧
          (pkg.J : ℝ) ≤
            Real.log (Real.sqrt (B + eta) / Real.sqrt eta) /
              Real.log 2 ∧
          (-1 : MvPolynomial (Fin n) ℝ) ∈ GenQuadraticModule a
            (conversionRefutationOrder pkg s d
              (t + 2 * d) d (t + 2 * d)) := by
  classical
  obtain ⟨R, t, hR, hcoord⟩ :=
    harch.exists_truncated_coordinate_square_bound
  let d : ℕ := r + ∑ i : Fin s, (a i).totalDegree
  let generatorSet : Finset (Fin s) := Finset.univ
  let sigmaSet : Finset (Finset (Fin s)) := Finset.univ
  let sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ :=
    activePreorderingCoefficient a c.certificate.sigma
  let B : ℝ := finiteFamilyEnvelope R generatorSet a
  let Hconvert : ℝ :=
    finiteFamilyEnvelopeBound sigmaSet.card n d R H
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have haDegree : ∀ i, (a i).totalDegree ≤ d := by
    intro i
    have hi :
        (a i).totalDegree ≤ ∑ j : Fin s, (a j).totalDegree :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun j => (a j).totalDegree)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [d]
    omega
  have hrle : r ≤ d := by
    dsimp [d]
    omega
  have hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d := by
    intro I
    exact (activePreorderingCoefficient_totalDegree_le
      a c.certificate I).trans hrle
  have hsigmaSOS : ∀ I, IsSOS (sigma I) := by
    intro I
    exact activePreorderingCoefficient_isSOS
      a c.certificate.sigma c.certificate.isSOS I
  have hH : 0 ≤ H := c.bound_nonneg
  have hHconvert : 0 ≤ Hconvert := by
    dsimp [Hconvert, finiteFamilyEnvelopeBound, polynomialEnvelopeBound]
    positivity
  have hB : 0 < B := by
    have hB1 :=
      one_le_finiteFamilyEnvelope hR0 generatorSet a
    exact zero_lt_one.trans_le hB1
  have ha :
      ∀ i, a i ∈ GenQuadraticModule a d := by
    intro i
    exact GenQuadraticModule_mono (haDegree i)
      (genQuadraticModule_generator a i)
  have hBa :
      ∀ i, C B - a i ∈ GenQuadraticModule a (t + 2 * d) := by
    intro i
    have hle := family_member_le_finiteFamilyEnvelope_at
      hR0 hcoord generatorSet a
      (fun j hj => haDegree j) (i := i) (by simp [generatorSet])
    simpa [ModuleLEAt, B, generatorSet] using hle
  have hfamilyBound :
      finiteFamilyEnvelope R sigmaSet sigma ≤ Hconvert := by
    dsimp [Hconvert]
    exact finiteFamilyEnvelope_le_finiteFamilyEnvelopeBound
      hR hH sigmaSet sigma
      (fun I hI => hsigmaDegree I)
      (fun I hI =>
        activePreorderingCoefficient_coeffL1Norm_le a c I)
  have hsigmaBound :
      ∀ I, ModuleLEAt a (t + 2 * d) (sigma I) (C Hconvert) := by
    intro I
    have hbase := family_member_le_finiteFamilyEnvelope_at
      hR0 hcoord sigmaSet sigma
      (fun J hJ => hsigmaDegree J) (i := I) (by simp [sigmaSet])
    have hconst : ModuleLEAt a 0
        (C (finiteFamilyEnvelope R sigmaSet sigma))
        (C Hconvert) :=
      ModuleLEAt.constant hfamilyBound
    have htrans := hbase.trans hconst
    simpa using htrans
  have hidentity :
      (-1 : MvPolynomial (Fin n) ℝ) =
        ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
          sigma I * ∏ i ∈ I, a i := by
    exact activePreorderingCoefficient_identity
      a c.certificate.sigma c.certificate.identity
  refine ⟨R, t, d, B, Hconvert, hR, rfl, rfl, rfl, ?_⟩
  simpa [generatorSet, sigmaSet, sigma] using
    bounded_preordering_refutation_to_module_at
      a sigma B Hconvert hB hHconvert hsigmaSOS hsigmaDegree
      hsigmaBound ha hBa haDegree hidentity

/-- Uniform version of the tracked Archimedean conversion.  The generator
envelope is computed only from common degree and coefficient bounds, so it is
stable for parameterized families such as the appended perturbation
generator. -/
theorem bounded_preordering_refutation_to_module_at_of_coordinate_bounds
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    {R : ℝ} {t : ℕ}
    (hR : 1 ≤ R)
    (hcoord : ∀ i : Fin n,
      C R - X i ^ 2 ∈ GenQuadraticModule a t)
    {r d : ℕ} {H G : ℝ}
    (c : BoundedPreorderingCertificate a
      (-1 : MvPolynomial (Fin n) ℝ) r H)
    (hrd : r ≤ d) (hG : 0 ≤ G)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G) :
    ∃ (B Hconvert : ℝ),
      B = finiteFamilyEnvelopeBound s n d R G ∧
      Hconvert =
        finiteFamilyEnvelopeBound
          ((Finset.univ : Finset (Finset (Fin s))).card)
          n d R H ∧
      let Bprime : ℝ := 2 * (B + 1)
      let eta : ℝ := absorptionScale s Hconvert Bprime
      ∃ pkg : Package eta B eta,
        (pkg.ell : ℝ) ≤
            Real.log (eta / 4) / Real.log (1 / 9) + 1 ∧
          (pkg.J : ℝ) ≤
            Real.log (Real.sqrt (B + eta) / Real.sqrt eta) /
              Real.log 2 ∧
          (-1 : MvPolynomial (Fin n) ℝ) ∈ GenQuadraticModule a
            (conversionRefutationOrder pkg s d
              (t + 2 * d) d (t + 2 * d)) := by
  classical
  let generatorSet : Finset (Fin s) := Finset.univ
  let sigmaSet : Finset (Finset (Fin s)) := Finset.univ
  let sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ :=
    activePreorderingCoefficient a c.certificate.sigma
  let B : ℝ := finiteFamilyEnvelopeBound s n d R G
  let Hconvert : ℝ :=
    finiteFamilyEnvelopeBound sigmaSet.card n d R H
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hH : 0 ≤ H := c.bound_nonneg
  have hsigmaDegree : ∀ I, (sigma I).totalDegree ≤ d := by
    intro I
    exact (activePreorderingCoefficient_totalDegree_le
      a c.certificate I).trans hrd
  have hsigmaSOS : ∀ I, IsSOS (sigma I) := by
    intro I
    exact activePreorderingCoefficient_isSOS
      a c.certificate.sigma c.certificate.isSOS I
  have hB : 0 < B := by
    dsimp [B, finiteFamilyEnvelopeBound, polynomialEnvelopeBound]
    positivity
  have hHconvert : 0 ≤ Hconvert := by
    dsimp [Hconvert, finiteFamilyEnvelopeBound, polynomialEnvelopeBound]
    positivity
  have ha :
      ∀ i, a i ∈ GenQuadraticModule a d := by
    intro i
    exact GenQuadraticModule_mono (haDegree i)
      (genQuadraticModule_generator a i)
  have hgeneratorFamily :
      finiteFamilyEnvelope R generatorSet a ≤ B := by
    have hbound := finiteFamilyEnvelope_le_finiteFamilyEnvelopeBound
      hR hG generatorSet a
      (fun i hi => haDegree i)
      (fun i hi => haNorm i)
    simpa [B, generatorSet] using hbound
  have hBa :
      ∀ i, C B - a i ∈ GenQuadraticModule a (t + 2 * d) := by
    intro i
    have hbase := family_member_le_finiteFamilyEnvelope_at
      hR0 hcoord generatorSet a
      (fun j hj => haDegree j) (i := i) (by simp [generatorSet])
    have hconst : ModuleLEAt a 0
        (C (finiteFamilyEnvelope R generatorSet a)) (C B) :=
      ModuleLEAt.constant hgeneratorFamily
    have htrans := hbase.trans hconst
    simpa [ModuleLEAt] using htrans
  have hfamilyBound :
      finiteFamilyEnvelope R sigmaSet sigma ≤ Hconvert := by
    dsimp [Hconvert]
    exact finiteFamilyEnvelope_le_finiteFamilyEnvelopeBound
      hR hH sigmaSet sigma
      (fun I hI => hsigmaDegree I)
      (fun I hI =>
        activePreorderingCoefficient_coeffL1Norm_le a c I)
  have hsigmaBound :
      ∀ I, ModuleLEAt a (t + 2 * d) (sigma I) (C Hconvert) := by
    intro I
    have hbase := family_member_le_finiteFamilyEnvelope_at
      hR0 hcoord sigmaSet sigma
      (fun J hJ => hsigmaDegree J) (i := I) (by simp [sigmaSet])
    have hconst : ModuleLEAt a 0
        (C (finiteFamilyEnvelope R sigmaSet sigma))
        (C Hconvert) :=
      ModuleLEAt.constant hfamilyBound
    have htrans := hbase.trans hconst
    simpa using htrans
  have hidentity :
      (-1 : MvPolynomial (Fin n) ℝ) =
        ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
          sigma I * ∏ i ∈ I, a i :=
    activePreorderingCoefficient_identity
      a c.certificate.sigma c.certificate.identity
  refine ⟨B, Hconvert, rfl, rfl, ?_⟩
  simpa [generatorSet, sigmaSet, sigma] using
    bounded_preordering_refutation_to_module_at
      a sigma B Hconvert hB hHconvert hsigmaSOS hsigmaDegree
      hsigmaBound ha hBa haDegree hidentity
/-- Archimedean wrapper around the fixed-coordinate uniform conversion. -/
theorem archimedean_bounded_preordering_refutation_to_module_at_of_bounds
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (harch : IsArchimedean a)
    {r d : ℕ} {H G : ℝ}
    (c : BoundedPreorderingCertificate a
      (-1 : MvPolynomial (Fin n) ℝ) r H)
    (hrd : r ≤ d) (hG : 0 ≤ G)
    (haDegree : ∀ i, (a i).totalDegree ≤ d)
    (haNorm : ∀ i, coeffL1Norm (a i) ≤ G) :
    ∃ (R : ℝ) (t : ℕ) (B Hconvert : ℝ),
      1 ≤ R ∧
      B = finiteFamilyEnvelopeBound s n d R G ∧
      Hconvert =
        finiteFamilyEnvelopeBound
          ((Finset.univ : Finset (Finset (Fin s))).card)
          n d R H ∧
      let Bprime : ℝ := 2 * (B + 1)
      let eta : ℝ := absorptionScale s Hconvert Bprime
      ∃ pkg : Package eta B eta,
        (pkg.ell : ℝ) ≤
            Real.log (eta / 4) / Real.log (1 / 9) + 1 ∧
          (pkg.J : ℝ) ≤
            Real.log (Real.sqrt (B + eta) / Real.sqrt eta) /
              Real.log 2 ∧
          (-1 : MvPolynomial (Fin n) ℝ) ∈ GenQuadraticModule a
            (conversionRefutationOrder pkg s d
              (t + 2 * d) d (t + 2 * d)) := by
  obtain ⟨R, t, hR, hcoord⟩ :=
    harch.exists_truncated_coordinate_square_bound
  obtain ⟨B, Hconvert, hB, hHconvert, hpkg⟩ :=
    bounded_preordering_refutation_to_module_at_of_coordinate_bounds
      a hR hcoord c hrd hG haDegree haNorm
  exact ⟨R, t, B, Hconvert, hR, hB, hHconvert, hpkg⟩

/-- A parameter-independent common coefficient bound for the original
generators and the appended perturbation generator when the perturbation lies
in the unit interval. -/
def perturbationGeneratorCommonCoeffBound
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  1 + ∑ i : Fin (m + 1), perturbationGeneratorCoeffEnvelope g p i

theorem perturbationGeneratorCommonCoeffBound_nonneg
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    0 ≤ perturbationGeneratorCommonCoeffBound g p := by
  dsimp [perturbationGeneratorCommonCoeffBound]
  exact add_nonneg zero_le_one <|
    Finset.sum_nonneg fun i _ =>
      perturbationGeneratorCoeffEnvelope_nonneg g p i

theorem appendPerturbation_coeffL1Norm_le_common
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∀ i,
      coeffL1Norm
          (KrivineStengle.appendGenerator g
            (KrivineStengle.perturbationGenerator p epsilon) i) ≤
        perturbationGeneratorCommonCoeffBound g p := by
  intro i
  have hbase :=
    appendPerturbation_coeffL1Norm_le g p hepsilon0 hepsilon1 i
  have hsingle :
      perturbationGeneratorCoeffEnvelope g p i ≤
        ∑ j : Fin (m + 1), perturbationGeneratorCoeffEnvelope g p j :=
    Finset.single_le_sum
      (s := Finset.univ)
      (f := perturbationGeneratorCoeffEnvelope g p)
      (fun j _ => perturbationGeneratorCoeffEnvelope_nonneg g p j)
      (Finset.mem_univ i)
  dsimp [perturbationGeneratorCommonCoeffBound]
  linarith

/-- A fixed common degree bound for the appended perturbation family. -/
def perturbationGeneratorDegreeBound
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) : ℕ :=
  p.totalDegree + ∑ i : Fin m, (g i).totalDegree

theorem appendPerturbation_totalDegree_le
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (epsilon : ℝ) :
    ∀ i,
      (KrivineStengle.appendGenerator g
        (KrivineStengle.perturbationGenerator p epsilon) i).totalDegree ≤
      perturbationGeneratorDegreeBound g p := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [KrivineStengle.appendGenerator_last]
    exact (KrivineStengle.perturbationGenerator_totalDegree_le p epsilon).trans
      (Nat.le_add_right _ _)
  · rw [KrivineStengle.appendGenerator_castSucc]
    have hj :
        (g j).totalDegree ≤ ∑ i : Fin m, (g i).totalDegree :=
      Finset.single_le_sum
        (s := Finset.univ) (f := fun i => (g i).totalDegree)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    dsimp [perturbationGeneratorDegreeBound]
    omega

/-- The Krivine--Stengle perturbation refutations convert uniformly to
finite-order quadratic-module refutations over the appended generator family.
All constants outside the displayed epsilon-dependent coefficient envelope are
fixed by the original Archimedean problem. -/
theorem exists_quantitative_perturbation_module_refutation
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (harch : IsArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ (k r d t : ℕ) (A R G B : ℝ),
      1 ≤ k ∧ 0 ≤ A ∧ 1 ≤ R ∧ 0 ≤ G ∧
      d = r + perturbationGeneratorDegreeBound g p ∧
      G = perturbationGeneratorCommonCoeffBound g p ∧
      B = finiteFamilyEnvelopeBound (m + 1) n d R G ∧
      ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
        let H : ℝ := (epsilon ^ (2 * k))⁻¹ * A
        let Hconvert : ℝ :=
          finiteFamilyEnvelopeBound
            ((Finset.univ :
              Finset (Finset (Fin (m + 1)))).card)
            n d R H
        let Bprime : ℝ := 2 * (B + 1)
        let eta : ℝ := absorptionScale (m + 1) Hconvert Bprime
        ∃ pkg : Package eta B eta,
          (pkg.ell : ℝ) ≤
              Real.log (eta / 4) / Real.log (1 / 9) + 1 ∧
            (pkg.J : ℝ) ≤
              Real.log (Real.sqrt (B + eta) / Real.sqrt eta) /
                Real.log 2 ∧
            (-1 : MvPolynomial (Fin n) ℝ) ∈
              GenQuadraticModule
                (KrivineStengle.appendGenerator g
                  (KrivineStengle.perturbationGenerator p epsilon))
                (conversionRefutationOrder pkg (m + 1) d
                  (t + 2 * d) d (t + 2 * d)) := by
  classical
  obtain ⟨k, r, A, hk, hA, hrefute⟩ :=
    exists_power_bounded_perturbation_refutation g p hp
  obtain ⟨R, t, hR, hcoord⟩ :=
    harch.exists_truncated_coordinate_square_bound
  let d : ℕ := r + perturbationGeneratorDegreeBound g p
  let G : ℝ := perturbationGeneratorCommonCoeffBound g p
  let B : ℝ := finiteFamilyEnvelopeBound (m + 1) n d R G
  have hG : 0 ≤ G := by
    dsimp [G]
    exact perturbationGeneratorCommonCoeffBound_nonneg g p
  refine ⟨k, r, d, t, A, R, G, B, hk, hA, hR, hG,
    rfl, rfl, rfl, ?_⟩
  intro epsilon hepsilon hepsilon1
  obtain ⟨c⟩ := hrefute hepsilon hepsilon1
  let a : Fin (m + 1) → MvPolynomial (Fin n) ℝ :=
    KrivineStengle.appendGenerator g
      (KrivineStengle.perturbationGenerator p epsilon)
  have hrd : r ≤ d := by
    dsimp [d]
    omega
  have haDegree : ∀ i, (a i).totalDegree ≤ d := by
    intro i
    have hi := appendPerturbation_totalDegree_le g p epsilon i
    dsimp [a, d]
    omega
  have haNorm : ∀ i, coeffL1Norm (a i) ≤ G := by
    intro i
    dsimp [a, G]
    exact appendPerturbation_coeffL1Norm_le_common
      g p hepsilon.le hepsilon1 i
  have hcoord' : ∀ i : Fin n,
      C R - X i ^ 2 ∈ GenQuadraticModule a t := by
    intro i
    exact genQuadraticModule_lift_appendGenerator (hcoord i)
  obtain ⟨B', Hconvert, hB', hHconvert, hpkg⟩ :=
    bounded_preordering_refutation_to_module_at_of_coordinate_bounds
      a hR hcoord' c hrd hG haDegree haNorm
  rw [hB', hHconvert] at hpkg
  simpa [a, B, G, d] using hpkg



end OptimalConvergenceRates.GeneralArchimedean

end
