/-
  The two-channel absorption estimate used by the sharp quantitative
  preordering-to-quadratic-module conversion.

  Unlike the coarse estimate in `RefutationConversion`, the approximation
  parameter `theta` is absorbed by the even part of the converted identity.
  Only terms which contain a genuine `delta` factor are charged to the
  common denominator.  This permits `theta` to remain fixed while
  `delta = O(1 / H)`.
-/
import OptimalConvergenceRates.GeneralArchimedean.RefutationConversion

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

/-- One term in the subset expansion of the product of the upper error
bounds.  The set `L` records the factors from which the `delta V_i²`
summand is selected. -/
def refinedErrorBoundTerm
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I K L : Finset (Fin s)) :
    MvPolynomial (Fin n) ℝ :=
  sigma I *
      (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2) *
      (∏ i ∈ L, C δ * (pkg i).substV (a i) ^ 2) *
      (∏ i ∈ K \ L, C theta * (pkg i).substP (a i) ^ 2) *
    ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2

/-- Exact subset expansion of an upper error-bound term. -/
theorem errorBoundTerm_eq_sum_refined
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I K : Finset (Fin s)) :
    errorBoundTerm pkg a sigma I K =
      ∑ L ∈ K.powerset, refinedErrorBoundTerm pkg a sigma I K L := by
  classical
  unfold errorBoundTerm refinedErrorBoundTerm
  have hswap :
      (∏ i ∈ K, (C theta * (pkg i).substP (a i) ^ 2 +
          C δ * (pkg i).substV (a i) ^ 2)) =
        ∏ i ∈ K, (C δ * (pkg i).substV (a i) ^ 2 +
          C theta * (pkg i).substP (a i) ^ 2) := by
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [hswap]
  rw [Finset.prod_add]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro L hL
  ring

/-- The summand with no `delta` factor is a scalar multiple of the
zero-error term. -/
theorem refinedErrorBoundTerm_empty
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I K : Finset (Fin s)) (hKI : K ⊆ I) :
    refinedErrorBoundTerm pkg a sigma I K ∅ =
      C (theta ^ K.card) * zeroErrorTerm pkg a sigma I := by
  classical
  have hsplit :
      (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2) *
          (∏ i ∈ K, (pkg i).substP (a i) ^ 2) =
        ∏ i ∈ I, (pkg i).substP (a i) ^ 2 :=
    Finset.prod_sdiff hKI
  unfold refinedErrorBoundTerm zeroErrorTerm errorExpansionTerm
  simp only [Finset.prod_empty, Finset.sdiff_empty,
    Finset.prod_mul_distrib, Finset.prod_const, map_pow,
    Finset.card_empty, pow_zero]
  rw [← hsplit]
  ring

/-- The scalar-denominator upper bound for a refined summand. -/
def refinedScalarBoundTerm
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (H Bprime : ℝ) (I K L : Finset (Fin s)) :
    MvPolynomial (Fin n) ℝ :=
  C H *
      (∏ i ∈ I \ K, C Bprime * (pkg i).substV (a i) ^ 2) *
      (∏ i ∈ L, C δ * (pkg i).substV (a i) ^ 2) *
      (∏ i ∈ K \ L,
        C (theta * Bprime) * (pkg i).substV (a i) ^ 2) *
    ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2

/-- Interval comparison turns a refined expansion term into its scalar
common-denominator bound. -/
theorem refinedErrorBoundTerm_le_refinedScalarBoundTerm
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H Bprime : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaBound : ∀ I, ModuleLE g (sigma I) (C H))
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hBa : ∀ i, QuadraticModuleMem g (C B - a i))
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBprime : 0 ≤ Bprime)
    (hBcondition : B + δ ≤ (1 - theta) * Bprime)
    (I K L : Finset (Fin s)) :
    ModuleLE g (refinedErrorBoundTerm pkg a sigma I K L)
      (refinedScalarBoundTerm pkg a H Bprime I K L) := by
  classical
  have hP (i : Fin s) :
      ModuleLE g ((pkg i).substP (a i) ^ 2)
        (C Bprime * (pkg i).substV (a i) ^ 2) :=
    (pkg i).substP_sq_le_B_mul_substV_sq hδ hB htheta1
      hBcondition (ha i) (hBa i)
  have hthetaP (i : Fin s) :
      ModuleLE g
        (C theta * (pkg i).substP (a i) ^ 2)
        (C (theta * Bprime) * (pkg i).substV (a i) ^ 2) := by
    have hscaled := ModuleLE.sos_mul_left
      (IsSOS_C_nonneg theta htheta) (hP i)
    convert hscaled using 1
    all_goals simp only [map_mul]
    all_goals ring
  have hPlo : IsSOS
      (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_sq _
  have hPup : IsSOS
      (∏ i ∈ I \ K,
        C Bprime * (pkg i).substV (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_mul (IsSOS_C_nonneg Bprime hBprime) (IsSOS_sq _)
  have hPprod : ModuleLE g
      (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2)
      (∏ i ∈ I \ K,
        C Bprime * (pkg i).substV (a i) ^ 2) := by
    apply ModuleLE.prod (I \ K)
    · intro i hi; exact IsSOS_sq _
    · intro i hi
      exact IsSOS_mul (IsSOS_C_nonneg Bprime hBprime) (IsSOS_sq _)
    · intro i hi; exact hP i
  have hL : IsSOS
      (∏ i ∈ L, C δ * (pkg i).substV (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _)
  have hThetaLo : IsSOS
      (∏ i ∈ K \ L,
        C theta * (pkg i).substP (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _)
  have hThetaUp : IsSOS
      (∏ i ∈ K \ L,
        C (theta * Bprime) * (pkg i).substV (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_mul
      (IsSOS_C_nonneg (theta * Bprime) (mul_nonneg htheta hBprime))
      (IsSOS_sq _)
  have hThetaProd : ModuleLE g
      (∏ i ∈ K \ L,
        C theta * (pkg i).substP (a i) ^ 2)
      (∏ i ∈ K \ L,
        C (theta * Bprime) * (pkg i).substV (a i) ^ 2) := by
    apply ModuleLE.prod (K \ L)
    · intro i hi
      exact IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _)
    · intro i hi
      exact IsSOS_mul
        (IsSOS_C_nonneg (theta * Bprime) (mul_nonneg htheta hBprime))
        (IsSOS_sq _)
    · intro i hi; exact hthetaP i
  have hV : IsSOS
      (∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_sq _
  have hfirst := ModuleLE.mul (hsigma I) hPup
    (hsigmaBound I) hPprod
  have hsecond := ModuleLE.mul
    (IsSOS_mul (hsigma I) hPlo) hL hfirst (ModuleLE.refl g _)
  have hthird := ModuleLE.mul
    (IsSOS_mul (IsSOS_mul (hsigma I) hPlo) hL) hThetaUp
    hsecond hThetaProd
  have hfourth := ModuleLE.mul
    (IsSOS_mul (IsSOS_mul (IsSOS_mul (hsigma I) hPlo) hL) hThetaLo)
    hV hthird (ModuleLE.refl g _)
  simpa only [refinedErrorBoundTerm, refinedScalarBoundTerm] using hfourth

/-- Numerical coefficient of a refined scalar-denominator term. -/
def refinedRemainderCoefficient
    (H Bprime theta δ : ℝ)
    (I K L : Finset (Fin s)) : ℝ :=
  H * Bprime ^ (I \ K).card * δ ^ L.card *
    (theta * Bprime) ^ (K \ L).card

/-- A refined scalar bound is exactly a scalar multiple of the common
denominator. -/
theorem refinedScalarBoundTerm_eq_coefficient_mul_denominator
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (H Bprime : ℝ) (I K L : Finset (Fin s))
    (hKI : K ⊆ I) (hLK : L ⊆ K) :
    refinedScalarBoundTerm pkg a H Bprime I K L =
      C (refinedRemainderCoefficient H Bprime theta δ I K L) *
        denominatorProduct pkg a := by
  classical
  let Vsq : Fin s → MvPolynomial (Fin n) ℝ :=
    fun i => (pkg i).substV (a i) ^ 2
  have hprod (S : Finset (Fin s)) (c : ℝ) :
      (∏ i ∈ S, C c * Vsq i) =
        C (c ^ S.card) * ∏ i ∈ S, Vsq i := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, map_pow]
  have hdisj₁ : Disjoint (I \ K) L := by
    exact Finset.disjoint_of_subset_right hLK Finset.sdiff_disjoint
  have hdisj₂ : Disjoint ((I \ K) ∪ L) (K \ L) := by
    rw [Finset.disjoint_union_left]
    constructor
    · exact Finset.disjoint_of_subset_right Finset.sdiff_subset
        Finset.sdiff_disjoint
    · exact Finset.disjoint_sdiff
  have hunion : ((I \ K) ∪ L) ∪ (K \ L) = I := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((⟨hi, _⟩ | hi) | ⟨hi, _⟩)
      · exact hi
      · exact hKI (hLK hi)
      · exact hKI hi
    · intro hi
      by_cases hiK : i ∈ K
      · by_cases hiL : i ∈ L
        · exact Or.inl (Or.inr hiL)
        · exact Or.inr ⟨hiK, hiL⟩
      · exact Or.inl (Or.inl ⟨hi, hiK⟩)
  have hinside :
      ((∏ i ∈ I \ K, Vsq i) * (∏ i ∈ L, Vsq i)) *
          (∏ i ∈ K \ L, Vsq i) =
        ∏ i ∈ I, Vsq i := by
    rw [← Finset.prod_union hdisj₁, ← Finset.prod_union hdisj₂, hunion]
  have hden :
      (∏ i ∈ I, Vsq i) * (∏ i ∈ Iᶜ, Vsq i) =
        denominatorProduct pkg a :=
    (denominatorProduct_eq_subset_mul_compl pkg a I).symm
  unfold refinedScalarBoundTerm
  change C H * (∏ i ∈ I \ K, C Bprime * Vsq i) *
      (∏ i ∈ L, C δ * Vsq i) *
      (∏ i ∈ K \ L, C (theta * Bprime) * Vsq i) *
      ∏ i ∈ Iᶜ, Vsq i = _
  rw [hprod, hprod, hprod]
  rw [← hden, ← hinside]
  unfold refinedRemainderCoefficient
  simp only [map_mul, map_pow]
  ring

/-- The contribution of all genuinely delta-dependent refined terms. -/
def sharpDeltaCoefficient
    (s : ℕ) (H Bprime theta δ : ℝ) : ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
    ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
      ∑ L ∈ K.powerset.erase ∅,
        refinedRemainderCoefficient H Bprime theta δ I K L

/-- Uniform coefficient used to absorb all pure-theta terms into the
zero-error aggregate. -/
def sharpThetaCoefficient (s : ℕ) (theta : ℝ) : ℝ :=
  (oddPairCount s : ℝ) * theta

/-- One odd error term is bounded by its pure-theta contribution plus all
of its genuinely delta-dependent denominator contributions. -/
theorem errorExpansionTerm_le_sharpPairBound
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H Bprime : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaBound : ∀ I, ModuleLE g (sigma I) (C H))
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hBa : ∀ i, QuadraticModuleMem g (C B - a i))
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBprime : 0 ≤ Bprime)
    (hBcondition : B + δ ≤ (1 - theta) * Bprime)
    (I K : Finset (Fin s)) (hKI : K ⊆ I)
    (hKodd : ¬ Even K.card) :
    ModuleLE g (errorExpansionTerm pkg a sigma I K)
      (C theta * zeroErrorTerm pkg a sigma I +
        ∑ L ∈ K.powerset.erase ∅,
          C (refinedRemainderCoefficient H Bprime theta δ I K L) *
            denominatorProduct pkg a) := by
  classical
  have htheta_le_one : theta ≤ 1 := le_of_lt htheta1
  have hodd : Odd K.card := Nat.not_even_iff_odd.mp hKodd
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hodd.pos.ne'
  have hthetaPow : theta ^ K.card ≤ theta := by
    rw [hj, pow_succ']
    exact (mul_le_mul_of_nonneg_left
      (pow_le_one₀ htheta htheta_le_one) htheta).trans_eq (mul_one theta)
  have hzeroSOS : IsSOS (zeroErrorTerm pkg a sigma I) :=
    errorExpansionTerm_isSOS pkg a sigma hsigma hδ I ∅
  have hempty : (∅ : Finset (Fin s)) ∈ K.powerset := by simp
  have hpure : ModuleLE g
      (refinedErrorBoundTerm pkg a sigma I K ∅)
      (C theta * zeroErrorTerm pkg a sigma I) := by
    rw [refinedErrorBoundTerm_empty pkg a sigma I K hKI]
    exact ModuleLE.sos_mul_right hzeroSOS
      (ModuleLE.constant hthetaPow)
  have hrem : ModuleLE g
      (∑ L ∈ K.powerset.erase ∅,
        refinedErrorBoundTerm pkg a sigma I K L)
      (∑ L ∈ K.powerset.erase ∅,
        C (refinedRemainderCoefficient H Bprime theta δ I K L) *
          denominatorProduct pkg a) := by
    apply ModuleLE.sum
    intro L hL
    have hLK : L ⊆ K :=
      Finset.mem_powerset.mp (Finset.mem_erase.mp hL).2
    have hcmp :=
      refinedErrorBoundTerm_le_refinedScalarBoundTerm
        pkg a sigma hsigma hsigmaBound ha hBa hδ hB htheta htheta1
        hBprime hBcondition I K L
    rw [refinedScalarBoundTerm_eq_coefficient_mul_denominator
      pkg a H Bprime I K L hKI hLK] at hcmp
    exact hcmp
  have hsplit :
      errorBoundTerm pkg a sigma I K =
        refinedErrorBoundTerm pkg a sigma I K ∅ +
          ∑ L ∈ K.powerset.erase ∅,
            refinedErrorBoundTerm pkg a sigma I K L := by
    rw [errorBoundTerm_eq_sum_refined]
    calc
      ∑ L ∈ K.powerset, refinedErrorBoundTerm pkg a sigma I K L =
          (∑ L ∈ K.powerset.erase ∅,
            refinedErrorBoundTerm pkg a sigma I K L) +
              refinedErrorBoundTerm pkg a sigma I K ∅ :=
        (Finset.sum_erase_add K.powerset
          (fun L => refinedErrorBoundTerm pkg a sigma I K L) hempty).symm
      _ = _ := add_comm _ _
  have hbound : ModuleLE g (errorBoundTerm pkg a sigma I K)
      (C theta * zeroErrorTerm pkg a sigma I +
        ∑ L ∈ K.powerset.erase ∅,
          C (refinedRemainderCoefficient H Bprime theta δ I K L) *
            denominatorProduct pkg a) := by
    rw [hsplit]
    exact ModuleLE.add hpure hrem
  exact (errorExpansionTerm_le_errorBoundTerm
    pkg a sigma hsigma ha hBa hδ hB htheta I K).trans hbound

/-- Pure-theta coefficients for one outer subset are bounded by the
uniform global coefficient. -/
theorem odd_card_mul_theta_le_sharpThetaCoefficient
    {s : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (I : Finset (Fin s))
    (hI : I ∈ (Finset.univ : Finset (Fin s)).powerset) :
    ((I.powerset.filter (fun K => ¬ Even K.card)).card : ℝ) * theta ≤
      sharpThetaCoefficient s theta := by
  have hcardNat :
      (I.powerset.filter (fun K => ¬ Even K.card)).card ≤
        oddPairCount s := by
    unfold oddPairCount
    exact Finset.single_le_sum
      (fun J hJ => Nat.zero_le
        (J.powerset.filter (fun K => ¬ Even K.card)).card) hI
  have hcard :
      ((I.powerset.filter (fun K => ¬ Even K.card)).card : ℝ) ≤
        (oddPairCount s : ℝ) := by
    exact_mod_cast hcardNat
  exact mul_le_mul_of_nonneg_right hcard htheta

/-- The pure-theta part of the global odd sum is absorbed by the
zero-error aggregate. -/
theorem sharpThetaSum_le_convertedZero
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hδ : 0 < δ) (htheta : 0 ≤ theta) :
    ModuleLE g
      (∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        C (((I.powerset.filter (fun K => ¬ Even K.card)).card : ℝ) *
          theta) * zeroErrorTerm pkg a sigma I)
      (C (sharpThetaCoefficient s theta) *
        convertedZero pkg a sigma) := by
  classical
  have hsum := ModuleLE.sum (g := g)
    (s := (Finset.univ : Finset (Fin s)).powerset)
    (p := fun I =>
      C (((I.powerset.filter (fun K => ¬ Even K.card)).card : ℝ) *
        theta) * zeroErrorTerm pkg a sigma I)
    (q := fun I =>
      C (sharpThetaCoefficient s theta) * zeroErrorTerm pkg a sigma I)
    (fun I hI => by
      exact ModuleLE.sos_mul_right
        (errorExpansionTerm_isSOS pkg a sigma hsigma hδ I ∅)
        (ModuleLE.constant (g := g)
          (odd_card_mul_theta_le_sharpThetaCoefficient htheta I hI)))
  simpa [convertedZero, Finset.mul_sum] using hsum

/-- Global two-channel absorption: the fixed approximation error is charged
to the converted even SOS, while only delta-dependent terms are charged to
the common denominator. -/
theorem convertedOdd_le_sharpAbsorption
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H Bprime : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaBound : ∀ I, ModuleLE g (sigma I) (C H))
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hBa : ∀ i, QuadraticModuleMem g (C B - a i))
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBprime : 0 ≤ Bprime)
    (hBcondition : B + δ ≤ (1 - theta) * Bprime) :
    ModuleLE g (convertedOdd pkg a sigma)
      (C (sharpThetaCoefficient s theta) * convertedEven pkg a sigma +
        C (sharpDeltaCoefficient s H Bprime theta δ) *
          denominatorProduct pkg a) := by
  classical
  let Sall : Finset (Finset (Fin s)) :=
    (Finset.univ : Finset (Fin s)).powerset
  let T : Finset (Fin s) → Finset (Finset (Fin s)) :=
    fun I => I.powerset.filter (fun K => ¬ Even K.card)
  let D := denominatorProduct pkg a
  have hraw := ModuleLE.sum (g := g)
    (s := Sall)
    (p := fun I => oddErrorSum pkg a sigma I)
    (q := fun I =>
      ∑ K ∈ T I,
        (C theta * zeroErrorTerm pkg a sigma I +
          ∑ L ∈ K.powerset.erase ∅,
            C (refinedRemainderCoefficient H Bprime theta δ I K L) *
              D))
    (fun I hI => by
      apply ModuleLE.sum
      intro K hK
      have hfilter := Finset.mem_filter.mp hK
      exact errorExpansionTerm_le_sharpPairBound
        pkg a sigma hsigma hsigmaBound ha hBa hδ hB htheta htheta1
        hBprime hBcondition I K (Finset.mem_powerset.mp hfilter.1)
        hfilter.2)
  have hrhs :
      (∑ I ∈ Sall,
        ∑ K ∈ T I,
          (C theta * zeroErrorTerm pkg a sigma I +
            ∑ L ∈ K.powerset.erase ∅,
              C (refinedRemainderCoefficient H Bprime theta δ I K L) *
                D)) =
        (∑ I ∈ Sall,
          C (((T I).card : ℝ) * theta) *
            zeroErrorTerm pkg a sigma I) +
          C (sharpDeltaCoefficient s H Bprime theta δ) * D := by
    dsimp [Sall, T, D]
    unfold sharpDeltaCoefficient
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      map_sum, Finset.sum_mul, map_mul, map_natCast]
    simp only [mul_comm, mul_assoc]
  have hnormalized : ModuleLE g (convertedOdd pkg a sigma)
      ((∑ I ∈ Sall,
          C (((T I).card : ℝ) * theta) *
            zeroErrorTerm pkg a sigma I) +
        C (sharpDeltaCoefficient s H Bprime theta δ) * D) := by
    rw [hrhs] at hraw
    simpa [convertedOdd, oddErrorSum, Sall, T] using hraw
  have hthetaBound := sharpThetaSum_le_convertedZero
    (g := g) pkg a sigma hsigma hδ htheta
  have htoZero := ModuleLE.add hthetaBound
    (ModuleLE.refl g
      (C (sharpDeltaCoefficient s H Bprime theta δ) * D))
  have halpha : 0 ≤ sharpThetaCoefficient s theta := by
    unfold sharpThetaCoefficient
    positivity
  have hzeroEven : ModuleLE g
      (C (sharpThetaCoefficient s theta) * convertedZero pkg a sigma)
      (C (sharpThetaCoefficient s theta) * convertedEven pkg a sigma) :=
    ModuleLE.sos_mul_left
      (IsSOS_C_nonneg (sharpThetaCoefficient s theta) halpha)
      (convertedZero_le_convertedEven (g := g) pkg a sigma hsigma hδ)
  have htoEven := ModuleLE.add hzeroEven
    (ModuleLE.refl g
      (C (sharpDeltaCoefficient s H Bprime theta δ) * D))
  exact hnormalized.trans (htoZero.trans htoEven)


/-- Number of triples L ⊆ K ⊆ I occurring in the genuinely
delta-dependent part of the odd expansion. -/
def sharpTripleCount (s : ℕ) : ℕ :=
  ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
    ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
      (K.powerset.erase ∅).card

/-- Every genuinely delta-dependent scalar is bounded by the same
H * delta * (Bprime + 1)^s envelope. -/
theorem refinedRemainderCoefficient_le_common
    {s : ℕ} {H Bprime theta δ : ℝ}
    (hH : 0 ≤ H) (hBprime : 0 ≤ Bprime)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (I K L : Finset (Fin s))
    (hKI : K ⊆ I) (hLK : L ⊆ K) (hL : L ≠ ∅) :
    refinedRemainderCoefficient H Bprime theta δ I K L ≤
      H * δ * (Bprime + 1) ^ s := by
  let M : ℝ := Bprime + 1
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hthetaB : 0 ≤ theta * Bprime :=
    mul_nonneg htheta hBprime
  have hthetaB_le : theta * Bprime ≤ M := by
    have hle : theta * Bprime ≤ Bprime := by
      nlinarith [mul_nonneg (sub_nonneg.mpr htheta1) hBprime]
    dsimp [M]
    linarith
  have hBprimeM : Bprime ≤ M := by dsimp [M]; linarith
  have hdisj : Disjoint (I \ K) (K \ L) := by
    exact Finset.disjoint_of_subset_right Finset.sdiff_subset
      Finset.sdiff_disjoint
  have hcard : (I \ K).card + (K \ L).card ≤ s := by
    have hsub :
        (I \ K) ∪ (K \ L) ⊆ (Finset.univ : Finset (Fin s)) :=
      Finset.subset_univ _
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at hc
    simpa using hc
  have hpowers :
      Bprime ^ (I \ K).card *
          (theta * Bprime) ^ (K \ L).card ≤ M ^ s := by
    calc
      Bprime ^ (I \ K).card *
          (theta * Bprime) ^ (K \ L).card ≤
          M ^ (I \ K).card * M ^ (K \ L).card := by
        exact mul_le_mul
          (pow_le_pow_left₀ hBprime hBprimeM _)
          (pow_le_pow_left₀ hthetaB hthetaB_le _)
          (pow_nonneg hthetaB _)
          (pow_nonneg (by positivity : 0 ≤ M) _)
      _ = M ^ ((I \ K).card + (K \ L).card) := by
        rw [pow_add]
      _ ≤ M ^ s := pow_le_pow_right₀ hM hcard
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero
    (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hL))
  have hδpow : δ ^ L.card ≤ δ := by
    rw [hj, pow_succ']
    exact (mul_le_mul_of_nonneg_left
      (pow_le_one₀ hδ hδ1) hδ).trans_eq (mul_one δ)
  unfold refinedRemainderCoefficient
  calc
    H * Bprime ^ (I \ K).card * δ ^ L.card *
        (theta * Bprime) ^ (K \ L).card =
        H * δ ^ L.card *
          (Bprime ^ (I \ K).card *
            (theta * Bprime) ^ (K \ L).card) := by ring
    _ ≤ H * δ * M ^ s := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hδpow hH)
        hpowers
        (mul_nonneg (pow_nonneg hBprime _)
          (pow_nonneg hthetaB _))
        (mul_nonneg hH hδ)
    _ = H * δ * (Bprime + 1) ^ s := rfl

/-- The complete denominator coefficient is bounded by the triple count
times the common delta-dependent envelope. -/
theorem sharpDeltaCoefficient_le
    {s : ℕ} {H Bprime theta δ : ℝ}
    (hH : 0 ≤ H) (hBprime : 0 ≤ Bprime)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    sharpDeltaCoefficient s H Bprime theta δ ≤
      (sharpTripleCount s : ℝ) *
        (H * δ * (Bprime + 1) ^ s) := by
  classical
  unfold sharpDeltaCoefficient
  calc
    (∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
      ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
        ∑ L ∈ K.powerset.erase ∅,
          refinedRemainderCoefficient H Bprime theta δ I K L) ≤
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
          ∑ _L ∈ K.powerset.erase ∅,
            H * δ * (Bprime + 1) ^ s := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro K hK
      apply Finset.sum_le_sum
      intro L hL
      have hfilter := Finset.mem_filter.mp hK
      exact refinedRemainderCoefficient_le_common
        hH hBprime htheta htheta1 hδ hδ1 I K L
        (Finset.mem_powerset.mp hfilter.1)
        (Finset.mem_powerset.mp (Finset.mem_erase.mp hL).2)
        (Finset.mem_erase.mp hL).1
    _ = (sharpTripleCount s : ℝ) *
        (H * δ * (Bprime + 1) ^ s) := by
      unfold sharpTripleCount
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      simp_rw [Finset.sum_mul]

/-- Fixed approximation accuracy.  It depends only on the number of
artificial generators, not on the size H of the preordering certificate. -/
def sharpThetaScale (s : ℕ) : ℝ :=
  (2 * ((oddPairCount s : ℝ) + 1))⁻¹

/-- Scalar error scale.  For fixed s and Bprime it is O(1 / (H + 1)). -/
def sharpDeltaScale (s : ℕ) (H Bprime : ℝ) : ℝ :=
  (2 * ((sharpTripleCount s : ℝ) + 1) * (H + 1) *
    (Bprime + 1) ^ s)⁻¹

theorem sharpThetaScale_pos (s : ℕ) :
    0 < sharpThetaScale s := by
  unfold sharpThetaScale
  positivity

theorem sharpThetaScale_le_half (s : ℕ) :
    sharpThetaScale s ≤ 1 / 2 := by
  let count : ℝ := oddPairCount s
  have hcount : 0 ≤ count := by positivity
  have hden : 0 < 2 * (count + 1) := by positivity
  unfold sharpThetaScale
  change (2 * (count + 1))⁻¹ ≤ 1 / 2
  apply (inv_le_iff_one_le_mul₀' hden).2
  nlinarith

theorem sharpThetaCoefficient_scale_lt_one (s : ℕ) :
    sharpThetaCoefficient s (sharpThetaScale s) < 1 := by
  let count : ℝ := oddPairCount s
  have hcount : 0 ≤ count := by positivity
  have hden : 0 < 2 * (count + 1) := by positivity
  have heq :
      sharpThetaCoefficient s (sharpThetaScale s) =
        count / (2 * (count + 1)) := by
    unfold sharpThetaCoefficient sharpThetaScale
    dsimp [count]
    rw [inv_eq_one_div]
    ring
  rw [heq, div_lt_one hden]
  nlinarith

theorem sharpDeltaScale_pos
    {s : ℕ} {H Bprime : ℝ}
    (hH : 0 ≤ H) (hBprime : 0 ≤ Bprime) :
    0 < sharpDeltaScale s H Bprime := by
  unfold sharpDeltaScale
  positivity

theorem sharpDeltaScale_le_half
    {s : ℕ} {H Bprime : ℝ}
    (hH : 0 ≤ H) (hBprime : 0 ≤ Bprime) :
    sharpDeltaScale s H Bprime ≤ 1 / 2 := by
  let count : ℝ := sharpTripleCount s
  let M : ℝ := Bprime + 1
  have hcount : 0 ≤ count := by positivity
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hMpow : 1 ≤ M ^ s := one_le_pow₀ hM
  have hden :
      0 < 2 * (count + 1) * (H + 1) * M ^ s := by
    positivity
  have hdenTwo :
      2 ≤ 2 * (count + 1) * (H + 1) * M ^ s := by
    have hc1 : 1 ≤ count + 1 := by linarith
    have hH1 : 1 ≤ H + 1 := by linarith
    calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ 2 * (count + 1) :=
        mul_le_mul_of_nonneg_left hc1 (by norm_num)
      _ = (2 * (count + 1)) * 1 := by ring
      _ ≤ (2 * (count + 1)) * (H + 1) :=
        mul_le_mul_of_nonneg_left hH1 (by positivity)
      _ = (2 * (count + 1) * (H + 1)) * 1 := by ring
      _ ≤ (2 * (count + 1) * (H + 1)) * M ^ s :=
        mul_le_mul_of_nonneg_left hMpow (by positivity)
  unfold sharpDeltaScale
  change (2 * (count + 1) * (H + 1) * M ^ s)⁻¹ ≤ 1 / 2
  apply (inv_le_iff_one_le_mul₀' hden).2
  nlinarith

theorem sharpDeltaCoefficient_scale_lt_one
    {s : ℕ} {H Bprime theta : ℝ}
    (hH : 0 ≤ H) (hBprime : 0 ≤ Bprime)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    sharpDeltaCoefficient s H Bprime theta
      (sharpDeltaScale s H Bprime) < 1 := by
  let count : ℝ := sharpTripleCount s
  let M : ℝ := Bprime + 1
  let delta : ℝ := sharpDeltaScale s H Bprime
  have hcount : 0 ≤ count := by positivity
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hdelta : 0 < delta :=
    sharpDeltaScale_pos hH hBprime
  have hdeltaHalf : delta ≤ 1 / 2 :=
    sharpDeltaScale_le_half hH hBprime
  have hupper : sharpDeltaCoefficient s H Bprime theta delta ≤
      (sharpTripleCount s : ℝ) *
        (H * delta * (Bprime + 1) ^ s) :=
    sharpDeltaCoefficient_le (s := s) hH hBprime htheta htheta1 hdelta.le
      (hdeltaHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hvalue :
      count * (H * delta * M ^ s) =
        count * H / (2 * (count + 1) * (H + 1)) := by
    dsimp [delta, sharpDeltaScale, count, M]
    rw [inv_eq_one_div]
    field_simp
  have hratio :
      count * H / (2 * (count + 1) * (H + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [mul_nonneg hcount hH]
  exact hupper.trans_lt (hvalue.trans_lt hratio)

/-- Sharp qualitative conversion with the parameter architecture required
for the logarithmic degree estimate: theta is fixed as H varies, while
delta is proportional to 1 / (H + 1). -/
theorem sharp_bounded_preordering_refutation_to_module
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (B H : ℝ)
    (hB : 0 < B) (hH : 0 ≤ H)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaBound : ∀ I, ModuleLE g (sigma I) (C H))
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hBa : ∀ i, QuadraticModuleMem g (C B - a i))
    (hidentity : (-1 : MvPolynomial (Fin n) ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i) :
    QuadraticModuleMem g (-1) := by
  let Bprime : ℝ := 2 * (B + 1)
  let theta : ℝ := sharpThetaScale s
  let delta : ℝ := sharpDeltaScale s H Bprime
  have hBprime : 0 ≤ Bprime := by
    dsimp [Bprime]
    positivity
  have htheta : 0 < theta := by
    dsimp [theta]
    exact sharpThetaScale_pos s
  have hthetaHalf : theta ≤ 1 / 2 := by
    dsimp [theta]
    exact sharpThetaScale_le_half s
  have hthetaOne : theta ≤ 1 :=
    hthetaHalf.trans (by norm_num)
  have hthetaLtOne : theta < 1 :=
    lt_of_le_of_lt hthetaHalf (by norm_num)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact sharpDeltaScale_pos hH hBprime
  have hdeltaHalf : delta ≤ 1 / 2 := by
    dsimp [delta]
    exact sharpDeltaScale_le_half hH hBprime
  have hdeltaOne : delta ≤ 1 :=
    hdeltaHalf.trans (by norm_num)
  have hcondition : B + delta ≤ (1 - theta) * Bprime := by
    have hfactor : 1 ≤ 2 * (1 - theta) := by
      linarith
    have hB1 : 0 ≤ B + 1 := by linarith
    calc
      B + delta ≤ B + 1 := by linarith
      _ = 1 * (B + 1) := by ring
      _ ≤ (2 * (1 - theta)) * (B + 1) :=
        mul_le_mul_of_nonneg_right hfactor hB1
      _ = (1 - theta) * Bprime := by
        dsimp [Bprime]
        ring
  obtain ⟨pkg0⟩ :=
    RationalSquareRoot.package_nonempty hdelta hB.le htheta
  let pkg : Fin s → Package delta B theta := fun _ => pkg0
  apply refutation_of_absorption pkg a sigma hsigma ha hdelta hidentity
    (sharpThetaCoefficient_scale_lt_one s).le
    (sharpDeltaCoefficient_scale_lt_one hH hBprime htheta.le hthetaOne)
  exact convertedOdd_le_sharpAbsorption
    pkg a sigma hsigma hsigmaBound ha hBa hdelta hB htheta.le
      hthetaLtOne hBprime hcondition

end OptimalConvergenceRates.GeneralArchimedean

end
