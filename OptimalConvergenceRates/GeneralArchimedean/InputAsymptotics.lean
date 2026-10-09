/-
  Elementary bounds for the fixed-power coefficient input delivered by
  Krivine--Stengle.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpBridgeAsymptotics

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

/-- There is always at least the constant monomial of bounded degree. -/
theorem one_le_boundedMonomialCount (n d : ℕ) :
    1 ≤ boundedMonomialCount n d := by
  have hfinite :
      ({alpha : Fin n →₀ ℕ | alpha.degree ≤ d} : Set (Fin n →₀ ℕ)).Finite :=
    Finsupp.finite_of_degree_le d
  unfold boundedMonomialCount
  exact (Set.ncard_pos hfinite).2 ⟨0, by simp⟩

/-- A fixed constant controlling a finite-family envelope whose coefficient
bound is at most `A * x^q`. -/
def finiteFamilyPowerConstant
    (familyCard n d : ℕ) (R A : ℝ) : ℝ :=
  2 + (familyCard : ℝ) * (boundedMonomialCount n d : ℝ) *
    ((A / 2) ^ 2 * R ^ d + 1)

theorem one_le_finiteFamilyPowerConstant
    (familyCard n d : ℕ) {R A : ℝ}
    (hR : 0 ≤ R) :
    1 ≤ finiteFamilyPowerConstant familyCard n d R A := by
  unfold finiteFamilyPowerConstant
  have hpow : 0 ≤ R ^ d := pow_nonneg hR d
  have hterm : 0 ≤ (familyCard : ℝ) * (boundedMonomialCount n d : ℝ) *
      ((A / 2) ^ 2 * R ^ d + 1) := by positivity
  linarith

/-- The common finite-family envelope dominates its input coefficient bound
as soon as the family is nonempty and the radius is at least one. -/
theorem le_finiteFamilyEnvelopeBound
    {familyCard n d : ℕ} {R H : ℝ}
    (hcard : 1 ≤ familyCard) (hR : 1 ≤ R) (hH : 0 ≤ H) :
    H ≤ finiteFamilyEnvelopeBound familyCard n d R H := by
  have hcountNat := one_le_boundedMonomialCount n d
  have hcardReal : (1 : ℝ) ≤ familyCard := by exact_mod_cast hcard
  have hcountReal : (1 : ℝ) ≤ boundedMonomialCount n d := by
    exact_mod_cast hcountNat
  have hfactor : (1 : ℝ) ≤
      (familyCard : ℝ) * (boundedMonomialCount n d : ℝ) := by
    nlinarith
  have hRpow : 1 ≤ R ^ d := one_le_pow₀ hR
  have hquad : H ≤ (H / 2) ^ 2 + 1 := by
    nlinarith [sq_nonneg (H / 2 - 1)]
  have hinside : H ≤ (H / 2) ^ 2 * R ^ d + 1 := by
    have hsquare : (H / 2) ^ 2 ≤ (H / 2) ^ 2 * R ^ d :=
      le_mul_of_one_le_right (sq_nonneg _) hRpow
    linarith
  have hinside0 : 0 ≤ (H / 2) ^ 2 * R ^ d + 1 := by positivity
  have hscaled :
      (H / 2) ^ 2 * R ^ d + 1 ≤
        ((familyCard : ℝ) * (boundedMonomialCount n d : ℝ)) *
          ((H / 2) ^ 2 * R ^ d + 1) :=
    le_mul_of_one_le_left hinside0 hfactor
  unfold finiteFamilyEnvelopeBound polynomialEnvelopeBound
  linarith

/-- A finite-family coefficient envelope with power-bounded input is itself
bounded by a fixed constant times twice that power. -/
theorem finiteFamilyEnvelopeBound_add_one_le_const_mul_pow
    {familyCard n d q : ℕ} {R H A x : ℝ}
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hA : 0 ≤ A) (hx : 1 ≤ x)
    (hHbound : H ≤ A * x ^ q) :
    finiteFamilyEnvelopeBound familyCard n d R H + 1 ≤
      finiteFamilyPowerConstant familyCard n d R A * x ^ (2 * q) := by
  let c : ℝ :=
    (familyCard : ℝ) * (boundedMonomialCount n d : ℝ)
  let z : ℝ := x ^ (2 * q)
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hz : 1 ≤ z := by
    dsimp [z]
    exact one_le_pow₀ hx
  have hAx : 0 ≤ A * x ^ q := mul_nonneg hA (pow_nonneg hx0 q)
  have hsq : (H / 2) ^ 2 ≤ (A / 2) ^ 2 * z := by
    calc
      (H / 2) ^ 2 ≤ (A * x ^ q / 2) ^ 2 := by
        gcongr
      _ = (A / 2) ^ 2 * z := by
        dsimp [z]
        rw [pow_mul]
        ring
  have hRpow : 0 ≤ R ^ d := pow_nonneg hR d
  have hfirst :
      finiteFamilyEnvelopeBound familyCard n d R H + 1 ≤
        2 + c * ((A / 2) ^ 2 * z * R ^ d + 1) := by
    calc
      finiteFamilyEnvelopeBound familyCard n d R H + 1 =
          2 + c * ((H / 2) ^ 2 * R ^ d + 1) := by
        unfold finiteFamilyEnvelopeBound polynomialEnvelopeBound
        dsimp [c]
        ring
      _ ≤ 2 + c * ((A / 2) ^ 2 * z * R ^ d + 1) := by gcongr
  have hsecond :
      2 + c * ((A / 2) ^ 2 * z * R ^ d + 1) ≤
        (2 + c * ((A / 2) ^ 2 * R ^ d + 1)) * z := by
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hz)]
  exact hfirst.trans (by
    simpa [finiteFamilyPowerConstant, c, z] using hsecond)

end OptimalConvergenceRates.GeneralArchimedean

end
