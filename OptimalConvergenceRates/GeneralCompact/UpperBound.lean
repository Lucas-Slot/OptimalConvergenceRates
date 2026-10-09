/-
  Single-log degree cost and its log-square/r-square inversion.
-/
import OptimalConvergenceRates.GeneralCompact.Elimination
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeAssembly
import OptimalConvergenceRates.GeneralArchimedean.LogSquareBounds
import OptimalConvergenceRates.GeneralArchimedean.EliminationAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralCompact

variable {n m : ℕ}

/-- Degree scale produced by direct preordering elimination. -/
def schmudgenDegreeCost (D K epsilon : ℝ) : ℝ :=
  D + K / Real.sqrt epsilon * (1 + Real.log epsilon⁻¹)

/-- Fixed constant in the polynomial envelope for a direct refutation
multiplier. -/
def directMultiplierPowerConstant (n r : ℕ) (B A : ℝ) : ℝ :=
  1 + (GeneralArchimedean.boundedMonomialCount n r : ℝ) *
    (((max 1 A / 2) ^ 2 * B ^ r) + 1)

/-- A fixed upper bound for the perturbed objective used in elimination. -/
def objectivePreorderingEnvelope
    (B : ℝ) (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  2 + GeneralArchimedean.weightedCoeffEnvelope B p

/-- Quantitative input to the elementary inversion. The factor two records
that elimination turns a refutation at `p + epsilon` into a certificate at
`p + 2 epsilon`. -/
def HasSchmudgenDegreeCostBound
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧
    ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
      p + C (2 * epsilon) ∈
        GenPreordering g (Nat.ceil (schmudgenDegreeCost D K epsilon))

/-- Membership in a truncated preordering bounds the degree of the represented
polynomial, independently of the chosen representation. -/
theorem totalDegree_le_of_mem_genPreordering
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hq : q ∈ GenPreordering g r) : q.totalDegree ≤ r := by
  obtain ⟨sigma, _hsigma, hdegree, rfl⟩ := hq
  exact KrivineStengle.totalDegree_sum_le_of_each _ _ r
    (fun I _ ↦ hdegree I)

/-- The algebraic part of the quantitative argument. A direct fixed-order
refutation is eliminated without converting it to a quadratic module. -/
theorem eliminate_bounded_direct_refutation
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p s t : MvPolynomial (Fin n) ℝ)
    {B : ℝ} {envelopeOrder refutationOrder : ℕ}
    (hB : 1 ≤ B)
    (henvelope : ∀ q : MvPolynomial (Fin n) ℝ,
      C (GeneralArchimedean.weightedCoeffEnvelope B q) + q ∈
          GenPreordering g (envelopeOrder + 2 * q.totalDegree) ∧
        C (GeneralArchimedean.weightedCoeffEnvelope B q) - q ∈
          GenPreordering g (envelopeOrder + 2 * q.totalDegree))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hs : s ∈ GenPreordering g refutationOrder)
    (ht : t ∈ GenPreordering g refutationOrder)
    (hrefute : (-1 : MvPolynomial (Fin n) ℝ) =
      s - (p + C epsilon) * t) :
    let Czero := 1 + GeneralArchimedean.weightedCoeffEnvelope B t
    let U := 2 + GeneralArchimedean.weightedCoeffEnvelope B p
    p + C (2 * epsilon) ∈ GenPreordering g
      (GeneralArchimedean.perturbationEliminationOrder p.totalDegree
        refutationOrder envelopeOrder
        (GeneralArchimedean.chebyshevDegree epsilon Czero⁻¹ U)) := by
  dsimp only
  let Czero := 1 + GeneralArchimedean.weightedCoeffEnvelope B t
  let U := 2 + GeneralArchimedean.weightedCoeffEnvelope B p
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hCzero : 0 < Czero := by
    dsimp [Czero]
    have := GeneralArchimedean.weightedCoeffEnvelope_nonneg hB0 t
    linarith
  have hCzero_t : C Czero - t ∈
      GenPreordering g (envelopeOrder + 2 * refutationOrder) := by
    have hbase := (henvelope t).2
    have htDegree := totalDegree_le_of_mem_genPreordering ht
    have hbase' := GenPreordering_mono
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 htDegree) envelopeOrder)
      hbase
    have hone : (C (1 : ℝ) : MvPolynomial (Fin n) ℝ) ∈
        GenPreordering g 0 :=
      KrivineStengle.genPreordering_C_nonneg g zero_le_one
    have hone' : (C (1 : ℝ) : MvPolynomial (Fin n) ℝ) ∈
        GenPreordering g (envelopeOrder + 2 * refutationOrder) :=
      GenPreordering_mono (Nat.zero_le _) hone
    have hsum := KrivineStengle.genPreordering_add hbase' hone'
    have hsum' : C (GeneralArchimedean.weightedCoeffEnvelope B t) - t +
        C (1 : ℝ) ∈ GenPreordering g
          (envelopeOrder + 2 * refutationOrder) := by simpa using hsum
    convert hsum' using 1
    simp only [Czero, map_add, map_one]
    ring
  have hone_tau : 1 - C Czero⁻¹ * t ∈
      GenPreordering g (envelopeOrder + 2 * refutationOrder) := by
    have hc : (C Czero⁻¹ : MvPolynomial (Fin n) ℝ) ∈
        GenPreordering g 0 :=
      KrivineStengle.genPreordering_C_nonneg g
        (inv_nonneg.mpr hCzero.le)
    have hscaled := KrivineStengle.genPreordering_mul hc hCzero_t
    rw [show 1 - C Czero⁻¹ * t = C Czero⁻¹ * (C Czero - t) by
      rw [mul_sub, ← map_mul, inv_mul_cancel₀ hCzero.ne', map_one]]
    simpa using hscaled
  have hU : 0 < U := by
    dsimp [U]
    have := GeneralArchimedean.weightedCoeffEnvelope_nonneg hB0 p
    linarith
  have hUq : C U - (p + C epsilon) ∈
      GenPreordering g (envelopeOrder + 2 * p.totalDegree) := by
    have hbase := (henvelope p).2
    have hconst : (C (2 - epsilon) : MvPolynomial (Fin n) ℝ) ∈
        GenPreordering g 0 :=
      KrivineStengle.genPreordering_C_nonneg g (by linarith)
    have hconst' : (C (2 - epsilon) : MvPolynomial (Fin n) ℝ) ∈
        GenPreordering g (envelopeOrder + 2 * p.totalDegree) :=
      GenPreordering_mono (Nat.zero_le _) hconst
    have hsum := KrivineStengle.genPreordering_add hbase hconst'
    have hsum' : C (GeneralArchimedean.weightedCoeffEnvelope B p) - p +
        C (2 - epsilon) ∈ GenPreordering g
          (envelopeOrder + 2 * p.totalDegree) := by simpa using hsum
    convert hsum' using 1
    simp only [U, map_add, map_sub]
    ring
  obtain ⟨W, hWdegree⟩ :=
    GeneralArchimedean.chebyshevEliminationWeight_exists
      hepsilon (inv_pos.mpr hCzero) hU
  have hqDegree : (p + C epsilon).totalDegree ≤ p.totalDegree :=
    (MvPolynomial.totalDegree_add _ _).trans (by simp)
  have hcert := eliminate_refutation_of_weight_at_bound
    p s t epsilon Czero U hCzero hepsilon.le hrefute hs ht hone_tau
    hUq W hWdegree hqDegree
  simpa [GeneralArchimedean.perturbationEliminationOrder] using hcert

/-- The normalization constant of a fixed-order direct refutation grows only
polynomially in `epsilon⁻¹`. -/
theorem direct_multiplier_envelope_le_power
    {B A epsilon : ℝ} {k r : ℕ}
    (hB : 1 ≤ B)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (t : MvPolynomial (Fin n) ℝ)
    (htDegree : t.totalDegree ≤ r)
    (htNorm : coeffL1Norm t ≤ (epsilon ^ (2 * k))⁻¹ * A) :
    1 + GeneralArchimedean.weightedCoeffEnvelope B t ≤
      directMultiplierPowerConstant n r B A * epsilon⁻¹ ^ (4 * k) := by
  let x := epsilon⁻¹
  let A₁ := max 1 A
  let P := x ^ (4 * k)
  have hx : 1 ≤ x := (one_le_inv₀ hepsilon).2 hepsilon1
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hA₁ : 1 ≤ A₁ := le_max_left _ _
  have hAA₁ : A ≤ A₁ := le_max_right _ _
  have hP : 1 ≤ P := by
    dsimp [P]
    exact one_le_pow₀ hx
  have hnorm : coeffL1Norm t ≤ A₁ * x ^ (2 * k) := by
    calc
      coeffL1Norm t ≤ (epsilon ^ (2 * k))⁻¹ * A := htNorm
      _ = x ^ (2 * k) * A := by simp [x, inv_pow]
      _ ≤ x ^ (2 * k) * A₁ :=
        mul_le_mul_of_nonneg_left hAA₁ (pow_nonneg hx0 _)
      _ = A₁ * x ^ (2 * k) := by ring
  have henv :=
    GeneralArchimedean.weightedCoeffEnvelope_le_polynomialEnvelopeBound
      hB (mul_nonneg (zero_le_one.trans hA₁) (pow_nonneg hx0 _)) t htDegree hnorm
  have hpowIdentity : (x ^ (2 * k)) ^ 2 = P := by
    dsimp [P]
    rw [← pow_mul]
    congr 1
    omega
  have hinside :
      ((A₁ * x ^ (2 * k)) / 2) ^ 2 * B ^ r + 1 ≤
        (((A₁ / 2) ^ 2 * B ^ r) + 1) * P := by
    rw [show ((A₁ * x ^ (2 * k)) / 2) ^ 2 =
        (A₁ / 2) ^ 2 * P by rw [div_pow, mul_pow, hpowIdentity]; ring]
    have hterm : 0 ≤ (A₁ / 2) ^ 2 * B ^ r := by positivity
    nlinarith
  have hcount : 0 ≤
      (GeneralArchimedean.boundedMonomialCount n r : ℝ) := by positivity
  calc
    1 + GeneralArchimedean.weightedCoeffEnvelope B t ≤
        1 + GeneralArchimedean.polynomialEnvelopeBound n r B
          (A₁ * x ^ (2 * k)) := by
            simpa [add_comm] using add_le_add_left henv 1
    _ ≤ 1 + (GeneralArchimedean.boundedMonomialCount n r : ℝ) *
          ((((A₁ / 2) ^ 2 * B ^ r) + 1) * P) := by
      unfold GeneralArchimedean.polynomialEnvelopeBound
      gcongr
    _ ≤ (1 + (GeneralArchimedean.boundedMonomialCount n r : ℝ) *
          (((A₁ / 2) ^ 2 * B ^ r) + 1)) * P := by
      have hq : 0 ≤ ((A₁ / 2) ^ 2 * B ^ r) + 1 := by positivity
      nlinarith [mul_nonneg hcount hq]
    _ = directMultiplierPowerConstant n r B A * epsilon⁻¹ ^ (4 * k) := by
      rfl

/-- A polynomial bound for the normalization constant produces the
inverse-square-root/single-log Chebyshev degree bound. -/
theorem chebyshevDegree_le_invSqrt_log
    {epsilon Czero U C x : ℝ} {q : ℕ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hxdef : x = epsilon⁻¹) (hU : 2 ≤ U)
    (hCzero : 1 ≤ Czero) (hC : 1 ≤ C)
    (hCzeroBound : Czero ≤ C * x ^ q) :
    (GeneralArchimedean.chebyshevDegree epsilon Czero⁻¹ U : ℝ) ≤
      (Real.sqrt (2 / U))⁻¹ * (1 + Real.log (4 * C) + q) /
          Real.sqrt epsilon * (1 + Real.log x) + 1 := by
  subst x
  have hx : 1 ≤ epsilon⁻¹ := (one_le_inv₀ hepsilon).2 hepsilon1
  have hUpos : 0 < U := by linarith
  have htwoU : 0 < 2 / U := div_pos (by norm_num) hUpos
  have hCzeroPos : 0 < Czero := zero_lt_one.trans_le hCzero
  have hc : 0 < Czero⁻¹ := inv_pos.mpr hCzeroPos
  have hsmall : (2 / U) * epsilon ≤ 1 := by
    have hfac : 2 / U ≤ 1 := (div_le_one hUpos).2 hU
    nlinarith [mul_nonneg htwoU.le hepsilon.le]
  have hbase := GeneralArchimedean.chebyshevDegree_cast_le
    hepsilon hc hUpos hsmall
  let y := 2 * (1 + epsilon / Czero⁻¹)
  have hyOne : 1 ≤ y := by
    dsimp [y]
    have : 0 < epsilon / Czero⁻¹ := div_pos hepsilon hc
    linarith
  have hCxOne : 1 ≤ C * epsilon⁻¹ ^ q := by
    exact one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hx)
  have hepsC : epsilon / Czero⁻¹ ≤ C * epsilon⁻¹ ^ q := by
    rw [div_eq_mul_inv, inv_inv]
    exact (mul_le_of_le_one_left hCzeroPos.le hepsilon1).trans hCzeroBound
  have hyBound : y ≤ (4 * C) * epsilon⁻¹ ^ q := by
    dsimp [y]
    nlinarith
  have hfourC : 1 ≤ 4 * C := by nlinarith
  have hlogBound :
      1 + Real.log y ≤
        (1 + Real.log (4 * C) + q) *
          (1 + Real.log epsilon⁻¹) := by
    exact GeneralArchimedean.one_add_log_le_of_le_const_mul_pow
      hx hyOne hfourC hyBound
  have hlogNumerator :
      Real.log y ≤
        (1 + Real.log (4 * C) + q) *
          (1 + Real.log epsilon⁻¹) := by
    linarith
  have hsqrt : Real.sqrt ((2 / U) * epsilon) =
      Real.sqrt (2 / U) * Real.sqrt epsilon := by
    rw [Real.sqrt_mul htwoU.le]
  have hsqrtFac : 0 < Real.sqrt (2 / U) := Real.sqrt_pos.2 htwoU
  have hsqrtEps : 0 < Real.sqrt epsilon := Real.sqrt_pos.2 hepsilon
  calc
    (GeneralArchimedean.chebyshevDegree epsilon Czero⁻¹ U : ℝ) ≤
        Real.log y / Real.sqrt ((2 / U) * epsilon) + 1 := by
          simpa [y] using hbase
    _ ≤ ((1 + Real.log (4 * C) + q) *
          (1 + Real.log epsilon⁻¹)) /
          Real.sqrt ((2 / U) * epsilon) + 1 := by
      gcongr
    _ = (Real.sqrt (2 / U))⁻¹ * (1 + Real.log (4 * C) + q) /
          Real.sqrt epsilon * (1 + Real.log epsilon⁻¹) + 1 := by
      rw [hsqrt]
      field_simp

/-- Insert a single-log Chebyshev bound into the explicit elimination order. -/
theorem perturbationEliminationOrder_le_invSqrt_log
    (degreeP refutationOrder envelopeOrder chebyshevOrder : ℕ)
    {epsilon Kn : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hchebyshev : (chebyshevOrder : ℝ) ≤
      Kn / Real.sqrt epsilon * (1 + Real.log epsilon⁻¹) + 1) :
    (GeneralArchimedean.perturbationEliminationOrder degreeP
        refutationOrder envelopeOrder chebyshevOrder : ℝ) ≤
      envelopeOrder + 2 * refutationOrder +
        (6 * (Kn + 2) * (degreeP + 1)) / Real.sqrt epsilon *
          (1 + Real.log epsilon⁻¹) := by
  let L := 1 + Real.log epsilon⁻¹
  let Q := (Real.sqrt epsilon)⁻¹ * L
  have hx : 1 ≤ epsilon⁻¹ := (one_le_inv₀ hepsilon).2 hepsilon1
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hx]
  have hsqrtPos : 0 < Real.sqrt epsilon := Real.sqrt_pos.2 hepsilon
  have hsqrtLe : Real.sqrt epsilon ≤ 1 := by
    nlinarith [Real.sq_sqrt hepsilon.le, Real.sqrt_nonneg epsilon]
  have hinv : 1 ≤ (Real.sqrt epsilon)⁻¹ :=
    (one_le_inv₀ hsqrtPos).2 hsqrtLe
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith [mul_nonneg (zero_le_one.trans hinv)
      (zero_le_one.trans hL)]
  have hchebyshev' :
      (chebyshevOrder : ℝ) + 1 ≤ (Kn + 2) * Q := by
    have hform : Kn / Real.sqrt epsilon * L = Kn * Q := by
      dsimp [Q]
      rw [div_eq_mul_inv]
      ring
    rw [show 1 + Real.log epsilon⁻¹ = L by rfl, hform] at hchebyshev
    nlinarith
  have hbase := GeneralArchimedean.perturbationEliminationOrder_cast_le
    degreeP refutationOrder envelopeOrder chebyshevOrder
  have hdegree : (0 : ℝ) ≤ degreeP + 1 := by positivity
  calc
    (GeneralArchimedean.perturbationEliminationOrder degreeP
        refutationOrder envelopeOrder chebyshevOrder : ℝ) ≤
        envelopeOrder + 2 * refutationOrder +
          6 * (chebyshevOrder + 1) * (degreeP + 1) := hbase
    _ ≤ envelopeOrder + 2 * refutationOrder +
          6 * ((Kn + 2) * Q) * (degreeP + 1) := by
      gcongr
    _ = envelopeOrder + 2 * refutationOrder +
        (6 * (Kn + 2) * (degreeP + 1)) / Real.sqrt epsilon *
          (1 + Real.log epsilon⁻¹) := by
      dsimp [Q, L]
      rw [div_eq_mul_inv]
      ring

/-- The direct Krivine--Stengle refutation and preordering elimination give
the fixed-instance square-root/single-log degree bound. -/
theorem hasSchmudgenDegreeCostBound_of_preorderingArchimedean
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsPreorderingArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    HasSchmudgenDegreeCostBound g p := by
  obtain ⟨B, envelopeOrder, hB, henvelope⟩ :=
    harch.exists_truncated_coefficient_envelope
  obtain ⟨k, refutationOrder, A, _hk, hA, hrefutations⟩ :=
    exists_direct_power_bounded_refutation g p hne hp
  let Cpower := directMultiplierPowerConstant n refutationOrder B A
  let U := objectivePreorderingEnvelope B p
  let Kn := (Real.sqrt (2 / U))⁻¹ *
    (1 + Real.log (4 * Cpower) + (4 * k : ℕ))
  let D : ℝ := envelopeOrder + 2 * refutationOrder
  let K : ℝ := 6 * (Kn + 2) * (p.totalDegree + 1)
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hCpower : 1 ≤ Cpower := by
    dsimp [Cpower, directMultiplierPowerConstant]
    have hterm : 0 ≤
        (GeneralArchimedean.boundedMonomialCount n refutationOrder : ℝ) *
          (((max 1 A / 2) ^ 2 * B ^ refutationOrder) + 1) := by
      positivity
    linarith
  have hUtwo : 2 ≤ U := by
    dsimp [U, objectivePreorderingEnvelope]
    exact le_add_of_nonneg_right
      (GeneralArchimedean.weightedCoeffEnvelope_nonneg hB0 p)
  have hUpos : 0 < U := by linarith
  have hKn : 0 ≤ Kn := by
    dsimp [Kn]
    have hsqrt : 0 ≤ (Real.sqrt (2 / U))⁻¹ := by positivity
    have hlog : 0 ≤ Real.log (4 * Cpower) :=
      Real.log_nonneg (by nlinarith)
    positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨D, K, hD, hK, ?_⟩
  intro epsilon hepsilon hepsilon1
  obtain ⟨s, t, hs, ht, htNorm, hrefute⟩ :=
    hrefutations hepsilon hepsilon1
  have htDegree := totalDegree_le_of_mem_genPreordering ht
  let Czero := 1 + GeneralArchimedean.weightedCoeffEnvelope B t
  have hCzero : 1 ≤ Czero := by
    dsimp [Czero]
    linarith [GeneralArchimedean.weightedCoeffEnvelope_nonneg hB0 t]
  have hCzeroBound :
      Czero ≤ Cpower * epsilon⁻¹ ^ (4 * k) := by
    dsimp [Czero, Cpower]
    exact direct_multiplier_envelope_le_power hB hepsilon hepsilon1
      t htDegree htNorm
  let chebyshevOrder :=
    GeneralArchimedean.chebyshevDegree epsilon Czero⁻¹ U
  have hchebyshev : (chebyshevOrder : ℝ) ≤
      Kn / Real.sqrt epsilon * (1 + Real.log epsilon⁻¹) + 1 := by
    dsimp [chebyshevOrder, Kn]
    exact chebyshevDegree_le_invSqrt_log hepsilon hepsilon1 rfl hUtwo
      hCzero hCpower hCzeroBound
  let outputOrder :=
    GeneralArchimedean.perturbationEliminationOrder p.totalDegree
      refutationOrder envelopeOrder chebyshevOrder
  have houtputOrder : (outputOrder : ℝ) ≤
      envelopeOrder + 2 * refutationOrder +
        (6 * (Kn + 2) * (p.totalDegree + 1)) /
          Real.sqrt epsilon * (1 + Real.log epsilon⁻¹) := by
    dsimp [outputOrder]
    exact perturbationEliminationOrder_le_invSqrt_log
      p.totalDegree refutationOrder envelopeOrder chebyshevOrder
      hepsilon hepsilon1 hchebyshev
  have hcertificate : p + C (2 * epsilon) ∈
      GenPreordering g outputOrder := by
    have hbase := eliminate_bounded_direct_refutation
      g p s t hB henvelope hepsilon hepsilon1 hs ht hrefute
    simpa [outputOrder, chebyshevOrder, Czero, U,
      objectivePreorderingEnvelope] using hbase
  have hdegree : (outputOrder : ℝ) ≤
      schmudgenDegreeCost D K epsilon := by
    dsimp [schmudgenDegreeCost, D, K]
    exact houtputOrder
  apply GenPreordering_mono _ hcertificate
  have hceil := Nat.le_ceil (schmudgenDegreeCost D K epsilon)
  exact_mod_cast hdegree.trans hceil

/-- Fixed-instance compact-domain certificate rate in degree-cost form. -/
theorem hasSchmudgenDegreeCostBound_of_compact
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    HasSchmudgenDegreeCostBound g p :=
  hasSchmudgenDegreeCostBound_of_preorderingArchimedean g p hne
    (compact_isPreorderingArchimedean g hne hcompact) hp

theorem log_pow_two_le_four_mul
    {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 4 * x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  let y := Real.sqrt x
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y ^ 2 = x := Real.sq_sqrt hx0
  have hlog : Real.log x = 2 * Real.log y := by
    dsimp [y]
    rw [Real.log_sqrt hx0]
    ring
  have hlogy : Real.log y ≤ y := Real.log_le_self hy0
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hupper : Real.log x ≤ 2 * y := by
    rw [hlog]
    linarith
  have hpow := pow_le_pow_left₀ hlog0 hupper 2
  calc
    Real.log x ^ 2 ≤ (2 * y) ^ 2 := hpow
    _ = 4 * y ^ 2 := by ring
    _ = 4 * x := by rw [hy2]

theorem one_add_log_inv_logTwo_scale_le
    {A x : ℝ} (hA : 1 ≤ A) (hx : 0 < x)
    (hlogx : 1 ≤ Real.log x) :
    1 + Real.log (A * Real.log x ^ 2 / x ^ 2)⁻¹ ≤
      3 * Real.log x := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hlpos : 0 < Real.log x := zero_lt_one.trans_le hlogx
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hloglog : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlogx
  have hformula :
      Real.log (A * Real.log x ^ 2 / x ^ 2)⁻¹ =
        -(Real.log A + 2 * Real.log (Real.log x) -
          2 * Real.log x) := by
    rw [Real.log_inv]
    rw [Real.log_div (mul_ne_zero hApos.ne' (pow_ne_zero _ hlpos.ne'))
      (pow_ne_zero _ hx.ne')]
    rw [Real.log_mul hApos.ne' (pow_ne_zero _ hlpos.ne')]
    rw [Real.log_pow, Real.log_pow]
    ring
  rw [hformula]
  linarith

theorem logTwo_scale_pos_and_le_one
    {A x : ℝ} (hA : 0 < A) (hx : 1 < x)
    (hthreshold : 4 * A ≤ x) :
    0 < A * Real.log x ^ 2 / x ^ 2 ∧
      A * Real.log x ^ 2 / x ^ 2 ≤ 1 := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  constructor
  · positivity
  · have hlogbound := log_pow_two_le_four_mul hx.le
    have hscaled : A * Real.log x ^ 2 ≤ A * (4 * x) :=
      mul_le_mul_of_nonneg_left hlogbound hA.le
    have hright : A * (4 * x) ≤ x ^ 2 := by nlinarith
    rw [div_le_one (sq_pos_of_pos hxpos)]
    exact hscaled.trans hright

theorem schmudgenDegreeCost_scale_le
    {D K A x : ℝ}
    (hK : 0 ≤ K) (hA : 1 ≤ A)
    (hlogx : 1 ≤ Real.log x) (hx : 0 < x)
    (hsmall : A * Real.log x ^ 2 / x ^ 2 ≤ 1)
    (hDsize : 2 * D ≤ x) (hKsize : 6 * K ≤ Real.sqrt A) :
    schmudgenDegreeCost D K
        (A * Real.log x ^ 2 / x ^ 2) ≤ x := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hlpos : 0 < Real.log x := zero_lt_one.trans_le hlogx
  let epsilon := A * Real.log x ^ 2 / x ^ 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hLnonneg : 0 ≤ 1 + Real.log epsilon⁻¹ := by
    have hinv : 1 ≤ epsilon⁻¹ :=
      (one_le_inv₀ hepsilon).2 (by simpa [epsilon] using hsmall)
    exact add_nonneg zero_le_one (Real.log_nonneg hinv)
  have hL : 1 + Real.log epsilon⁻¹ ≤ 3 * Real.log x := by
    simpa [epsilon] using one_add_log_inv_logTwo_scale_le hA hx hlogx
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
  have hsqrt : Real.sqrt epsilon = Real.sqrt A * Real.log x / x := by
    dsimp [epsilon]
    rw [Real.sqrt_div (mul_nonneg hApos.le (pow_nonneg hlpos.le 2))]
    rw [Real.sqrt_mul hApos.le]
    rw [Real.sqrt_sq hlpos.le, Real.sqrt_sq hx.le]
  have hdenom : 0 < Real.sqrt A * Real.log x / x := by positivity
  have hcostTerm :
      K / Real.sqrt epsilon * (1 + Real.log epsilon⁻¹) ≤
        3 * K / Real.sqrt A * x := by
    rw [hsqrt]
    calc
      K / (Real.sqrt A * Real.log x / x) *
          (1 + Real.log epsilon⁻¹) ≤
        K / (Real.sqrt A * Real.log x / x) * (3 * Real.log x) :=
        mul_le_mul_of_nonneg_left hL (div_nonneg hK hdenom.le)
      _ = 3 * K / Real.sqrt A * x := by field_simp
  have hhalf : 3 * K / Real.sqrt A ≤ 1 / 2 := by
    rw [div_le_iff₀ hsqrtA]
    nlinarith
  have hlinear : 3 * K / Real.sqrt A * x ≤ x / 2 := by
    convert mul_le_mul_of_nonneg_right hhalf hx.le using 1
    all_goals ring
  dsimp [schmudgenDegreeCost]
  dsimp [epsilon] at hcostTerm
  linarith

/-- Analytic inversion of the direct square-root/single-log degree bound. -/
theorem upperRate_of_degreeCostBound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hcost : HasSchmudgenDegreeCostBound g p) :
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (C₀ * logTwoOverSq r) ∈ GenPreordering g r := by
  obtain ⟨D, K, hD, hK, hcert⟩ := hcost
  let S := max 1 (6 * K)
  let A := S ^ 2
  let C₀ := 2 * A
  have hS : 1 ≤ S := le_max_left _ _
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hC₀pos : 0 < C₀ := by dsimp [C₀]; positivity
  have hsqrtA : Real.sqrt A = S := by
    dsimp [A]
    exact Real.sqrt_sq hS0
  obtain ⟨r₀, hr₀⟩ := exists_nat_gt
    (max (Real.exp 1) (max (4 * A) (max (2 * D) 2)))
  have hr₀pos : 0 < r₀ := by
    have : (2 : ℝ) < r₀ := lt_of_le_of_lt
      ((le_max_right (2 * D) 2).trans
        ((le_max_right (4 * A) (max (2 * D) 2)).trans
          (le_max_right (Real.exp 1) (max (4 * A) (max (2 * D) 2))))) hr₀
    exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 2) this)
  refine ⟨C₀, r₀, hC₀pos, hr₀pos, ?_⟩
  intro r hrr₀
  have hcast : (r₀ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrr₀
  have hrLower :
      max (Real.exp 1) (max (4 * A) (max (2 * D) 2)) < (r : ℝ) :=
    hr₀.trans_le hcast
  have hrex : Real.exp 1 ≤ (r : ℝ) :=
    (le_max_left _ _).trans hrLower.le
  have hrA : 4 * A ≤ (r : ℝ) :=
    (le_max_left (4 * A) (max (2 * D) 2)).trans
      ((le_max_right (Real.exp 1) _).trans hrLower.le)
  have hrD : 2 * D ≤ (r : ℝ) :=
    (le_max_left (2 * D) 2).trans
      ((le_max_right (4 * A) _).trans
        ((le_max_right (Real.exp 1) _).trans hrLower.le))
  have hrTwo : (2 : ℝ) ≤ (r : ℝ) :=
    (le_max_right (2 * D) 2).trans
      ((le_max_right (4 * A) _).trans
        ((le_max_right (Real.exp 1) _).trans hrLower.le))
  have hrNat : 2 ≤ r := by exact_mod_cast hrTwo
  have hmax : max r 2 = r := max_eq_left hrNat
  have hlog : 1 ≤ Real.log (r : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hrex
  let epsilon := A * logTwoOverSq r
  have hepsilonEq :
      epsilon = A * Real.log (r : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
    simp [epsilon, logTwoOverSq, hmax]
    ring
  have hscaleExplicit := logTwo_scale_pos_and_le_one hApos
    (show (1 : ℝ) < r by linarith) hrA
  have hscale : 0 < epsilon ∧ epsilon ≤ 1 := by
    rw [hepsilonEq]
    exact hscaleExplicit
  have hKsize : 6 * K ≤ Real.sqrt A := by
    rw [hsqrtA]
    exact le_max_right 1 (6 * K)
  have hdegree : schmudgenDegreeCost D K epsilon ≤ (r : ℝ) := by
    rw [hepsilonEq]
    exact schmudgenDegreeCost_scale_le hK hA hlog
      (show (0 : ℝ) < r by linarith) hscaleExplicit.2 hrD hKsize
  have hbase := hcert hscale.1 hscale.2
  have hmono := GenPreordering_mono (Nat.ceil_le.mpr hdegree) hbase
  convert hmono using 1
  dsimp [epsilon, C₀]
  simp only [map_mul]
  ring

end OptimalConvergenceRates.GeneralCompact

end
