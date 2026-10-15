/- The original three-variable example and secondary consequences. -/
import OptimalConvergenceRates.GeneralCompact.UpperBound
import OptimalConvergenceRates.GeneralCompact.SharpBivariate.LowerBound
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.Geometry

noncomputable section

open Finset MvPolynomial Filter Asymptotics

namespace OptimalConvergenceRates.GeneralCompact

/-- The universal theorem gives the logarithmic-square upper rate for the
original three-variable example without changing its generators. -/
theorem originalExample_upper_rate :
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        GeneralArchimedean.sharpArchimedeanObjective +
            C (C₀ * logTwoOverSq r) ∈
          GenPreordering
            GeneralArchimedean.sharpArchimedeanGenerators r := by
  exact upperRate_of_degreeCostBound
    (hasSchmudgenDegreeCostBound_of_compact
      GeneralArchimedean.sharpArchimedeanGenerators
      GeneralArchimedean.sharpArchimedeanObjective
      GeneralArchimedean.sharpArchimedean_set_nonempty
      GeneralArchimedean.sharpArchimedean_isArchimedean.isCompact_basicClosedSet
      GeneralArchimedean.sharpArchimedeanObjective_nonnegOn)

/-- The family of nontrivial bivariate generators mentioned in the note. -/
def familyGenerator (ell : ℕ) : MvPolynomial (Fin 2) ℝ :=
  sharpZ * (sharpA ^ 2 + sharpZ ^ (2 * ell))

/-- The elementary identity behind the family of examples. -/
theorem sharpZ_mul_familyGenerator (ell : ℕ) :
    sharpZ * familyGenerator ell =
      sharpZ ^ (2 * ell + 2) + (sharpA * sharpZ) ^ 2 := by
  unfold familyGenerator
  ring

/-- An objective already in the untruncated preordering has finite
certificate convergence at some truncation order. -/
theorem finite_convergence_of_preorderingMem
    {n m : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hp : KrivineStengle.PreorderingMem g p) :
    ∃ r, p ∈ GenPreordering g r :=
  hp

/-- At every later order, an objective already in the preordering remains
certified with zero perturbation. -/
theorem finite_convergence_of_preorderingMem_at_later_orders
    {n m : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hp : KrivineStengle.PreorderingMem g p) :
    ∃ r₀, ∀ r, r₀ ≤ r → p + C (0 : ℝ) ∈ GenPreordering g r := by
  obtain ⟨r₀, hr₀⟩ := hp
  exact ⟨r₀, fun r hrr => by
    simpa using GenPreordering_mono hrr hr₀⟩

/-- Restriction of a trivariate polynomial to the first coordinate line. -/
def originalRestrictA (b z : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C b, Polynomial.C z] p

@[simp] theorem originalRestrictA_eval (a b z : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    (originalRestrictA b z p).eval a =
      MvPolynomial.eval ![a, b, z] p := by
  rw [originalRestrictA]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
        Polynomial.eval_mul]
      rw [hp]
      congr 1
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]

theorem originalRestrictA_natDegree_le (b z : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    (originalRestrictA b z p).natDegree ≤ p.totalDegree := by
  have h := MvPolynomial.aeval_natDegree_le p (le_refl p.totalDegree)
    ![Polynomial.X, Polynomial.C b, Polynomial.C z] (n := 1) (by
      intro i
      fin_cases i <;> simp)
  simpa [originalRestrictA] using h

/-- Restriction of a trivariate polynomial to the second coordinate line. -/
def originalRestrictB (a z : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.C a, Polynomial.X, Polynomial.C z] p

@[simp] theorem originalRestrictB_eval (a b z : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    (originalRestrictB a z p).eval b =
      MvPolynomial.eval ![a, b, z] p := by
  rw [originalRestrictB]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
        Polynomial.eval_mul]
      rw [hp]
      congr 1
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]

theorem originalRestrictB_natDegree_le (a z : ℝ)
    (p : MvPolynomial (Fin 3) ℝ) :
    (originalRestrictB a z p).natDegree ≤ p.totalDegree := by
  have h := MvPolynomial.aeval_natDegree_le p (le_refl p.totalDegree)
    ![Polynomial.C a, Polynomial.X, Polynomial.C z] (n := 1) (by
      intro i
      fin_cases i <;> simp)
  simpa [originalRestrictB] using h

private theorem originalGeneratorProd_ne_zero (J : Finset (Fin 4)) :
    (∏ j ∈ J, GeneralArchimedean.sharpArchimedeanGenerators j) ≠
      (0 : MvPolynomial (Fin 3) ℝ) := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact GeneralArchimedean.sharpArchimedeanGenerator_ne_zero i

private theorem originalMultiplier_totalDegree_le
    {sigma : Finset (Fin 4) → MvPolynomial (Fin 3) ℝ} {r : ℕ}
    (hdegree : ∀ J,
      (sigma J * ∏ j ∈ J,
        GeneralArchimedean.sharpArchimedeanGenerators j).totalDegree ≤ r)
    (J) :
    (sigma J).totalDegree ≤ r := by
  by_cases hsigma : sigma J = 0
  · simp [hsigma]
  · have hmul := MvPolynomial.totalDegree_mul_of_isDomain hsigma
      (originalGeneratorProd_ne_zero J)
    have hw := hdegree J
    omega

private theorem originalGenerator_nonneg_on_box
    {a b z : ℝ} (ha0 : 0 ≤ a) (ha4 : a ≤ 1 / 4)
    (hb0 : 0 ≤ b) (hb4 : b ≤ 1 / 4)
    (hz0 : 0 ≤ z) (hz4 : z ≤ 1 / 4) (i : Fin 4) :
    0 ≤ MvPolynomial.eval ![a, b, z]
      (GeneralArchimedean.sharpArchimedeanGenerators i) := by
  fin_cases i
  · simpa [GeneralArchimedean.sharpArchimedeanGenerators,
      KrivineStengle.sharpSeedGenerators, KrivineStengle.sharpSeedA]
  · simpa [GeneralArchimedean.sharpArchimedeanGenerators,
      KrivineStengle.sharpSeedGenerators, KrivineStengle.sharpSeedB]
  · simp [GeneralArchimedean.sharpArchimedeanGenerators,
      KrivineStengle.sharpSeedGenerators, KrivineStengle.sharpSeedW,
      KrivineStengle.sharpSeedA, KrivineStengle.sharpSeedB,
      KrivineStengle.sharpSeedZ]
    positivity
  · simp [GeneralArchimedean.sharpArchimedeanGenerators,
      KrivineStengle.sharpSeedGenerators, KrivineStengle.sharpSeedA,
      KrivineStengle.sharpSeedB, KrivineStengle.sharpSeedZ]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg z,
      sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4),
      sq_nonneg (z - 1 / 4)]

private theorem originalCertificate_term_nonneg
    {sigma : Finset (Fin 4) → MvPolynomial (Fin 3) ℝ}
    (hsos : ∀ J, IsSOS (sigma J))
    {a b z : ℝ} (ha0 : 0 ≤ a) (ha4 : a ≤ 1 / 4)
    (hb0 : 0 ≤ b) (hb4 : b ≤ 1 / 4)
    (hz0 : 0 ≤ z) (hz4 : z ≤ 1 / 4) (J : Finset (Fin 4)) :
    0 ≤ MvPolynomial.eval ![a, b, z]
      (sigma J * ∏ j ∈ J,
        GeneralArchimedean.sharpArchimedeanGenerators j) := by
  rw [map_mul, map_prod]
  apply mul_nonneg
  · exact IsSOS_nonneg _ (hsos J) _ (Set.mem_univ _)
  · apply Finset.prod_nonneg
    intro i hi
    exact originalGenerator_nonneg_on_box ha0 ha4 hb0 hb4 hz0 hz4 i

/-- The coefficients of the terms containing the nonlinear generator
obey a uniform product-weighted bound on the positive slab. -/
theorem originalCertificate_weighted_multiplier_bounds
    {epsilon t : ℝ}
    (hepsilon : 0 < epsilon) (ht : t = 2 * epsilon)
    {sigma : Finset (Fin 4) → MvPolynomial (Fin 3) ℝ}
    (hsos : ∀ J, IsSOS (sigma J))
    (hidentity :
      GeneralArchimedean.sharpArchimedeanObjective + C epsilon =
        ∑ J ∈ Finset.univ.powerset,
          sigma J * ∏ j ∈ J,
            GeneralArchimedean.sharpArchimedeanGenerators j)
    {a b z : ℝ} (ha0 : 0 ≤ a) (ha4 : a ≤ 1 / 4)
    (hb0 : 0 ≤ b) (hb4 : b ≤ 1 / 4)
    (hz : t ≤ z) (hz4 : z ≤ 1 / 4) :
    a * b * MvPolynomial.eval ![a, b, z] (sigma {2}) ≤ 2 ∧
    a * b * MvPolynomial.eval ![a, b, z] (sigma {2, 3}) ≤ 2 := by
  have ht0 : 0 < t := by rw [ht]; positivity
  have hz0 : 0 ≤ z := ht0.le.trans hz
  have hsigma2 : 0 ≤ MvPolynomial.eval ![a, b, z] (sigma {2}) :=
    IsSOS_nonneg _ (hsos {2}) _ (Set.mem_univ _)
  have hsigma23 : 0 ≤ MvPolynomial.eval ![a, b, z] (sigma {2, 3}) :=
    IsSOS_nonneg _ (hsos {2, 3}) _ (Set.mem_univ _)
  have hball : (13 / 16 : ℝ) ≤ 1 - a ^ 2 - b ^ 2 - z ^ 2 := by
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg z,
      sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4),
      sq_nonneg (z - 1 / 4)]
  have hwhole :
      MvPolynomial.eval ![a, b, z]
          (∑ J ∈ Finset.univ.powerset,
            sigma J * ∏ j ∈ J,
              GeneralArchimedean.sharpArchimedeanGenerators j) =
        z + epsilon := by
    rw [← hidentity]
    simp [GeneralArchimedean.sharpArchimedeanObjective,
      GeneralArchimedean.sharpArchimedeanZ,
      KrivineStengle.sharpSeedZ]
  have hterm (J : Finset (Fin 4))
      (hJ : J ∈ (Finset.univ : Finset (Fin 4)).powerset) :
      MvPolynomial.eval ![a, b, z]
          (sigma J * ∏ j ∈ J,
            GeneralArchimedean.sharpArchimedeanGenerators j) ≤
        z + epsilon := by
    rw [← hwhole, map_sum]
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 4)).powerset)
      (f := fun K => MvPolynomial.eval ![a, b, z]
        (sigma K * ∏ j ∈ K,
          GeneralArchimedean.sharpArchimedeanGenerators j))
      (fun K hK => originalCertificate_term_nonneg hsos
        ha0 ha4 hb0 hb4 hz0 hz4 K) hJ
  have hW := hterm {2} (by simp)
  have hWB := hterm {2, 3} (by simp)
  simp only [map_mul, map_prod] at hW hWB
  simp only [Finset.prod_singleton] at hW
  rw [Finset.prod_insert (by decide), Finset.prod_singleton] at hWB
  have hgen2 :
      MvPolynomial.eval ![a, b, z]
        (GeneralArchimedean.sharpArchimedeanGenerators (2 : Fin 4)) =
          z * a * b + z ^ 5 := by
    simp [GeneralArchimedean.sharpArchimedeanGenerators,
      KrivineStengle.sharpSeedGenerators, KrivineStengle.sharpSeedW,
      KrivineStengle.sharpSeedA, KrivineStengle.sharpSeedB,
      KrivineStengle.sharpSeedZ]
  have hgen3 :
      MvPolynomial.eval ![a, b, z]
        (GeneralArchimedean.sharpArchimedeanGenerators (3 : Fin 4)) =
          1 - a ^ 2 - b ^ 2 - z ^ 2 := by
    simp [GeneralArchimedean.sharpArchimedeanGenerators,
      KrivineStengle.sharpSeedGenerators, KrivineStengle.sharpSeedA,
      KrivineStengle.sharpSeedB, KrivineStengle.sharpSeedZ]
  rw [hgen2] at hW hWB
  rw [hgen3] at hWB
  change MvPolynomial.eval ![a, b, z] (sigma {2}) *
    (z * a * b + z ^ 5) ≤ z + epsilon at hW
  change MvPolynomial.eval ![a, b, z] (sigma {2, 3}) *
    ((z * a * b + z ^ 5) * (1 - a ^ 2 - b ^ 2 - z ^ 2)) ≤
      z + epsilon at hWB
  have hWform : z * a * b + z ^ 5 = z * (a * b + z ^ 4) := by ring
  rw [hWform] at hW hWB
  have hepsz : epsilon ≤ z / 2 := by rw [ht] at hz; linarith
  constructor
  · have hfac : z * (a * b) ≤ z * (a * b + z ^ 4) := by
      have hzpow : 0 ≤ z ^ 4 := by positivity
      nlinarith [mul_nonneg hz0 hzpow]
    nlinarith [mul_le_mul_of_nonneg_left hfac hsigma2]
  · have hfac :
        z * (a * b) * (13 / 16 : ℝ) ≤
          z * (a * b + z ^ 4) * (1 - a ^ 2 - b ^ 2 - z ^ 2) := by
      have hzpow : 0 ≤ z ^ 4 := by positivity
      have hsum : 0 ≤ a * b + z ^ 4 :=
        add_nonneg (mul_nonneg ha0 hb0) hzpow
      have hleft := mul_le_mul_of_nonneg_left hball
        (mul_nonneg hz0 hsum)
      have hquad : z * (a * b) ≤ z * (a * b + z ^ 4) := by
        nlinarith [mul_nonneg hz0 hzpow]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfac hsigma23]

/-- Polynomial envelope produced by the two scalar face estimates. -/
def originalSlabEnvelope (r : ℕ) : ℝ :=
  128 * Real.exp 12 * (r : ℝ) ^ 4

/-- Two applications of the quarter-interval face estimate turn the
product-weighted slab bound into a bound at the coordinate origin. -/
theorem originalSOS_face_bound
    {sigma : MvPolynomial (Fin 3) ℝ} {r : ℕ} {z : ℝ}
    (hr : 2 ≤ r) (hsos : IsSOS sigma)
    (hdegree : sigma.totalDegree ≤ r)
    (hweighted : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 / 4 →
      0 ≤ b → b ≤ 1 / 4 →
      a * b * MvPolynomial.eval ![a, b, z] sigma ≤ 2) :
    MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z] sigma ≤
      originalSlabEnvelope r := by
  let firstEnvelope : ℝ := 16 * Real.exp 6 * (r : ℝ) ^ 2
  have hfirstEnvelope : 0 < firstEnvelope := by
    dsimp [firstEnvelope]
    positivity
  have hfirst : ∀ b : ℝ, 0 ≤ b → b ≤ 1 / 4 →
      b * MvPolynomial.eval ![(0 : ℝ), b, z] sigma ≤
        firstEnvelope := by
    intro b hb0 hb4
    let pA : Polynomial ℝ :=
      Polynomial.C (b / 2) * originalRestrictA b z sigma
    have hpAdegree : pA.natDegree ≤ r := by
      dsimp [pA]
      calc
        (Polynomial.C (b / 2) * originalRestrictA b z sigma).natDegree ≤
            (Polynomial.C (b / 2)).natDegree +
              (originalRestrictA b z sigma).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ 0 + sigma.totalDegree := by
          rw [Polynomial.natDegree_C]
          exact Nat.add_le_add_left
            (originalRestrictA_natDegree_le b z sigma) 0
        _ ≤ r := by simpa using hdegree
    have hpAnonneg : ∀ a : ℝ, 0 ≤ a → a ≤ 1 / 4 →
        0 ≤ pA.eval a := by
      intro a ha0 ha4
      dsimp [pA]
      simp only [Polynomial.eval_mul, Polynomial.eval_C,
        originalRestrictA_eval]
      exact mul_nonneg (div_nonneg hb0 (by norm_num))
        (IsSOS_nonneg _ hsos _ (Set.mem_univ _))
    have hpAweighted : ∀ a : ℝ, 0 ≤ a → a ≤ 1 / 4 →
        a * pA.eval a ≤ 1 := by
      intro a ha0 ha4
      have hw := hweighted a b ha0 ha4 hb0 hb4
      dsimp [pA]
      simp only [Polynomial.eval_mul, Polynomial.eval_C,
        originalRestrictA_eval]
      nlinarith
    have hmark :=
      quarterInterval_face_multiplier_bound hr pA
        hpAdegree hpAnonneg hpAweighted (x := (0 : ℝ))
        (by norm_num) (by norm_num)
    dsimp [pA] at hmark
    simp only [Polynomial.eval_mul, Polynomial.eval_C,
      originalRestrictA_eval] at hmark
    dsimp [firstEnvelope]
    nlinarith
  let pB : Polynomial ℝ :=
    Polynomial.C firstEnvelope⁻¹ * originalRestrictB 0 z sigma
  have hpBdegree : pB.natDegree ≤ r := by
    dsimp [pB]
    calc
      (Polynomial.C firstEnvelope⁻¹ *
          originalRestrictB 0 z sigma).natDegree ≤
          (Polynomial.C firstEnvelope⁻¹).natDegree +
            (originalRestrictB 0 z sigma).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + sigma.totalDegree := by
        rw [Polynomial.natDegree_C]
        exact Nat.add_le_add_left
          (originalRestrictB_natDegree_le 0 z sigma) 0
      _ ≤ r := by simpa using hdegree
  have hpBnonneg : ∀ b : ℝ, 0 ≤ b → b ≤ 1 / 4 →
      0 ≤ pB.eval b := by
    intro b hb0 hb4
    dsimp [pB]
    simp only [Polynomial.eval_mul, Polynomial.eval_C,
      originalRestrictB_eval]
    exact mul_nonneg (inv_nonneg.mpr hfirstEnvelope.le)
      (IsSOS_nonneg _ hsos _ (Set.mem_univ _))
  have hpBweighted : ∀ b : ℝ, 0 ≤ b → b ≤ 1 / 4 →
      b * pB.eval b ≤ 1 := by
    intro b hb0 hb4
    have hb := hfirst b hb0 hb4
    dsimp [pB]
    simp only [Polynomial.eval_mul, Polynomial.eval_C,
      originalRestrictB_eval]
    rw [show b * (firstEnvelope⁻¹ *
      MvPolynomial.eval ![(0 : ℝ), b, z] sigma) =
        (b * MvPolynomial.eval ![(0 : ℝ), b, z] sigma) / firstEnvelope by ring]
    exact (div_le_one hfirstEnvelope).2 hb
  have hmark :=
    quarterInterval_face_multiplier_bound hr pB
      hpBdegree hpBnonneg hpBweighted (x := (0 : ℝ))
      (by norm_num) (by norm_num)
  dsimp [pB] at hmark
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    originalRestrictB_eval] at hmark
  have hrescaled :
      MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z] sigma ≤
        firstEnvelope * (8 * Real.exp 6 * (r : ℝ) ^ 2) :=
    (inv_mul_le_iff₀ hfirstEnvelope).mp hmark
  have hexp : Real.exp 6 * Real.exp 6 = Real.exp 12 := by
    rw [← Real.exp_add]
    norm_num
  calc
    MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z] sigma ≤
        firstEnvelope * (8 * Real.exp 6 * (r : ℝ) ^ 2) := hrescaled
    _ = originalSlabEnvelope r := by
      unfold originalSlabEnvelope
      dsimp [firstEnvelope]
      calc
        16 * Real.exp 6 * (r : ℝ) ^ 2 *
            (8 * Real.exp 6 * (r : ℝ) ^ 2) =
          128 * (Real.exp 6 * Real.exp 6) * (r : ℝ) ^ 4 := by ring
        _ = 128 * Real.exp 12 * (r : ℝ) ^ 4 := by rw [hexp]

/-- Common envelope for the two critical multipliers on the reflected
face.  The polynomial factor comes from the two coordinate-face estimates;
the exponential factor comes from Chebyshev extrapolation in `z`. -/
def originalNegativeFaceEnvelope (t : ℝ) (r : ℕ) : ℝ :=
  Real.exp (100 * (r : ℝ) * Real.sqrt t) * originalSlabEnvelope r

/-- The two multipliers containing the nonlinear generator remain controlled
after extrapolating from the positive slab to the reflected point. -/
theorem originalCertificate_negative_face_bounds
    {epsilon t : ℝ} {r : ℕ}
    (hr : 2 ≤ r) (hepsilon : 0 < epsilon) (ht : t = 2 * epsilon)
    (htsmall : t ≤ (1 : ℝ) / 64)
    {sigma : Finset (Fin 4) → MvPolynomial (Fin 3) ℝ}
    (hsos : ∀ J, IsSOS (sigma J))
    (hdegree : ∀ J,
      (sigma J * ∏ j ∈ J,
        GeneralArchimedean.sharpArchimedeanGenerators j).totalDegree ≤ r)
    (hidentity :
      GeneralArchimedean.sharpArchimedeanObjective + C epsilon =
        ∑ J ∈ Finset.univ.powerset,
          sigma J * ∏ j ∈ J,
            GeneralArchimedean.sharpArchimedeanGenerators j) :
    MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {2}) ≤
        originalNegativeFaceEnvelope t r ∧
      MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {2, 3}) ≤
        originalNegativeFaceEnvelope t r := by
  have ht0 : 0 < t := by rw [ht]; positivity
  have hface (J : Finset (Fin 4))
      (hselect : ∀ {a b z : ℝ}, 0 ≤ a → a ≤ 1 / 4 →
        0 ≤ b → b ≤ 1 / 4 → t ≤ z → z ≤ 1 / 4 →
          a * b * MvPolynomial.eval ![a, b, z] (sigma J) ≤ 2) :
      ∀ z : ℝ, t ≤ z → z ≤ 1 / 4 →
        MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z] (sigma J) ≤
          originalSlabEnvelope r := by
    intro z hz hz4
    exact originalSOS_face_bound hr (hsos J)
      (originalMultiplier_totalDegree_le hdegree J)
      (fun a b ha0 ha4 hb0 hb4 => hselect ha0 ha4 hb0 hb4 hz hz4)
  have hextrapolate (J : Finset (Fin 4))
      (hfaceJ : ∀ z : ℝ, t ≤ z → z ≤ 1 / 4 →
        MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z] (sigma J) ≤
          originalSlabEnvelope r) :
      MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma J) ≤
        originalNegativeFaceEnvelope t r := by
    let p := GeneralArchimedean.sharpRestrictAB 0 0 (sigma J)
    have hpdeg : p.natDegree ≤ r :=
      (GeneralArchimedean.sharpRestrictAB_natDegree_le 0 0 (sigma J)).trans
        (originalMultiplier_totalDegree_le hdegree J)
    have hpbound : ∀ z : ℝ, t ≤ z → z ≤ 1 / 4 →
        |p.eval z| ≤ originalSlabEnvelope r := by
      intro z hz hz4
      rw [GeneralArchimedean.sharpRestrictAB_eval]
      rw [abs_of_nonneg
        (IsSOS_nonneg _ (hsos J) _ (Set.mem_univ _))]
      exact hfaceJ z hz hz4
    have hext :=
      GeneralArchimedean.polynomial_extrapolate_negative_slab
        hr ht0 htsmall p hpdeg hpbound
    rw [GeneralArchimedean.sharpRestrictAB_eval] at hext
    exact (le_abs_self _).trans (by
      simpa [originalNegativeFaceEnvelope] using hext)
  have hweighted := fun {a b z : ℝ} (ha0 : 0 ≤ a) (ha4 : a ≤ 1 / 4)
      (hb0 : 0 ≤ b) (hb4 : b ≤ 1 / 4) (hz : t ≤ z) (hz4 : z ≤ 1 / 4) =>
    originalCertificate_weighted_multiplier_bounds hepsilon ht hsos
      hidentity ha0 ha4 hb0 hb4 hz hz4
  exact ⟨hextrapolate {2} (hface {2} (fun ha0 ha4 hb0 hb4 hz hz4 =>
      (hweighted ha0 ha4 hb0 hb4 hz hz4).1)),
    hextrapolate {2, 3} (hface {2, 3}
      (fun ha0 ha4 hb0 hb4 hz hz4 =>
        (hweighted ha0 ha4 hb0 hb4 hz hz4).2))⟩

/-- On the coordinate axis, every preordering term containing either linear
generator vanishes, leaving exactly the four subsets of the two remaining
generators. -/
theorem originalPreordering_eval_axis
    (sigma : Finset (Fin 4) → MvPolynomial (Fin 3) ℝ) (z : ℝ) :
    MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z]
        (∑ J ∈ (Finset.univ : Finset (Fin 4)).powerset,
          sigma J * ∏ j ∈ J,
            GeneralArchimedean.sharpArchimedeanGenerators j) =
      MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z] (sigma ∅) +
        MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z] (sigma {2}) * z ^ 5 +
        MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z] (sigma {3}) *
          (1 - z ^ 2) +
        MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z] (sigma {2, 3}) *
          (z ^ 5 * (1 - z ^ 2)) := by
  classical
  rw [map_sum]
  calc
    (∑ J ∈ (Finset.univ : Finset (Fin 4)).powerset,
        MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z]
          (sigma J * ∏ j ∈ J,
            GeneralArchimedean.sharpArchimedeanGenerators j)) =
      ∑ J ∈ ({2, 3} : Finset (Fin 4)).powerset,
        MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z]
          (sigma J * ∏ j ∈ J,
            GeneralArchimedean.sharpArchimedeanGenerators j) := by
      symm
      apply Finset.sum_subset
      · intro J hJ
        simp only [Finset.mem_powerset] at hJ ⊢
        exact hJ.trans
          (Finset.subset_univ ({2, 3} : Finset (Fin 4)))
      · intro J hJuniv hJnot
        have hnotSub : ¬J ⊆ ({2, 3} : Finset (Fin 4)) := by
          simpa only [Finset.mem_powerset] using hJnot
        have hzeroOrOne : (0 : Fin 4) ∈ J ∨ (1 : Fin 4) ∈ J := by
          by_contra hne
          simp only [not_or] at hne
          apply hnotSub
          intro i hi
          fin_cases i
          · exact (hne.1 hi).elim
          · exact (hne.2 hi).elim
          · simp
          · simp
        rw [map_mul, map_prod]
        have hprod :
            (∏ j ∈ J, MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z]
              (GeneralArchimedean.sharpArchimedeanGenerators j)) = 0 := by
          rcases hzeroOrOne with hzero | hone
          · apply Finset.prod_eq_zero hzero
            simp [GeneralArchimedean.sharpArchimedeanGenerators,
              KrivineStengle.sharpSeedGenerators,
              KrivineStengle.sharpSeedA]
          · apply Finset.prod_eq_zero hone
            simp [GeneralArchimedean.sharpArchimedeanGenerators,
              KrivineStengle.sharpSeedGenerators,
              KrivineStengle.sharpSeedB]
        rw [hprod, mul_zero]
    _ = _ := by
      have hgen2 :
          MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z]
            (GeneralArchimedean.sharpArchimedeanGenerators (2 : Fin 4)) =
              z ^ 5 := by
        simp [GeneralArchimedean.sharpArchimedeanGenerators,
          KrivineStengle.sharpSeedGenerators, KrivineStengle.sharpSeedW,
          KrivineStengle.sharpSeedA, KrivineStengle.sharpSeedB,
          KrivineStengle.sharpSeedZ, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two]
      have hgen3 :
          MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z]
            (GeneralArchimedean.sharpArchimedeanGenerators (3 : Fin 4)) =
              1 - z ^ 2 := by
        simp [GeneralArchimedean.sharpArchimedeanGenerators,
          KrivineStengle.sharpSeedGenerators, KrivineStengle.sharpSeedA,
          KrivineStengle.sharpSeedB, KrivineStengle.sharpSeedW,
          KrivineStengle.sharpSeedZ, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two]
      have hgen23 :
          (∏ j ∈ ({2, 3} : Finset (Fin 4)),
            MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), z]
              (GeneralArchimedean.sharpArchimedeanGenerators j)) =
            z ^ 5 * (1 - z ^ 2) := by
        rw [Finset.prod_insert (by decide), Finset.prod_singleton,
          hgen2, hgen3]
      have hpowerset : ({2, 3} : Finset (Fin 4)).powerset =
          {∅, {2}, {3}, {2, 3}} := by decide
      rw [hpowerset, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
      simp only [map_mul, map_prod]
      norm_num [hgen2, hgen3, hgen23]
      ring

/-- Evaluation at the reflected coordinate-axis point forces the growth
obstruction used for the lower rate. -/
theorem originalCertificate_forces_growth
    {epsilon t : ℝ} {r : ℕ}
    (hr : 2 ≤ r) (hepsilon : 0 < epsilon) (ht : t = 2 * epsilon)
    (htsmall : t ≤ (1 : ℝ) / 64)
    (hcert :
      GeneralArchimedean.sharpArchimedeanObjective + C epsilon ∈
        GenPreordering
          GeneralArchimedean.sharpArchimedeanGenerators r) :
    1 ≤ 4 * t ^ 4 * originalNegativeFaceEnvelope t r := by
  obtain ⟨sigma, hsos, hdegree, hidentity⟩ := hcert
  have hnegative := originalCertificate_negative_face_bounds hr hepsilon ht
    htsmall hsos hdegree hidentity
  have ht0 : 0 < t := by rw [ht]; positivity
  have htSq : t ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg t]
  have hball0 : 0 ≤ 1 - t ^ 2 := by linarith
  have hball1 : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  let sigmaZero :=
    MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma ∅)
  let sigmaW :=
    MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {2})
  let sigmaBall :=
    MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {3})
  let sigmaWBall :=
    MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {2, 3})
  have hsigmaZero : 0 ≤ sigmaZero :=
    IsSOS_nonneg _ (hsos ∅) _ (Set.mem_univ _)
  have hsigmaW : 0 ≤ sigmaW :=
    IsSOS_nonneg _ (hsos {2}) _ (Set.mem_univ _)
  have hsigmaBall : 0 ≤ sigmaBall :=
    IsSOS_nonneg _ (hsos {3}) _ (Set.mem_univ _)
  have hsigmaWBall : 0 ≤ sigmaWBall :=
    IsSOS_nonneg _ (hsos {2, 3}) _ (Set.mem_univ _)
  have hWbound : sigmaW ≤ originalNegativeFaceEnvelope t r :=
    hnegative.1
  have hWBallBound : sigmaWBall ≤ originalNegativeFaceEnvelope t r :=
    hnegative.2
  have heval := congr_arg
    (MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t]) hidentity
  rw [originalPreordering_eval_axis] at heval
  simp only [map_add] at heval
  simp [GeneralArchimedean.sharpArchimedeanObjective,
    GeneralArchimedean.sharpArchimedeanZ,
    KrivineStengle.sharpSeedZ, Matrix.cons_val_two] at heval
  have heval' : -t + epsilon =
      sigmaZero + -(sigmaW * t ^ 5) +
        sigmaBall * (1 - t ^ 2) +
          -(sigmaWBall * (t ^ 5 * (1 - t ^ 2))) := by
    dsimp only [sigmaZero, sigmaW, sigmaBall, sigmaWBall]
    calc
      -t + epsilon =
          MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma ∅) +
            MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {2}) *
              (-t) ^ 5 +
            MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {3}) *
              (1 - t ^ 2) +
            MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {2, 3}) *
              ((-t) ^ 5 * (1 - t ^ 2)) := heval
      _ = MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma ∅) +
          -(MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {2}) * t ^ 5) +
          MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {3}) *
            (1 - t ^ 2) +
          -(MvPolynomial.eval ![(0 : ℝ), (0 : ℝ), -t] (sigma {2, 3}) *
            (t ^ 5 * (1 - t ^ 2))) := by ring
  clear heval
  have hepsilonEq : epsilon = t / 2 := by rw [ht]; ring
  rw [hepsilonEq] at heval'
  have henvelope0 : 0 ≤ originalNegativeFaceEnvelope t r := by
    unfold originalNegativeFaceEnvelope originalSlabEnvelope
    positivity
  have hcritical :
      t / 2 ≤ t ^ 5 * (sigmaW + (1 - t ^ 2) * sigmaWBall) := by
    nlinarith [mul_nonneg hsigmaBall hball0]
  have hcriticalUpper :
      t ^ 5 * (sigmaW + (1 - t ^ 2) * sigmaWBall) ≤
        2 * t ^ 5 * originalNegativeFaceEnvelope t r := by
    have ht5 : 0 ≤ t ^ 5 := by positivity
    have hweighted :
        sigmaW + (1 - t ^ 2) * sigmaWBall ≤
          2 * originalNegativeFaceEnvelope t r := by
      nlinarith [mul_le_mul_of_nonneg_right hWBallBound hball0,
        mul_le_mul_of_nonneg_right hball1 hsigmaWBall]
    nlinarith [mul_le_mul_of_nonneg_left hweighted ht5]
  nlinarith [mul_nonneg (show 0 ≤ t ^ 4 by positivity) henvelope0]

/-- A convenient fixed scale for the original-example lower bound. -/
def originalCompactLowerScale : ℝ :=
  ((10 : ℝ) ^ 10 * Real.exp 6) ^ 2

/-- A fixed positive constant for the original-example lower bound. -/
def originalCompactLowerConstant : ℝ :=
  1 / (2 * originalCompactLowerScale)

theorem originalExample_logTwo_over_sq_lower_pos :
    ∃ r0 : ℕ, 0 < r0 ∧
      ∀ r, r0 ≤ r → ∀ epsilon : ℝ, 0 < epsilon →
        GeneralArchimedean.sharpArchimedeanObjective + C epsilon ∈
          GenPreordering
            GeneralArchimedean.sharpArchimedeanGenerators r →
          originalCompactLowerConstant * logTwoOverSq r ≤ epsilon := by
  obtain ⟨r0, hr0⟩ := eventually_atTop.mp
    GeneralArchimedean.eventually_sharpLowerConditions
  refine ⟨max r0 1, by omega, ?_⟩
  intro r hrr epsilon hepsilon hcert
  have hcond := hr0 r (le_trans (le_max_left r0 1) hrr)
  rcases hcond with ⟨hr, hlogLarge, hdom, hrateFour⟩
  by_contra hnot
  have hepsilonLt :
      epsilon < originalCompactLowerConstant * logTwoOverSq r :=
    lt_of_not_ge hnot
  have hmax : max r 2 = r := max_eq_left (by omega)
  have hrR : (0 : ℝ) < (r : ℝ) := by positivity
  have hlogPos : 0 < Real.log (r : ℝ) := by linarith
  have hrateEq : logTwoOverSq r =
      Real.log (r : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
    simp [logTwoOverSq, hmax]
  have hrateNonneg : 0 ≤ logTwoOverSq r := by
    rw [hrateEq]
    positivity
  have hrateOne : logTwoOverSq r ≤ 1 := by
    have hfourEq : GeneralArchimedean.logFourOverSq r =
        Real.log (r : ℝ) ^ 4 / (r : ℝ) ^ 2 := by
      simp [GeneralArchimedean.logFourOverSq, hmax]
    rw [hfourEq] at hrateFour
    rw [hrateEq]
    have hpow : Real.log (r : ℝ) ^ 2 ≤
        Real.log (r : ℝ) ^ 4 := by
      nlinarith [sq_nonneg (Real.log (r : ℝ) ^ 2 - 1)]
    exact (div_le_div_of_nonneg_right hpow (sq_nonneg _)).trans hrateFour
  let t : ℝ := 2 * epsilon
  have ht0 : 0 < t := by dsimp [t]; positivity
  have htRate : t <
      Real.log (r : ℝ) ^ 2 /
        (originalCompactLowerScale * (r : ℝ) ^ 2) := by
    calc
      t < 2 * (originalCompactLowerConstant * logTwoOverSq r) := by
        dsimp [t]
        linarith
      _ = Real.log (r : ℝ) ^ 2 /
          (originalCompactLowerScale * (r : ℝ) ^ 2) := by
        rw [hrateEq]
        unfold originalCompactLowerConstant
        have hscale : originalCompactLowerScale ≠ 0 := by
          unfold originalCompactLowerScale
          positivity
        field_simp [hscale]
  have hexpSixOne : (1 : ℝ) ≤ Real.exp 6 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hscalePos : 0 < originalCompactLowerScale := by
    unfold originalCompactLowerScale
    positivity
  have hscale64 : (64 : ℝ) ≤ originalCompactLowerScale := by
    unfold originalCompactLowerScale
    calc
      (64 : ℝ) ≤ ((10 : ℝ) ^ 10) ^ 2 := by norm_num
      _ ≤ ((10 : ℝ) ^ 10 * Real.exp 6) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity)
          (le_mul_of_one_le_right (by positivity) hexpSixOne) 2
  have hc : (2 : ℝ) * originalCompactLowerConstant ≤ 1 / 64 := by
    unfold originalCompactLowerConstant
    rw [show (2 : ℝ) * (1 / (2 * originalCompactLowerScale)) =
      1 / originalCompactLowerScale by field_simp]
    exact one_div_le_one_div_of_le (by norm_num) hscale64
  have htsmall : t ≤ (1 : ℝ) / 64 := by
    calc
      t ≤ 2 * originalCompactLowerConstant * logTwoOverSq r := by
        dsimp [t]
        nlinarith [hepsilonLt]
      _ ≤ ((1 : ℝ) / 64) * logTwoOverSq r :=
        mul_le_mul_of_nonneg_right hc hrateNonneg
      _ ≤ (1 : ℝ) / 64 := by nlinarith
  have hY0 : 0 ≤ Real.log (r : ℝ) /
      (((10 : ℝ) ^ 10 * Real.exp 6) * (r : ℝ)) := by positivity
  have htY : t ≤
      (Real.log (r : ℝ) /
        (((10 : ℝ) ^ 10 * Real.exp 6) * (r : ℝ))) ^ 2 := by
    calc
      t ≤ Real.log (r : ℝ) ^ 2 /
          (originalCompactLowerScale * (r : ℝ) ^ 2) := htRate.le
      _ = (Real.log (r : ℝ) /
          (((10 : ℝ) ^ 10 * Real.exp 6) * (r : ℝ))) ^ 2 := by
        unfold originalCompactLowerScale
        field_simp
  have hsqrt : Real.sqrt t ≤
      Real.log (r : ℝ) /
        (((10 : ℝ) ^ 10 * Real.exp 6) * (r : ℝ)) := by
    calc
      Real.sqrt t ≤ Real.sqrt
          ((Real.log (r : ℝ) /
            (((10 : ℝ) ^ 10 * Real.exp 6) * (r : ℝ))) ^ 2) :=
        Real.sqrt_le_sqrt htY
      _ = _ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hY0]
  have hcoefficient :
      (100 : ℝ) ≤ (10 : ℝ) ^ 10 * Real.exp 6 := by
    calc
      (100 : ℝ) ≤ (10 : ℝ) ^ 10 := by norm_num
      _ ≤ (10 : ℝ) ^ 10 * Real.exp 6 := by
        exact le_mul_of_one_le_right (by positivity) hexpSixOne
  have hexponent :
      100 * (r : ℝ) * Real.sqrt t ≤ Real.log (r : ℝ) := by
    calc
      100 * (r : ℝ) * Real.sqrt t ≤
          100 * (r : ℝ) *
            (Real.log (r : ℝ) /
              (((10 : ℝ) ^ 10 * Real.exp 6) * (r : ℝ))) := by
        gcongr
      _ = (100 / ((10 : ℝ) ^ 10 * Real.exp 6)) *
          Real.log (r : ℝ) := by field_simp
      _ ≤ 1 * Real.log (r : ℝ) := by
        gcongr
        exact (div_le_one (by positivity)).2 hcoefficient
      _ = Real.log (r : ℝ) := one_mul _
  have hexp :
      Real.exp (100 * (r : ℝ) * Real.sqrt t) ≤ (r : ℝ) := by
    calc
      Real.exp (100 * (r : ℝ) * Real.sqrt t) ≤
          Real.exp (Real.log (r : ℝ)) := Real.exp_le_exp.mpr hexponent
      _ = (r : ℝ) := Real.exp_log hrR
  have hforce := originalCertificate_forces_growth (r := r) (by omega)
    hepsilon (by rfl : t = 2 * epsilon) htsmall hcert
  unfold originalNegativeFaceEnvelope originalSlabEnvelope at hforce
  have hforceUpper :
      1 ≤ 512 * Real.exp 12 * t ^ 4 * (r : ℝ) ^ 5 := by
    calc
      1 ≤ 4 * t ^ 4 *
          (Real.exp (100 * (r : ℝ) * Real.sqrt t) *
            (128 * Real.exp 12 * (r : ℝ) ^ 4)) := hforce
      _ ≤ 4 * t ^ 4 *
          ((r : ℝ) * (128 * Real.exp 12 * (r : ℝ) ^ 4)) := by
        gcongr
      _ = 512 * Real.exp 12 * t ^ 4 * (r : ℝ) ^ 5 := by ring
  have hexpSquare : Real.exp 12 = (Real.exp 6) ^ 2 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hexpPow :
      (Real.exp 6) ^ 2 ≤ (Real.exp 6) ^ 8 := by
    have hpowSix : (1 : ℝ) ≤ (Real.exp 6) ^ 6 :=
      one_le_pow₀ hexpSixOne
    calc
      (Real.exp 6) ^ 2 = (Real.exp 6) ^ 2 * 1 := by ring
      _ ≤ (Real.exp 6) ^ 2 * (Real.exp 6) ^ 6 :=
        mul_le_mul_of_nonneg_left hpowSix (sq_nonneg _)
      _ = (Real.exp 6) ^ 8 := by ring
  have hconstant :
      64 * Real.exp 12 * (10 : ℝ) ^ 32 <
        originalCompactLowerScale ^ 4 := by
    calc
      64 * Real.exp 12 * (10 : ℝ) ^ 32 =
          (64 * (10 : ℝ) ^ 32) * (Real.exp 6) ^ 2 := by
        rw [hexpSquare]
        ring
      _ < (10 : ℝ) ^ 80 * (Real.exp 6) ^ 2 := by
        gcongr
        norm_num
      _ ≤ (10 : ℝ) ^ 80 * (Real.exp 6) ^ 8 := by gcongr
      _ = originalCompactLowerScale ^ 4 := by
        unfold originalCompactLowerScale
        ring
  have hscaledDom :
      512 * Real.exp 12 * Real.log (r : ℝ) ^ 8 ≤
        64 * Real.exp 12 * ((10 : ℝ) ^ 32 * (r : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hdom
      (show 0 ≤ 64 * Real.exp 12 by positivity)
    convert hmul using 1
    all_goals ring
  have hrCube : (r : ℝ) ≤ (r : ℝ) ^ 3 := by
    have hrOne : (1 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (show 1 ≤ r by omega)
    calc
      (r : ℝ) = (r : ℝ) * 1 := by ring
      _ ≤ (r : ℝ) * (r : ℝ) ^ 2 := by
        gcongr
        nlinarith [sq_nonneg ((r : ℝ) - 1)]
      _ = (r : ℝ) ^ 3 := by ring
  have hdominates :
      512 * Real.exp 12 * Real.log (r : ℝ) ^ 8 <
        originalCompactLowerScale ^ 4 * (r : ℝ) ^ 3 := by
    calc
      512 * Real.exp 12 * Real.log (r : ℝ) ^ 8 ≤
          64 * Real.exp 12 * ((10 : ℝ) ^ 32 * (r : ℝ)) := hscaledDom
      _ = (64 * Real.exp 12 * (10 : ℝ) ^ 32) * (r : ℝ) := by ring
      _ < originalCompactLowerScale ^ 4 * (r : ℝ) :=
        mul_lt_mul_of_pos_right hconstant hrR
      _ ≤ originalCompactLowerScale ^ 4 * (r : ℝ) ^ 3 := by
        gcongr
  have hupper :
      512 * Real.exp 12 * t ^ 4 * (r : ℝ) ^ 5 < 1 := by
    calc
      512 * Real.exp 12 * t ^ 4 * (r : ℝ) ^ 5 <
          512 * Real.exp 12 *
            (Real.log (r : ℝ) ^ 2 /
              (originalCompactLowerScale * (r : ℝ) ^ 2)) ^ 4 *
                (r : ℝ) ^ 5 := by gcongr
      _ = (512 * Real.exp 12 * Real.log (r : ℝ) ^ 8) /
          (originalCompactLowerScale ^ 4 * (r : ℝ) ^ 3) := by
        field_simp
      _ < 1 := (div_lt_one (by positivity)).mpr hdominates
  linarith

/-- Matching lower certificate bound for the original three-variable
example, including the zero endpoint. -/
theorem originalExample_logTwo_over_sq_lower :
    ∃ c r0, 0 < c ∧ 0 < r0 ∧
      ∀ r, r0 ≤ r → ∀ epsilon : ℝ, 0 ≤ epsilon →
        GeneralArchimedean.sharpArchimedeanObjective + C epsilon ∈
          GenPreordering
            GeneralArchimedean.sharpArchimedeanGenerators r →
          c * logTwoOverSq r ≤ epsilon := by
  obtain ⟨r0, hr0, hlower⟩ :=
    originalExample_logTwo_over_sq_lower_pos
  refine ⟨originalCompactLowerConstant, max r0 3, ?_, by omega, ?_⟩
  · unfold originalCompactLowerConstant originalCompactLowerScale
    positivity
  · intro r hrr epsilon hepsilon hcert
    have hrr0 : r0 ≤ r := le_trans (le_max_left r0 3) hrr
    rcases hepsilon.eq_or_lt with rfl | hepsilonPos
    · have hr3 : 3 ≤ r := le_trans (le_max_right r0 3) hrr
      have hmax : max r 2 = r := max_eq_left (by omega)
      have hlog : 0 < Real.log (r : ℝ) := by
        apply Real.log_pos
        exact_mod_cast (show 1 < r by omega)
      have hratePos : 0 < logTwoOverSq r := by
        rw [logTwoOverSq, hmax]
        positivity
      let delta : ℝ :=
        originalCompactLowerConstant * logTwoOverSq r / 2
      have hdelta : 0 < delta := by
        dsimp [delta]
        exact div_pos (mul_pos (by
          unfold originalCompactLowerConstant originalCompactLowerScale
          positivity) hratePos) (by norm_num)
      have hconst : C delta ∈
          GenPreordering
            GeneralArchimedean.sharpArchimedeanGenerators 0 :=
        KrivineStengle.genPreordering_C_nonneg
          GeneralArchimedean.sharpArchimedeanGenerators hdelta.le
      have hconstR : C delta ∈
          GenPreordering
            GeneralArchimedean.sharpArchimedeanGenerators r :=
        GenPreordering_mono (Nat.zero_le r) hconst
      have hcertDelta :
          GeneralArchimedean.sharpArchimedeanObjective + C delta ∈
            GenPreordering
              GeneralArchimedean.sharpArchimedeanGenerators r := by
        have hsum := KrivineStengle.genPreordering_add hcert hconstR
        simpa using hsum
      have hcontra := hlower r hrr0 delta hdelta hcertDelta
      dsimp [delta] at hcontra
      nlinarith
    · exact hlower r hrr0 epsilon hepsilonPos hcert

end OptimalConvergenceRates.GeneralCompact

end
