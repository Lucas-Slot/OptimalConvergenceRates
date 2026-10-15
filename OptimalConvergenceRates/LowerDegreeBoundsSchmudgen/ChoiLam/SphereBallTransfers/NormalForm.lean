/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/SphereBallTransfers/NormalForm.lean

  Normal forms modulo the sphere relation u^2 = 1 - sum_i x_i^2.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.SphereBallTransfers.Transfer

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace SphereBallTransfers

/-! ## The `Option (Fin 4)` presentation of `R[x,u]` -/

/-- Polynomial ring in variables `(u, x_0, ..., x_3)`, with `none` indexing `u`. -/
abbrev SphereOptionRing := MvPolynomial (Option (Fin 4)) ℝ

/-- Polynomial ring in the four `x` variables. -/
abbrev BallRing := MvPolynomial (Fin 4) ℝ

/-- Embed a ball polynomial into the option-indexed sphere ring. -/
noncomputable def ballToOption : BallRing →ₐ[ℝ] SphereOptionRing :=
  MvPolynomial.rename Option.some

/-- Convert the option-indexed sphere ring to the existing `Fin 5` presentation. -/
noncomputable def optionToFinSphere : SphereOptionRing →ₐ[ℝ] MvPolynomial (Fin 5) ℝ :=
  MvPolynomial.aeval fun
    | none => X uIndexInSphere
    | some i => X (xIndexInSphere i)

/-- Convert the existing `Fin 5` presentation to the option-indexed sphere ring. -/
noncomputable def finSphereToOption : MvPolynomial (Fin 5) ℝ →ₐ[ℝ] SphereOptionRing :=
  MvPolynomial.aeval fun i : Fin 5 =>
    if h : i.val < 4 then X (some ⟨i.val, h⟩) else X none

@[simp] theorem optionToFinSphere_X_none :
    optionToFinSphere (X none) = X uIndexInSphere := by
  simp [optionToFinSphere]

@[simp] theorem optionToFinSphere_X_some (i : Fin 4) :
    optionToFinSphere (X (some i)) = X (xIndexInSphere i) := by
  simp [optionToFinSphere]

@[simp] theorem finSphereToOption_X_x (i : Fin 4) :
    finSphereToOption (X (xIndexInSphere i)) = X (some i) := by
  simp [finSphereToOption, xIndexInSphere]

@[simp] theorem finSphereToOption_X_u :
    finSphereToOption (X uIndexInSphere) = X none := by
  simp [finSphereToOption, uIndexInSphere]

/-- The ball quadratic in the option-indexed sphere ring. -/
def optionBallQuadratic : SphereOptionRing :=
  ∑ i : Fin 4, (X (some i)) ^ 2

/-- The ball generator `g = 1 - sum_i x_i^2` in the option-indexed sphere ring. -/
def optionBallGenerator : SphereOptionRing :=
  1 - optionBallQuadratic

/-- The option-indexed sphere relation `u^2 - g`. -/
def optionSphereRelation : SphereOptionRing :=
  (X none) ^ 2 - optionBallGenerator

/-- The option-indexed analogue of `rho = sum_i x_i^2 + u^2`. -/
def optionSphereRho : SphereOptionRing :=
  optionBallQuadratic + (X none) ^ 2

@[simp] theorem optionSphereRelation_eq_rho_sub_one :
    optionSphereRelation = optionSphereRho - 1 := by
  unfold optionSphereRelation optionSphereRho optionBallGenerator
  ring

@[simp] theorem optionToFinSphere_ballQuadratic :
    optionToFinSphere optionBallQuadratic = ballQuadraticInSphere := by
  unfold optionBallQuadratic ballQuadraticInSphere
  simp [map_sum, map_pow]

@[simp] theorem optionToFinSphere_ballGenerator :
    optionToFinSphere optionBallGenerator = ballGeneratorInSphere := by
  unfold optionBallGenerator ballGeneratorInSphere
  simp [map_sub]

@[simp] theorem optionToFinSphere_relation :
    optionToFinSphere optionSphereRelation = sphereRhoRelation := by
  unfold optionSphereRelation
  rw [sphereRhoRelation_eq_u_sq_sub_ballGenerator]
  simp [map_sub, map_pow]

@[simp] theorem optionToFinSphere_ballToOption (p : BallRing) :
    optionToFinSphere (ballToOption p) = MvPolynomial.rename xIndexInSphere p := by
  have h : optionToFinSphere.comp ballToOption = MvPolynomial.rename xIndexInSphere := by
    ext i
    simp [ballToOption]
  exact DFunLike.congr_fun h p

@[simp] theorem finSphereToOption_choiLamSphereQuartic :
    finSphereToOption choiLamSphereQuartic = ballToOption choiLamQuartic := by
  unfold choiLamSphereQuartic
  have h : finSphereToOption.comp (MvPolynomial.rename xIndexInSphere) = ballToOption := by
    ext i
    simp [ballToOption]
  exact DFunLike.congr_fun h choiLamQuartic

@[simp] theorem finSphereToOption_sphereRho :
    finSphereToOption sphereRho = optionSphereRho := by
  unfold sphereRho optionSphereRho ballQuadraticInSphere optionBallQuadratic
  simp [map_add, map_sum, map_pow]

@[simp] theorem finSphereToOption_sphereChoiLamPerturbed (epsilon : ℝ) :
    finSphereToOption (sphereChoiLamPerturbed epsilon) =
      ballToOption choiLamQuartic + MvPolynomial.C epsilon * optionSphereRho ^ 2 := by
  unfold sphereChoiLamPerturbed
  simp [map_add, map_mul, map_pow]

@[simp] theorem finSphereToOption_ballGeneratorInSphere :
    finSphereToOption ballGeneratorInSphere = optionBallGenerator := by
  unfold ballGeneratorInSphere optionBallGenerator ballQuadraticInSphere optionBallQuadratic
  simp [map_sub, map_sum, map_pow]

@[simp] theorem finSphereToOption_sphereRhoRelation :
    finSphereToOption sphereRhoRelation = optionSphereRelation := by
  rw [sphereRhoRelation_eq_u_sq_sub_ballGenerator]
  unfold optionSphereRelation
  simp [map_sub, map_pow]

@[simp] theorem finSphereToOption_sphereRelation :
    finSphereToOption (sphereRelation 5) = optionSphereRelation := by
  rw [← sphereRhoRelation_eq_sphereRelation]
  exact finSphereToOption_sphereRhoRelation

private theorem totalDegree_aeval_le_of_linear_option {n : ℕ} {τ : Type*}
    (f : Fin n → MvPolynomial τ ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : MvPolynomial (Fin n) ℝ) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  calc
    (algebraMap ℝ (MvPolynomial τ ℝ) (p.coeff d) *
        d.prod fun i k => f i ^ k).totalDegree
        ≤ (algebraMap ℝ (MvPolynomial τ ℝ) (p.coeff d)).totalDegree +
            (d.prod fun i k => f i ^ k).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ = (d.prod fun i k => f i ^ k).totalDegree := by
          rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C]
          simp
    _ ≤ ∑ i ∈ d.support, (f i ^ d i).totalDegree := by
          simp only [Finsupp.prod]
          exact MvPolynomial.totalDegree_finsetProd d.support _
    _ ≤ ∑ i ∈ d.support, d i := by
          apply Finset.sum_le_sum
          intro i _
          calc
            (f i ^ d i).totalDegree ≤ d i * (f i).totalDegree :=
              MvPolynomial.totalDegree_pow _ _
            _ ≤ d i * 1 := Nat.mul_le_mul_left (d i) (hf i)
            _ = d i := Nat.mul_one (d i)
    _ = d.sum (fun _ e => e) := by rfl
    _ ≤ p.totalDegree := Finset.le_sup (f := fun s => s.sum fun _ e => e) hd

/-- The coordinate map from the existing five-variable sphere presentation to the
option presentation does not increase total degree. -/
theorem finSphereToOption_totalDegree_le (p : MvPolynomial (Fin 5) ℝ) :
    (finSphereToOption p).totalDegree ≤ p.totalDegree := by
  unfold finSphereToOption
  apply totalDegree_aeval_le_of_linear_option
  intro i
  by_cases h : i.val < 4
  · simp [h]
  · simp [h]

/-! ## Congruence modulo the sphere relation -/

/-- Congruence modulo the principal ideal generated by `u^2 - g`. -/
def OptionSphereCongruent (p q : SphereOptionRing) : Prop :=
  ∃ r : SphereOptionRing, p - q = optionSphereRelation * r

@[simp] theorem ballToOption_ballGenerator4 :
    ballToOption ballGenerator4 = optionBallGenerator := by
  unfold ballToOption ballGenerator4 ballQuadratic4 optionBallGenerator optionBallQuadratic
  simp [map_sub, map_sum, map_pow]

@[refl] theorem OptionSphereCongruent.refl (p : SphereOptionRing) :
    OptionSphereCongruent p p := by
  use 0
  simp

theorem OptionSphereCongruent.symm {p q : SphereOptionRing}
    (h : OptionSphereCongruent p q) : OptionSphereCongruent q p := by
  rcases h with ⟨r, hr⟩
  refine ⟨-r, ?_⟩
  calc
    q - p = -(p - q) := by ring
    _ = optionSphereRelation * (-r) := by rw [hr]; ring

theorem OptionSphereCongruent.trans {p q r : SphereOptionRing}
    (hpq : OptionSphereCongruent p q) (hqr : OptionSphereCongruent q r) :
    OptionSphereCongruent p r := by
  rcases hpq with ⟨a, ha⟩
  rcases hqr with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  calc
    p - r = (p - q) + (q - r) := by ring
    _ = optionSphereRelation * a + optionSphereRelation * b := by rw [ha, hb]
    _ = optionSphereRelation * (a + b) := by ring

theorem OptionSphereCongruent.add {p q r s : SphereOptionRing}
    (hpq : OptionSphereCongruent p q) (hrs : OptionSphereCongruent r s) :
    OptionSphereCongruent (p + r) (q + s) := by
  rcases hpq with ⟨a, ha⟩
  rcases hrs with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  calc
    p + r - (q + s) = (p - q) + (r - s) := by ring
    _ = optionSphereRelation * a + optionSphereRelation * b := by rw [ha, hb]
    _ = optionSphereRelation * (a + b) := by ring

theorem OptionSphereCongruent.finset_sum {ι : Type*} (s : Finset ι)
    (p q : ι → SphereOptionRing) (h : ∀ i ∈ s, OptionSphereCongruent (p i) (q i)) :
    OptionSphereCongruent (∑ i ∈ s, p i) (∑ i ∈ s, q i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact OptionSphereCongruent.refl 0
  · intro a s has ih h
    rw [Finset.sum_insert has, Finset.sum_insert has]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem OptionSphereCongruent.mul {p q r s : SphereOptionRing}
    (hpq : OptionSphereCongruent p q) (hrs : OptionSphereCongruent r s) :
    OptionSphereCongruent (p * r) (q * s) := by
  rcases hpq with ⟨a, ha⟩
  rcases hrs with ⟨b, hb⟩
  refine ⟨a * r + q * b, ?_⟩
  calc
    p * r - q * s = (p - q) * r + q * (r - s) := by ring
    _ = (optionSphereRelation * a) * r + q * (optionSphereRelation * b) := by
      rw [ha, hb]
    _ = optionSphereRelation * (a * r + q * b) := by ring

/-- The defining congruence `u^2 ≡ g`. -/
theorem OptionSphereCongruent.u_sq :
    OptionSphereCongruent ((X none : SphereOptionRing) ^ 2) (ballToOption ballGenerator4) := by
  use 1
  rw [ballToOption_ballGenerator4]
  unfold optionSphereRelation
  ring

/-- Even powers reduce by `u^(2l) ≡ g^l`. -/
theorem OptionSphereCongruent.u_pow_even (l : ℕ) :
    OptionSphereCongruent
      ((X none : SphereOptionRing) ^ (2 * l)) (ballToOption (ballGenerator4 ^ l)) := by
  induction l with
  | zero =>
      simpa only [mul_zero, pow_zero, map_one] using
        OptionSphereCongruent.refl (1 : SphereOptionRing)
  | succ l ih =>
      have h := ih.mul OptionSphereCongruent.u_sq
      simpa [pow_succ, Nat.mul_succ, pow_add, map_mul, mul_comm, mul_left_comm, mul_assoc]
        using h

/-- Odd powers reduce by `u^(2l+1) ≡ u g^l`. -/
theorem OptionSphereCongruent.u_pow_odd (l : ℕ) :
    OptionSphereCongruent ((X none : SphereOptionRing) ^ (2 * l + 1))
      (X none * ballToOption (ballGenerator4 ^ l)) := by
  have h := (OptionSphereCongruent.u_pow_even l).mul
    (OptionSphereCongruent.refl (X none : SphereOptionRing))
  simpa [pow_succ, pow_add, map_mul, mul_comm, mul_left_comm, mul_assoc, Nat.add_comm]
    using h

/-! ## Polynomial-in-`u` relation -/

/-- The sphere relation viewed as a univariate polynomial in `u` over `R[x]`. -/
def sphereRelationPolynomial : Polynomial BallRing :=
  Polynomial.X ^ 2 - Polynomial.C ballGenerator4

@[simp] theorem optionEquivLeft_relation :
    (MvPolynomial.optionEquivLeft ℝ (Fin 4)) optionSphereRelation = sphereRelationPolynomial := by
  unfold optionSphereRelation sphereRelationPolynomial optionBallGenerator optionBallQuadratic
    ballGenerator4 ballQuadratic4
  rw [map_sub, map_pow]
  simp [map_sub, map_sum, map_pow, MvPolynomial.optionEquivLeft_X_none,
    MvPolynomial.optionEquivLeft_X_some]

/-- The univariate sphere relation is monic in `u`. -/
theorem sphereRelationPolynomial_monic : sphereRelationPolynomial.Monic := by
  unfold sphereRelationPolynomial
  exact Polynomial.monic_X_pow_sub_C ballGenerator4 (by norm_num)

/-! ## Coefficients and the formal even/odd remainder -/

/-- View an option-indexed sphere polynomial as a univariate polynomial in `u`
with coefficients in the four `x` variables. -/
noncomputable def asUPolynomial (p : SphereOptionRing) : Polynomial BallRing :=
  MvPolynomial.optionEquivLeft ℝ (Fin 4) p

/-- Coefficient of `u^m` in an option-indexed sphere polynomial. -/
noncomputable def uCoeff (p : SphereOptionRing) (m : ℕ) : BallRing :=
  (asUPolynomial p).coeff m

private noncomputable def polynomialCAlg : BallRing →ₐ[ℝ] Polynomial BallRing :=
  { Polynomial.C with
    commutes' := by
      intro r
      rfl }

@[simp] theorem optionEquivLeft_ballToOption (a : BallRing) :
    (MvPolynomial.optionEquivLeft ℝ (Fin 4)) (ballToOption a) = Polynomial.C a := by
  have h : (MvPolynomial.optionEquivLeft ℝ (Fin 4)).toAlgHom.comp ballToOption =
      polynomialCAlg := by
    ext i
    simp [ballToOption, polynomialCAlg, MvPolynomial.optionEquivLeft_X_some]
  exact DFunLike.congr_fun h a

@[simp] theorem optionEquivLeft_uTerm (a : BallRing) (m : ℕ) :
    (MvPolynomial.optionEquivLeft ℝ (Fin 4))
      (ballToOption a * (X none : SphereOptionRing) ^ m) =
      Polynomial.C a * Polynomial.X ^ m := by
  rw [map_mul, map_pow, optionEquivLeft_ballToOption]
  simp [MvPolynomial.optionEquivLeft_X_none]

/-- A polynomial of the form `a + u b` has degree strictly below the quadratic sphere relation. -/
theorem linearPolynomial_degree_lt_relation (a b : BallRing) :
    (Polynomial.C a + Polynomial.X * Polynomial.C b).degree < sphereRelationPolynomial.degree := by
  have hlin : (Polynomial.C a + Polynomial.X * Polynomial.C b).degree ≤ (1 : WithBot ℕ) := by
    calc
      (Polynomial.C a + Polynomial.X * Polynomial.C b).degree
          ≤ max (Polynomial.C a).degree (Polynomial.X * Polynomial.C b).degree :=
            Polynomial.degree_add_le _ _
      _ ≤ (1 : WithBot ℕ) := by
        apply max_le
        · exact le_trans Polynomial.degree_C_le (by norm_num)
        · calc
            (Polynomial.X * Polynomial.C b).degree
                ≤ Polynomial.X.degree + (Polynomial.C b).degree := Polynomial.degree_mul_le _ _
            _ ≤ (1 : WithBot ℕ) + 0 := by
              apply add_le_add
              · simp
              · exact Polynomial.degree_C_le
            _ = (1 : WithBot ℕ) := by norm_num
  have hrel : sphereRelationPolynomial.degree = (2 : WithBot ℕ) := by
    unfold sphereRelationPolynomial
    exact Polynomial.degree_X_pow_sub_C (by norm_num : 0 < 2) ballGenerator4
  rw [hrel]
  exact lt_of_le_of_lt hlin (by norm_num)

/-- If `p` has total degree at most `k`, it is the finite sum of its `u`-coefficient
terms through degree `k`. -/
theorem eq_sum_uCoeff_terms_of_totalDegree_le (p : SphereOptionRing) (k : ℕ)
    (hp : p.totalDegree ≤ k) :
    p = ∑ m ∈ Finset.range (k + 1), ballToOption (uCoeff p m) * (X none) ^ m := by
  apply (MvPolynomial.optionEquivLeft ℝ (Fin 4)).injective
  simp only [map_sum, optionEquivLeft_uTerm]
  change asUPolynomial p =
    ∑ x ∈ Finset.range (k + 1), Polynomial.C ((asUPolynomial p).coeff x) *
      Polynomial.X ^ x
  have hnat : (asUPolynomial p).natDegree < k + 1 := by
    rw [asUPolynomial, MvPolynomial.natDegree_optionEquivLeft]
    have hdegOf : p.degreeOf none ≤ p.totalDegree :=
      MvPolynomial.degreeOf_le_totalDegree p none
    omega
  exact Polynomial.as_sum_range_C_mul_X_pow' (asUPolynomial p) hnat

/-- One even `u`-coefficient term reduces to its contribution to the even normal form. -/
theorem OptionSphereCongruent.uCoeff_term_even (a : BallRing) (l : ℕ) :
    OptionSphereCongruent (ballToOption a * (X none : SphereOptionRing) ^ (2 * l))
      (ballToOption (a * ballGenerator4 ^ l)) := by
  have h := (OptionSphereCongruent.refl (ballToOption a)).mul
    (OptionSphereCongruent.u_pow_even l)
  simpa [map_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- One odd `u`-coefficient term reduces to its contribution to the odd normal form. -/
theorem OptionSphereCongruent.uCoeff_term_odd (a : BallRing) (l : ℕ) :
    OptionSphereCongruent (ballToOption a * (X none : SphereOptionRing) ^ (2 * l + 1))
      (X none * ballToOption (a * ballGenerator4 ^ l)) := by
  have h := (OptionSphereCongruent.refl (ballToOption a)).mul
    (OptionSphereCongruent.u_pow_odd l)
  simpa [map_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- The even normal-form component obtained by replacing `u^(2l)` by `g^l`. -/
noncomputable def evenRemainder (k : ℕ) (p : SphereOptionRing) : BallRing :=
  ∑ l ∈ Finset.range (k / 2 + 1),
    uCoeff p (2 * l) * ballGenerator4 ^ l

/-- The odd normal-form component obtained by replacing `u^(2l+1)` by `u g^l`.
This is the coefficient of the final `u` in the reduced form. -/
noncomputable def oddRemainder (k : ℕ) (p : SphereOptionRing) : BallRing :=
  ∑ l ∈ Finset.range ((k - 1) / 2 + 1),
    uCoeff p (2 * l + 1) * ballGenerator4 ^ l

/-- Reassemble a pair `a + u b` in the option-indexed sphere ring. -/
noncomputable def linearRemainder (a b : BallRing) : SphereOptionRing :=
  ballToOption a + X none * ballToOption b

@[simp] theorem optionEquivLeft_linearRemainder (a b : BallRing) :
    (MvPolynomial.optionEquivLeft ℝ (Fin 4)) (linearRemainder a b) =
      Polynomial.C a + Polynomial.X * Polynomial.C b := by
  unfold linearRemainder
  rw [map_add, map_mul, optionEquivLeft_ballToOption, optionEquivLeft_ballToOption]
  simp [MvPolynomial.optionEquivLeft_X_none]

/-- Reassemble the degree-`k` formal normal remainder of `p`. -/
noncomputable def normalRemainder (k : ℕ) (p : SphereOptionRing) : SphereOptionRing :=
  linearRemainder (evenRemainder k p) (oddRemainder k p)

/-- Range-indexed even component: this avoids reindexing by parity in the main
congruence proof. -/
noncomputable def evenRemainderRange (k : ℕ) (p : SphereOptionRing) : BallRing :=
  ∑ m ∈ Finset.range (k + 1),
    if m % 2 = 0 then uCoeff p m * ballGenerator4 ^ (m / 2) else 0

/-- Range-indexed odd component: this avoids reindexing by parity in the main
congruence proof. -/
noncomputable def oddRemainderRange (k : ℕ) (p : SphereOptionRing) : BallRing :=
  ∑ m ∈ Finset.range (k + 1),
    if m % 2 = 1 then uCoeff p m * ballGenerator4 ^ (m / 2) else 0

/-- One range-indexed normal-form term. -/
noncomputable def normalRemainderRangeTerm (p : SphereOptionRing) (m : ℕ) :
    SphereOptionRing :=
  if m % 2 = 0 then ballToOption (uCoeff p m * ballGenerator4 ^ (m / 2))
  else X none * ballToOption (uCoeff p m * ballGenerator4 ^ (m / 2))

/-- Range-indexed normal remainder, definitionally close to the coefficient expansion. -/
noncomputable def normalRemainderRange (k : ℕ) (p : SphereOptionRing) : SphereOptionRing :=
  ∑ m ∈ Finset.range (k + 1), normalRemainderRangeTerm p m

/-- The range-indexed normal remainder is also a linear remainder. -/
theorem normalRemainderRange_eq_linearRemainder (k : ℕ) (p : SphereOptionRing) :
    normalRemainderRange k p =
      linearRemainder (evenRemainderRange k p) (oddRemainderRange k p) := by
  unfold normalRemainderRange normalRemainderRangeTerm linearRemainder evenRemainderRange
    oddRemainderRange
  simp [Finset.mul_sum, map_sum, Finset.sum_ite]

/-- A single coefficient term reduces according to the parity of its `u` exponent. -/
theorem OptionSphereCongruent.uCoeff_term_mod (p : SphereOptionRing) (m : ℕ) :
    OptionSphereCongruent (ballToOption (uCoeff p m) * (X none : SphereOptionRing) ^ m)
      (normalRemainderRangeTerm p m) := by
  unfold normalRemainderRangeTerm
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · rw [ite_eq_left h0]
    have hm : m = 2 * (m / 2) := by
      have h := Nat.mod_add_div m 2
      omega
    convert OptionSphereCongruent.uCoeff_term_even (uCoeff p m) (m / 2) using 1
    · rw [hm]
      rw [Nat.mul_div_right (m / 2) (by norm_num : 0 < 2)]
  · rw [ite_eq_right (by omega)]
    have hm : m = 2 * (m / 2) + 1 := by
      have h := Nat.mod_add_div m 2
      omega
    convert OptionSphereCongruent.uCoeff_term_odd (uCoeff p m) (m / 2) using 1
    · rw [hm]
      rw [show (2 * (m / 2) + 1) / 2 = m / 2 by
        rw [add_comm, Nat.add_mul_div_left 1 (m / 2) (by norm_num : 0 < 2)]
        norm_num]

/-- A polynomial is congruent to its range-indexed normal remainder modulo `u^2 - g`. -/
theorem OptionSphereCongruent.normalRemainderRange_congruent (k : ℕ) (p : SphereOptionRing)
    (hp : p.totalDegree ≤ k) :
    OptionSphereCongruent p (normalRemainderRange k p) := by
  conv_lhs => rw [eq_sum_uCoeff_terms_of_totalDegree_le p k hp]
  unfold SphereBallTransfers.normalRemainderRange
  exact OptionSphereCongruent.finset_sum (Finset.range (k + 1))
    (fun m => ballToOption (uCoeff p m) * (X none : SphereOptionRing) ^ m)
    (fun m => normalRemainderRangeTerm p m)
    (fun m _ => OptionSphereCongruent.uCoeff_term_mod p m)

/-- Squaring a linear normal form and reducing `u^2` to `g`. -/
theorem OptionSphereCongruent.linearRemainder_sq (a b : BallRing) :
    OptionSphereCongruent ((linearRemainder a b) ^ 2)
      (linearRemainder (a ^ 2 + ballGenerator4 * b ^ 2) (2 * a * b)) := by
  refine ⟨ballToOption (b ^ 2), ?_⟩
  unfold linearRemainder optionSphereRelation
  rw [← ballToOption_ballGenerator4]
  simp [map_add, map_mul, map_pow, map_ofNat]
  ring_nf

/-- A finite sum of linear remainders is the linear remainder of the summed coefficients. -/
theorem sum_linearRemainder {N : ℕ} (a b : Fin N → BallRing) :
    (∑ j : Fin N, linearRemainder (a j) (b j)) =
      linearRemainder (∑ j : Fin N, a j) (∑ j : Fin N, b j) := by
  unfold linearRemainder
  simp [Finset.sum_add_distrib, Finset.mul_sum, map_sum]

/-- Reducing a finite sum of squared linear remainders termwise. -/
theorem OptionSphereCongruent.sum_linearRemainder_sq {N : ℕ} (a b : Fin N → BallRing) :
    OptionSphereCongruent (∑ j : Fin N, (linearRemainder (a j) (b j)) ^ 2)
      (∑ j : Fin N,
        linearRemainder ((a j) ^ 2 + ballGenerator4 * (b j) ^ 2) (2 * a j * b j)) := by
  simpa only [Finset.mem_univ] using
    OptionSphereCongruent.finset_sum Finset.univ
      (fun j : Fin N => (linearRemainder (a j) (b j)) ^ 2)
      (fun j : Fin N =>
        linearRemainder ((a j) ^ 2 + ballGenerator4 * (b j) ^ 2) (2 * a j * b j))
      (fun j _ => OptionSphereCongruent.linearRemainder_sq (a j) (b j))

/-- Uniqueness of the linear normal form modulo `u^2 - g`: the only linear
remainder in the ideal is zero. -/
theorem linearRemainder_congruent_zero_iff {a b : BallRing} :
    OptionSphereCongruent (linearRemainder a b) 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    rcases h with ⟨r, hr⟩
    let L : Polynomial BallRing := Polynomial.C a + Polynomial.X * Polynomial.C b
    have hdiv : sphereRelationPolynomial ∣ L := by
      refine ⟨(MvPolynomial.optionEquivLeft ℝ (Fin 4)) r, ?_⟩
      have hmap := congrArg (MvPolynomial.optionEquivLeft ℝ (Fin 4)) hr
      change (MvPolynomial.optionEquivLeft ℝ (Fin 4)) (linearRemainder a b - 0) =
        (MvPolynomial.optionEquivLeft ℝ (Fin 4)) (optionSphereRelation * r) at hmap
      rw [map_sub, map_zero, optionEquivLeft_linearRemainder, sub_zero, map_mul,
        optionEquivLeft_relation] at hmap
      exact hmap
    have hmod_zero : L %ₘ sphereRelationPolynomial = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd sphereRelationPolynomial_monic).2 hdiv
    have hmod_self : L %ₘ sphereRelationPolynomial = L :=
      (Polynomial.modByMonic_eq_self_iff sphereRelationPolynomial_monic).2
        (linearPolynomial_degree_lt_relation a b)
    have hL_zero : L = 0 := by
      rw [← hmod_self, hmod_zero]
    have h0 := congrArg (fun P : Polynomial BallRing => P.coeff 0) hL_zero
    have h1 := congrArg (fun P : Polynomial BallRing => P.coeff 1) hL_zero
    change (Polynomial.C a + Polynomial.X * Polynomial.C b).coeff 0 = 0 at h0
    change (Polynomial.C a + Polynomial.X * Polynomial.C b).coeff 1 = 0 at h1
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero,
      add_zero] at h0
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, one_ne_zero, ↓reduceIte,
      Polynomial.coeff_X_mul, zero_add] at h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    simp [OptionSphereCongruent, linearRemainder]

/-- The degree estimate for coefficients in the `u` expansion, provided by mathlib. -/
theorem uCoeff_totalDegree_le (p : SphereOptionRing) (m : ℕ) :
    (uCoeff p m).totalDegree ≤ p.totalDegree := by
  simpa [uCoeff, asUPolynomial] using
    MvPolynomial.totalDegree_coeff_optionEquivLeft_le (R := ℝ) (S₁ := Fin 4) p m

/-- The stronger coefficient estimate when the selected `u` power is within the
ambient total degree. -/
theorem uCoeff_totalDegree_add_le (p : SphereOptionRing) (m : ℕ)
    (hm : m ≤ p.totalDegree) :
    (uCoeff p m).totalDegree + m ≤ p.totalDegree := by
  simpa [uCoeff, asUPolynomial] using
    MvPolynomial.totalDegree_coeff_optionEquivLeft_add_le (R := ℝ) (S₁ := Fin 4) p m hm

/-- The ball generator `1 - sum_i x_i^2` has total degree at most two. -/
theorem ballGenerator4_totalDegree_le_two : (ballGenerator4 : BallRing).totalDegree ≤ 2 := by
  unfold ballGenerator4 ballQuadratic4
  calc
    (1 - ∑ i : Fin 4, (X i : BallRing) ^ 2).totalDegree
        ≤ max (1 : BallRing).totalDegree
            (∑ i : Fin 4, (X i : BallRing) ^ 2).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
    _ ≤ 2 := by
      apply max_le
      · simp
      · apply MvPolynomial.totalDegree_finsetSum_le
        intro i _
        calc
          ((X i : BallRing) ^ 2).totalDegree
              ≤ 2 * (X i : BallRing).totalDegree := MvPolynomial.totalDegree_pow _ _
          _ ≤ 2 := by simp

/-- A coefficient of `u^m` has total degree bounded by the ambient total-degree
bound minus `m`; if `m` is above the actual `u` degree, the coefficient is zero. -/
theorem uCoeff_totalDegree_sub_le (p : SphereOptionRing) (m k : ℕ)
    (hp : p.totalDegree ≤ k) :
    (uCoeff p m).totalDegree ≤ k - m := by
  by_cases hm : m ≤ p.totalDegree
  · have h := uCoeff_totalDegree_add_le p m hm
    omega
  · have hmdeg : (asUPolynomial p).natDegree < m := by
      rw [asUPolynomial, MvPolynomial.natDegree_optionEquivLeft]
      have hdegOf : p.degreeOf none ≤ p.totalDegree :=
        MvPolynomial.degreeOf_le_totalDegree p none
      omega
    have hzero : uCoeff p m = 0 := by
      unfold uCoeff
      exact Polynomial.coeff_eq_zero_of_natDegree_lt hmdeg
    rw [hzero]
    simp

/-- The range-indexed even component preserves the root-degree bound. -/
theorem evenRemainderRange_totalDegree_le (k : ℕ) (p : SphereOptionRing)
    (hp : p.totalDegree ≤ k) :
    (evenRemainderRange k p).totalDegree ≤ k := by
  unfold evenRemainderRange
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  rw [Finset.mem_range] at hm
  by_cases hpar : m % 2 = 0
  · simp only [hpar, ↓reduceIte]
    have hm_even : m = 2 * (m / 2) := by
      have h := Nat.mod_add_div m 2
      omega
    calc
      (uCoeff p m * ballGenerator4 ^ (m / 2)).totalDegree
          ≤ (uCoeff p m).totalDegree + (ballGenerator4 ^ (m / 2)).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ ≤ (k - m) + 2 * (m / 2) := by
        apply Nat.add_le_add
        · exact uCoeff_totalDegree_sub_le p m k hp
        · calc
            (ballGenerator4 ^ (m / 2)).totalDegree
                ≤ (m / 2) * ballGenerator4.totalDegree := MvPolynomial.totalDegree_pow _ _
            _ ≤ (m / 2) * 2 := Nat.mul_le_mul_left (m / 2) ballGenerator4_totalDegree_le_two
            _ = 2 * (m / 2) := by omega
      _ ≤ k := by omega
  · simp only [hpar, ↓reduceIte]
    exact Nat.zero_le k

/-- The range-indexed odd component has root-degree one less. -/
theorem oddRemainderRange_totalDegree_le (k : ℕ) (p : SphereOptionRing)
    (hk : 1 ≤ k) (hp : p.totalDegree ≤ k) :
    (oddRemainderRange k p).totalDegree ≤ k - 1 := by
  unfold oddRemainderRange
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  rw [Finset.mem_range] at hm
  by_cases hpar : m % 2 = 1
  · simp only [hpar, ↓reduceIte]
    have hm_odd : m = 2 * (m / 2) + 1 := by
      have h := Nat.mod_add_div m 2
      omega
    calc
      (uCoeff p m * ballGenerator4 ^ (m / 2)).totalDegree
          ≤ (uCoeff p m).totalDegree + (ballGenerator4 ^ (m / 2)).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ ≤ (k - m) + 2 * (m / 2) := by
        apply Nat.add_le_add
        · exact uCoeff_totalDegree_sub_le p m k hp
        · calc
            (ballGenerator4 ^ (m / 2)).totalDegree
                ≤ (m / 2) * ballGenerator4.totalDegree := MvPolynomial.totalDegree_pow _ _
            _ ≤ (m / 2) * 2 := Nat.mul_le_mul_left (m / 2) ballGenerator4_totalDegree_le_two
            _ = 2 * (m / 2) := by omega
      _ ≤ k - 1 := by omega
  · simp only [hpar, ↓reduceIte]
    exact Nat.zero_le (k - 1)

/-- The even component of the normal form preserves the root-degree bound. -/
theorem evenRemainder_totalDegree_le (k : ℕ) (p : SphereOptionRing)
    (hp : p.totalDegree ≤ k) :
    (evenRemainder k p).totalDegree ≤ k := by
  unfold evenRemainder
  apply MvPolynomial.totalDegree_finsetSum_le
  intro l hl
  rw [Finset.mem_range] at hl
  calc
    (uCoeff p (2 * l) * ballGenerator4 ^ l).totalDegree
        ≤ (uCoeff p (2 * l)).totalDegree + (ballGenerator4 ^ l).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ (k - 2 * l) + 2 * l := by
      apply Nat.add_le_add
      · exact uCoeff_totalDegree_sub_le p (2 * l) k hp
      · calc
          (ballGenerator4 ^ l).totalDegree ≤ l * ballGenerator4.totalDegree :=
            MvPolynomial.totalDegree_pow _ _
          _ ≤ l * 2 := Nat.mul_le_mul_left l ballGenerator4_totalDegree_le_two
          _ = 2 * l := by omega
    _ = k := by omega

/-- The odd component of the normal form has root-degree one less. -/
theorem oddRemainder_totalDegree_le (k : ℕ) (p : SphereOptionRing)
    (hk : 1 ≤ k) (hp : p.totalDegree ≤ k) :
    (oddRemainder k p).totalDegree ≤ k - 1 := by
  unfold oddRemainder
  apply MvPolynomial.totalDegree_finsetSum_le
  intro l hl
  rw [Finset.mem_range] at hl
  calc
    (uCoeff p (2 * l + 1) * ballGenerator4 ^ l).totalDegree
        ≤ (uCoeff p (2 * l + 1)).totalDegree + (ballGenerator4 ^ l).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ (k - (2 * l + 1)) + 2 * l := by
      apply Nat.add_le_add
      · exact uCoeff_totalDegree_sub_le p (2 * l + 1) k hp
      · calc
          (ballGenerator4 ^ l).totalDegree ≤ l * ballGenerator4.totalDegree :=
            MvPolynomial.totalDegree_pow _ _
          _ ≤ l * 2 := Nat.mul_le_mul_left l ballGenerator4_totalDegree_le_two
          _ = 2 * l := by omega
    _ = k - 1 := by omega

end SphereBallTransfers
end OptimalConvergenceRates

end
