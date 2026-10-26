import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Matrix.Order
import OptimalConvergenceRates.SphereDimensionBounds.HomogeneousQuarticForm

/-! Actual finite positive matrix marginals and the centered-quartic estimate.
This module does not assert the full improved upper theorem. -/
noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.SelectorCentering
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
variable {I : Type*} [Fintype I]

def diagonalMass (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : ℝ := ∑ t, Z t i i

theorem psd_diagonal_nonneg (Z : Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : Z.PosSemidef) (i : Fin 3) : 0 ≤ Z i i := by
  have h := hZ.dotProduct_mulVec_nonneg (Pi.single i 1)
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq',
    Finset.sum_ite_eq, star_trivial] using h

theorem psd_entry_sq_le (Z : Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : Z.PosSemidef) (i j : Fin 3) : Z i j ^ 2 ≤ Z i i * Z j j := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.nonneg
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, star_trivial, pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => B k i) (fun k => B k j)

theorem diagonalMass_nonneg (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : ∀ t, (Z t).PosSemidef) (i : Fin 3) : 0 ≤ diagonalMass Z i := by
  exact Finset.sum_nonneg fun t _ => psd_diagonal_nonneg (Z t) (hZ t) i

theorem psd_entry_abs_le (Z : Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : Z.PosSemidef) (i j : Fin 3) :
    |Z i j| ≤ Real.sqrt (Z i i) * Real.sqrt (Z j j) := by
  have hi := psd_diagonal_nonneg Z hZ i
  have hj := psd_diagonal_nonneg Z hZ j
  have hsq := psd_entry_sq_le Z hZ i j
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hi, Real.sq_sqrt hj]
  exact hsq

theorem psd_entry_abs_sum_le (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : ∀ t, (Z t).PosSemidef) (i j : Fin 3) :
    (∑ t, |Z t i j|) ≤ Real.sqrt (diagonalMass Z i * diagonalMass Z j) := by
  let f : I → ℝ := fun t => Real.sqrt (Z t i i)
  let g : I → ℝ := fun t => Real.sqrt (Z t j j)
  have hfg : (∑ t, |Z t i j|) ≤ ∑ t, f t * g t :=
    Finset.sum_le_sum fun t _ => psd_entry_abs_le (Z t) (hZ t) i j
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hf : ∀ t, f t ^ 2 = Z t i i := fun t =>
    Real.sq_sqrt (psd_diagonal_nonneg (Z t) (hZ t) i)
  have hg : ∀ t, g t ^ 2 = Z t j j := fun t =>
    Real.sq_sqrt (psd_diagonal_nonneg (Z t) (hZ t) j)
  simp_rw [hf, hg] at hcs
  have hleft : 0 ≤ ∑ t, |Z t i j| := Finset.sum_nonneg fun t _ => abs_nonneg _
  have hsquare := (pow_le_pow_left₀ hleft hfg 2).trans hcs
  have hmass : 0 ≤ diagonalMass Z i * diagonalMass Z j :=
    mul_nonneg (diagonalMass_nonneg Z hZ i) (diagonalMass_nonneg Z hZ j)
  apply (sq_le_sq₀ hleft (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hmass]
  exact hsquare

theorem diagonal_pairing_abs_le (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : ∀ t, (Z t).PosSemidef) (i : Fin 3) (f : I → ℝ) (K : ℝ)
    (hf : ∀ t, |f t| ≤ K) :
    |∑ t, Z t i i * f t| ≤ K * diagonalMass Z i := by
  calc
    _ ≤ ∑ t, |Z t i i * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, Z t i i * K := by
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul, abs_of_nonneg (psd_diagonal_nonneg (Z t) (hZ t) i)]
      exact mul_le_mul_of_nonneg_left (hf t) (psd_diagonal_nonneg (Z t) (hZ t) i)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]; rfl

theorem offDiagonal_pairing_abs_le (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : ∀ t, (Z t).PosSemidef) (i j : Fin 3) (f : I → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hf : ∀ t, |f t| ≤ K) :
    |∑ t, Z t i j * f t| ≤ K * Real.sqrt (diagonalMass Z i * diagonalMass Z j) := by
  calc
    _ ≤ ∑ t, |Z t i j * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, |Z t i j| * K := by
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf t) (abs_nonneg _)
    _ = K * ∑ t, |Z t i j| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (psd_entry_abs_sum_le Z hZ i j) hK

/-- The trace of the selector Hankel consistency. Full quadratic consistency
implies this condition on unit sphere points. -/
def TraceConsistency (Z : I → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  (∑ t, Z t 0 2) = diagonalMass Z 1

theorem middleMass_sq_le (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : ∀ t, (Z t).PosSemidef) (htrace : TraceConsistency Z) :
    diagonalMass Z 1 ^ 2 ≤ diagonalMass Z 0 * diagonalMass Z 2 := by
  have hv := diagonalMass_nonneg Z hZ 1
  have hbound : diagonalMass Z 1 ≤
      Real.sqrt (diagonalMass Z 0 * diagonalMass Z 2) := by
    calc
      _ = |∑ t, Z t 0 2| := by
        rw [htrace, abs_of_nonneg hv]
      _ ≤ ∑ t, |Z t 0 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := psd_entry_abs_sum_le Z hZ 0 2
  have hsq := pow_le_pow_left₀ hv hbound 2
  rw [Real.sq_sqrt (mul_nonneg (diagonalMass_nonneg Z hZ 0)
    (diagonalMass_nonneg Z hZ 2))] at hsq
  exact hsq

section Center
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual finite third-moment vector. -/
def thirdMomentVector (h : I → E) (Z : I → Matrix (Fin 3) (Fin 3) ℝ) : E :=
  ∑ t, (Z t 0 1) • h t

/-- Centering is defined also when the leading fourth mass vanishes. -/
def centeringVector (h : I → E) (Z : I → Matrix (Fin 3) (Fin 3) ℝ) : E :=
  (diagonalMass Z 0)⁻¹ • thirdMomentVector h Z

theorem thirdMomentVector_norm_sq_le (h : I → E) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef) :
    ‖thirdMomentVector h Z‖ ^ 2 ≤ diagonalMass Z 0 * diagonalMass Z 1 := by
  have hnorm : ‖thirdMomentVector h Z‖ ≤
      Real.sqrt (diagonalMass Z 0 * diagonalMass Z 1) := by
    calc
      _ ≤ ∑ t, ‖(Z t 0 1) • h t‖ := norm_sum_le _ _
      _ = ∑ t, |Z t 0 1| := by
        apply Finset.sum_congr rfl
        intro t _
        rw [norm_smul, Real.norm_eq_abs, hh t, mul_one]
      _ ≤ _ := psd_entry_abs_sum_le Z hZ 0 1
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [Real.sq_sqrt (mul_nonneg (diagonalMass_nonneg Z hZ 0)
    (diagonalMass_nonneg Z hZ 1))] at hsquare
  exact hsquare

theorem leadingMass_smul_centeringVector (h : I → E)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hU : diagonalMass Z 0 ≠ 0) :
    diagonalMass Z 0 • centeringVector h Z = thirdMomentVector h Z := by
  rw [centeringVector, smul_smul, mul_inv_cancel₀ hU, one_smul]

theorem centeringVector_norm_sq_mass_le (h : I → E) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (hU : 0 < diagonalMass Z 0) :
    ‖centeringVector h Z‖ ^ 2 * diagonalMass Z 0 ≤ diagonalMass Z 1 := by
  have hnorm := congrArg norm (leadingMass_smul_centeringVector h Z hU.ne')
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hU] at hnorm
  have hsq := thirdMomentVector_norm_sq_le h hh Z hZ
  rw [← hnorm] at hsq
  apply (mul_le_mul_iff_right₀ hU).mp
  nlinarith only [hsq]

/-- The three scalar centering bounds are derived from actual finite PSD
marginals, unit vectors and the trace of Hankel consistency. -/
theorem centeringVector_bounds (h : I → E) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (htrace : TraceConsistency Z) :
    ‖centeringVector h Z‖^4 * diagonalMass Z 0 ≤ diagonalMass Z 2 ∧
    ‖centeringVector h Z‖^2 * diagonalMass Z 1 ≤ diagonalMass Z 2 ∧
    ‖centeringVector h Z‖ *
        Real.sqrt (diagonalMass Z 1 * diagonalMass Z 2) ≤ diagonalMass Z 2 := by
  have hU := diagonalMass_nonneg Z hZ 0
  have hV := diagonalMass_nonneg Z hZ 1
  have hW := diagonalMass_nonneg Z hZ 2
  by_cases hzero : diagonalMass Z 0 = 0
  · simp only [centeringVector, hzero, inv_zero, zero_smul, norm_zero,
      zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_mul]
    exact ⟨hW,hW,hW⟩
  · have hUpos : 0 < diagonalMass Z 0 := lt_of_le_of_ne hU (Ne.symm hzero)
    have hmU := centeringVector_norm_sq_mass_le h hh Z hZ hUpos
    have hVW := middleMass_sq_le Z hZ htrace
    have hmU0 : 0 ≤ ‖centeringVector h Z‖^2 * diagonalMass Z 0 := by positivity
    have hmU2 := pow_le_pow_left₀ hmU0 hmU 2
    have hm4 : ‖centeringVector h Z‖^4 * diagonalMass Z 0 ≤ diagonalMass Z 2 := by
      apply (mul_le_mul_iff_right₀ hUpos).mp
      nlinarith only [hmU2,hVW]
    have hm2 : ‖centeringVector h Z‖^2 * diagonalMass Z 1 ≤ diagonalMass Z 2 := by
      have hmUV := mul_le_mul_of_nonneg_right hmU hV
      apply (mul_le_mul_iff_right₀ hUpos).mp
      nlinarith only [hmUV,hVW]
    have hm1 : ‖centeringVector h Z‖ *
        Real.sqrt (diagonalMass Z 1 * diagonalMass Z 2) ≤ diagonalMass Z 2 := by
      apply (sq_le_sq₀ (by positivity) hW).mp
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hV hW)]
      nlinarith only [mul_le_mul_of_nonneg_right hm2 hW]
    exact ⟨hm4,hm2,hm1⟩

/-- The defining third-moment vector identity also holds in the zero-mass case. -/
theorem leadingMass_smul_centeringVector_of_psd (h : I → E)
    (hh : ∀ t, ‖h t‖ = 1) (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : ∀ t, (Z t).PosSemidef) :
    diagonalMass Z 0 • centeringVector h Z = thirdMomentVector h Z := by
  by_cases hzero : diagonalMass Z 0 = 0
  · have hsquare := thirdMomentVector_norm_sq_le h hh Z hZ
    rw [hzero, zero_mul] at hsquare
    have hnorm : ‖thirdMomentVector h Z‖ = 0 := by nlinarith [norm_nonneg (thirdMomentVector h Z)]
    have hv : thirdMomentVector h Z = 0 := norm_eq_zero.mp hnorm
    simp [hzero, hv]
  · exact leadingMass_smul_centeringVector h Z hzero

end Center

section Quartic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual four-term finite contraction. The polynomial-functional identity
is a separate interface; no missing representation is assumed here. -/
def centeredContraction (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (h : I → E) (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (mu : E) : ℝ :=
  (∑ t, Z t 2 2 * quarticDiagonal A (h t))
    - 4 * (∑ t, Z t 1 2 * quarticApply A mu (h t) (h t) (h t))
    + 6 * (∑ t, Z t 1 1 * quarticApply A mu mu (h t) (h t))
    - 3 * (diagonalMass Z 0 * quarticDiagonal A mu)

/-- The dimension-free `332/3` contraction estimate. The scalar centering
bounds are explicit hypotheses; this theorem does not assume an unproved
polynomial functional representation. -/
theorem centeredContraction_abs_le
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hA : SymmetricQuarticForm A) (N : ℝ) (hN : 0 ≤ N)
    (hdiag : ∀ x : E, |A (fun _ => x)| ≤ N * ‖x‖^4)
    (h : I → E) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (mu : E)
    (hmu4 : ‖mu‖^4 * diagonalMass Z 0 ≤ diagonalMass Z 2)
    (hmu2 : ‖mu‖^2 * diagonalMass Z 1 ≤ diagonalMass Z 2)
    (hmu1 : ‖mu‖ * Real.sqrt (diagonalMass Z 1 * diagonalMass Z 2) ≤
      diagonalMass Z 2) :
    |centeredContraction A h Z mu| ≤ (332/3 : ℝ) * N * diagonalMass Z 2 := by
  have h0 : |∑ t, Z t 2 2 * quarticDiagonal A (h t)| ≤ N * diagonalMass Z 2 := by
    apply diagonal_pairing_abs_le Z hZ 2 _ N
    intro t
    simpa only [quarticDiagonal_eq, hh t, one_pow, mul_one] using hdiag (h t)
  have hmixed (t : I) :
      |quarticApply A mu (h t) (h t) (h t)| ≤ (32/3 : ℝ) * N * ‖mu‖ := by
    have hb := symmetricQuarticForm_product_bound A hA N hN hdiag ![mu,h t,h t,h t]
    simpa [quarticApply, Real.norm_eq_abs, Fin.prod_univ_four, hh t] using hb
  have h1 : |∑ t, Z t 1 2 * quarticApply A mu (h t) (h t) (h t)| ≤
      (32/3 : ℝ) * N * diagonalMass Z 2 := by
    have hp := offDiagonal_pairing_abs_le Z hZ 1 2 _
      ((32/3 : ℝ) * N * ‖mu‖) (by positivity) hmixed
    calc
      _ ≤ _ := hp
      _ = ((32/3 : ℝ) * N) * (‖mu‖ * Real.sqrt
          (diagonalMass Z 1 * diagonalMass Z 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmu1 (by positivity)
  have hquadratic (t : I) :
      |quarticApply A mu mu (h t) (h t)| ≤ (32/3 : ℝ) * N * ‖mu‖^2 := by
    have hb := symmetricQuarticForm_product_bound A hA N hN hdiag ![mu,mu,h t,h t]
    simpa [quarticApply, Real.norm_eq_abs, Fin.prod_univ_four, hh t, pow_two,
      mul_assoc] using hb
  have h2 : |∑ t, Z t 1 1 * quarticApply A mu mu (h t) (h t)| ≤
      (32/3 : ℝ) * N * diagonalMass Z 2 := by
    have hp := diagonal_pairing_abs_le Z hZ 1 _ ((32/3 : ℝ) * N * ‖mu‖^2) hquadratic
    calc
      _ ≤ _ := hp
      _ = ((32/3 : ℝ) * N) * (‖mu‖^2 * diagonalMass Z 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmu2 (by positivity)
  have h3 : |diagonalMass Z 0 * quarticDiagonal A mu| ≤ N * diagonalMass Z 2 := by
    rw [abs_mul, abs_of_nonneg (diagonalMass_nonneg Z hZ 0)]
    calc
      _ ≤ diagonalMass Z 0 * (N * ‖mu‖^4) :=
        mul_le_mul_of_nonneg_left (by simpa only [quarticDiagonal_eq] using hdiag mu)
          (diagonalMass_nonneg Z hZ 0)
      _ = N * (‖mu‖^4 * diagonalMass Z 0) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmu4 hN
  rw [abs_le] at h0 h1 h2 h3 ⊢
  unfold centeredContraction
  constructor <;> linarith

/-- The centering bounds are now discharged from actual finite PSD data;
there is no scalar moment-bound hypothesis in this theorem. -/
theorem finite_centeredContraction_abs_le
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hA : SymmetricQuarticForm A) (N : ℝ) (hN : 0 ≤ N)
    (hdiag : ∀ x : E, |A (fun _ => x)| ≤ N * ‖x‖^4)
    (h : I → E) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (htrace : TraceConsistency Z) :
    |centeredContraction A h Z (centeringVector h Z)| ≤
      (332/3 : ℝ) * N * diagonalMass Z 2 := by
  obtain ⟨h4,h2,h1⟩ := centeringVector_bounds h hh Z hZ htrace
  exact centeredContraction_abs_le A hA N hN hdiag h hh Z hZ _ h4 h2 h1

theorem quarticApply_smul_last
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (a b c x : E) (r : ℝ) :
    quarticApply A a b c (r • x) = r * quarticApply A a b c x := by
  have h := A.map_update_smul ![a,b,c,(0 : E)] (3 : Fin 4) r x
  simpa only [quarticApply, quarticTuple_update3, smul_eq_mul] using h

theorem quarticApply_sum_last
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (a b c : E) (f : I → E) :
    quarticApply A a b c (∑ t, f t) = ∑ t, quarticApply A a b c (f t) := by
  classical
  have hall (S : Finset I) :
      quarticApply A a b c (∑ t ∈ S, f t) = ∑ t ∈ S, quarticApply A a b c (f t) := by
    induction S using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact A.map_coord_zero (3 : Fin 4) rfl
    | @insert t S ht ih =>
        rw [Finset.sum_insert ht, Finset.sum_insert ht, quarticApply_add3, ih]
  exact hall Finset.univ

/-- A genuine finite linear functional on continuous quartic tensors. The
coefficient factors are the actual univariate quartic binomial coefficients. -/
def tensorMarginalFunctional (e : E) (h : I → E)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ →ₗ[ℝ] ℝ where
  toFun A := ∑ t, (Z t 0 0 * quarticDiagonal A e
    + 4 * Z t 0 1 * quarticApply A e e e (h t)
    + 6 * Z t 1 1 * quarticApply A e e (h t) (h t)
    + 4 * Z t 1 2 * quarticApply A e (h t) (h t) (h t)
    + Z t 2 2 * quarticDiagonal A (h t))
  map_add' A B := by
    simp only [quarticDiagonal, quarticApply, ContinuousMultilinearMap.add_apply,
      mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r A := by
    simp only [quarticDiagonal, quarticApply, ContinuousMultilinearMap.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring

theorem tensorMarginalFunctional_apply (e : E) (h : I → E)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    tensorMarginalFunctional e h Z A = ∑ t, (Z t 0 0 * quarticDiagonal A e
    + 4 * Z t 0 1 * quarticApply A e e e (h t)
    + 6 * Z t 1 1 * quarticApply A e e (h t) (h t)
    + 4 * Z t 1 2 * quarticApply A e (h t) (h t) (h t)
    + Z t 2 2 * quarticDiagonal A (h t)) := rfl

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem quarticApply_pullback
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (L : D →L[ℝ] E) (a b c d : D) :
    quarticApply (A.compContinuousLinearMap (fun _ => L)) a b c d =
      quarticApply A (L a) (L b) (L c) (L d) := by
  unfold quarticApply
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Exact pullback identity: no polynomial or functional representation premise
is silently substituted for this finite tensor calculation. -/
theorem tensorMarginalFunctional_pullback
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (e : D) (v : I → D) (L : D →L[ℝ] E) (h : I → E)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (mu : E)
    (he : L e = -mu) (hv : ∀ t, L (v t) = h t)
    (hcenter : thirdMomentVector h Z = diagonalMass Z 0 • mu) :
    tensorMarginalFunctional e v Z (A.compContinuousLinearMap (fun _ => L)) =
      centeredContraction A h Z mu := by
  have hthird : (∑ t, Z t 0 1 * quarticApply A mu mu mu (h t)) =
      diagonalMass Z 0 * quarticDiagonal A mu := by
    calc
      _ = quarticApply A mu mu mu (thirdMomentVector h Z) := by
        rw [thirdMomentVector, quarticApply_sum_last]
        simp_rw [quarticApply_smul_last]
      _ = _ := by rw [hcenter, quarticApply_smul_last]; rfl
  rw [tensorMarginalFunctional_apply]
  simp only [quarticDiagonal, quarticApply_pullback, he, hv,
    quarticApply_neg0, quarticApply_neg1, quarticApply_neg2, quarticApply_neg3,
    mul_neg, neg_mul, neg_neg]
  simp only [mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul] at *
  change _ = _ at hthird
  unfold centeredContraction diagonalMass quarticDiagonal at *
  linarith

theorem symmetricQuarticForm_eq_of_diagonal
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hA : SymmetricQuarticForm A) (hB : SymmetricQuarticForm B)
    (hdiag : ∀ x, A (fun _ => x) = B (fun _ => x)) : A = B := by
  ext v
  have hsum : quarticPolarizationSum A (v 0) (v 1) (v 2) (v 3) =
      quarticPolarizationSum B (v 0) (v 1) (v 2) (v 3) := by
    simp only [quarticPolarizationSum, quarticDiagonal_eq, hdiag]
  rw [quarticPolarization_identity A hA, quarticPolarization_identity B hB] at hsum
  have hvalue : quarticApply A (v 0) (v 1) (v 2) (v 3) =
      quarticApply B (v 0) (v 1) (v 2) (v 3) := by linarith
  have hv : ![v 0,v 1,v 2,v 3] = v := by ext i; fin_cases i <;> rfl
  simpa only [quarticApply,hv] using hvalue

end Quartic

section Polynomial

open MvPolynomial

abbrev EP (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev P (n : ℕ) := MvPolynomial (Fin n) ℝ

/-- Full coordinate form of the finite quadratic Hankel consistency. -/
def QuadraticConsistency {n : ℕ} (h : I → EP n)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j, (∑ t, (Z t 0 2 - Z t 1 1) * (h t i * h t j)) = 0

theorem traceConsistency_of_quadraticConsistency {n : ℕ}
    (h : I → EP n) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hcons : QuadraticConsistency h Z) :
    TraceConsistency Z := by
  have hunit (t : I) : (∑ i, h t i * h t i) = 1 := by
    have hsq := congrArg (fun r : ℝ => r^2) (hh t)
    change ‖h t‖ ^ 2 = (1 : ℝ)^2 at hsq
    rw [PiLp.norm_sq_eq_of_L2] at hsq
    have hfinal : (∑ i, (h t i)^2) = 1 := by
      simpa only [Real.norm_eq_abs, sq_abs, one_pow] using hsq
    simpa only [pow_two] using hfinal
  have hsum : (∑ t, (Z t 0 2 - Z t 1 1)) = 0 := by
    calc
      _ = ∑ t, (Z t 0 2 - Z t 1 1) * (∑ i, h t i * h t i) := by
        simp_rw [hunit, mul_one]
      _ = ∑ i, ∑ t, (Z t 0 2 - Z t 1 1) * (h t i * h t i) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = 0 := Finset.sum_eq_zero fun i _ => hcons i i
  unfold TraceConsistency diagonalMass
  simpa only [Finset.sum_sub_distrib, sub_eq_zero] using hsum

/-- Actual evaluation as a real linear functional on the entire polynomial ring. -/
def polynomialEvaluation {n : ℕ} (x : EP n) : P n →ₗ[ℝ] ℝ where
  toFun p := euclideanPolynomialEval p x
  map_add' p q := by simp [euclideanPolynomialEval]
  map_smul' r p := by simp [euclideanPolynomialEval, smul_eq_C_mul]

@[simp] theorem polynomialEvaluation_apply {n : ℕ} (x : EP n) (p : P n) :
    polynomialEvaluation x p = euclideanPolynomialEval p x := rfl

/-- Sixteen actual evaluations, normalized by the exact real polarization identity. -/
def polarizedEvaluation {n : ℕ} (a b c d : EP n) : P n →ₗ[ℝ] ℝ :=
  (384 : ℝ)⁻¹ • ∑ s0 : Bool, ∑ s1 : Bool, ∑ s2 : Bool, ∑ s3 : Bool,
    (quarticSign s0 * quarticSign s1 * quarticSign s2 * quarticSign s3) •
      polynomialEvaluation (quarticSign s0 • a + quarticSign s1 • b +
        quarticSign s2 • c + quarticSign s3 • d)

theorem polarizedEvaluation_homogeneous {n : ℕ} (p : P n)
    (hp : p.IsHomogeneous 4) (a b c d : EP n) :
    polarizedEvaluation a b c d p = quarticApply (homogeneousQuarticForm p) a b c d := by
  have hsum : polarizedEvaluation a b c d p = (384 : ℝ)⁻¹ *
      quarticPolarizationSum (homogeneousQuarticForm p) a b c d := by
    simp only [polarizedEvaluation, LinearMap.smul_apply, LinearMap.sum_apply,
      smul_eq_mul, polynomialEvaluation_apply,
      quarticPolarizationSum, quarticDiagonal_eq, homogeneousQuarticForm_diagonal p hp]
  rw [hsum, quarticPolarization_identity _ (homogeneousQuarticForm_symmetric p)]
  ring

/-- A genuine finite selector-marginal functional on all ambient polynomials. -/
def polynomialMarginalFunctional {n : ℕ} (e : EP n) (h : I → EP n)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) : P n →ₗ[ℝ] ℝ :=
  ∑ t, ((Z t 0 0) • polarizedEvaluation e e e e
    + (4 * Z t 0 1) • polarizedEvaluation e e e (h t)
    + (6 * Z t 1 1) • polarizedEvaluation e e (h t) (h t)
    + (4 * Z t 1 2) • polarizedEvaluation e (h t) (h t) (h t)
    + (Z t 2 2) • polarizedEvaluation (h t) (h t) (h t) (h t))

theorem polynomialMarginalFunctional_homogeneous {n : ℕ} (p : P n)
    (hp : p.IsHomogeneous 4) (e : EP n) (h : I → EP n)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) :
    polynomialMarginalFunctional e h Z p =
      tensorMarginalFunctional e h Z (homogeneousQuarticForm p) := by
  simp only [polynomialMarginalFunctional, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, polarizedEvaluation_homogeneous p hp,
    tensorMarginalFunctional_apply, quarticDiagonal]

/-- The actual finite linear functional obtained after centering in the transverse
polynomial variables. It is defined on the full polynomial ring. -/
def centeredPolynomialFunctional {n : ℕ} (h : I → EP n)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (mu : EP n) : P n →ₗ[ℝ] ℝ :=
  (∑ t, (Z t 2 2) • polynomialEvaluation (h t))
    - 4 • (∑ t, (Z t 1 2) • polarizedEvaluation mu (h t) (h t) (h t))
    + 6 • (∑ t, (Z t 1 1) • polarizedEvaluation mu mu (h t) (h t))
    - (3 * diagonalMass Z 0) • polynomialEvaluation mu

theorem centeredPolynomialFunctional_homogeneous {n : ℕ} (p : P n)
    (hp : p.IsHomogeneous 4) (h : I → EP n)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (mu : EP n) :
    centeredPolynomialFunctional h Z mu p =
      centeredContraction (homogeneousQuarticForm p) h Z mu := by
  simp only [centeredPolynomialFunctional, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    polarizedEvaluation_homogeneous p hp, polynomialEvaluation_apply,
    centeredContraction, quarticDiagonal_eq,
    homogeneousQuarticForm_diagonal p hp]
  ring

/-- The dimension-free estimate for an ACTUAL homogeneous quartic polynomial
and an ACTUAL finite linear functional. No tensor-representation premise is
assumed on the polynomial, and no scalar centering estimates are assumed. -/
theorem finite_centeredPolynomialFunctional_abs_le {n : ℕ} (hn : 0 < n)
    (p : P n) (hp : p.IsHomogeneous 4)
    (h : I → EP n) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (htrace : TraceConsistency Z) :
    |centeredPolynomialFunctional h Z (centeringVector h Z) p| ≤
      (332/3 : ℝ) * OptimalConvergenceRates.SphereDimensionBounds.Foundation.sphereSupNorm p * diagonalMass Z 2 := by
  rw [centeredPolynomialFunctional_homogeneous p hp]
  apply finite_centeredContraction_abs_le _ (homogeneousQuarticForm_symmetric p)
    _ (polynomial_sphereSupNorm_nonneg hn p) _ h hh Z hZ htrace
  intro x
  rw [homogeneousQuarticForm_diagonal p hp]
  exact euclideanPolynomialEval_homogeneous_bound p hp x

/-- Exact identity for the ACTUAL polynomial functional under an actual linear
pullback of an actual quartic. The evaluation identity is an explicit polynomial
substitution hypothesis, not a tensor-existence assumption. -/
theorem polynomialMarginalFunctional_pullback {n m : ℕ}
    (p : P n) (hp : p.IsHomogeneous 4) (q : P m) (hq : q.IsHomogeneous 4)
    (L : EP m →L[ℝ] EP n)
    (hpull : ∀ x, euclideanPolynomialEval q x = euclideanPolynomialEval p (L x))
    (e : EP m) (v : I → EP m) (h : I → EP n)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (mu : EP n)
    (he : L e = -mu) (hv : ∀ t, L (v t) = h t)
    (hcenter : thirdMomentVector h Z = diagonalMass Z 0 • mu) :
    polynomialMarginalFunctional e v Z q = centeredPolynomialFunctional h Z mu p := by
  have hcomp : SymmetricQuarticForm
      ((homogeneousQuarticForm p).compContinuousLinearMap (fun _ => L)) := by
    intro sig v
    change homogeneousQuarticForm p (fun i => L (v (sig i))) =
      homogeneousQuarticForm p (fun i => L (v i))
    exact homogeneousQuarticForm_symmetric p sig (fun i => L (v i))
  have hform : homogeneousQuarticForm q =
      (homogeneousQuarticForm p).compContinuousLinearMap (fun _ => L) := by
    apply symmetricQuarticForm_eq_of_diagonal _ _ (homogeneousQuarticForm_symmetric q) hcomp
    intro x
    rw [homogeneousQuarticForm_diagonal q hq,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [homogeneousQuarticForm_diagonal p hp]
    exact hpull x
  rw [polynomialMarginalFunctional_homogeneous q hq, hform,
    centeredPolynomialFunctional_homogeneous p hp]
  exact tensorMarginalFunctional_pullback _ e v L h Z mu he hv hcenter

/-- The actual finite selector-marginal functional applied to an actual centered
quartic, with every scalar centering estimate discharged. -/
theorem polynomialMarginalFunctional_pullback_abs_le {n m : ℕ} (hn : 0 < n)
    (p : P n) (hp : p.IsHomogeneous 4) (q : P m) (hq : q.IsHomogeneous 4)
    (L : EP m →L[ℝ] EP n)
    (hpull : ∀ x, euclideanPolynomialEval q x = euclideanPolynomialEval p (L x))
    (e : EP m) (v : I → EP m) (h : I → EP n) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (htrace : TraceConsistency Z)
    (he : L e = -centeringVector h Z) (hv : ∀ t, L (v t) = h t) :
    |polynomialMarginalFunctional e v Z q| ≤
      (332/3 : ℝ) * OptimalConvergenceRates.SphereDimensionBounds.Foundation.sphereSupNorm p * diagonalMass Z 2 := by
  rw [polynomialMarginalFunctional_pullback p hp q hq L hpull e v h Z _ he hv
    (leadingMass_smul_centeringVector_of_psd h hh Z hZ).symm]
  exact finite_centeredPolynomialFunctional_abs_le hn p hp h hh Z hZ htrace

/-- Version with the full quadratic Hankel consistency rather than its trace. -/
theorem finite_centeredPolynomialFunctional_abs_le_of_consistency {n : ℕ}
    (hn : 0 < n) (p : P n) (hp : p.IsHomogeneous 4)
    (h : I → EP n) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (hcons : QuadraticConsistency h Z) :
    |centeredPolynomialFunctional h Z (centeringVector h Z) p| ≤
      (332/3 : ℝ) * OptimalConvergenceRates.SphereDimensionBounds.Foundation.sphereSupNorm p * diagonalMass Z 2 :=
  finite_centeredPolynomialFunctional_abs_le hn p hp h hh Z hZ
    (traceConsistency_of_quadraticConsistency h hh Z hcons)

/-- Full-consistency ambient pullback version of the actual polynomial estimate. -/
theorem polynomialMarginalFunctional_pullback_abs_le_of_consistency {n m : ℕ}
    (hn : 0 < n) (p : P n) (hp : p.IsHomogeneous 4)
    (q : P m) (hq : q.IsHomogeneous 4) (L : EP m →L[ℝ] EP n)
    (hpull : ∀ x, euclideanPolynomialEval q x = euclideanPolynomialEval p (L x))
    (e : EP m) (v : I → EP m) (h : I → EP n) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (hcons : QuadraticConsistency h Z)
    (he : L e = -centeringVector h Z) (hv : ∀ t, L (v t) = h t) :
    |polynomialMarginalFunctional e v Z q| ≤
      (332/3 : ℝ) * OptimalConvergenceRates.SphereDimensionBounds.Foundation.sphereSupNorm p * diagonalMass Z 2 :=
  polynomialMarginalFunctional_pullback_abs_le hn p hp q hq L hpull e v h hh Z hZ
    (traceConsistency_of_quadraticConsistency h hh Z hcons) he hv

end Polynomial

end OptimalConvergenceRates.SphereDimensionBounds.SelectorCentering
