/-
  Shifted angular bounds on the whole cube.

  The sine-removal theorem in `AngularVectorBounds` is naturally stated on
  the central half-period.  For an arbitrary cube point, each arccos angle
  is translated by either zero or pi to enter that half-period.  Translation
  preserves the angular derivative tower and its uniform bounds; the sine
  factors change only by signs, which disappear after taking a squared norm.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.AngularVectorBounds

open MvPolynomial Finset Set
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-! ## Centering arccos angles -/

/-- The nearest endpoint of `[0, pi]` chosen using the sign of a cube
coordinate. -/
def centeredArccosBase (x : ℝ) : ℝ :=
  if 0 ≤ x then 0 else Real.pi

/-- The sign introduced when translating a sine by `centeredArccosBase`. -/
def centeredArccosSign (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

/-- The arccos angle translated to the central half-period. -/
def centeredArccosAngle (x : ℝ) : ℝ :=
  Real.arccos x - centeredArccosBase x

theorem centeredArccosAngle_range {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |centeredArccosAngle x| ≤ Real.pi / 2 := by
  rcases hx with ⟨hxlower, hxupper⟩
  by_cases hxzero : 0 ≤ x
  · have harccosNonneg : 0 ≤ Real.arccos x := Real.arccos_nonneg x
    have harccosHalf : Real.arccos x ≤ Real.pi / 2 :=
      Real.arccos_le_pi_div_two.mpr hxzero
    simp only [centeredArccosAngle, centeredArccosBase, if_pos hxzero, sub_zero,
      abs_of_nonneg harccosNonneg]
    exact harccosHalf
  · have hxneg : x < 0 := lt_of_not_ge hxzero
    have harccosHalf : Real.pi / 2 ≤ Real.arccos x := by
      apply le_of_not_gt
      rw [Real.arccos_lt_pi_div_two]
      exact not_lt_of_ge hxneg.le
    have harccosPi : Real.arccos x ≤ Real.pi := Real.arccos_le_pi x
    have hnonpos : Real.arccos x - Real.pi ≤ 0 := sub_nonpos.mpr harccosPi
    simp only [centeredArccosAngle, centeredArccosBase, if_neg hxzero,
      abs_of_nonpos hnonpos]
    linarith

@[simp] theorem centeredArccosAngle_add_base (x : ℝ) :
    centeredArccosAngle x + centeredArccosBase x = Real.arccos x := by
  unfold centeredArccosAngle
  ring

theorem sin_add_centeredArccosBase (x t : ℝ) :
    Real.sin (t + centeredArccosBase x) =
      centeredArccosSign x * Real.sin t := by
  by_cases hx : 0 ≤ x
  · simp [centeredArccosBase, centeredArccosSign, hx]
  · simp [centeredArccosBase, centeredArccosSign, hx, Real.sin_add_pi]

@[simp] theorem abs_centeredArccosSign (x : ℝ) :
    |centeredArccosSign x| = 1 := by
  by_cases hx : 0 ≤ x <;> simp [centeredArccosSign, hx]

/-- Pointwise translation of an angular parameter. -/
def translateAngles {n : ℕ} (base theta : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ theta i + base i

/-- The inverse pointwise translation. -/
def untranslateAngles {n : ℕ} (base theta : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ theta i - base i

@[simp] theorem translateAngles_apply {n : ℕ}
    (base theta : Fin n → ℝ) (i : Fin n) :
    translateAngles base theta i = theta i + base i := rfl

@[simp] theorem translateAngles_untranslateAngles {n : ℕ}
    (base theta : Fin n → ℝ) :
    translateAngles base (untranslateAngles base theta) = theta := by
  funext i
  simp [translateAngles, untranslateAngles]

@[simp] theorem untranslateAngles_translateAngles {n : ℕ}
    (base theta : Fin n → ℝ) :
    untranslateAngles base (translateAngles base theta) = theta := by
  funext i
  simp [translateAngles, untranslateAngles]

theorem translateAngles_replaceAngle {n : ℕ}
    (base theta : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    translateAngles base (replaceAngle theta i t) =
      replaceAngle (translateAngles base theta) i (t + base i) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [replaceAngle_apply_of_ne _ hji, translateAngles]

/-- Translation of every level of an angular derivative tower. -/
def translatedAngularTower
    {n : ℕ} {E : Type*}
    (base : Fin n → ℝ)
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (pref : List (Fin n)) (theta : Fin n → ℝ) : E :=
  F pref (translateAngles base theta)

theorem translatedAngularTower_isAngularDerivativeTower
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (base : Fin n → ℝ)
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (hderiv : IsAngularDerivativeTower F) :
    IsAngularDerivativeTower (translatedAngularTower base F) := by
  intro pref i theta
  have h := hderiv pref i (translateAngles base theta)
  have hcomp := h.comp_add_const (theta i) (base i)
  simpa only [translatedAngularTower, translateAngles_apply,
    translateAngles_replaceAngle] using hcomp

theorem uniformAngularSqBound_translated_iff
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (base : Fin n → ℝ)
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (pref : List (Fin n)) (Q : ℝ) :
    UniformAngularSqBound (translatedAngularTower base F) pref Q ↔
      UniformAngularSqBound F pref Q := by
  constructor
  · intro h theta
    simpa [translatedAngularTower] using h (untranslateAngles base theta)
  · intro h theta
    exact h (translateAngles base theta)

/-! ## Signs contributed by the selected coordinates -/

def centeredArccosSignProd {n : ℕ}
    (x : Fin n → ℝ) (indices : List (Fin n)) : ℝ :=
  (indices.map (fun i ↦ centeredArccosSign (x i))).prod

@[simp] theorem abs_centeredArccosSignProd {n : ℕ}
    (x : Fin n → ℝ) (indices : List (Fin n)) :
    |centeredArccosSignProd x indices| = 1 := by
  induction indices with
  | nil => simp [centeredArccosSignProd]
  | cons i indices ih =>
      change
        |centeredArccosSign (x i) * centeredArccosSignProd x indices| = 1
      rw [abs_mul, abs_centeredArccosSign, ih, one_mul]

theorem prod_sin_translate_centeredArccosBase {n : ℕ}
    (x theta : Fin n → ℝ) (indices : List (Fin n)) :
    (indices.map (fun i ↦ Real.sin
      (translateAngles (fun j ↦ centeredArccosBase (x j)) theta i))).prod =
      centeredArccosSignProd x indices *
        (indices.map (fun i ↦ Real.sin (theta i))).prod := by
  induction indices with
  | nil => simp [centeredArccosSignProd]
  | cons i indices ih =>
      change
        Real.sin (theta i + centeredArccosBase (x i)) *
            (indices.map (fun j ↦ Real.sin
              (translateAngles (fun l ↦ centeredArccosBase (x l)) theta j))).prod =
          (centeredArccosSign (x i) * centeredArccosSignProd x indices) *
            (Real.sin (theta i) *
              (indices.map (fun j ↦ Real.sin (theta j))).prod)
      rw [sin_add_centeredArccosBase, ih]
      ring

/-! ## Whole-cube weighted parity estimate -/

/-- The two-rotation seed estimate implies the weighted parity bound at an
arbitrary point of the cube.  The hypotheses are exactly those of
`eval_weightedParitySum_le_of_twoRotationSeed`; the central-half-period
restriction has been replaced by cube membership of `x`. -/
theorem eval_weightedParitySum_le_of_twoRotationSeed_hypercube
    {n N : ℕ} (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    {I J : Finset (Fin n)} (hJI : J ⊆ I)
    (a b : Fin n) (remaining : List (Fin n))
    (hselected : (a :: b :: remaining).toFinset = J)
    (hnodup : (a :: b :: remaining).Nodup)
    {D H : ℝ} (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hseed : UniformAngularSqBound
      (parityTermAngularDerivativeVector P I) [b, a] H)
    (hstep : ∀ (pref : List (Fin n)) (i : Fin n) {Q : ℝ},
      0 ≤ Q →
        UniformAngularSqBound (parityTermAngularDerivativeVector P I) pref Q →
        UniformAngularSqBound (parityTermAngularDerivativeVector P I)
          (i :: pref) (D ^ 2 * Q))
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    MvPolynomial.eval x
        (BoxSemialgebraicGeneratorProd (I \ J) *
          ∑ nu, (circleParityComponent (P nu) I) ^ 2) ≤
      (Real.pi / 2) ^ (2 * (remaining.length + 2)) *
        (D ^ (2 * remaining.length) * H) := by
  let selected : List (Fin n) := a :: b :: remaining
  let Q : Fin N → MvPolynomial (CubeCircleVar n) ℝ :=
    fun nu ↦ pairedPolynomialParityTerm (P nu) I
  let F : List (Fin n) → (Fin n → ℝ) → EuclideanSpace ℝ (Fin N) :=
    parityTermAngularDerivativeVector P I
  let theta : Fin n → ℝ := fun i ↦ Real.arccos (x i)
  let base : Fin n → ℝ := fun i ↦ centeredArccosBase (x i)
  let delta : Fin n → ℝ := fun i ↦ centeredArccosAngle (x i)
  let G : List (Fin n) → (Fin n → ℝ) → EuclideanSpace ℝ (Fin N) :=
    translatedAngularTower base F
  let sign : ℝ := centeredArccosSignProd x selected
  let V : (Fin n → ℝ) → EuclideanSpace ℝ (Fin N) :=
    parityResidualVector P I J
  let W : (Fin n → ℝ) → EuclideanSpace ℝ (Fin N) :=
    fun phi ↦ sign • V (translateAngles base phi)
  have hderivF : IsAngularDerivativeTower F := by
    exact circlePolynomialAngularDerivativeVector_isAngularDerivativeTower Q
  have hderivG : IsAngularDerivativeTower G := by
    exact translatedAngularTower_isAngularDerivativeTower base F hderivF
  have hseedG : UniformAngularSqBound G [b, a] H := by
    exact (uniformAngularSqBound_translated_iff base F [b, a] H).2 hseed
  have hstepG : ∀ (pref : List (Fin n)) (i : Fin n) {R : ℝ},
      0 ≤ R → UniformAngularSqBound G pref R →
        UniformAngularSqBound G (i :: pref) (D ^ 2 * R) := by
    intro pref i R hR hpref
    have hprefF : UniformAngularSqBound F pref R :=
      (uniformAngularSqBound_translated_iff base F pref R).1 hpref
    have hnextF := hstep pref i hR hprefF
    exact (uniformAngularSqBound_translated_iff
      base F (i :: pref) (D ^ 2 * R)).2 hnextF
  have hfactorF (phi : Fin n → ℝ) :
      F [] phi =
        (selected.map (fun i ↦ Real.sin (phi i))).prod • V phi := by
    have hsplit :=
      finiteEuclideanVector_pairedPolynomialParityTerm_split_factor
        P hJI phi
    have hprod :
        (∏ i ∈ J, Real.sin (phi i)) =
          (selected.map (fun i ↦ Real.sin (phi i))).prod := by
      rw [← hselected]
      exact List.prod_toFinset _ hnodup
    simpa [F, Q, V, selected, parityTermAngularDerivativeVector, hprod] using hsplit
  have hfactorG (phi : Fin n → ℝ) :
      G [] phi =
        (selected.map (fun i ↦ Real.sin (phi i))).prod • W phi := by
    rw [show G [] phi = F [] (translateAngles base phi) by rfl,
      hfactorF]
    have hprod := prod_sin_translate_centeredArccosBase x phi selected
    rw [show (fun j ↦ centeredArccosBase (x j)) = base by rfl] at hprod
    rw [hprod]
    simp only [W, sign, V]
    rw [mul_comm, smul_smul]
  have hbaseG : ∀ i ∈ selected, ∀ phi,
      G [] (replaceAngle phi i 0) = 0 := by
    intro i hi phi
    rw [hfactorG]
    have hzero :
        (selected.map (fun j ↦ Real.sin (replaceAngle phi i 0 j))).prod = 0 := by
      apply List.prod_eq_zero
      exact List.mem_map.mpr ⟨i, hi, by simp⟩
    rw [hzero, zero_smul]
  have hoddG : IsOddAngularDerivativeTower selected G :=
    isOddAngularDerivativeTower_of_base_vanish G selected hderivG hbaseG
  have hVcont : Continuous V := by
    apply continuous_finiteEuclideanVector
    intro nu
    apply Continuous.mul
    · exact (MvPolynomial.continuous_eval _).comp
        (continuous_pi (fun i ↦ Real.continuous_cos.comp (continuous_apply i)))
    · apply continuous_finset_prod
      intro i _hi
      exact Real.continuous_sin.comp (continuous_apply i)
  have htranslateCont : Continuous (translateAngles base) := by
    apply continuous_pi
    intro i
    exact (continuous_apply i).add continuous_const
  have hWcont : Continuous W := by
    exact (hVcont.comp htranslateCont).const_smul sign
  have hdeltaRange : ∀ i ∈ selected, |delta i| ≤ Real.pi / 2 := by
    intro i _hi
    exact centeredArccosAngle_range ((Hypercube_mem_iff x).mp hx i)
  have hsquare :
      ‖W delta‖ ^ 2 ≤
        (Real.pi / 2) ^ (2 * (remaining.length + 2)) *
          (D ^ (2 * remaining.length) * H) := by
    exact oddSineRemoval_sq_le_of_twoRotationSeed G W a b remaining
      hD hH hderivG (by simpa [selected] using hoddG) hnodup hseedG
      hstepG hWcont (by simpa [selected] using hfactorG) delta hdeltaRange
  have htranslateDelta : translateAngles base delta = theta := by
    funext i
    exact centeredArccosAngle_add_base (x i)
  have hsignAbs : |sign| = 1 := by
    exact abs_centeredArccosSignProd x selected
  have hnormW : ‖W delta‖ ^ 2 = ‖V theta‖ ^ 2 := by
    rw [show W delta = sign • V (translateAngles base delta) by rfl,
      htranslateDelta, norm_smul, Real.norm_eq_abs, hsignAbs, one_mul]
  have hcosTheta : (fun i ↦ Real.cos (theta i)) = x := by
    funext i
    exact Real.cos_arccos (((Hypercube_mem_iff x).mp hx i).1)
      (((Hypercube_mem_iff x).mp hx i).2)
  calc
    MvPolynomial.eval x
        (BoxSemialgebraicGeneratorProd (I \ J) *
          ∑ nu, (circleParityComponent (P nu) I) ^ 2) =
        ‖V theta‖ ^ 2 := by
      rw [← hcosTheta]
      exact (parityResidualVector_norm_sq_eq_weightedParity
        P I J theta).symm
    _ = ‖W delta‖ ^ 2 := hnormW.symm
    _ ≤ _ := hsquare

end QuarticConvergence
end OptimalConvergenceRates

end
