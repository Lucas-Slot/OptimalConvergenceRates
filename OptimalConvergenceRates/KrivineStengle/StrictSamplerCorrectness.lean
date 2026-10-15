/-
  OptimalConvergenceRates/KrivineStengle/StrictSamplerCorrectness.lean

  Completeness and exact semantics of the finite strict sampler.
-/
import OptimalConvergenceRates.KrivineStengle.StrictSamplerFormula
import OptimalConvergenceRates.KrivineStengle.StrictSignSampler

noncomputable section

open MvPolynomial Polynomial

namespace OptimalConvergenceRates.KrivineStengle

theorem specialize_polynomialListProduct
    {n : ℕ} {F : Type*} [CommRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (fs : List ((MvPolynomial (Fin n) ℝ)[X])) :
    specializePolynomial coeff x (polynomialListProduct fs) =
      (fs.map (specializePolynomial coeff x)).prod := by
  change fs.prod.map (eval₂Hom coeff x) =
    (fs.map (fun f => f.map (eval₂Hom coeff x))).prod
  exact Polynomial.map_list_prod (f := eval₂Hom coeff x) fs

theorem specialize_derivative_polynomialListProduct
    {n : ℕ} {F : Type*} [CommRing F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (fs : List ((MvPolynomial (Fin n) ℝ)[X])) :
    specializePolynomial coeff x (polynomialListProduct fs).derivative =
      (fs.map (specializePolynomial coeff x)).prod.derivative := by
  change fs.prod.derivative.map (eval₂Hom coeff x) =
    (fs.map (specializePolynomial coeff x)).prod.derivative
  rw [← Polynomial.derivative_map]
  exact congrArg Polynomial.derivative
    (specialize_polynomialListProduct coeff x fs)

/-- Completeness of the strict sampler formula. If a finite family has a
simultaneously positive point, either one tail is already positive or the
derivative of the product samples the bounded sign cell containing it. -/
theorem exists_imp_realizes_strictSamplerFormula
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (fs : List ((MvPolynomial (Fin n) ℝ)[X]))
    (hexists : ∃ y : F, ∀ f ∈ fs,
      0 < (specializePolynomial coeff x f).eval y) :
    (strictSamplerFormula fs).Realizes coeff x := by
  obtain ⟨y, hy⟩ := hexists
  rw [strictSamplerFormula, SignFormula.realizes_disj,
    SignFormula.realizes_disj]
  by_cases hposTail : ∃ B : F, ∀ z, B < z → ∀ f ∈ fs,
      0 < (specializePolynomial coeff x f).eval z
  · exact Or.inl
      ((realizes_allPositiveLeadingFormula_iff_exists_tail coeff x fs).2 hposTail)
  by_cases hnegTail : ∃ B : F, ∀ z, z < B → ∀ f ∈ fs,
      0 < (specializePolynomial coeff x f).eval z
  · exact Or.inr (Or.inl
      ((realizes_allNegativeTailFormula_iff coeff x fs).2 hnegTail))
  right
  right
  have hrightBad : ∃ z : F, y < z ∧ ∃ f ∈ fs,
      (specializePolynomial coeff x f).eval z ≤ 0 := by
    have hfail := not_exists.mp hposTail y
    push Not at hfail
    exact hfail
  have hleftBad : ∃ z : F, z < y ∧ ∃ f ∈ fs,
      (specializePolynomial coeff x f).eval z ≤ 0 := by
    have hfail := not_exists.mp hnegTail y
    push Not at hfail
    exact hfail
  let specialized : List F[X] := fs.map (specializePolynomial coeff x)
  have hspecialized : ∀ p ∈ specialized, 0 < p.eval y := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
    exact hy f hf
  have hleftRoot : ∃ a, a < y ∧ specialized.prod.IsRoot a := by
    obtain ⟨z, hzy, f, hf, hfz⟩ := hleftBad
    let p := specializePolynomial coeff x f
    obtain ⟨a, ha, haRoot⟩ :=
      exists_isRoot_mem_Icc_of_eval_mul_nonpos hzy.le
        (mul_nonpos_of_nonpos_of_nonneg hfz (hy f hf).le)
    have hay : a < y := ha.2.lt_of_ne fun hayEq ↦
      (hy f hf).ne' (by simpa [p, hayEq] using haRoot.eq_zero)
    refine ⟨a, hay, ?_⟩
    exact haRoot.dvd (by
      apply List.dvd_prod
      exact List.mem_map.mpr ⟨f, hf, rfl⟩)
  have hrightRoot : ∃ b, y < b ∧ specialized.prod.IsRoot b := by
    obtain ⟨z, hyz, f, hf, hfz⟩ := hrightBad
    let p := specializePolynomial coeff x f
    obtain ⟨b, hb, hbRoot⟩ :=
      exists_isRoot_mem_Icc_of_eval_mul_nonpos hyz.le
        (mul_nonpos_of_nonneg_of_nonpos (hy f hf).le hfz)
    have hyb : y < b := hb.1.lt_of_ne fun hybEq ↦
      (hy f hf).ne' (by simpa [p, hybEq] using hbRoot.eq_zero)
    refine ⟨b, hyb, ?_⟩
    exact hbRoot.dvd (by
      apply List.dvd_prod
      exact List.mem_map.mpr ⟨f, hf, rfl⟩)
  obtain ⟨z, hzRoot, hzPos⟩ :=
    exists_derivative_isRoot_with_all_pos_of_roots_on_both_sides
      specialized y hspecialized hleftRoot hrightRoot
  apply (realizes_branchedRootExistenceFormula_iff coeff x
    (polynomialListProduct fs).derivative (listFamily fs)).2
  have hderivative0 : specialized.prod.derivative ≠ 0 := by
    intro hzero
    obtain ⟨a, _, haRoot⟩ := hleftRoot
    have hconstant := eq_C_of_derivative_eq_zero hzero
    have hcoeffZero : specialized.prod.coeff 0 = 0 := by
      have haZero := haRoot.eq_zero
      rw [hconstant, Polynomial.eval_C] at haZero
      exact haZero
    have hprodZero : specialized.prod = 0 := by
      rw [hconstant, hcoeffZero, Polynomial.C_0]
    have hpositive : 0 < specialized.prod.eval y := by
      rw [eval_list_prod]
      apply List.prod_pos
      intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      exact hspecialized p hp
    simp [hprodZero] at hpositive
  refine ⟨z, ?_, ?_⟩
  · rw [specialize_derivative_polynomialListProduct]
    exact Multiset.mem_toFinset.mpr ((mem_roots hderivative0).2 hzRoot)
  · exact (forall_listFamily_iff fs
      (fun f ↦ 0 < (specializePolynomial coeff x f).eval z)).2 (by
        intro f hf
        exact hzPos _ (List.mem_map.mpr ⟨f, hf, rfl⟩))

/-- Exact semantics of the finite strict-sign sampler. -/
theorem realizes_strictSamplerFormula_iff_exists
    {n : ℕ} {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] [IsRealClosed F]
    (coeff : ℝ →+* F) (x : Fin n → F)
    (fs : List ((MvPolynomial (Fin n) ℝ)[X])) :
    (strictSamplerFormula fs).Realizes coeff x ↔
      ∃ y : F, ∀ f ∈ fs,
        0 < (specializePolynomial coeff x f).eval y :=
  ⟨realizes_strictSamplerFormula_imp_exists coeff x fs,
    exists_imp_realizes_strictSamplerFormula coeff x fs⟩

end OptimalConvergenceRates.KrivineStengle

end
