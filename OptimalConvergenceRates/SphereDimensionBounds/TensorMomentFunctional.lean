import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.QuarticTensorAmplification

/-! Actual polynomial functionals from symmetric positive fourth moments. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.TensorMomentFunctional

open scoped BigOperators Matrix
open MvPolynomial QuarticTensorAmplification

variable {ι : Type*}

attribute [local instance] Classical.propDecidable

def tupleExponent {d : ℕ} (v : Fin d → ι) : ι →₀ ℕ :=
  ∑ s, Finsupp.single (v s) 1

theorem tupleExponent_degree {d : ℕ} (v : Fin d → ι) :
    (tupleExponent v).sum (fun _ n => n) = d := by
  classical
  change (tupleExponent v).sum (fun _ => id) = d
  rw [← Finsupp.card_toMultiset]
  simp [tupleExponent, Finsupp.toMultiset_sum, Finsupp.toMultiset_single,
    Multiset.card_sum]

theorem tupleExponent_fiber_card {d : ℕ} (v : Fin d → ι) (a : ι) :
    tupleExponent v a = Fintype.card {s : Fin d // v s = a} := by
  classical
  simp only [tupleExponent, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
    Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Ordered lists of variables with the same exponent differ by a slot permutation. -/
theorem exists_perm_of_tupleExponent_eq {d : ℕ} (v w : Fin d → ι)
    (h : tupleExponent v = tupleExponent w) :
    ∃ σ : Equiv.Perm (Fin d), ∀ s, w (σ s) = v s := by
  classical
  have hc (a : ι) : Fintype.card {s : Fin d // v s = a} =
      Fintype.card {s : Fin d // w s = a} := by
    rw [← tupleExponent_fiber_card v a, ← tupleExponent_fiber_card w a, h]
  let e (a : ι) : {s : Fin d // v s = a} ≃ {s : Fin d // w s = a} :=
    Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- Every monomial exponent of degree `d` has an ordered `d`-tuple of variables. -/
theorem exists_tupleExponent (d : ℕ) (e : ι →₀ ℕ)
    (he : e.sum (fun _ n => n) = d) :
    ∃ v : Fin d → ι, tupleExponent v = e := by
  classical
  have hall (s : Multiset ι) :
      ∃ v : Fin s.card → ι, tupleExponent v = s.toFinsupp := by
    induction s using Multiset.induction_on with
    | empty =>
        refine ⟨Fin.elim0, ?_⟩
        simp [tupleExponent]
    | @cons a s ih =>
        obtain ⟨v, hv⟩ := ih
        have hcons : tupleExponent (Fin.cons a v) = (a ::ₘ s).toFinsupp := by
          rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
          simp only [tupleExponent, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
          exact congrArg (fun z => Finsupp.single a 1 + z) hv
        rw [Multiset.card_cons]
        exact ⟨Fin.cons a v, hcons⟩
  have hh := hall e.toMultiset
  have hc : Multiset.card e.toMultiset = d := by
    exact (Finsupp.card_toMultiset e).trans he
  rw [hc, Finsupp.toMultiset_toFinsupp] at hh
  exact hh

theorem moment_eq_of_tupleExponent_eq (M : FourthMoment ι)
    (hM : FullSymmetricMoment M) (v w : Fin 4 → ι)
    (h : tupleExponent v = tupleExponent w) :
    M (v 0) (v 1) (v 2) (v 3) = M (w 0) (w 1) (w 2) (w 3) := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_tupleExponent_eq v w h
  have hh := hM σ w
  rw [hσ 0, hσ 1, hσ 2, hσ 3] at hh
  exact hh.symm

def momentWeight (M : FourthMoment ι) (e : ι →₀ ℕ) : ℝ :=
  if h : ∃ v : Fin 4 → ι, tupleExponent v = e then
    M (Classical.choose h 0) (Classical.choose h 1)
      (Classical.choose h 2) (Classical.choose h 3)
  else 0

theorem momentWeight_tuple (M : FourthMoment ι) (hM : FullSymmetricMoment M)
    (v : Fin 4 → ι) :
    momentWeight M (tupleExponent v) = M (v 0) (v 1) (v 2) (v 3) := by
  classical
  have h : ∃ w : Fin 4 → ι, tupleExponent w = tupleExponent v := ⟨v, rfl⟩
  rw [momentWeight, dite_eq_left h]
  exact moment_eq_of_tupleExponent_eq M hM (Classical.choose h) v
    (Classical.choose_spec h)

theorem momentWeight_eq_zero (M : FourthMoment ι) (e : ι →₀ ℕ)
    (he : e.sum (fun _ n => n) ≠ 4) : momentWeight M e = 0 := by
  classical
  have hn : ¬ ∃ v : Fin 4 → ι, tupleExponent v = e := by
    rintro ⟨v, rfl⟩
    exact he (tupleExponent_degree v)
  simp [momentWeight, hn]

/-- A genuine real linear functional on the full multivariate polynomial ring. -/
def momentFunctional (M : FourthMoment ι) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ (momentWeight M)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

theorem momentFunctional_monomial (M : FourthMoment ι) (e : ι →₀ ℕ) (a : ℝ) :
    momentFunctional M (monomial e a) = a * momentWeight M e := by
  change (Finsupp.linearCombination ℝ (momentWeight M)) (Finsupp.single e a) = _
  rw [Finsupp.linearCombination_single]
  rfl

theorem prod_X_tupleExponent {d : ℕ} (v : Fin d → ι) :
    (∏ s, (X (v s) : MvPolynomial ι ℝ)) = monomial (tupleExponent v) 1 := by
  classical
  induction d with
  | zero => simp [tupleExponent]
  | succ d ih =>
      simp only [Fin.prod_univ_succ, tupleExponent, Fin.sum_univ_succ]
      rw [ih (fun s => v s.succ)]
      simp only [X, monomial_mul, mul_one]
      rfl

/-- The constructed functional realizes every prescribed fourth monomial. -/
theorem momentFunctional_prod_X (M : FourthMoment ι) (hM : FullSymmetricMoment M)
    (v : Fin 4 → ι) :
    momentFunctional M (∏ s, X (v s)) = M (v 0) (v 1) (v 2) (v 3) := by
  rw [prod_X_tupleExponent, momentFunctional_monomial, one_mul, momentWeight_tuple M hM]

theorem momentFunctional_X4 (M : FourthMoment ι) (hM : FullSymmetricMoment M)
    (i j k l : ι) :
    momentFunctional M (X i * X j * X k * X l) = M i j k l := by
  simpa [Fin.prod_univ_four] using momentFunctional_prod_X M hM ![i, j, k, l]

theorem momentFunctional_homogeneous_zero (M : FourthMoment ι) {d : ℕ}
    (hd : d ≠ 4) (p : MvPolynomial ι ℝ) (hp : p.IsHomogeneous d) :
    momentFunctional M p = 0 := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply Finset.sum_eq_zero
  intro e he
  rw [momentFunctional_monomial]
  have hdeg : e.sum (fun _ n => n) = d := by
    simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using
      hp (mem_support_iff.mp he)
  rw [momentWeight_eq_zero M e (fun h4 => hd (hdeg.symm.trans h4)), mul_zero]

variable [Fintype ι]

/-- An arbitrary ordered quadratic coefficient array as an actual polynomial. -/
def quadraticPolynomial : ((ι × ι) → ℝ) →ₗ[ℝ] MvPolynomial ι ℝ :=
  ∑ ij, (LinearMap.proj ij).smulRight (X ij.1 * X ij.2)

theorem quadraticPolynomial_apply (Q : (ι × ι) → ℝ) :
    quadraticPolynomial Q = ∑ ij, C (Q ij) * X ij.1 * X ij.2 := by
  simp only [quadraticPolynomial, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, smul_eq_C_mul, mul_assoc]

theorem quadraticPolynomial_single (i j : ι) (a : ℝ) :
    quadraticPolynomial (Pi.single (i, j) a) = C a * X i * X j := by
  classical
  simp [quadraticPolynomial_apply, Pi.single_apply, apply_ite, ite_mul]

/-- Every homogeneous quadratic has an actual finite ordered coefficient array. -/
theorem exists_quadraticPolynomial (p : MvPolynomial ι ℝ) (hp : p.IsHomogeneous 2) :
    ∃ Q : (ι × ι) → ℝ, quadraticPolynomial Q = p := by
  classical
  have hmem : p ∈ LinearMap.range (quadraticPolynomial (ι := ι)) := by
    rw [← p.support_sum_monomial_coeff]
    apply Submodule.sum_mem
    intro e he
    have hd : e.sum (fun _ n => n) = 2 := by
      simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using
        hp (mem_support_iff.mp he)
    obtain ⟨v, hv⟩ := exists_tupleExponent 2 e hd
    refine ⟨Pi.single (v 0, v 1) (p.coeff e), ?_⟩
    rw [quadraticPolynomial_single, ← hv]
    calc
      _ = C (p.coeff (tupleExponent v)) * ∏ s, (X (v s) : MvPolynomial ι ℝ) := by
        simp [Fin.prod_univ_two, mul_assoc]
      _ = _ := by rw [prod_X_tupleExponent, C_mul_monomial, mul_one]
  exact hmem

/-- The actual quartic square has exactly the prescribed quadratic Gram value. -/
theorem momentFunctional_quadraticPolynomial_square (M : FourthMoment ι)
    (hM : FullSymmetricMoment M) (Q : (ι × ι) → ℝ) :
    momentFunctional M ((quadraticPolynomial Q)^2) =
      dotProduct Q (momentGram M *ᵥ Q) := by
  classical
  rw [quadraticPolynomial_apply, pow_two, Fintype.sum_mul_sum, map_sum]
  simp only [map_sum, dotProduct, Matrix.mulVec, Finset.mul_sum, momentGram]
  apply Finset.sum_congr rfl
  intro ij _
  apply Finset.sum_congr rfl
  intro kl _
  have hpoly :
      (C (Q ij) * X ij.1 * X ij.2) * (C (Q kl) * X kl.1 * X kl.2) =
        C (Q ij * Q kl) * (X ij.1 * X ij.2 * X kl.1 * X kl.2) := by
    rw [map_mul]
    ring
  rw [hpoly, ← smul_eq_C_mul, map_smul, smul_eq_mul, momentFunctional_X4 M hM]
  ring

theorem momentFunctional_homogeneous_square_nonneg (M : FourthMoment ι)
    (hM : FullSymmetricMoment M) (hGram : (momentGram M).PosSemidef)
    (q : MvPolynomial ι ℝ) (hq : q.IsHomogeneous 2) :
    0 ≤ momentFunctional M (q^2) := by
  obtain ⟨Q, rfl⟩ := exists_quadraticPolynomial q hq
  rw [momentFunctional_quadraticPolynomial_square M hM]
  simpa only [star_trivial] using hGram.dotProduct_mulVec_nonneg Q

omit [Fintype ι] in
theorem linearMap_C_mul (E : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (a : ℝ)
    (p : MvPolynomial ι ℝ) : E (C a * p) = a * E p := by
  rw [← smul_eq_C_mul, map_smul]
  rfl

omit [Fintype ι] in
theorem decomposition_two (q : MvPolynomial ι ℝ) (hq : q.totalDegree ≤ 2) :
    q = homogeneousComponent 0 q + homogeneousComponent 1 q + homogeneousComponent 2 q := by
  have hs := sum_homogeneousComponent q
  have hd : q.totalDegree = 0 ∨ q.totalDegree = 1 ∨ q.totalDegree = 2 := by omega
  rcases hd with hd | hd | hd
  · have h1 := homogeneousComponent_eq_zero (φ := q) (n := 1) (by omega)
    have h2 := homogeneousComponent_eq_zero (φ := q) (n := 2) (by omega)
    simpa [hd, Finset.sum_range_succ, h1, h2] using hs.symm
  · have h2 := homogeneousComponent_eq_zero (φ := q) (n := 2) (by omega)
    simpa [hd, Finset.sum_range_succ, h2] using hs.symm
  · simpa [hd, Finset.sum_range_succ, add_assoc] using hs.symm

/-- Positivity holds for every root of total degree at most two, including
arbitrary constant and linear terms. -/
theorem momentFunctional_square_nonneg (M : FourthMoment ι)
    (hM : FullSymmetricMoment M) (hGram : (momentGram M).PosSemidef)
    (q : MvPolynomial ι ℝ) (hq : q.totalDegree ≤ 2) :
    0 ≤ momentFunctional M (q^2) := by
  let a := homogeneousComponent 0 q
  let b := homogeneousComponent 1 q
  let c := homogeneousComponent 2 q
  have ha : a.IsHomogeneous 0 := homogeneousComponent_isHomogeneous _ _
  have hb : b.IsHomogeneous 1 := homogeneousComponent_isHomogeneous _ _
  have hc : c.IsHomogeneous 2 := homogeneousComponent_isHomogeneous _ _
  have hdec : q = a+b+c := decomposition_two q hq
  have hexp : q^2 = a^2+b^2+c^2+C 2*(a*b)+C 2*(a*c)+C 2*(b*c) := by
    rw [hdec, map_ofNat]
    ring
  have h0 : momentFunctional M (a^2) = 0 :=
    momentFunctional_homogeneous_zero M (by decide : 0 ≠ 4) _ (by simpa using ha.pow 2)
  have h2 : momentFunctional M (b^2) = 0 :=
    momentFunctional_homogeneous_zero M (by decide : 2 ≠ 4) _ (by simpa using hb.pow 2)
  have hab : momentFunctional M (a*b) = 0 :=
    momentFunctional_homogeneous_zero M (by decide : 1 ≠ 4) _ (by simpa using ha.mul hb)
  have hac : momentFunctional M (a*c) = 0 :=
    momentFunctional_homogeneous_zero M (by decide : 2 ≠ 4) _ (by simpa using ha.mul hc)
  have hbc : momentFunctional M (b*c) = 0 :=
    momentFunctional_homogeneous_zero M (by decide : 3 ≠ 4) _ (by simpa using hb.mul hc)
  rw [hexp]
  simp only [map_add, linearMap_C_mul, h0, h2, hab, hac, hbc, mul_zero, zero_add, add_zero]
  exact momentFunctional_homogeneous_square_nonneg M hM hGram c hc

/-- Radius-four normalization is the actual polynomial functional value. -/
theorem momentFunctional_radius (M : FourthMoment ι) (hM : FullSymmetricMoment M) :
    momentFunctional M ((∑ i, (X i : MvPolynomial ι ℝ)^2)^2) = momentRadius M := by
  classical
  have hid : ((∑ i, (X i : MvPolynomial ι ℝ)^2)^2) =
      ∑ i, ∑ j, X i * X i * X j * X j := by
    rw [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hid, map_sum]
  simp only [map_sum, momentFunctional_X4 M hM, momentRadius]

def linearPolynomial (a : ι → ℝ) : MvPolynomial ι ℝ := ∑ i, C (a i) * X i

/-- Evaluation of an actual linear fourth power realizes the finite row moment. -/
theorem momentFunctional_linearFourth (M : FourthMoment ι) (hM : FullSymmetricMoment M)
    (a : ι → ℝ) :
    momentFunctional M ((linearPolynomial a)^4) = rowFourthMoment M a := by
  classical
  have hid : (linearPolynomial a)^4 =
      ∑ v : Fin 4 → ι, C (∏ s, a (v s)) * ∏ s, X (v s) := by
    calc
      _ = ∏ _s : Fin 4, linearPolynomial a := by rw [Fin.prod_univ_four]; ring
      _ = ∑ v : Fin 4 → ι, ∏ s, C (a (v s)) * X (v s) :=
        Fintype.prod_sum (fun (_s : Fin 4) i => C (a i) * X i)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.prod_mul_distrib, map_prod]
  rw [hid, map_sum]
  unfold rowFourthMoment
  apply Finset.sum_congr rfl
  intro v _
  rw [linearMap_C_mul, momentFunctional_prod_X M hM]
  ring

/-- The matrix objective is an actual sum of linear fourth powers. -/
theorem momentFunctional_matrixFourth {α : Type*} [Fintype α]
    (M : FourthMoment ι) (hM : FullSymmetricMoment M) (A : α → ι → ℝ) :
    momentFunctional M (∑ j, (∑ i, C (A j i) * X i)^4) = matrixFourthMoment M A := by
  classical
  rw [map_sum]
  unfold matrixFourthMoment
  apply Finset.sum_congr rfl
  intro j _
  exact momentFunctional_linearFourth M hM (A j)

/-- Fourth moments of any actual real polynomial linear functional. -/
def ofLinearFunctional (E : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : FourthMoment ι :=
  fun i j k l => E (X i * X j * X k * X l)

omit [Fintype ι] in
theorem ofLinearFunctional_fullSymmetric (E : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) :
    FullSymmetricMoment (ofLinearFunctional E) := by
  classical
  intro σ v
  have h := congrArg E (Equiv.prod_comp σ (fun s => (X (v s) : MvPolynomial ι ℝ)))
  simpa only [Fin.prod_univ_four, ofLinearFunctional] using h.symm

omit [Fintype ι] in
theorem ofLinearFunctional_agrees (E : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (p : MvPolynomial ι ℝ) (hp : p.IsHomogeneous 4) :
    momentFunctional (ofLinearFunctional E) p = E p := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hd : e.sum (fun _ n => n) = 4 := by
    simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using
      hp (mem_support_iff.mp he)
  obtain ⟨v, hv⟩ := exists_tupleExponent 4 e hd
  have hmono : monomial e (p.coeff e) = C (p.coeff e) * ∏ s, X (v s) := by
    rw [prod_X_tupleExponent, hv, C_mul_monomial, mul_one]
  rw [hmono, linearMap_C_mul, linearMap_C_mul,
    momentFunctional_prod_X _ (ofLinearFunctional_fullSymmetric E)]
  simp only [ofLinearFunctional, Fin.prod_univ_four]

theorem quadraticPolynomial_homogeneous (Q : (ι × ι) → ℝ) :
    (quadraticPolynomial Q).IsHomogeneous 2 := by
  classical
  rw [quadraticPolynomial_apply]
  apply IsHomogeneous.sum
  intro ij _
  simpa using ((isHomogeneous_C ι (Q ij)).mul
    (isHomogeneous_X ℝ ij.1)).mul (isHomogeneous_X ℝ ij.2)

/-- Positivity of an actual functional implies positivity of its complete
ordered-pair quadratic moment Gram matrix. -/
theorem ofLinearFunctional_gram_posSemidef (E : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hE : ∀ q : MvPolynomial ι ℝ, q.totalDegree ≤ 2 → 0 ≤ E (q^2)) :
    (momentGram (ofLinearFunctional E)).PosSemidef := by
  classical
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext ij kl
    simp only [Matrix.conjTranspose_apply, momentGram, ofLinearFunctional, star_trivial]
    congr 1
    ring
  · intro Q
    have hq := quadraticPolynomial_homogeneous Q
    have hval := momentFunctional_quadraticPolynomial_square (ofLinearFunctional E)
      (ofLinearFunctional_fullSymmetric E) Q
    rw [ofLinearFunctional_agrees E _ (by simpa using hq.pow 2)] at hval
    have hpos := hE _ hq.totalDegree_le
    rw [hval] at hpos
    simpa only [star_trivial] using hpos

theorem ofLinearFunctional_radius (E : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) :
    momentRadius (ofLinearFunctional E) = E ((∑ i, (X i : MvPolynomial ι ℝ)^2)^2) := by
  classical
  have hR : (∑ i, (X i : MvPolynomial ι ℝ)^2).IsHomogeneous 2 := by
    apply IsHomogeneous.sum
    intro i _
    simpa using (isHomogeneous_X ℝ i).pow 2
  have h := momentFunctional_radius (ofLinearFunctional E) (ofLinearFunctional_fullSymmetric E)
  rw [ofLinearFunctional_agrees E _ (by simpa using hR.pow 2)] at h
  exact h.symm

theorem linearPolynomial_homogeneous (a : ι → ℝ) : (linearPolynomial a).IsHomogeneous 1 := by
  classical
  apply IsHomogeneous.sum
  intro i _
  simpa using (isHomogeneous_C ι (a i)).mul (isHomogeneous_X ℝ i)

theorem ofLinearFunctional_matrixFourth {α : Type*} [Fintype α]
    (E : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (A : α → ι → ℝ) :
    matrixFourthMoment (ofLinearFunctional E) A = E (∑ j, (∑ i, C (A j i) * X i)^4) := by
  classical
  have hhom : (∑ j, (linearPolynomial (A j))^4).IsHomogeneous 4 := by
    apply IsHomogeneous.sum
    intro j _
    simpa using (linearPolynomial_homogeneous (A j)).pow 4
  change (∑ j, (∑ i, C (A j i) * X i)^4).IsHomogeneous 4 at hhom
  have h := momentFunctional_matrixFourth (ofLinearFunctional E)
    (ofLinearFunctional_fullSymmetric E) A
  rw [ofLinearFunctional_agrees E _ hhom] at h
  exact h.symm

end OptimalConvergenceRates.SphereDimensionBounds.TensorMomentFunctional
