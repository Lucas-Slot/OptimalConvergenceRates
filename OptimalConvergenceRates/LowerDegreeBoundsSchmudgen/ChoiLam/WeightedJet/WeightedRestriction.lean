/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/WeightedJet/WeightedRestriction.lean

  Weighted-degree encoding and univariate restrictions for four-variable jets.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.WeightedJet.DirectionalDerivatives

open MvPolynomial Finset
open scoped Pointwise

noncomputable section

namespace OptimalConvergenceRates

def weight4 (i : Fin 4) : ℕ :=
  match i with
  | 0 => 1
  | 1 => 5
  | 2 => 25
  | 3 => 125

def weightedDegree4 (α : Fin 4 →₀ ℕ) : ℕ :=
  α.sum fun i e => e * weight4 i

noncomputable def weightedRestriction4 (p : MvPolynomial (Fin 4) ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval (R := ℝ) (fun i => (Polynomial.X : Polynomial ℝ) ^ weight4 i) p

lemma weightedDegree4_apply (α : Fin 4 →₀ ℕ) :
    weightedDegree4 α = α 0 + 5 * α 1 + 25 * α 2 + 125 * α 3 := by
  unfold weightedDegree4
  rw [Finsupp.sum_fintype]
  · simp [weight4, Fin.sum_univ_four]
    ring
  · intro i
    simp

lemma weightedDegree4_nat_injective
    {a0 a1 a2 a3 b0 b1 b2 b3 : ℕ}
    (ha : a0 + a1 + a2 + a3 ≤ 4) (hb : b0 + b1 + b2 + b3 ≤ 4)
    (h : a0 + 5 * a1 + 25 * a2 + 125 * a3 =
      b0 + 5 * b1 + 25 * b2 + 125 * b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have hmod := congrArg (fun n : ℕ => n % 5) h
  have hmoda : (a0 + 5 * a1 + 25 * a2 + 125 * a3) % 5 = a0 := by omega
  have hmodb : (b0 + 5 * b1 + 25 * b2 + 125 * b3) % 5 = b0 := by omega
  change (a0 + 5 * a1 + 25 * a2 + 125 * a3) % 5 =
      (b0 + 5 * b1 + 25 * b2 + 125 * b3) % 5 at hmod
  rw [hmoda, hmodb] at hmod
  have hdiv := congrArg (fun n : ℕ => n / 5) h
  have hdiva : (a0 + 5 * a1 + 25 * a2 + 125 * a3) / 5 =
      a1 + 5 * a2 + 25 * a3 := by
    omega
  have hdivb : (b0 + 5 * b1 + 25 * b2 + 125 * b3) / 5 =
      b1 + 5 * b2 + 25 * b3 := by
    omega
  change (a0 + 5 * a1 + 25 * a2 + 125 * a3) / 5 =
      (b0 + 5 * b1 + 25 * b2 + 125 * b3) / 5 at hdiv
  rw [hdiva, hdivb] at hdiv
  have hmod1 := congrArg (fun n : ℕ => n % 5) hdiv
  have hmod1a : (a1 + 5 * a2 + 25 * a3) % 5 = a1 := by omega
  have hmod1b : (b1 + 5 * b2 + 25 * b3) % 5 = b1 := by omega
  change (a1 + 5 * a2 + 25 * a3) % 5 = (b1 + 5 * b2 + 25 * b3) % 5 at hmod1
  rw [hmod1a, hmod1b] at hmod1
  have hdiv1 := congrArg (fun n : ℕ => n / 5) hdiv
  have hdiv1a : (a1 + 5 * a2 + 25 * a3) / 5 = a2 + 5 * a3 := by omega
  have hdiv1b : (b1 + 5 * b2 + 25 * b3) / 5 = b2 + 5 * b3 := by omega
  change (a1 + 5 * a2 + 25 * a3) / 5 = (b1 + 5 * b2 + 25 * b3) / 5 at hdiv1
  rw [hdiv1a, hdiv1b] at hdiv1
  have hmod2 := congrArg (fun n : ℕ => n % 5) hdiv1
  have hmod2a : (a2 + 5 * a3) % 5 = a2 := by omega
  have hmod2b : (b2 + 5 * b3) % 5 = b2 := by omega
  change (a2 + 5 * a3) % 5 = (b2 + 5 * b3) % 5 at hmod2
  rw [hmod2a, hmod2b] at hmod2
  omega

lemma weightedDegree4_injective_of_sum_le_four
    {α β : Fin 4 →₀ ℕ} (hα : α.sum (fun _ e => e) ≤ 4)
    (hβ : β.sum (fun _ e => e) ≤ 4) (hw : weightedDegree4 α = weightedDegree4 β) :
    α = β := by
  rw [weightedDegree4_apply α, weightedDegree4_apply β] at hw
  have hαsum : α 0 + α 1 + α 2 + α 3 ≤ 4 := by
    rw [Finsupp.sum_fintype] at hα
    · simpa [Fin.sum_univ_four] using hα
    · intro i
      rfl
  have hβsum : β 0 + β 1 + β 2 + β 3 ≤ 4 := by
    rw [Finsupp.sum_fintype] at hβ
    · simpa [Fin.sum_univ_four] using hβ
    · intro i
      rfl
  rcases weightedDegree4_nat_injective hαsum hβsum hw with ⟨h0, h1, h2, h3⟩
  ext i
  fin_cases i <;> assumption

lemma weightedAeval_monomial (α : Fin 4 →₀ ℕ) (c : ℝ) :
    MvPolynomial.aeval (R := ℝ) (fun i => (Polynomial.X : Polynomial ℝ) ^ weight4 i)
        (MvPolynomial.monomial α c) = Polynomial.C c * Polynomial.X ^ weightedDegree4 α := by
  unfold weightedDegree4
  rw [MvPolynomial.aeval_monomial]
  simp only [Polynomial.algebraMap_eq]
  congr 1
  rw [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [← pow_mul]
  ring_nf

lemma coeff_weightedRestriction4_eq_coeff
    {m : ℕ} (hm : m ≤ 4) {p : MvPolynomial (Fin 4) ℝ}
    (hp : homogeneousPart4 m p = p) (α : Fin 4 →₀ ℕ)
    (hα : α.sum (fun _ e => e) = m) :
    (weightedRestriction4 p).coeff (weightedDegree4 α) = legacyMvCoeff α p := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  unfold weightedRestriction4
  rw [map_sum]
  change (Polynomial.lcoeff ℝ (weightedDegree4 α))
      (∑ x ∈ p.support,
        MvPolynomial.aeval (R := ℝ) (fun i => (Polynomial.X : Polynomial ℝ) ^ weight4 i)
          (MvPolynomial.monomial x (legacyMvCoeff x p))) = legacyMvCoeff α p
  rw [map_sum]
  change (∑ x ∈ p.support,
      (MvPolynomial.aeval (R := ℝ) (fun i => (Polynomial.X : Polynomial ℝ) ^ weight4 i)
        (MvPolynomial.monomial x (legacyMvCoeff x p))).coeff (weightedDegree4 α)) =
        legacyMvCoeff α p
  rw [Finset.sum_eq_single α]
  · rw [weightedAeval_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [ite_eq_left rfl]
    ring
  · intro β hβ hβα
    have hhom := isHomogeneous_of_homogeneousPart4_eq hp
    have hweight := hhom (MvPolynomial.mem_support_iff.mp hβ)
    have hβsum : β.sum (fun _ e => e) = m := by
      have hdeg : Finsupp.degree β = m := by
        rw [Finsupp.degree_eq_weight_one]
        exact hweight
      rw [finsupp_sum_fintype4_linear]
      simpa only [Finsupp.degree_eq_sum] using hdeg
    have hne : weightedDegree4 α ≠ weightedDegree4 β := by
      intro hw
      have hαle : α.sum (fun _ e => e) ≤ 4 := by omega
      have hβle : β.sum (fun _ e => e) ≤ 4 := by omega
      exact hβα ((weightedDegree4_injective_of_sum_le_four
        (α := α) (β := β) hαle hβle hw).symm)
    rw [weightedAeval_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [ite_eq_right hne]
    ring
  · intro hnot
    have hcoeff : legacyMvCoeff α p = 0 := MvPolynomial.notMem_support_iff.mp hnot
    simp [hcoeff]



lemma weightedRestriction4_eval (p : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    (weightedRestriction4 p).eval t = MvPolynomial.eval (fun i => t ^ weight4 i) p := by
  unfold weightedRestriction4
  rw [← Polynomial.coe_aeval_eq_eval]
  rw [show (Polynomial.aeval t : Polynomial ℝ → ℝ)
      (MvPolynomial.aeval (R := ℝ)
        (fun i => (Polynomial.X : Polynomial ℝ) ^ weight4 i) p) =
      ((Polynomial.aeval t).comp
        (MvPolynomial.aeval (R := ℝ)
          (fun i => (Polynomial.X : Polynomial ℝ) ^ weight4 i))) p from rfl]
  rw [MvPolynomial.comp_aeval]
  simp [MvPolynomial.aeval_eq_eval]

lemma weightedDegree4_le_500_of_sum_le_four {α : Fin 4 →₀ ℕ}
    (hα : α.sum (fun _ e => e) ≤ 4) : weightedDegree4 α ≤ 500 := by
  unfold weightedDegree4
  rw [Finsupp.sum_fintype]
  · have hsum : α 0 + α 1 + α 2 + α 3 ≤ 4 := by
      rw [Finsupp.sum_fintype] at hα
      · simpa [Fin.sum_univ_four] using hα
      · intro i
        rfl
    simp [weight4, Fin.sum_univ_four]
    omega
  · intro i
    simp

lemma weightedRestriction4_natDegree_le_500 {p : MvPolynomial (Fin 4) ℝ}
    (hp : p.totalDegree ≤ 4) : (weightedRestriction4 p).natDegree ≤ 500 := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  unfold weightedRestriction4
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro α hα
  rw [weightedAeval_monomial]
  calc
    (Polynomial.C (legacyMvCoeff α p) * Polynomial.X ^ weightedDegree4 α).natDegree ≤
        (Polynomial.X ^ weightedDegree4 α).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ weightedDegree4 α := by simp
    _ ≤ 500 := by
      apply weightedDegree4_le_500_of_sum_le_four
      have hdeg := MvPolynomial.le_totalDegree hα
      exact hdeg.trans hp


lemma interiorVecNorm_eval_homogeneous_le_of_localSqNorm_le_four
    {N m : ℕ} {C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    (H : Fin N → MvPolynomial (Fin 4) ℝ)
    (hhom : ∀ i, homogeneousPart4 m (H i) = H i)
    (hunit : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) ≤ C)
    (x : Fin 4 → ℝ) (hxle : localSqNorm x ≤ 4) :
    interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (H i)) ≤ 2 ^ m * C := by
  by_cases hxzero : localSqNorm x = 0
  · have hxnorm : interiorVecNorm x ≤ 0 := by
      unfold interiorVecNorm interiorVecSqNorm
      rw [show (∑ i : Fin 4, x i ^ 2) = localSqNorm x by rfl]
      rw [hxzero]
      simp
    have hxcomp : x = 0 := by
      funext j
      exact component_eq_zero_of_interiorVecNorm_le_zero hxnorm j
    subst x
    have heval0 : (fun i : Fin N => MvPolynomial.eval (0 : Fin 4 → ℝ) (H i)) = 0 := by
      funext i
      have hscale := isHomogeneous_eval_smul
        (isHomogeneous_of_homogeneousPart4_eq (hhom i)) 0 (fun _ : Fin 4 => (1 : ℝ))
      simpa [hm.ne'] using hscale
    rw [heval0]
    simpa [interiorVecNorm, interiorVecSqNorm] using
      mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ m) hC
  · have hxpos : 0 < localSqNorm x := lt_of_le_of_ne (localSqNorm_nonneg x) (Ne.symm hxzero)
    let c : ℝ := Real.sqrt (localSqNorm x)
    let v : Fin 4 → ℝ := fun i => c⁻¹ * x i
    have hv : localSqNorm v = 1 := by
      dsimp [v, c]
      exact localSqNorm_normalize_eq_one hxpos
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      exact Real.sqrt_nonneg _
    have hc_le_two : c ≤ 2 := by
      dsimp [c]
      have hsqrt4 : Real.sqrt (localSqNorm x) ≤ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt hxle
      have hs4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        rw [Real.sqrt_sq_eq_abs]
        norm_num
      simpa [hs4] using hsqrt4
    have hscale_fun : (fun i : Fin N => MvPolynomial.eval v (H i)) =
        fun i : Fin N => c⁻¹ ^ m * MvPolynomial.eval x (H i) := by
      funext i
      dsimp [v]
      exact isHomogeneous_eval_smul (isHomogeneous_of_homogeneousPart4_eq (hhom i)) c⁻¹ x
    have hscale_norm : interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) =
        c⁻¹ ^ m * interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (H i)) := by
      rw [hscale_fun]
      exact vecNorm_smul_nonneg (N := N) (c := c⁻¹ ^ m)
        (pow_nonneg (inv_nonneg.mpr hc_nonneg) m)
        (fun i : Fin N => MvPolynomial.eval x (H i))
    have hunitv := hunit v hv
    have hcpos : 0 < c := by
      dsimp [c]
      exact Real.sqrt_pos.mpr hxpos
    have hmul : c⁻¹ ^ m * interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (H i)) ≤ C := by
      simpa [hscale_norm] using hunitv
    have hmain : interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (H i)) ≤ c ^ m * C := by
      have hcpow : 0 < c ^ m := pow_pos hcpos m
      have hcpow_inv : (c⁻¹ ^ m) = (c ^ m)⁻¹ := by rw [inv_pow]
      rw [hcpow_inv] at hmul
      exact (inv_mul_le_iff₀ hcpow).mp hmul
    have hc_pow_le : c ^ m ≤ 2 ^ m := pow_le_pow_left₀ hc_nonneg hc_le_two m
    calc
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (H i)) ≤ c ^ m * C := hmain
      _ ≤ 2 ^ m * C := mul_le_mul_of_nonneg_right hc_pow_le hC

lemma localSqNorm_weightedPath_le_four {t : ℝ} (ht : |t| ≤ 1) :
    localSqNorm (fun i : Fin 4 => t ^ weight4 i) ≤ 4 := by
  unfold localSqNorm
  rw [Fin.sum_univ_four]
  have hsq : ∀ n : ℕ, (t ^ n) ^ 2 ≤ 1 := by
    intro n
    have habs : |t ^ n| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg t) ht
    have hs : |t ^ n| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    simpa [sq_abs] using hs
  have h0 := hsq (weight4 0)
  have h1 := hsq (weight4 1)
  have h2 := hsq (weight4 2)
  have h3 := hsq (weight4 3)
  nlinarith

lemma finset_sum_image_le_sum_of_nonneg_weighted {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (g : β → ℝ) (hg : ∀ x ∈ s, 0 ≤ g (f x)) :
    ∑ y ∈ s.image f, g y ≤ ∑ x ∈ s, g (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ih' : ∑ y ∈ s.image f, g y ≤ ∑ x ∈ s, g (f x) := by
        exact ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
      by_cases hfa : f a ∈ s.image f
      · have himage : (insert a s).image f = s.image f := by
          ext y
          constructor
          · intro hy
            rw [Finset.mem_image] at hy ⊢
            rcases hy with ⟨x, hx, rfl⟩
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · exact Finset.mem_image.mp hfa
            · exact ⟨x, hx, rfl⟩
          · intro hy
            rw [Finset.mem_image] at hy ⊢
            rcases hy with ⟨x, hx, rfl⟩
            exact ⟨x, Finset.mem_insert_of_mem hx, rfl⟩
        rw [himage, Finset.sum_insert ha]
        exact le_trans ih' (le_add_of_nonneg_left (hg a (Finset.mem_insert_self a s)))
      · rw [Finset.image_insert, Finset.sum_insert hfa, Finset.sum_insert ha]
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left ih' (g (f a))

lemma finsupp_degree_three_as_sum_single {a : Fin 4 →₀ ℕ} (ha : a.degree = 3) :
    ∃ i j k : Fin 4,
      a = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 := by
  classical
  have hmem : a ∈ (3 : ℕ) • ((fun i : Fin 4 => Finsupp.single i 1) '' Set.univ) := by
    rw [Finsupp.nsmul_single_one_image]
    exact ⟨ha, by simp⟩
  rw [three_nsmul] at hmem
  rcases hmem with ⟨x, hx, y, hy, hxy⟩
  rcases hx with ⟨i, -, rfl⟩
  rcases hy with ⟨u, hu, v, hv, huv⟩
  rcases hu with ⟨j, -, rfl⟩
  rcases hv with ⟨k, -, rfl⟩
  refine ⟨i, j, k, ?_⟩
  simp [huv, hxy, add_assoc]

lemma finsupp_degree_four_as_sum_single {a : Fin 4 →₀ ℕ} (ha : a.degree = 4) :
    ∃ i j k l : Fin 4,
      a = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 +
        Finsupp.single l 1 := by
  classical
  let S : Set (Fin 4 →₀ ℕ) := (fun i : Fin 4 => Finsupp.single i 1) '' Set.univ
  have hmem : a ∈ (4 : ℕ) • S := by
    dsimp [S]
    rw [Finsupp.nsmul_single_one_image]
    exact ⟨ha, by simp⟩
  have hfour : (4 : ℕ) • S = S + (3 : ℕ) • S := by
    calc
      (4 : ℕ) • S = (1 + 3 : ℕ) • S := by norm_num
      _ = (1 : ℕ) • S + (3 : ℕ) • S := by rw [add_nsmul]
      _ = S + (3 : ℕ) • S := by rw [one_nsmul]
  rw [hfour] at hmem
  rw [three_nsmul] at hmem
  rcases hmem with ⟨x, hx, y, hy, hxy⟩
  rcases hx with ⟨i, -, rfl⟩
  rcases hy with ⟨u, hu, v, hv, huv⟩
  rcases hu with ⟨j, -, rfl⟩
  rcases hv with ⟨u2, hu2, v2, hv2, huv2⟩
  rcases hu2 with ⟨k, -, rfl⟩
  rcases hv2 with ⟨l, -, rfl⟩
  refine ⟨i, j, k, l, ?_⟩
  simp [huv, huv2, hxy, add_assoc]

lemma coeffNorm4_cubic_le_ordered_sum_coeff {p : MvPolynomial (Fin 4) ℝ}
    (hp : homogeneousPart4 3 p = p) :
    coeffNorm4 p ≤ ∑ ijk : Fin 4 × Fin 4 × Fin 4,
      |legacyMvCoeff
        (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
          Finsupp.single ijk.2.2 1) p| := by
  classical
  unfold coeffNorm4
  let f : Fin 4 × Fin 4 × Fin 4 → Fin 4 →₀ ℕ := fun ijk =>
    Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 + Finsupp.single ijk.2.2 1
  have hsubset : p.support ⊆ (Finset.univ.image f) := by
    intro α hα
    have hhom := isHomogeneous_of_homogeneousPart4_eq hp
    have hweight := hhom (MvPolynomial.mem_support_iff.mp hα)
    have hdeg : Finsupp.degree α = 3 := by
      rw [Finsupp.degree_eq_weight_one]
      exact hweight
    rcases finsupp_degree_three_as_sum_single hdeg with ⟨i, j, k, rfl⟩
    exact Finset.mem_image.mpr ⟨(i, j, k), Finset.mem_univ _, rfl⟩
  calc
    ∑ α ∈ p.support, |legacyMvCoeff α p| ≤
        ∑ α ∈ Finset.univ.image f, |legacyMvCoeff α p| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro x _ _
          exact abs_nonneg _
    _ ≤ ∑ ijk : Fin 4 × Fin 4 × Fin 4, |legacyMvCoeff (f ijk) p| := by
      exact finset_sum_image_le_sum_of_nonneg_weighted Finset.univ f
        (fun α => |legacyMvCoeff α p|) (fun _ _ => abs_nonneg _)

/- Recursion-depth budget: expanding degree-four coefficient support into ordered
quadruples creates deeply nested finite-product terms during elaboration. -/
set_option maxRecDepth 5000 in
lemma coeffNorm4_quartic_le_ordered_sum_coeff {p : MvPolynomial (Fin 4) ℝ}
    (hp : homogeneousPart4 4 p = p) :
    coeffNorm4 p ≤ ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      |legacyMvCoeff
        (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
          Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1) p| := by
  classical
  unfold coeffNorm4
  let f : ((Fin 4 × Fin 4) × Fin 4) × Fin 4 → Fin 4 →₀ ℕ := fun ijkl =>
    Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
      Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1
  have hsubset : p.support ⊆ (Finset.univ.image f) := by
    intro α hα
    have hhom := isHomogeneous_of_homogeneousPart4_eq hp
    have hweight := hhom (MvPolynomial.mem_support_iff.mp hα)
    have hdeg : Finsupp.degree α = 4 := by
      rw [Finsupp.degree_eq_weight_one]
      exact hweight
    rcases finsupp_degree_four_as_sum_single hdeg with ⟨i, j, k, l, rfl⟩
    exact Finset.mem_image.mpr ⟨(((i, j), k), l), Finset.mem_univ _, rfl⟩
  calc
    ∑ α ∈ p.support, |legacyMvCoeff α p| ≤
        ∑ α ∈ Finset.univ.image f, |legacyMvCoeff α p| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro x _ _
          exact abs_nonneg _
    _ ≤ ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4, |legacyMvCoeff (f ijkl) p| := by
      exact finset_sum_image_le_sum_of_nonneg_weighted Finset.univ f
        (fun α => |legacyMvCoeff α p|) (fun _ _ => abs_nonneg _)

lemma vecCoeffNorm4_cubic_le_ordered_sum_coeff_vectors {N : ℕ}
    (H : Fin N → MvPolynomial (Fin 4) ℝ)
    (hhom : ∀ i, homogeneousPart4 3 (H i) = H i) :
    vecCoeffNorm4 H ≤ ∑ ijk : Fin 4 × Fin 4 × Fin 4, interiorVecNorm
      (fun i : Fin N => legacyMvCoeff
        (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
          Finsupp.single ijk.2.2 1) (H i)) := by
  let f : Fin 4 × Fin 4 × Fin 4 → Fin 4 →₀ ℕ := fun ijk =>
    Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 + Finsupp.single ijk.2.2 1
  have hpoint : ∀ i : Fin N, coeffNorm4 (H i) ≤
      ∑ ijk : Fin 4 × Fin 4 × Fin 4, |legacyMvCoeff (f ijk) (H i)| := by
    intro i
    exact coeffNorm4_cubic_le_ordered_sum_coeff (hhom i)
  have hnorm_point : vecCoeffNorm4 H ≤
      interiorVecNorm (fun i : Fin N => ∑ ijk : Fin 4 × Fin 4 × Fin 4,
        |legacyMvCoeff (f ijk) (H i)|) := by
    unfold vecCoeffNorm4 interiorVecNorm interiorVecSqNorm
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    rw [sq_le_sq]
    rw [abs_of_nonneg (coeffNorm4_nonneg _)]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
    exact hpoint i
  calc
    vecCoeffNorm4 H ≤ interiorVecNorm (fun i : Fin N =>
        ∑ ijk : Fin 4 × Fin 4 × Fin 4, |legacyMvCoeff (f ijk) (H i)|) :=
      hnorm_point
    _ ≤ ∑ ijk : Fin 4 × Fin 4 × Fin 4, interiorVecNorm
        (fun i : Fin N => |legacyMvCoeff (f ijk) (H i)|) := by
          simpa using interiorVecNorm_finset_sum_le_sum_norm
            (Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4))
            (fun ijk i => |legacyMvCoeff (f ijk) (H i)|)
    _ = ∑ ijk : Fin 4 × Fin 4 × Fin 4, interiorVecNorm
        (fun i : Fin N => legacyMvCoeff (f ijk) (H i)) := by
          apply Finset.sum_congr rfl
          intro ijk _
          exact interiorVecNorm_abs _

lemma vecCoeffNorm4_quartic_le_ordered_sum_coeff_vectors {N : ℕ}
    (H : Fin N → MvPolynomial (Fin 4) ℝ)
    (hhom : ∀ i, homogeneousPart4 4 (H i) = H i) :
    vecCoeffNorm4 H ≤ ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4, interiorVecNorm
      (fun i : Fin N => legacyMvCoeff
        (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
          Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1) (H i)) := by
  let f : ((Fin 4 × Fin 4) × Fin 4) × Fin 4 → Fin 4 →₀ ℕ := fun ijkl =>
    Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
      Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1
  have hpoint : ∀ i : Fin N, coeffNorm4 (H i) ≤
      ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
        |legacyMvCoeff (f ijkl) (H i)| := by
    intro i
    exact coeffNorm4_quartic_le_ordered_sum_coeff (hhom i)
  have hnorm_point : vecCoeffNorm4 H ≤
      interiorVecNorm (fun i : Fin N =>
        ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
          |legacyMvCoeff (f ijkl) (H i)|) := by
    unfold vecCoeffNorm4 interiorVecNorm interiorVecSqNorm
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    rw [sq_le_sq]
    rw [abs_of_nonneg (coeffNorm4_nonneg _)]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
    exact hpoint i
  calc
    vecCoeffNorm4 H ≤ interiorVecNorm (fun i : Fin N =>
        ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
          |legacyMvCoeff (f ijkl) (H i)|) := hnorm_point
    _ ≤ ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4, interiorVecNorm
        (fun i : Fin N => |legacyMvCoeff (f ijkl) (H i)|) := by
          simpa using interiorVecNorm_finset_sum_le_sum_norm
            (Finset.univ : Finset (((Fin 4 × Fin 4) × Fin 4) × Fin 4))
            (fun ijkl i => |legacyMvCoeff (f ijkl) (H i)|)
    _ = ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4, interiorVecNorm
        (fun i : Fin N => legacyMvCoeff (f ijkl) (H i)) := by
          apply Finset.sum_congr rfl
          intro ijkl _
          exact interiorVecNorm_abs _



lemma orderedTriple_degree (ijk : Fin 4 × Fin 4 × Fin 4) :
    (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
      Finsupp.single ijk.2.2 1 : Fin 4 →₀ ℕ).degree = 3 := by
  rcases ijk with ⟨i, j, k⟩
  have hmem : (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 :
      Fin 4 →₀ ℕ) ∈ (3 : ℕ) • ((fun i : Fin 4 => Finsupp.single i 1) '' Set.univ) := by
    rw [three_nsmul]
    refine ⟨Finsupp.single i 1, ?_, Finsupp.single j 1 + Finsupp.single k 1, ?_, ?_⟩
    · exact ⟨i, Set.mem_univ _, rfl⟩
    · refine ⟨Finsupp.single j 1, ?_, Finsupp.single k 1, ?_, rfl⟩
      · exact ⟨j, Set.mem_univ _, rfl⟩
      · exact ⟨k, Set.mem_univ _, rfl⟩
    · rw [add_assoc]
  rw [Finsupp.nsmul_single_one_image] at hmem
  exact hmem.1

lemma orderedTriple_sum (ijk : Fin 4 × Fin 4 × Fin 4) :
    (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
      Finsupp.single ijk.2.2 1 : Fin 4 →₀ ℕ).sum (fun _ e => e) = 3 := by
  rw [finsupp_sum_fintype4_linear]
  simpa only [Finsupp.degree_eq_sum] using orderedTriple_degree ijk

lemma orderedQuad_degree (ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4) :
    (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
      Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1 : Fin 4 →₀ ℕ).degree = 4 := by
  rcases ijkl with ⟨⟨⟨i, j⟩, k⟩, l⟩
  let S : Set (Fin 4 →₀ ℕ) := (fun i : Fin 4 => Finsupp.single i 1) '' Set.univ
  have hfour : (4 : ℕ) • S = S + (3 : ℕ) • S := by
    calc
      (4 : ℕ) • S = (1 + 3 : ℕ) • S := by norm_num
      _ = (1 : ℕ) • S + (3 : ℕ) • S := by rw [add_nsmul]
      _ = S + (3 : ℕ) • S := by rw [one_nsmul]
  have hmem : (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 +
      Finsupp.single l 1 : Fin 4 →₀ ℕ) ∈ (4 : ℕ) • S := by
    rw [hfour, three_nsmul]
    refine ⟨Finsupp.single i 1, ?_,
      Finsupp.single j 1 + (Finsupp.single k 1 + Finsupp.single l 1), ?_, ?_⟩
    · exact ⟨i, Set.mem_univ _, rfl⟩
    · refine ⟨Finsupp.single j 1, ?_, Finsupp.single k 1 + Finsupp.single l 1, ?_, rfl⟩
      · exact ⟨j, Set.mem_univ _, rfl⟩
      · refine ⟨Finsupp.single k 1, ?_, Finsupp.single l 1, ?_, rfl⟩
        · exact ⟨k, Set.mem_univ _, rfl⟩
        · exact ⟨l, Set.mem_univ _, rfl⟩
    · abel_nf
  rw [Finsupp.nsmul_single_one_image] at hmem
  exact hmem.1

lemma orderedQuad_sum (ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4) :
    (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
      Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1 : Fin 4 →₀ ℕ).sum
      (fun _ e => e) = 4 := by
  rw [finsupp_sum_fintype4_linear]
  simpa only [Finsupp.degree_eq_sum] using orderedQuad_degree ijkl

theorem weightedJet_coeff_bound_of_unit_eval_bound
    {N m : ℕ} {C : ℝ}
    (hmpos : 0 < m) (hmle : m ≤ 4)
    (H : Fin N → MvPolynomial (Fin 4) ℝ)
    (hhom : ∀ i, homogeneousPart4 m (H i) = H i)
    (hC : 0 ≤ C)
    (hunit : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) ≤ C)
    (α : Fin 4 →₀ ℕ) (hα : α.sum (fun _ e => e) = m) :
    interiorVecNorm (fun i : Fin N => legacyMvCoeff α (H i)) ≤
      (500 : ℝ) ^ (2 * weightedDegree4 α) * (2 ^ m * C) := by
  let P : Fin N → Polynomial ℝ := fun i => weightedRestriction4 (H i)
  let M : ℝ := 2 ^ m * C
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hdegP : ∀ i, (P i).natDegree ≤ 500 := by
    intro i
    dsimp [P]
    apply weightedRestriction4_natDegree_le_500
    exact ((isHomogeneous_of_homogeneousPart4_eq (hhom i)).totalDegree_le).trans hmle
  have hbound : ∀ t : ℝ, |t| ≤ 1 → interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M := by
    intro t ht
    let x : Fin 4 → ℝ := fun i => t ^ weight4 i
    have hxle : localSqNorm x ≤ 4 := localSqNorm_weightedPath_le_four ht
    have heval : (fun i : Fin N => (P i).eval t) =
        fun i : Fin N => MvPolynomial.eval x (H i) := by
      funext i
      dsimp [P, x]
      rw [weightedRestriction4_eval]
    rw [heval]
    dsimp [M]
    exact interiorVecNorm_eval_homogeneous_le_of_localSqNorm_le_four
      hmpos hC H hhom hunit x hxle
  have hmark := interior_markov_vector_iterate_derivative_unit
    (k := 500) (ell := weightedDegree4 α) P hM_nonneg hdegP hbound
  have hderiv : (fun i : Fin N => ((Polynomial.derivative^[weightedDegree4 α]) (P i)).eval 0) =
      fun i : Fin N => (Nat.factorial (weightedDegree4 α) : ℝ) *
        legacyMvCoeff α (H i) := by
    funext i
    dsimp [P]
    rw [polynomial_iterate_derivative_eval_zero]
    rw [coeff_weightedRestriction4_eq_coeff hmle (hhom i) α hα]
  let V : Fin N → ℝ := fun i => legacyMvCoeff α (H i)
  have hfact_nonneg : 0 ≤ (Nat.factorial (weightedDegree4 α) : ℝ) := by positivity
  have hscale : interiorVecNorm
      (fun i : Fin N => (Nat.factorial (weightedDegree4 α) : ℝ) * V i) =
        (Nat.factorial (weightedDegree4 α) : ℝ) * interiorVecNorm V := by
    simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
      vecNorm_smul_nonneg (N := N) (c := (Nat.factorial (weightedDegree4 α) : ℝ))
        hfact_nonneg V
  have hfact_one : (1 : ℝ) ≤ (Nat.factorial (weightedDegree4 α) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (weightedDegree4 α)
  have hVnon : 0 ≤ interiorVecNorm V := interiorVecNorm_nonneg V
  have hscaled : (Nat.factorial (weightedDegree4 α) : ℝ) * interiorVecNorm V ≤
      (500 : ℝ) ^ (2 * weightedDegree4 α) * M := by
    simpa [hderiv, V, hscale] using hmark
  have hV : interiorVecNorm V ≤ (500 : ℝ) ^ (2 * weightedDegree4 α) * M := by
    nlinarith
  simpa [V, M, mul_assoc] using hV

theorem weightedJet_ordered_cubic_coeff_bound_of_unit_eval_bound
    {N : ℕ} {C : ℝ}
    (H : Fin N → MvPolynomial (Fin 4) ℝ)
    (hhom : ∀ i, homogeneousPart4 3 (H i) = H i)
    (hC : 0 ≤ C)
    (hunit : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) ≤ C) :
    ∀ ijk : Fin 4 × Fin 4 × Fin 4,
      interiorVecNorm (fun i : Fin N => legacyMvCoeff
        (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
          Finsupp.single ijk.2.2 1) (H i)) ≤
        (500 : ℝ) ^ (2 * weightedDegree4
          (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
            Finsupp.single ijk.2.2 1)) * (8 * C) := by
  intro ijk
  have hα := orderedTriple_sum ijk
  have h := weightedJet_coeff_bound_of_unit_eval_bound
    (N := N) (m := 3) (C := C) (by norm_num) (by norm_num) H hhom hC hunit
    (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 + Finsupp.single ijk.2.2 1) hα
  convert h using 1
  ring

theorem weightedJet_ordered_quartic_coeff_bound_of_unit_eval_bound
    {N : ℕ} {C : ℝ}
    (H : Fin N → MvPolynomial (Fin 4) ℝ)
    (hhom : ∀ i, homogeneousPart4 4 (H i) = H i)
    (hC : 0 ≤ C)
    (hunit : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) ≤ C) :
    ∀ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      interiorVecNorm (fun i : Fin N => legacyMvCoeff
        (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
          Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1) (H i)) ≤
        (500 : ℝ) ^ (2 * weightedDegree4
          (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
            Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1)) * (16 * C) := by
  intro ijkl
  have hα := orderedQuad_sum ijkl
  have h := weightedJet_coeff_bound_of_unit_eval_bound
    (N := N) (m := 4) (C := C) (by norm_num) (by norm_num) H hhom hC hunit
    (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
      Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1) hα
  convert h using 1
  ring

lemma pow_six_le_add_one_pow_eight_of_one_le {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ^ 6 ≤ ((k : ℝ) + 1) ^ 8 := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have h6 : (k : ℝ) ^ 6 ≤ ((k : ℝ) + 1) ^ 6 := pow_le_pow_left₀ hk0 hle 6
  have hbase2 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := one_le_pow₀ hk1
  have hnon : 0 ≤ ((k : ℝ) + 1) ^ 6 := pow_nonneg (by positivity) 6
  calc
    (k : ℝ) ^ 6 ≤ ((k : ℝ) + 1) ^ 6 := h6
    _ = ((k : ℝ) + 1) ^ 6 * 1 := by ring
    _ ≤ ((k : ℝ) + 1) ^ 6 * ((k : ℝ) + 1) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hbase2 hnon
    _ = ((k : ℝ) + 1) ^ 8 := by ring

lemma pow_eight_le_add_one_pow_eight (k : ℕ) :
    (k : ℝ) ^ 8 ≤ ((k : ℝ) + 1) ^ 8 := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  exact pow_le_pow_left₀ hk0 hle 8

def weightedJetCubicConst : ℝ :=
  let alpha : Fin 4 × Fin 4 × Fin 4 → Fin 4 →₀ ℕ := fun ijk =>
    Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 + Finsupp.single ijk.2.2 1
  let weightTerm : Fin 4 × Fin 4 × Fin 4 → ℝ := fun ijk =>
    (500 : ℝ) ^ (2 * weightedDegree4 (alpha ijk))
  let W : ℝ := ∑ ijk : Fin 4 × Fin 4 × Fin 4, weightTerm ijk
  let C0 : ℝ := Real.sqrt schmInteriorEpsilon0 + schmInteriorS ^ 2
  (W + 1) * (8 * 64) * C0

def weightedJetQuarticConst : ℝ :=
  let alpha : ((Fin 4 × Fin 4) × Fin 4) × Fin 4 → Fin 4 →₀ ℕ := fun ijkl =>
    Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
      Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1
  let weightTerm : ((Fin 4 × Fin 4) × Fin 4) × Fin 4 → ℝ := fun ijkl =>
    (500 : ℝ) ^ (2 * weightedDegree4 (alpha ijkl))
  let W : ℝ := ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4, weightTerm ijkl
  let C0 : ℝ := Real.sqrt schmInteriorEpsilon0 + schmInteriorS ^ 2
  (W + 1) * (16 * 256) * C0

def weightedJetHigherConst : ℝ :=
  8000 * (Real.sqrt schmInteriorEpsilon0 + schmInteriorS ^ 2) +
    weightedJetCubicConst + weightedJetQuarticConst + 1

theorem weightedJetCubicConst_nonneg : 0 ≤ weightedJetCubicConst := by
  dsimp [weightedJetCubicConst]
  have hWnon : 0 ≤ ∑ ijk : Fin 4 × Fin 4 × Fin 4,
      (500 : ℝ) ^ (2 * weightedDegree4
        (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 + Finsupp.single ijk.2.2 1)) := by
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hC0non : 0 ≤ Real.sqrt schmInteriorEpsilon0 + schmInteriorS ^ 2 := by
    exact add_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  nlinarith

theorem weightedJetQuarticConst_nonneg : 0 ≤ weightedJetQuarticConst := by
  dsimp [weightedJetQuarticConst]
  have hWnon : 0 ≤ ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      (500 : ℝ) ^ (2 * weightedDegree4
        (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
          Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1)) := by
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hC0non : 0 ≤ Real.sqrt schmInteriorEpsilon0 + schmInteriorS ^ 2 := by
    exact add_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  nlinarith

theorem weightedJetHigherConst_pos : 0 < weightedJetHigherConst := by
  dsimp [weightedJetHigherConst]
  have hB2nn : 0 ≤ 8000 * (Real.sqrt schmInteriorEpsilon0 + schmInteriorS ^ 2) := by
    have hC0non : 0 ≤ Real.sqrt schmInteriorEpsilon0 + schmInteriorS ^ 2 := by
      exact add_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
    nlinarith
  nlinarith [weightedJetCubicConst_nonneg, weightedJetQuarticConst_nonneg]

end OptimalConvergenceRates
