/-
  OptimalConvergenceRates/SlotLaurent2022/KernelOperator.lean

  Chebyshev-diagonal Jackson kernel operator and inverse operator estimates.
-/
import OptimalConvergenceRates.SlotLaurent2022.JacksonKernel
import OptimalConvergenceRates.BasicNotions.SumsOfSquares
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.MvPolynomial.Funext

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## Kernel operator definition -/

/-- The kernel operator K_r: scales each Chebyshev coefficient by λ_κ.
    K_r(p) = ∑_{κ ∈ ℕ^n_r} λ_κ · chebyCoeff(p,κ) · T_κ -/
noncomputable def kernelOperator (n r : ℕ) :
    MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ :=
  fun p => ∑ κ ∈ multiIndices n r,
    MvPolynomial.C (jacksonCoeffMulti κ r * chebyCoeff n r p κ) *
    chebyshevMulti κ

/-- The inverse kernel operator K_r⁻¹: scales each coefficient by 1/λ_κ.
    K_r⁻¹(p) = ∑_{κ ∈ ℕ^n_r} (1/λ_κ) · chebyCoeff(p,κ) · T_κ -/
noncomputable def kernelOperatorInv (n r : ℕ) :
    MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ :=
  fun p => ∑ κ ∈ multiIndices n r,
    MvPolynomial.C (chebyCoeff n r p κ / jacksonCoeffMulti κ r) *
    chebyshevMulti κ

/-! ## Helper: Jackson coefficient positivity from multiIndices membership -/

private theorem jacksonCoeffMulti_pos_of_mem {κ : Fin n → ℕ} {r : ℕ}
    (hκ : κ ∈ multiIndices n r) : 0 < jacksonCoeffMulti κ r :=
  jacksonCoeffMulti_pos (fun i => (multiIndices_mem_iff.mp hκ).2 i)

/-! ## Linearity and diagonalization -/

/-- K_r is linear -/
theorem kernelOperator_linear (n r : ℕ) (a b : ℝ) (p q : MvPolynomial (Fin n) ℝ) :
    kernelOperator n r (MvPolynomial.C a * p + MvPolynomial.C b * q) =
    MvPolynomial.C a * kernelOperator n r p +
    MvPolynomial.C b * kernelOperator n r q := by
  simp only [kernelOperator, chebyCoeff_add, chebyCoeff_C_mul]
  -- Each summand splits into two terms
  have h : ∀ κ ∈ multiIndices n r,
      MvPolynomial.C (jacksonCoeffMulti κ r *
        (a * chebyCoeff n r p κ + b * chebyCoeff n r q κ)) *
      chebyshevMulti κ =
      MvPolynomial.C (a * (jacksonCoeffMulti κ r * chebyCoeff n r p κ)) *
        chebyshevMulti κ +
      MvPolynomial.C (b * (jacksonCoeffMulti κ r * chebyCoeff n r q κ)) *
        chebyshevMulti κ := by
    intro κ _
    rw [show jacksonCoeffMulti κ r *
        (a * chebyCoeff n r p κ + b * chebyCoeff n r q κ) =
      a * (jacksonCoeffMulti κ r * chebyCoeff n r p κ) +
      b * (jacksonCoeffMulti κ r * chebyCoeff n r q κ) from by ring]
    rw [MvPolynomial.C_add, add_mul]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  -- Pull C(a), C(b) out of the sums
  congr 1 <;> {
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro κ _
    rw [map_mul, mul_assoc] }

/-- K_r diagonalizes w.r.t. the Chebyshev basis with eigenvalues λ_κ^r -/
theorem kernelOperator_diag (r : ℕ) (κ : Fin n → ℕ) (hκ : multiDegree κ ≤ r) :
    kernelOperator n r (chebyshevMulti κ) =
    MvPolynomial.C (jacksonCoeffMulti κ r) * chebyshevMulti κ := by
  have hκ_mem := multiDegree_le_mem hκ
  simp only [kernelOperator]
  -- The sum reduces to a single term at κ
  rw [Finset.sum_eq_single κ
    (fun μ hμ hμκ => by
      rw [chebyCoeff_chebyshev r μ κ hμ hκ_mem, if_neg (Ne.symm hμκ)]
      simp)
    (fun h => absurd hκ_mem h)]
  rw [chebyCoeff_chebyshev r κ κ hκ_mem hκ_mem, if_pos rfl, mul_one]

/-! ## Inverse properties -/

/-- K_r⁻¹ preserves the degree bound -/
theorem kernelOperatorInv_degree (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (_hp : p.totalDegree ≤ r) :
    (kernelOperatorInv n r p).totalDegree ≤ r := by
  unfold kernelOperatorInv
  apply MvPolynomial.totalDegree_finsetSum_le
  intro κ hκ
  have hκ_deg : multiDegree κ ≤ r := (multiIndices_mem_iff.mp hκ).1
  calc (MvPolynomial.C _ * chebyshevMulti κ).totalDegree
      ≤ (MvPolynomial.C _).totalDegree + (chebyshevMulti κ).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ = (chebyshevMulti κ).totalDegree := by
        rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ multiDegree κ := chebyshevMulti_totalDegree κ
    _ ≤ r := hκ_deg

/-- K_r⁻¹ is a left inverse of K_r on polynomials of degree ≤ r -/
theorem kernelOperator_inv_left (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ r) :
    kernelOperatorInv n r (kernelOperator n r p) = p := by
  unfold kernelOperatorInv kernelOperator
  -- Step 1: Compute chebyCoeff of K_r(p) = ∑ C(λ_κ c_κ) T_κ
  -- Step 2: λ_μ c_μ / λ_μ = c_μ
  -- Step 3: ∑ C(c_μ) T_μ = p by Chebyshev expansion
  have h : ∀ μ ∈ multiIndices n r,
      MvPolynomial.C (chebyCoeff n r (∑ κ ∈ multiIndices n r,
        MvPolynomial.C (jacksonCoeffMulti κ r * chebyCoeff n r p κ) *
        chebyshevMulti κ) μ / jacksonCoeffMulti μ r) * chebyshevMulti μ =
      MvPolynomial.C (chebyCoeff n r p μ) * chebyshevMulti μ := by
    intro μ hμ
    congr 1; congr 1
    rw [chebyCoeff_expansion_coeff r _ μ hμ]
    exact mul_div_cancel_left₀ _ (ne_of_gt (jacksonCoeffMulti_pos_of_mem hμ))
  rw [Finset.sum_congr rfl h]
  exact (chebyshev_expansion r p hp).symm

/-- K_r⁻¹ is a right inverse of K_r on polynomials of degree ≤ r -/
theorem kernelOperator_inv_right (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ r) :
    kernelOperator n r (kernelOperatorInv n r p) = p := by
  unfold kernelOperator kernelOperatorInv
  have h : ∀ μ ∈ multiIndices n r,
      MvPolynomial.C (jacksonCoeffMulti μ r * chebyCoeff n r (∑ κ ∈ multiIndices n r,
        MvPolynomial.C (chebyCoeff n r p κ / jacksonCoeffMulti κ r) *
        chebyshevMulti κ) μ) * chebyshevMulti μ =
      MvPolynomial.C (chebyCoeff n r p μ) * chebyshevMulti μ := by
    intro μ hμ
    congr 1; congr 1
    rw [chebyCoeff_expansion_coeff r _ μ hμ]
    exact mul_div_cancel₀ _ (ne_of_gt (jacksonCoeffMulti_pos_of_mem hμ))
  rw [Finset.sum_congr rfl h]
  exact (chebyshev_expansion r p hp).symm

/-! ## Quadrature representation of kernel operator -/

/-- Chebyshev-Gauss quadrature representation of the kernel operator.
    K_r(p) = ∑_j C((1/(r+2))^n · p(y_j)) · ∏_i embed_i(jacksonKernelPoly r (y_{j_i}))

    Proved via discrete Chebyshev orthogonality and MvPolynomial.funext. -/
theorem kernel_quadrature_rep (n r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ r) :
    kernelOperator n r p =
    ∑ j ∈ quadratureNodes n r,
      MvPolynomial.C ((1 / (r + 2 : ℝ)) ^ n *
        MvPolynomial.eval (fun i => chebyNode r (j i)) p) *
      (∏ i : Fin n, embedUnivariate i (jacksonKernelPoly r (chebyNode r (j i)))) := by
  -- Reduce to pointwise evaluation equality via funext
  apply MvPolynomial.funext; intro x
  -- Evaluate LHS: unfold kernelOperator, eval distributes
  have hLHS :
    MvPolynomial.eval x (kernelOperator n r p) =
    ∑ κ ∈ multiIndices n r,
      jacksonCoeffMulti κ r * chebyCoeff n r p κ *
      ∏ i, (chebyshevT (κ i)).eval (x i) := by
    simp only [kernelOperator, map_sum, map_mul, MvPolynomial.eval_C, chebyshevMulti,
      map_prod, eval_embedUnivariate]
  -- Evaluate RHS
  have hRHS :
    MvPolynomial.eval x
      (∑ j ∈ quadratureNodes n r,
        MvPolynomial.C ((1 / (r + 2 : ℝ)) ^ n *
          MvPolynomial.eval (fun i => chebyNode r (j i)) p) *
        ∏ i : Fin n, embedUnivariate i (jacksonKernelPoly r (chebyNode r (j i)))) =
    ∑ j ∈ quadratureNodes n r,
      (1 / (r + 2 : ℝ)) ^ n *
      (∑ μ ∈ multiIndices n r,
        chebyCoeff n r p μ * ∏ i, (chebyshevT (μ i)).eval (chebyNode r (j i))) *
      (∏ i, ∑ k ∈ Finset.range (r + 1),
        jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
        (chebyshevT k).eval (chebyNode r (j i))) := by
    rw [map_sum]; apply Finset.sum_congr rfl; intro j _
    rw [map_mul, MvPolynomial.eval_C, map_prod]
    congr 1
    · congr 1
      conv_lhs => rw [chebyshev_expansion r p hp]
      rw [map_sum]; congr 1; ext μ
      rw [map_mul, MvPolynomial.eval_C]; congr 1
      simp only [chebyshevMulti, map_prod, eval_embedUnivariate]
    · apply Finset.prod_congr rfl; intro i _
      rw [eval_embedUnivariate, jacksonKernelPoly_eval, jacksonKernelUni_chebyshev_sum]
  rw [hLHS, hRHS]
  -- Apply the core identity
  exact (quadrature_eval_eq_kernel_eval n r p hp x).symm

/-! ## Property (P1): K_r maps P(B^n)_r into Q(B^n)_{(r+1)n} -/

/-- Property (P1): If p is nonneg on B^n with degree ≤ r, then K_r(p) ∈ Q(B^n)_{(r+1)n}.

    Proof: By the quadrature representation (kernel_quadrature_rep),
    K_r(p) = ∑_j c_j · ∏_i embed_i(K^ja(·, y_{j_i}))
    where c_j = (1/(r+2))^n · p(y_j).

    For each summand:
    - y_j ∈ B^n (Chebyshev nodes are in [-1,1]), so p(y_j) ≥ 0 (hp_nonneg)
    - c_j ≥ 0 since p(y_j) ≥ 0 and (1/(r+2))^n > 0
    - K^ja(·, y_{j_i}) ∈ BoxUniPreordering(r+1) by Markov-Lukacz (jackson_nonneg + degree bound)
    - ∏_i embed_i(K^ja(·, y_{j_i})) ∈ BoxPreordering n ((r+1)n)
      by prod_BoxUniPreordering_in_BoxPreordering
    - c_j · (that product) ∈ BoxPreordering n ((r+1)n) by BoxPreordering_nonneg_scale
    - The sum is in BoxPreordering n ((r+1)n) by BoxPreordering_sum -/
theorem kernel_property_P1 (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp_deg : p.totalDegree ≤ r) (hp_nonneg : IsNonnegOn p (Hypercube n)) :
    kernelOperator n r p ∈ BoxPreordering n ((r + 1) * n) := by
  rw [kernel_quadrature_rep n r p hp_deg]
  apply BoxPreordering_sum
  intro j _
  -- The j-th summand is C(c_j) * ∏_i embed_i(K^ja(·, y_{j_i}))
  apply BoxPreordering_nonneg_scale
  · -- c_j ≥ 0: (1/(r+2))^n * p(y_j) ≥ 0
    apply mul_nonneg
    · positivity
    · exact hp_nonneg _ (chebyNode_vec_mem_Hypercube r j)
  · -- ∏_i embed_i(K^ja(·, y_{j_i})) ∈ BoxPreordering n ((r+1)*n)
    apply box_preordering_mono (show (r + 1) * n ≤ (r + 1) * n from le_refl _)
    exact prod_BoxUniPreordering_in_BoxPreordering n
      (fun i => jacksonKernelPoly r (chebyNode r (j i)))
      (r + 1)
      (fun i => jacksonKernelPoly_in_BoxUniPreordering r (chebyNode r (j i))
        (chebyNode_mem_Icc r _))

/-! ## Property (P2): Sup-norm bound on K_r⁻¹(F̃) - F̃ -/

/-- L² ≤ L∞ bound: chebyInnerMulti(p, p) ≤ (polySupNorm p)².
    The integrand (eval(cosθ,p))² ≤ ‖p‖_∞² pointwise since cosθ ∈ Hypercube,
    and the normalized measure has total mass 1. -/
private theorem chebyInnerMulti_self_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    chebyInnerMulti p p ≤ (polySupNorm p) ^ 2 := by
  set μ := MeasureTheory.Measure.pi
    (fun _ : Fin n => MeasureTheory.volume.restrict (Set.Icc 0 Real.pi)) with hμ_def
  unfold chebyInnerMulti
  have hprefix_nonneg : (0 : ℝ) ≤ (1 / Real.pi) ^ n :=
    pow_nonneg (div_nonneg zero_le_one Real.pi_pos.le) n
  -- Pointwise bound: f(θ)² ≤ (polySupNorm p)²
  have hbound : ∀ θ : Fin n → ℝ,
      MvPolynomial.eval (fun i => Real.cos (θ i)) p *
      MvPolynomial.eval (fun i => Real.cos (θ i)) p ≤
      (polySupNorm p) ^ 2 := by
    intro θ
    have hsq : MvPolynomial.eval (fun i => Real.cos (θ i)) p *
        MvPolynomial.eval (fun i => Real.cos (θ i)) p =
        (MvPolynomial.eval (fun i => Real.cos (θ i)) p) ^ 2 := by ring
    rw [hsq, ← sq_abs]
    have hcos_hyp : (fun i => Real.cos (θ i)) ∈ Hypercube n := by
      intro i _
      exact ⟨Real.neg_one_le_cos (θ i), Real.cos_le_one (θ i)⟩
    have hbdd : BddAbove ((fun x => |MvPolynomial.eval x p|) '' Hypercube n) :=
      (Hypercube_compact.image
        (continuous_abs.comp (MvPolynomial.continuous_eval p))).bddAbove
    have hle : |MvPolynomial.eval (fun i => Real.cos (θ i)) p| ≤ polySupNorm p :=
      le_csSup hbdd ⟨_, hcos_hyp, rfl⟩
    exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  -- Integrability (re-derive since chebyInnerMulti_integrand_integrable is private)
  have hf_int : MeasureTheory.Integrable
      (fun θ : Fin n → ℝ =>
        MvPolynomial.eval (fun i => Real.cos (θ i)) p *
        MvPolynomial.eval (fun i => Real.cos (θ i)) p) μ := by
    rw [hμ_def, ← MeasureTheory.Measure.restrict_pi_pi
      (μ := fun _ => MeasureTheory.volume) (s := fun _ => Set.Icc 0 Real.pi)]
    have hcont : Continuous (fun θ : Fin n → ℝ =>
        MvPolynomial.eval (fun i => Real.cos (θ i)) p *
        MvPolynomial.eval (fun i => Real.cos (θ i)) p) :=
      Continuous.mul
        ((MvPolynomial.continuous_eval p).comp
          (continuous_pi fun i =>
            Real.continuous_cos.comp (continuous_apply i)))
        ((MvPolynomial.continuous_eval p).comp
          (continuous_pi fun i =>
            Real.continuous_cos.comp (continuous_apply i)))
    exact hcont.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have hconst_int : MeasureTheory.Integrable
      (fun _ : Fin n → ℝ => (polySupNorm p) ^ 2) μ :=
    MeasureTheory.integrable_const _
  -- Integral bound
  have hint_le : ∫ θ,
      MvPolynomial.eval (fun i => Real.cos (θ i)) p *
      MvPolynomial.eval (fun i => Real.cos (θ i)) p ∂μ ≤
      ∫ _, (polySupNorm p) ^ 2 ∂μ :=
    MeasureTheory.integral_mono hf_int hconst_int hbound
  rw [MeasureTheory.integral_const] at hint_le
  -- From orthogonality: (1/π)^n * μ.real(univ) = 1
  have hT0 := chebyshevMulti_orthogonality (n := n) (fun _ => 0) (fun _ => 0)
  rw [if_pos rfl, hammingWeight_zero, Int.ofNat_zero, neg_zero, zpow_zero] at hT0
  unfold chebyInnerMulti at hT0
  simp only [eval_chebyshevMulti_cos, Nat.cast_zero, zero_mul, Real.cos_zero,
    Finset.prod_const_one, one_mul] at hT0
  rw [MeasureTheory.integral_const] at hT0
  simp only [smul_eq_mul, mul_one] at hT0
  -- Combine
  calc (1 / Real.pi) ^ n *
      ∫ θ,
        MvPolynomial.eval (fun i => Real.cos (θ i)) p *
        MvPolynomial.eval (fun i => Real.cos (θ i)) p ∂μ
      ≤ (1 / Real.pi) ^ n * (μ.real Set.univ • (polySupNorm p) ^ 2) :=
        mul_le_mul_of_nonneg_left hint_le hprefix_nonneg
    _ = (1 / Real.pi) ^ n * (μ.real Set.univ * (polySupNorm p) ^ 2) := by
        rw [smul_eq_mul]
    _ = ((1 / Real.pi) ^ n * μ.real Set.univ) * (polySupNorm p) ^ 2 := by ring
    _ = 1 * (polySupNorm p) ^ 2 := by rw [hT0]
    _ = (polySupNorm p) ^ 2 := one_mul _

/-- Squared Chebyshev coefficient bound via Parseval:
    (chebyCoeff p κ)² ≤ 2^{w(κ)} · (polySupNorm p)². -/
private theorem chebyCoeff_sq_le {n : ℕ} (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ r) (κ : Fin n → ℕ) (hκ : κ ∈ multiIndices n r) :
    (chebyCoeff n r p κ) ^ 2 ≤ (2 : ℝ) ^ (hammingWeight κ) * (polySupNorm p) ^ 2 := by
  -- Step 1: By Parseval, chebyInnerMulti p p = ∑ 2^{-w(μ)} * (chebyCoeff p μ)^2
  have hParseval := chebyInnerMulti_eq_parseval r p p hp hp
  -- Step 2: The single term for κ is ≤ the sum (all terms nonneg)
  have h_term_le : (2 : ℝ) ^ (-(hammingWeight κ : ℤ)) * (chebyCoeff n r p κ) ^ 2 ≤
      chebyInnerMulti p p := by
    rw [hParseval, show (2 : ℝ) ^ (-(hammingWeight κ : ℤ)) * (chebyCoeff n r p κ) ^ 2 =
      (2 : ℝ) ^ (-(hammingWeight κ : ℤ)) * chebyCoeff n r p κ * chebyCoeff n r p κ from by ring]
    apply Finset.single_le_sum (fun μ _ => ?_) hκ
    · -- Each term is nonneg: 2^{-w} * c * c = 2^{-w} * c^2 ≥ 0
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(hammingWeight μ : ℤ)) := by positivity
      nlinarith [sq_nonneg (chebyCoeff n r p μ)]
  -- Step 3: chebyInnerMulti p p ≤ (polySupNorm p)^2
  have h_inner_le := chebyInnerMulti_self_le p
  -- Step 4: Combine: 2^{-w} * c^2 ≤ ‖p‖^2
  have h_combined : (2 : ℝ) ^ (-(hammingWeight κ : ℤ)) * (chebyCoeff n r p κ) ^ 2 ≤
      (polySupNorm p) ^ 2 := le_trans h_term_le h_inner_le
  -- Step 5: Multiply both sides by 2^{w} (which is > 0)
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have h2w_pos : (0 : ℝ) < (2 : ℝ) ^ (hammingWeight κ : ℤ) := by positivity
  rw [show (2 : ℝ) ^ (hammingWeight κ) = (2 : ℝ) ^ (hammingWeight κ : ℤ) from
    (zpow_natCast 2 (hammingWeight κ)).symm]
  calc (chebyCoeff n r p κ) ^ 2
      = (2 : ℝ) ^ (hammingWeight κ : ℤ) * ((2 : ℝ) ^ (-(hammingWeight κ : ℤ)) *
          (chebyCoeff n r p κ) ^ 2) := by
        rw [← mul_assoc, ← zpow_add₀ h2ne, add_neg_cancel, zpow_zero, one_mul]
    _ ≤ (2 : ℝ) ^ (hammingWeight κ : ℤ) * (polySupNorm p) ^ 2 :=
        mul_le_mul_of_nonneg_left h_combined (le_of_lt h2w_pos)

/-- Chebyshev coefficient bound (Lemma 6): for ‖p‖_∞ ≤ 1,
    |p_κ| ≤ 2^{w(κ)/2}. From Parseval + L² ≤ L∞ bound. -/
theorem chebyCoeff_bound {n : ℕ} (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ r) (hp_norm : polySupNorm p ≤ 1)
    (κ : Fin n → ℕ) (hκ : κ ∈ multiIndices n r) :
    |chebyCoeff n r p κ| ≤ (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) := by
  -- Step 1: From chebyCoeff_sq_le: c^2 ≤ 2^w * ‖p‖^2
  have h_sq := chebyCoeff_sq_le r p hp κ hκ
  -- Step 2: Since ‖p‖ ≤ 1, we get c^2 ≤ 2^w * 1 = 2^w
  have h_sq_le : (chebyCoeff n r p κ) ^ 2 ≤ (2 : ℝ) ^ (hammingWeight κ) := by
    calc (chebyCoeff n r p κ) ^ 2
        ≤ (2 : ℝ) ^ (hammingWeight κ) * (polySupNorm p) ^ 2 := h_sq
      _ ≤ (2 : ℝ) ^ (hammingWeight κ) * 1 ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h0 : (0 : ℝ) ≤ polySupNorm p := by
            obtain ⟨x, hx⟩ := Hypercube_nonempty (n := n)
            exact le_csSup_of_le
              (Hypercube_compact.image
                (continuous_abs.comp (MvPolynomial.continuous_eval p))).bddAbove
              ⟨x, hx, rfl⟩ (abs_nonneg _)
          exact pow_le_pow_left₀ h0 hp_norm 2
      _ = (2 : ℝ) ^ (hammingWeight κ) := by ring
  -- Step 3: |c| ≤ √(2^w)
  -- Since |c|^2 = c^2, we have |c|^2 ≤ 2^w
  have h_abs_sq : |chebyCoeff n r p κ| ^ 2 ≤ (2 : ℝ) ^ (hammingWeight κ) := by
    rwa [sq_abs]
  have h_abs_le_sqrt : |chebyCoeff n r p κ| ≤ Real.sqrt ((2 : ℝ) ^ (hammingWeight κ)) := by
    rw [← Real.sqrt_sq (abs_nonneg _)]
    exact Real.sqrt_le_sqrt h_abs_sq
  -- Step 4: √(2^w) = 2^(w/2)
  -- Use: √x = x^(1/2) for x ≥ 0, and (2^w)^(1/2) = 2^(w/2)
  have h_sqrt_eq : Real.sqrt ((2 : ℝ) ^ (hammingWeight κ)) =
      (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    rw [show (2 : ℝ) ^ (hammingWeight κ) = (2 : ℝ) ^ (hammingWeight κ : ℝ) from
      (Real.rpow_natCast 2 (hammingWeight κ)).symm]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  linarith

/-- Property (P2): The sup-norm of K_r⁻¹(p) - p is bounded by the sum of
    eigenvalue deviations weighted by Chebyshev coefficient bounds.
    Proof: K_r⁻¹(p) - p = ∑_κ (1/λ_κ - 1) p_κ T_κ. By triangle inequality,
    ‖T_κ‖_∞ ≤ 1 (chebyshevMulti_bounded), |p_κ| ≤ 2^{w(κ)/2} (chebyCoeff_bound),
    so ‖K_r⁻¹(p) - p‖_∞ ≤ ∑_κ 2^{w(κ)/2} |1 - 1/λ_κ|. -/
theorem kernel_property_P2 (r d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp_deg : p.totalDegree ≤ d) (hd : d ≤ r)
    (hp_norm : polySupNorm p ≤ 1) :
    polySupNorm (kernelOperatorInv n r p - p) ≤
    ∑ κ ∈ multiIndices n d,
      (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) *
      |1 - 1 / jacksonCoeffMulti κ r| := by
  have hp_r : p.totalDegree ≤ r := le_trans hp_deg hd
  -- Step 1: Express K_r⁻¹(p) - p as a Chebyshev sum
  -- K_r⁻¹(p) = ∑ C(c_κ/λ_κ) T_κ and p = ∑ C(c_κ) T_κ
  -- So K_r⁻¹(p) - p = ∑ C(c_κ(1/λ_κ - 1)) T_κ
  have hKinv_expand : kernelOperatorInv n r p - p =
      ∑ κ ∈ multiIndices n r,
        MvPolynomial.C (chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)) *
        chebyshevMulti κ := by
    -- Rewrite p using Chebyshev expansion, then combine the two sums
    have hp_expand := chebyshev_expansion r p hp_r
    unfold kernelOperatorInv
    conv_lhs => rhs; rw [hp_expand]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro κ hκ
    rw [← sub_mul, ← map_sub]
    congr 1; congr 1
    have hjpos := jacksonCoeffMulti_pos_of_mem hκ
    field_simp
  -- Step 2: Apply polySupNorm_le_of_bound
  apply polySupNorm_le_of_bound
  intro x hx
  rw [hKinv_expand]
  -- Step 3: eval distributes over the sum
  rw [map_sum]
  -- Step 4: Triangle inequality: |∑ f_κ| ≤ ∑ |f_κ|
  calc |∑ κ ∈ multiIndices n r,
        MvPolynomial.eval x
          (MvPolynomial.C (chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)) *
           chebyshevMulti κ)|
      ≤ ∑ κ ∈ multiIndices n r,
        |MvPolynomial.eval x
          (MvPolynomial.C (chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)) *
           chebyshevMulti κ)| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ κ ∈ multiIndices n r,
        |chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)| *
        |MvPolynomial.eval x (chebyshevMulti κ)| := by
      congr 1; ext κ
      rw [map_mul, MvPolynomial.eval_C, abs_mul]
    _ ≤ ∑ κ ∈ multiIndices n r,
        |chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)| := by
      apply Finset.sum_le_sum; intro κ hκ
      calc |chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)| *
              |MvPolynomial.eval x (chebyshevMulti κ)|
          ≤ |chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)| * 1 :=
            mul_le_mul_of_nonneg_left (chebyshevMulti_bounded κ x hx) (abs_nonneg _)
        _ = |chebyCoeff n r p κ * (1 / jacksonCoeffMulti κ r - 1)| := mul_one _
    -- Step 5: Split into |c_κ| * |1/λ_κ - 1| and use abs_sub_comm
    _ = ∑ κ ∈ multiIndices n r,
        |chebyCoeff n r p κ| * |1 - 1 / jacksonCoeffMulti κ r| := by
      congr 1; ext κ
      rw [abs_mul]
      congr 1
      rw [show 1 / jacksonCoeffMulti κ r - 1 = -(1 - 1 / jacksonCoeffMulti κ r) from by ring,
          abs_neg]
    -- Step 6: Terms with multiDegree κ > d vanish
    _ = ∑ κ ∈ multiIndices n d,
        |chebyCoeff n r p κ| * |1 - 1 / jacksonCoeffMulti κ r| := by
      -- multiIndices n d ⊆ multiIndices n r
      symm
      apply Finset.sum_subset
      · -- multiIndices n d ⊆ multiIndices n r
        intro κ hκ
        rw [multiIndices_mem_iff] at hκ ⊢
        exact ⟨le_trans hκ.1 hd, fun i => le_trans (hκ.2 i) hd⟩
      · -- For κ ∈ multiIndices n r \ multiIndices n d, the term is 0
        intro κ hκ_r hκ_not_d
        have hκ_deg : d < multiDegree κ := by
          by_contra h
          push_neg at h
          exact hκ_not_d (multiDegree_le_mem h)
        have hcoeff_zero := chebyCoeff_zero_of_degree_lt r p κ (by omega)
        simp [hcoeff_zero]
    -- Step 7: Apply chebyCoeff_bound to get |c_κ| ≤ 2^{w(κ)/2}
    _ ≤ ∑ κ ∈ multiIndices n d,
        (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2) *
        |1 - 1 / jacksonCoeffMulti κ r| := by
      apply Finset.sum_le_sum; intro κ hκ
      -- κ ∈ multiIndices n d ⊆ multiIndices n r
      have hκ_r : κ ∈ multiIndices n r := by
        rw [multiIndices_mem_iff] at hκ ⊢
        exact ⟨le_trans hκ.1 hd, fun i => le_trans (hκ.2 i) hd⟩
      apply mul_le_mul_of_nonneg_right (chebyCoeff_bound r p hp_r hp_norm κ hκ_r) (abs_nonneg _)


end OptimalConvergenceRates

end
