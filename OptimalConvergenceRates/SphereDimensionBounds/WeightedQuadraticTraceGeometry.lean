import Mathlib.Analysis.Matrix.Order
import OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticExistence

/-! Spectral geometry for nonlinear bounded weighted quadratic completion.
Scalar domination for a PSD weight gives an actual matrix completion with
Euclidean operator norm at most twice the scalar constant. The proof includes
singular weights and indefinite trace tests. No linear selection is claimed. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticTraceGeometry

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open Matrix
open OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticExistence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Mat := Matrix ι ι ℝ

def gramRoot (M : Mat (ι := ι)) : Mat (ι:=ι) :=
  CFC.sqrt (Mᴴ*M)

theorem gramRoot_posSemidef (M : Mat (ι := ι)) : (gramRoot M).PosSemidef :=
  (CFC.sqrt_nonneg (Mᴴ*M)).posSemidef

theorem gramRoot_transpose (M : Mat (ι := ι)) : (gramRoot M).transpose=gramRoot M := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using (gramRoot_posSemidef M).isHermitian.eq

theorem gramRoot_mul_self (M : Mat (ι := ι)) : gramRoot M * gramRoot M=M.transpose*M := by
  simpa only [gramRoot, conjTranspose_eq_transpose_of_trivial] using
    CFC.sqrt_mul_sqrt_self (Mᴴ*M) (Matrix.posSemidef_conjTranspose_mul_self M).nonneg

theorem gramRoot_isUnit (M : Mat (ι := ι)) (hM : IsUnit M) : IsUnit (gramRoot M) := by
  apply (isUnit_pow_iff (by decide : (2:ℕ)≠0)).mp
  rw [pow_two, gramRoot_mul_self]
  have ht : IsUnit M.transpose := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det M).mp hM
  exact ht.mul hM

def polarMatrix (M : Mat (ι := ι)) : Mat (ι:=ι) := M*(gramRoot M)⁻¹

theorem polarMatrix_transpose_mul_self (M : Mat (ι := ι)) (hM : IsUnit M) :
    (polarMatrix M).transpose*polarMatrix M=1 := by
  have hH := (Matrix.isUnit_iff_isUnit_det _).mp (gramRoot_isUnit M hM)
  have ht : ((gramRoot M)⁻¹).transpose=(gramRoot M)⁻¹ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (gramRoot_posSemidef M).isHermitian.inv.eq
  simp only [polarMatrix, Matrix.transpose_mul, ht, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc M.transpose M, ← gramRoot_mul_self]
  rw [← Matrix.mul_assoc]
  calc
    (gramRoot M)⁻¹*(gramRoot M*gramRoot M)*(gramRoot M)⁻¹ =
        ((gramRoot M)⁻¹*gramRoot M)*(gramRoot M*(gramRoot M)⁻¹) := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hH, Matrix.mul_nonsing_inv _ hH, Matrix.one_mul]

theorem polarMatrix_mem_unitary (M : Mat (ι := ι)) (hM : IsUnit M) :
    polarMatrix M ∈ Matrix.unitaryGroup ι ℝ := by
  rw [Matrix.mem_unitaryGroup_iff]
  simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
    (mul_eq_one_comm.mp (polarMatrix_transpose_mul_self M hM))

theorem polarMatrix_norm_le_one (M : Mat (ι := ι)) (hM : IsUnit M) :
    ‖polarMatrix M‖≤1 := by
  nontriviality Mat (ι:=ι)
  exact le_of_eq (CStarRing.norm_of_mem_unitary (polarMatrix_mem_unitary M hM))

theorem polarMatrix_mul_gramRoot (M : Mat (ι := ι)) (hM : IsUnit M) :
    polarMatrix M*gramRoot M=M := by
  have hH := (Matrix.isUnit_iff_isUnit_det _).mp (gramRoot_isUnit M hM)
  simp only [polarMatrix, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hH, Matrix.mul_one]

theorem gramRoot_trace_le_dualOperatorNorm (M : Mat (ι := ι)) (hM : IsUnit M) :
    Matrix.trace (gramRoot M) ≤ dualOperatorNorm M := by
  have hpair : tracePair M (polarMatrix M)=Matrix.trace (gramRoot M) := by
    simp only [tracePair, polarMatrix]
    rw [← Matrix.mul_assoc, ← gramRoot_mul_self]
    have hH := (Matrix.isUnit_iff_isUnit_det _).mp (gramRoot_isUnit M hM)
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hH, Matrix.mul_one]
  calc
    Matrix.trace (gramRoot M) = tracePair M (polarMatrix M) := hpair.symm
    _ ≤ |tracePair M (polarMatrix M)| := le_abs_self _
    _ ≤ dualOperatorNorm M*‖polarMatrix M‖ := tracePair_le_dualOperatorNorm _ _
    _ ≤ dualOperatorNorm M := by
      nlinarith [polarMatrix_norm_le_one M hM, dualOperatorNorm_nonneg M]

omit [DecidableEq ι] in
theorem rankOne_trace (x : EuclideanSpace ℝ ι) : Matrix.trace (rankOne x)=‖x‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i, x i*x i)=∑ i, ‖x i‖^2
  simp only [Real.norm_eq_abs, sq_abs, ← pow_two]

theorem rankOne_map (A : Mat (ι := ι)) (x : EuclideanSpace ℝ ι) :
    rankOne (Matrix.toEuclideanLin A x)=A*rankOne x*A.transpose := by
  ext i j
  simp only [rankOne, Matrix.toLpLin_apply, WithLp.equiv_symm_apply, PiLp.toLp_apply,
    WithLp.equiv_apply,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem orthonormal_rankOne_sum (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    (∑ k, rankOne (b k))=(1 : Mat (ι:=ι)) := by
  ext i j
  have h := b.sum_inner_mul_inner (EuclideanSpace.single i (1:ℝ))
    (EuclideanSpace.single j (1:ℝ))
  simp only [Matrix.sum_apply, rankOne, Matrix.one_apply]
  simpa only [EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, star_trivial, one_mul, mul_one,
    PiLp.single_apply, map_one, RCLike.conj_to_real, eq_comm] using h

theorem spectral_rankOne_sum (A : Mat (ι := ι)) (hA : A.IsHermitian) :
    A=∑ k, (hA.eigenvalues k) • rankOne (hA.eigenvectorBasis k) := by
  ext i j
  calc
    A i j = (hA.eigenvectorUnitary.1 * Matrix.diagonal hA.eigenvalues *
        hA.eigenvectorUnitary.1.transpose) i j := by
      simpa only [RCLike.ofReal_real_eq_id, Function.id_comp,
        Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
        conjTranspose_eq_transpose_of_trivial] using
        congrArg (fun M : Mat (ι:=ι) => M i j) hA.spectral_theorem
    _ = _ := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
        IsHermitian.eigenvectorUnitary_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, rankOne]
      change (∑ k, (hA.eigenvectorBasis k i*hA.eigenvalues k)*hA.eigenvectorBasis k j)=
        ∑ k, hA.eigenvalues k*(hA.eigenvectorBasis k i*hA.eigenvectorBasis k j)
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem quadraticValue_eq_inner (A : Mat (ι := ι)) (x : EuclideanSpace ℝ ι) :
    quadraticValue A x=inner ℝ x (Matrix.toEuclideanLin A x) := by
  simp only [quadraticValue, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, WithLp.equiv_symm_apply, PiLp.toLp_apply, WithLp.equiv_apply,
    Pi.star_apply, star_trivial,
    dotProduct, Matrix.mulVec]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem euclidean_norm_sq_gram (A : Mat (ι := ι)) (x : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanLin A x‖^2=quadraticValue (A.transpose*A) x := by
  rw [quadraticValue_eq_inner, ← real_inner_self_eq_norm_sq]
  let f := Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℝ) A
  have hmap : Matrix.toEuclideanLin (A.transpose*A) x=f.adjoint (f x) := by
    change Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℝ) (A.transpose*A) x=_
    have ht : A.transpose=star A := by simp only [star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial]
    rw [ht, map_mul, map_star]
    rfl
  rw [hmap]
  exact (ContinuousLinearMap.adjoint_inner_right f x (f x)).symm

theorem euclidean_norm_eq_of_gram_eq (A B : Mat (ι := ι))
    (h : A.transpose * A = B.transpose * B) (x : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanLin A x‖=‖Matrix.toEuclideanLin B x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [euclidean_norm_sq_gram, euclidean_norm_sq_gram, h]

theorem toEuclideanLin_mul_apply (A B : Mat (ι := ι)) (x : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanLin (A*B) x=
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) := by
  change Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℝ) (A*B) x=_
  rw [map_mul]
  rfl

theorem congruence_rankOne_sum (P : Mat (ι := ι))
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    (∑ k, rankOne (Matrix.toEuclideanLin P (b k)))=P*P.transpose := by
  simp_rw [rankOne_map]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, orthonormal_rankOne_sum, Matrix.mul_one]

theorem congruence_spectral_rankOne_sum (P K : Mat (ι := ι)) (hK : K.IsHermitian) :
    P*K*P.transpose=∑ k, hK.eigenvalues k •
      rankOne (Matrix.toEuclideanLin P (hK.eigenvectorBasis k)) := by
  nth_rw 1 [spectral_rankOne_sum K hK]
  simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, rankOne_map]

theorem toEuclideanLin_eigenvector (K : Mat (ι := ι)) (hK : K.IsHermitian) (i : ι) :
    Matrix.toEuclideanLin K (hK.eigenvectorBasis i)=
      hK.eigenvalues i • hK.eigenvectorBasis i := by
  apply PiLp.ext
  intro j
  simpa only [Matrix.toLpLin_apply, WithLp.equiv_symm_apply, PiLp.toLp_apply,
    WithLp.equiv_apply, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul] using
    congrFun (hK.mulVec_eigenvectorBasis i) j

theorem posSemidef_sqrt_isUnit (X : Mat (ι := ι)) (hX : X.PosSemidef) (hunit : IsUnit X) :
    IsUnit (CFC.sqrt X) := by
  apply (isUnit_pow_iff (by decide : (2:ℕ)≠0)).mp
  rwa [CFC.sq_sqrt X hX.nonneg]

def positiveKernel (L : Mat (ι := ι)) {X : Mat (ι := ι)} (hX : X.PosSemidef) : Mat (ι:=ι) :=
  (CFC.sqrt X)⁻¹ * gramRoot (L*X) * (CFC.sqrt X)⁻¹

theorem positiveKernel_posSemidef (L : Mat (ι := ι)) {X : Mat (ι := ι)}
    (hX : X.PosSemidef) : (positiveKernel L hX).PosSemidef := by
  simpa only [positiveKernel, ((CFC.sqrt_nonneg X).posSemidef.isHermitian.inv.eq :
    ((CFC.sqrt X)⁻¹)ᴴ=(CFC.sqrt X)⁻¹)] using
    (gramRoot_posSemidef (L*X)).conjTranspose_mul_mul_same ((CFC.sqrt X)⁻¹)

theorem positiveKernel_congruence (L : Mat (ι := ι)) {X : Mat (ι := ι)}
    (hX : X.PosSemidef) (hunit : IsUnit X) :
    (CFC.sqrt X) * positiveKernel L hX * (CFC.sqrt X)=gramRoot (L*X) := by
  have hp := (Matrix.isUnit_iff_isUnit_det _).mp (posSemidef_sqrt_isUnit X hX hunit)
  simp only [positiveKernel, Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hp]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ hp]

theorem positiveKernel_left (L : Mat (ι := ι)) {X : Mat (ι := ι)}
    (hX : X.PosSemidef) (hunit : IsUnit X) :
    (CFC.sqrt X) * positiveKernel L hX=gramRoot (L*X)*(CFC.sqrt X)⁻¹ := by
  have hp := (Matrix.isUnit_iff_isUnit_det _).mp (posSemidef_sqrt_isUnit X hX hunit)
  simp only [positiveKernel, Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hp]

theorem positiveKernel_gram_eq (L : Mat (ι := ι)) {X : Mat (ι := ι)}
    (hX : X.PosSemidef) (hunit : IsUnit X) :
    (gramRoot (L*X)*(CFC.sqrt X)⁻¹).transpose*(gramRoot (L*X)*(CFC.sqrt X)⁻¹)=
      (L*(CFC.sqrt X)).transpose*(L*(CFC.sqrt X)) := by
  have hp := (Matrix.isUnit_iff_isUnit_det _).mp (posSemidef_sqrt_isUnit X hX hunit)
  have htP : (CFC.sqrt X).transpose=(CFC.sqrt X) := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using (CFC.sqrt_nonneg X).posSemidef.isHermitian.eq
  have htQ : ((CFC.sqrt X)⁻¹).transpose=(CFC.sqrt X)⁻¹ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using (CFC.sqrt_nonneg X).posSemidef.isHermitian.inv.eq
  have htX : X.transpose=X := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hX.isHermitian.eq
  have hQX : (CFC.sqrt X)⁻¹*X=(CFC.sqrt X) := by
    calc
      (CFC.sqrt X)⁻¹*X=(CFC.sqrt X)⁻¹*((CFC.sqrt X)*(CFC.sqrt X)) := congrArg ((CFC.sqrt X)⁻¹*·) (CFC.sqrt_mul_sqrt_self X hX.nonneg).symm
      _ = (CFC.sqrt X) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul]
  have hXQ : X*(CFC.sqrt X)⁻¹=(CFC.sqrt X) := by
    calc
      X*(CFC.sqrt X)⁻¹=((CFC.sqrt X)*(CFC.sqrt X))*(CFC.sqrt X)⁻¹ := congrArg (·*(CFC.sqrt X)⁻¹) (CFC.sqrt_mul_sqrt_self X hX.nonneg).symm
      _ = (CFC.sqrt X) := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hp, Matrix.mul_one]
  calc
    _ = (CFC.sqrt X)⁻¹*(gramRoot (L*X)*gramRoot (L*X))*(CFC.sqrt X)⁻¹ := by
      simp only [Matrix.transpose_mul, htQ, gramRoot_transpose, Matrix.mul_assoc]
    _ = (CFC.sqrt X)⁻¹*((L*X).transpose*(L*X))*(CFC.sqrt X)⁻¹ := by rw [gramRoot_mul_self]
    _ = ((CFC.sqrt X)⁻¹*X)*(L.transpose*L)*(X*(CFC.sqrt X)⁻¹) := by
      simp only [Matrix.transpose_mul, htX, Matrix.mul_assoc]
    _ = (CFC.sqrt X)*(L.transpose*L)*(CFC.sqrt X) := by rw [hQX, hXQ]
    _ = _ := by simp only [Matrix.transpose_mul, htP, Matrix.mul_assoc]

def positiveTestVector (L : Mat (ι := ι)) {X : Mat (ι := ι)} (hX : X.PosSemidef)
    (i : ι) : EuclideanSpace ℝ ι :=
  Matrix.toEuclideanLin (CFC.sqrt X) ((positiveKernel_posSemidef L hX).isHermitian.eigenvectorBasis i)

theorem positiveTestVector_norm (L : Mat (ι := ι)) {X : Mat (ι := ι)}
    (hX : X.PosSemidef) (hunit : IsUnit X) (i : ι) :
    ‖Matrix.toEuclideanLin L (positiveTestVector L hX i)‖=
      (positiveKernel_posSemidef L hX).isHermitian.eigenvalues i *
        ‖positiveTestVector L hX i‖ := by
  let hK := positiveKernel_posSemidef L hX
  rw [positiveTestVector, ← toEuclideanLin_mul_apply]
  rw [← euclidean_norm_eq_of_gram_eq _ _ (positiveKernel_gram_eq L hX hunit)]
  rw [← positiveKernel_left L hX hunit, toEuclideanLin_mul_apply,
    toEuclideanLin_eigenvector, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (hK.eigenvalues_nonneg i)]

theorem positiveTestVector_rankOne_sum (L : Mat (ι := ι)) {X : Mat (ι := ι)}
    (hX : X.PosSemidef) : (∑ i, rankOne (positiveTestVector L hX i))=X := by
  simp only [positiveTestVector]
  rw [congruence_rankOne_sum]
  have ht : (CFC.sqrt X).transpose=(CFC.sqrt X) := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using (CFC.sqrt_nonneg X).posSemidef.isHermitian.eq
  rw [ht, (CFC.sqrt_mul_sqrt_self X hX.nonneg)]

theorem positiveTestVector_cost (L : Mat (ι := ι)) {X : Mat (ι := ι)}
    (hX : X.PosSemidef) (hunit : IsUnit X) :
    (∑ i, ‖Matrix.toEuclideanLin L (positiveTestVector L hX i)‖*
      ‖positiveTestVector L hX i‖)=Matrix.trace (gramRoot (L*X)) := by
  have hK := positiveKernel_posSemidef L hX
  have ht : (CFC.sqrt X).transpose=(CFC.sqrt X) := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using (CFC.sqrt_nonneg X).posSemidef.isHermitian.eq
  have hdec : gramRoot (L*X)=∑ i, hK.isHermitian.eigenvalues i •
      rankOne (positiveTestVector L hX i) := by
    calc
      gramRoot (L*X)=(CFC.sqrt X)*positiveKernel L hX*(CFC.sqrt X).transpose := by
        rw [ht, positiveKernel_congruence L hX hunit]
      _ = _ := congruence_spectral_rankOne_sum _ _ hK.isHermitian
  rw [hdec, Matrix.trace_sum]
  simp_rw [Matrix.trace_smul, smul_eq_mul, rankOne_trace, positiveTestVector_norm L hX hunit]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Actual cost-controlled rank-one decomposition, with no decomposition
or trace estimate assumed. The present theorem requires invertibility of
the source and test matrices; the boundary passage is separate. -/
theorem positive_test_rankOne_budget (L X : Mat (ι := ι)) (hLunit : IsUnit L)
    (hX : X.PosSemidef) (hXunit : IsUnit X) :
    ∃ v : ι → EuclideanSpace ℝ ι,
      (∑ i, rankOne (v i))=X ∧
      (∑ i, ‖Matrix.toEuclideanLin L (v i)‖*‖v i‖)≤dualOperatorNorm (L*X) := by
  refine ⟨positiveTestVector L hX, positiveTestVector_rankOne_sum L hX, ?_⟩
  rw [positiveTestVector_cost L hX hXunit]
  exact gramRoot_trace_le_dualOperatorNorm (L*X) (hLunit.mul hXunit)

theorem positive_trace_bound_isUnit (L S X : Mat (ι := ι)) (hLunit : IsUnit L)
    (hX : X.PosSemidef) (hXunit : IsUnit X) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ x : EuclideanSpace ℝ ι,
      |quadraticValue S x|≤D*‖Matrix.toEuclideanLin L x‖*‖x‖) :
    |tracePair X S|≤D*dualOperatorNorm (L*X) := by
  obtain ⟨v,hv,hcost⟩ := positive_test_rankOne_budget L X hLunit hX hXunit
  rw [tracePair_comm]
  change |traceFunctional S X|≤_
  conv_lhs => rw [← hv, map_sum]
  simp only [traceFunctional_apply, tracePair_rankOne]
  calc
    |∑ i, quadraticValue S (v i)|≤∑ i, |quadraticValue S (v i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, D*‖Matrix.toEuclideanLin L (v i)‖*‖v i‖ :=
      Finset.sum_le_sum fun i _ => hdom (v i)
    _ = D*(∑ i, ‖Matrix.toEuclideanLin L (v i)‖*‖v i‖) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcost hD

def traceFunctionalMap : Mat (ι:=ι) →ₗ[ℝ] (Mat (ι:=ι) →L[ℝ] ℝ) where
  toFun := traceFunctional
  map_add' A B := by
    ext Y
    simp [traceFunctional_apply, tracePair, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' r A := by
    ext Y
    simp [traceFunctional_apply, tracePair, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul]

theorem continuous_dualOperatorNorm : Continuous (dualOperatorNorm (ι:=ι)) := by
  letI : NormedAddCommGroup (Mat (ι:=ι) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  have hc : Continuous (traceFunctional (ι:=ι)) :=
    (traceFunctionalMap (ι:=ι)).toContinuousLinearMap.continuous
  unfold dualOperatorNorm
  exact (continuous_norm : Continuous (fun f : Mat (ι:=ι) →L[ℝ] ℝ => ‖f‖)).comp hc

def positiveRegularization (X : Mat (ι := ι)) (k : ℕ) : Mat (ι:=ι) :=
  X+(1/((k:ℝ)+1)) • (1:Mat (ι:=ι))

theorem positiveRegularization_posDef (X : Mat (ι := ι)) (hX : X.PosSemidef) (k : ℕ) :
    (positiveRegularization X k).PosDef := by
  change (X+_).PosDef
  apply Matrix.PosDef.posSemidef_add hX
  have hd : (Matrix.diagonal (fun _ : ι => 1/((k:ℝ)+1))).PosDef :=
    Matrix.PosDef.diagonal fun _ => by positivity
  convert hd using 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.diagonal_apply]
  split_ifs <;> simp

omit [Fintype ι] in
theorem positiveRegularization_tendsto (X : Mat (ι := ι)) :
    Filter.Tendsto (positiveRegularization X) Filter.atTop (nhds X) := by
  simpa only [positiveRegularization, zero_smul, add_zero] using!
    tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun k : ℕ => (1:ℝ)/((k:ℝ)+1)) Filter.atTop (nhds 0)).smul_const
        (1:Mat (ι:=ι)))

/-- The positive-test estimate includes singular PSD test matrices. -/
theorem positive_trace_bound_unit_source (L S X : Mat (ι := ι)) (hLunit : IsUnit L)
    (hX : X.PosSemidef) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ x : EuclideanSpace ℝ ι,
      |quadraticValue S x|≤D*‖Matrix.toEuclideanLin L x‖*‖x‖) :
    |tracePair X S|≤D*dualOperatorNorm (L*X) := by
  have hleft : Filter.Tendsto
      (fun k => |tracePair (positiveRegularization X k) S|) Filter.atTop
      (nhds |tracePair X S|) := by
    simpa only [tracePair_comm, traceFunctional_apply, Function.comp_def] using
      (traceFunctional S).continuous.abs.tendsto X |>.comp (positiveRegularization_tendsto X)
  have hright : Filter.Tendsto
      (fun k => D*dualOperatorNorm (L*positiveRegularization X k)) Filter.atTop
      (nhds (D*dualOperatorNorm (L*X))) := by
    exact (continuous_const.mul
      (continuous_dualOperatorNorm.comp (continuous_const.mul continuous_id))).tendsto X |>.comp
        (positiveRegularization_tendsto X)
  apply le_of_tendsto_of_tendsto hleft hright
  exact Filter.Eventually.of_forall fun k =>
    positive_trace_bound_isUnit L S (positiveRegularization X k) hLunit
      (positiveRegularization_posDef X hX k).posSemidef
      (positiveRegularization_posDef X hX k).isUnit hD hdom

theorem posSemidef_inner_nonneg (L : Mat (ι := ι)) (hL : L.PosSemidef)
    (x : EuclideanSpace ℝ ι) : (0:ℝ) ≤ inner ℝ x (Matrix.toEuclideanLin L x) := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    Equiv.apply_symm_apply, dotProduct_comm] using!
      hL.dotProduct_mulVec_nonneg ((WithLp.equiv 2 (ι→ℝ)) x)

theorem toEuclideanLin_add_scalar_one (L : Mat (ι := ι)) (t : ℝ) (x : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanLin (L+t • (1:Mat (ι:=ι))) x=Matrix.toEuclideanLin L x+t • x := by
  change Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℝ) (L+t • (1:Mat (ι:=ι))) x=_
  rw [map_add, map_smul, map_one]
  rfl

theorem norm_apply_le_posSemidef_shift (L : Mat (ι := ι)) (hL : L.PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) (x : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanLin L x‖≤‖Matrix.toEuclideanLin (L+t • (1:Mat (ι:=ι))) x‖ := by
  rw [toEuclideanLin_add_scalar_one]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    real_inner_smul_right]
  have hi := posSemidef_inner_nonneg L hL x
  rw [real_inner_comm] at hi
  nlinarith [norm_nonneg x]

/-- This positive-test theorem has no invertibility hypothesis. -/
theorem positive_trace_bound (L S X : Mat (ι := ι)) (hL : L.PosSemidef)
    (hX : X.PosSemidef) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ x : EuclideanSpace ℝ ι,
      |quadraticValue S x|≤D*‖Matrix.toEuclideanLin L x‖*‖x‖) :
    |tracePair X S|≤D*dualOperatorNorm (L*X) := by
  have ht (k : ℕ) : 0≤1/((k:ℝ)+1) := by positivity
  have hleft : Filter.Tendsto (fun _k : ℕ => |tracePair X S|) Filter.atTop
      (nhds |tracePair X S|) := tendsto_const_nhds
  have hright : Filter.Tendsto
      (fun k => D*dualOperatorNorm (positiveRegularization L k*X)) Filter.atTop
      (nhds (D*dualOperatorNorm (L*X))) := by
    exact (continuous_const.mul
      (continuous_dualOperatorNorm.comp (continuous_id.mul continuous_const))).tendsto L |>.comp
        (positiveRegularization_tendsto L)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro k
  apply positive_trace_bound_unit_source (positiveRegularization L k) S X
    (positiveRegularization_posDef L hL k).isUnit hX hD
  intro x
  exact (hdom x).trans (by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    apply mul_le_mul_of_nonneg_left _ hD
    exact norm_apply_le_posSemidef_shift L hL (ht k) x)

def spectralMatrix {A : Mat (ι := ι)} (hA : A.IsHermitian) (f : ℝ → ℝ) : Mat (ι:=ι) :=
  hA.eigenvectorUnitary.1 * Matrix.diagonal (f ∘ hA.eigenvalues) *
    hA.eigenvectorUnitary.1.transpose

theorem spectralMatrix_transpose {A : Mat (ι := ι)} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (spectralMatrix hA f).transpose=spectralMatrix hA f := by
  simp only [spectralMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

theorem spectralMatrix_id {A : Mat (ι := ι)} (hA : A.IsHermitian) :
    spectralMatrix hA id=A := by
  simpa only [spectralMatrix, Function.id_comp, RCLike.ofReal_real_eq_id,
    Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial] using hA.spectral_theorem.symm

theorem spectralMatrix_mul {A : Mat (ι := ι)} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    spectralMatrix hA f * spectralMatrix hA g=spectralMatrix hA (fun x => f x*g x) := by
  let Q := hA.eigenvectorUnitary.1
  have hQtQ : Q.transpose*Q=1 := by
    simpa only [Q, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  change (Q*_*Q.transpose)*(Q*_*Q.transpose)=Q*_*Q.transpose
  calc
    (Q*Matrix.diagonal (f ∘ hA.eigenvalues)*Q.transpose)*
        (Q*Matrix.diagonal (g ∘ hA.eigenvalues)*Q.transpose) =
      Q*(Matrix.diagonal (f ∘ hA.eigenvalues)*(Q.transpose*Q)*
        Matrix.diagonal (g ∘ hA.eigenvalues))*Q.transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hQtQ, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
      rfl

theorem spectralMatrix_sub {A : Mat (ι := ι)} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    spectralMatrix hA f-spectralMatrix hA g=spectralMatrix hA (fun x => f x-g x) := by
  unfold spectralMatrix
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  rfl

theorem spectralMatrix_neg {A : Mat (ι := ι)} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    -spectralMatrix hA f=spectralMatrix hA (fun x => -f x) := by
  unfold spectralMatrix
  change -(hA.eigenvectorUnitary.1*Matrix.diagonal (f ∘ hA.eigenvalues)*
    hA.eigenvectorUnitary.1.transpose)=hA.eigenvectorUnitary.1*
      Matrix.diagonal (fun i => -(f ∘ hA.eigenvalues) i)*hA.eigenvectorUnitary.1.transpose
  rw [← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]

theorem spectralMatrix_posSemidef {A : Mat (ι := ι)} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) : (spectralMatrix hA f).PosSemidef := by
  simpa only [spectralMatrix, conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosSemidef.diagonal (show 0≤f ∘ hA.eigenvalues from fun i => hf _)).mul_mul_conjTranspose_same
      hA.eigenvectorUnitary.1

theorem symmetric_projection_norm_le_one (P : Mat (ι := ι))
    (ht : P.transpose = P) (hP : P * P = P) : ‖P‖≤1 := by
  have hn := Matrix.l2_opNorm_conjTranspose_mul_self P
  simp only [conjTranspose_eq_transpose_of_trivial, ht, hP] at hn
  nlinarith [norm_nonneg P]

theorem spectralMatrix_indicator_norm_le_one {A : Mat (ι := ι)} (hA : A.IsHermitian)
    (p : ℝ → Prop) [DecidablePred p] :
    ‖spectralMatrix hA (fun x => if p x then 1 else 0)‖≤1 := by
  apply symmetric_projection_norm_le_one _ (spectralMatrix_transpose _ _)
  rw [spectralMatrix_mul]
  apply congrArg (spectralMatrix hA)
  funext x
  split_ifs <;> norm_num

theorem dualOperatorNorm_mul_le (A P : Mat (ι := ι)) :
    dualOperatorNorm (A*P)≤dualOperatorNorm A*‖P‖ := by
  apply (traceFunctional (A*P)).opNorm_le_bound (mul_nonneg (dualOperatorNorm_nonneg A) (norm_nonneg P))
  intro C
  have hp : tracePair (A*P) C=tracePair A (C*P.transpose) := by
    simp only [tracePair, Matrix.transpose_mul]
    rw [Matrix.trace_mul_cycle']
    rw [Matrix.mul_assoc]
  change |tracePair (A*P) C|≤_
  rw [hp]
  calc
    |tracePair A (C*P.transpose)|≤dualOperatorNorm A*‖C*P.transpose‖ :=
      tracePair_le_dualOperatorNorm _ _
    _ ≤ dualOperatorNorm A*(‖C‖*‖P.transpose‖) :=
      mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _) (dualOperatorNorm_nonneg A)
    _ = (dualOperatorNorm A*‖P‖)*‖C‖ := by
      have ht : ‖P.transpose‖=‖P‖ := by
        simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose P
      rw [ht]
      ring

theorem dualOperatorNorm_neg (A : Mat (ι := ι)) : dualOperatorNorm (-A)=dualOperatorNorm A := by
  change ‖traceFunctionalMap (-A)‖=‖traceFunctionalMap A‖
  rw [map_neg]
  exact norm_neg (traceFunctionalMap (ι:=ι) A)

def positivePart {X : Mat (ι := ι)} (hX : X.IsHermitian) : Mat (ι:=ι) :=
  spectralMatrix hX (fun t => max t 0)

def negativePart {X : Mat (ι := ι)} (hX : X.IsHermitian) : Mat (ι:=ι) :=
  spectralMatrix hX (fun t => max (-t) 0)

def positiveProjection {X : Mat (ι := ι)} (hX : X.IsHermitian) : Mat (ι:=ι) :=
  spectralMatrix hX (fun t => if 0<t then 1 else 0)

def negativeProjection {X : Mat (ι := ι)} (hX : X.IsHermitian) : Mat (ι:=ι) :=
  spectralMatrix hX (fun t => if t<0 then 1 else 0)

theorem positivePart_posSemidef {X : Mat (ι := ι)} (hX : X.IsHermitian) :
    (positivePart hX).PosSemidef := spectralMatrix_posSemidef hX _ fun _ => le_max_right _ _

theorem negativePart_posSemidef {X : Mat (ι := ι)} (hX : X.IsHermitian) :
    (negativePart hX).PosSemidef := spectralMatrix_posSemidef hX _ fun _ => le_max_right _ _

theorem spectral_parts_sub {X : Mat (ι := ι)} (hX : X.IsHermitian) :
    positivePart hX-negativePart hX=X := by
  rw [positivePart, negativePart, spectralMatrix_sub]
  have hf : (fun t : ℝ => max t 0-max (-t) 0)=id := by
    funext t
    by_cases ht : 0≤t
    · simp [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht)]
    · have ht' := le_of_not_ge ht
      simp [max_eq_right ht', max_eq_left (neg_nonneg.mpr ht')]
  rw [hf, spectralMatrix_id]

theorem mul_positiveProjection {X : Mat (ι := ι)} (hX : X.IsHermitian) :
    X*positiveProjection hX=positivePart hX := by
  calc
    X*positiveProjection hX=spectralMatrix hX id*positiveProjection hX := by
      rw [spectralMatrix_id]
    _ = spectralMatrix hX (fun t => t*(if 0<t then 1 else 0)) := spectralMatrix_mul _ _ _
    _ = positivePart hX := by
      apply congrArg (spectralMatrix hX)
      funext t
      by_cases ht : 0<t
      · simp [ht, max_eq_left ht.le]
      · simp [ht, max_eq_right (le_of_not_gt ht)]

theorem neg_mul_negativeProjection {X : Mat (ι := ι)} (hX : X.IsHermitian) :
    -(X*negativeProjection hX)=negativePart hX := by
  calc
    -(X*negativeProjection hX)=-(spectralMatrix hX id*negativeProjection hX) := by
      rw [spectralMatrix_id]
    _ = spectralMatrix hX (fun t => -(t*(if t<0 then 1 else 0))) := by
      rw [negativeProjection, spectralMatrix_mul, spectralMatrix_neg]
      rfl
    _ = negativePart hX := by
      apply congrArg (spectralMatrix hX)
      funext t
      by_cases ht : t<0
      · simp [ht, max_eq_left (neg_nonneg.mpr ht.le)]
      · simp [ht, max_eq_right (neg_nonpos.mpr (le_of_not_gt ht))]

theorem positivePart_dual_bound (L X : Mat (ι := ι)) (hX : X.IsHermitian) :
    dualOperatorNorm (L*positivePart hX)≤dualOperatorNorm (L*X) := by
  rw [← mul_positiveProjection hX, ← Matrix.mul_assoc]
  exact (dualOperatorNorm_mul_le _ _).trans (by
    exact mul_le_of_le_one_right (dualOperatorNorm_nonneg _) (spectralMatrix_indicator_norm_le_one hX _))

theorem negativePart_dual_bound (L X : Mat (ι := ι)) (hX : X.IsHermitian) :
    dualOperatorNorm (L*negativePart hX)≤dualOperatorNorm (L*X) := by
  rw [← neg_mul_negativeProjection hX, Matrix.mul_neg, dualOperatorNorm_neg, ← Matrix.mul_assoc]
  exact (dualOperatorNorm_mul_le _ _).trans (by
    exact mul_le_of_le_one_right (dualOperatorNorm_nonneg _) (spectralMatrix_indicator_norm_le_one hX _))

/-- Scalar quadratic domination gives every symmetric trace test, including
singular source and indefinite test matrices, with the required constant two. -/
theorem symmetric_trace_bound (L S X : Mat (ι := ι)) (hL : L.PosSemidef)
    (hX : X.IsHermitian) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ x : EuclideanSpace ℝ ι,
      |quadraticValue S x|≤D*‖Matrix.toEuclideanLin L x‖*‖x‖) :
    |tracePair X S|≤(2*D)*dualOperatorNorm (L*X) := by
  have hplus := positive_trace_bound L S (positivePart hX) hL
    (positivePart_posSemidef hX) hD hdom
  have hminus := positive_trace_bound L S (negativePart hX) hL
    (negativePart_posSemidef hX) hD hdom
  have hdec : tracePair X S=tracePair (positivePart hX) S-tracePair (negativePart hX) S := by
    simp only [tracePair_comm _ S]
    change traceFunctional S X=traceFunctional S (positivePart hX)-traceFunctional S (negativePart hX)
    rw [← map_sub, spectral_parts_sub]
  rw [hdec]
  calc
    |tracePair (positivePart hX) S-tracePair (negativePart hX) S|≤
        |tracePair (positivePart hX) S|+|tracePair (negativePart hX) S| := abs_sub _ _
    _ ≤ D*dualOperatorNorm (L*positivePart hX)+D*dualOperatorNorm (L*negativePart hX) :=
      add_le_add hplus hminus
    _ ≤ D*dualOperatorNorm (L*X)+D*dualOperatorNorm (L*X) :=
      add_le_add (mul_le_mul_of_nonneg_left (positivePart_dual_bound L X hX) hD)
        (mul_le_mul_of_nonneg_left (negativePart_dual_bound L X hX) hD)
    _ = _ := by ring

/-- Unconditional nonlinear bounded completion from the actual scalar
quadratic domination hypothesis. The matrix norm is Euclidean operator norm. -/
theorem exists_bounded_weighted_completion (L S : Mat (ι := ι))
    (hL : L.PosSemidef) (hS : S.transpose = S) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ x : EuclideanSpace ℝ ι,
      |quadraticValue S x|≤D*‖Matrix.toEuclideanLin L x‖*‖x‖) :
    ∃ C : Mat (ι:=ι), ‖C‖≤2*D ∧ (1/2:ℝ) • (L*C+C.transpose*L)=S := by
  have hLt : L.transpose=L := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hL.isHermitian.eq
  apply exists_explicit_matrix_completion_of_trace_tests L S hLt hS hD
  intro X hX
  apply symmetric_trace_bound L S X hL _ hD hdom
  simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using hX

/-- The same completion with its pointwise Euclidean norm bound, in the
form used by the nonlinear quadratic division step. -/
theorem exists_weighted_completion_apply_bound (L S : Mat (ι := ι))
    (hL : L.PosSemidef) (hS : S.transpose = S) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ x : EuclideanSpace ℝ ι,
      |quadraticValue S x|≤D*‖Matrix.toEuclideanLin L x‖*‖x‖) :
    ∃ C : Mat (ι:=ι), (1/2:ℝ) • (L*C+C.transpose*L)=S ∧
      ∀ x : EuclideanSpace ℝ ι, ‖Matrix.toEuclideanLin C x‖≤(2*D)*‖x‖ := by
  obtain ⟨C,hC,heq⟩ := exists_bounded_weighted_completion L S hL hS hD hdom
  refine ⟨C,heq,?_⟩
  intro x
  exact (euclidean_apply_le_operatorNorm C x).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg x))

end OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticTraceGeometry
