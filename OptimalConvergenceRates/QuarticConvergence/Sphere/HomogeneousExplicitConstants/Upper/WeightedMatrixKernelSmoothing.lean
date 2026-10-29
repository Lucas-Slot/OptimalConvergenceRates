import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.MatrixKernelSmoothing

/-! Matrix smoothing with a variable top budget. The actual polynomial
average of B(w)^2 is retained; no coordinate-block radius is replaced by1. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace WeightedMatrixKernelSmoothing

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory Matrix MvPolynomial MatrixSmoothing
open MatrixKernelSmoothing

abbrev P (n : ℕ) := Foundation.Polynomial n
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem schurField_integrable_variable {d e : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (F : Ω → Matrix (Fin d) (Fin e) ℝ) (B : Ω → ℝ)
    (ha : ∀ i j, Integrable (fun w ↦ a w i * a w j) μ)
    (hB : ∀ i j, Integrable (fun w ↦ a w i * a w j * (B w) ^ 2) μ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ)
    (i j : I) (p q : Fin d ⊕ Fin e) :
    Integrable (fun w ↦ a w i*a w j*schurField (B w) (F w) p q) μ := by
  cases p with
  | inl u =>
    cases q with
    | inl v =>
      simpa only [schurField,Matrix.fromBlocks_apply₁₁,Matrix.smul_apply,smul_eq_mul,mul_assoc]
        using
        (hB i j).mul_const ((1:Matrix (Fin d) (Fin d) ℝ) u v)
    | inr v => exact hF i j u v
  | inr u =>
    cases q with
    | inl v => exact hF i j v u
    | inr v =>
      simpa only [schurField,Matrix.fromBlocks_apply₂₂] using
        (ha i j).mul_const ((1:Matrix (Fin e) (Fin e) ℝ) u v)

def topPolynomial {n : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ) (b : I → P n) (B : Ω → ℝ) : P n :=
  weightedPolynomial μ a b (fun w ↦ (B w)^2)

def certificate {n d e : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ) (b : I → P n)
    (F : Ω → Matrix (Fin d) (Fin e) ℝ) (B : Ω → ℝ) : Matrix (Fin d) (Fin d) (P n) :=
  kernelPSDMatrix μ a (fun w ↦ schurField (B w) (F w))
    (schurBasis b (MatrixKernelSmoothing.meanMatrix μ a b F))

theorem certificate_boundedMatrixSOS {n d e s : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (hb : ∀ i, (b i).totalDegree ≤ s) (F : Ω → Matrix (Fin d) (Fin e) ℝ)
    (B : Ω → ℝ) (hBnonneg : ∀ w, 0 ≤ B w) (hnorm : ∀ w, ‖F w‖ ≤ B w)
    (ha : ∀ i j, Integrable (fun w ↦ a w i * a w j) μ)
    (hB : ∀ i j, Integrable (fun w ↦ a w i * a w j * (B w) ^ 2) μ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ) :
    FiniteMatrixVariance.BoundedMatrixSOS (3*s) (certificate μ a b F B) := by
  apply kernelPSDMatrix_boundedMatrixSOS
  · exact schurField_integrable_variable μ a F B ha hB hF
  · intro w
    exact schurField_posSemidef (F w) (hBnonneg w) (hnorm w)
  · exact schurBasis_degree b hb _ (meanMatrix_degree μ a b hb F)

omit [DecidableEq I] in
theorem topPolynomial_nonnegative {n : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (B : Ω → ℝ)
    (hB : ∀ i j, Integrable (fun w ↦ a w i * a w j * (B w) ^ 2) μ) (x : Fin n → ℝ) :
    0≤eval x (topPolynomial μ a b B) := by
  rw [topPolynomial,weightedPolynomial_eval μ a b _ hB x]
  exact integral_nonneg fun w ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)

omit [DecidableEq I] in
theorem normalized_schur_integral_variable {n d e : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (F : Ω → Matrix (Fin d) (Fin e) ℝ) (B : Ω → ℝ)
    (hB : ∀ i j, Integrable (fun w ↦ a w i * a w j * (B w) ^ 2) μ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ)
    (x : Fin n → ℝ) (hmass : (∫ w, eval x (rootPolynomial a b w) ^ 2 ∂μ) = 1) :
    entryIntegral μ (fun w ↦ eval x (rootPolynomial a b w)^2 • schurField (B w) (F w))=
      schurField (Real.sqrt (eval x (topPolynomial μ a b B)))
        (fun u v ↦ eval x (MatrixKernelSmoothing.meanMatrix μ a b F u v)) := by
  have hsqrt := Real.sq_sqrt (topPolynomial_nonnegative μ a b B hB x)
  apply Matrix.ext
  intro p q
  cases p with
  | inl u =>
    cases q with
    | inl v =>
      change (∫w, eval x (rootPolynomial a b w)^2*((B w)^2*((1:Matrix (Fin d) (Fin d) ℝ) u v)) ∂μ)=_
      simp_rw [←mul_assoc]
      rw [integral_mul_const]
      have hv := weightedPolynomial_eval μ a b (fun w ↦ (B w)^2) hB x
      rw [←hv]
      change eval x (topPolynomial μ a b B)*_=Real.sqrt (eval x (topPolynomial μ a b B))^2*_
      rw [hsqrt]
    | inr v => exact (meanMatrix_eval μ a b F hF x u v).symm
  | inr u =>
    cases q with
    | inl v => exact (meanMatrix_eval μ a b F hF x v u).symm
    | inr v =>
      change (∫w, eval x (rootPolynomial a b w)^2*((1:Matrix (Fin e) (Fin e) ℝ) u v) ∂μ)=_
      rw [integral_mul_const,hmass,one_mul]
      rfl

omit [DecidableEq I] in
theorem certificate_eval {n d e : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (F : Ω → Matrix (Fin d) (Fin e) ℝ) (B : Ω → ℝ)
    (ha : ∀ i j, Integrable (fun w ↦ a w i * a w j) μ)
    (hB : ∀ i j, Integrable (fun w ↦ a w i * a w j * (B w) ^ 2) μ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ)
    (x : Fin n → ℝ) (hmass : (∫ w, eval x (rootPolynomial a b w) ^ 2 ∂μ) = 1)
    (u v : Fin d) :
    eval x (certificate μ a b F B u v)=
      eval x (topPolynomial μ a b B)*(if u=v then 1 else 0)-
        ∑k, eval x (MatrixKernelSmoothing.meanMatrix μ a b F u k)*
          eval x (MatrixKernelSmoothing.meanMatrix μ a b F v k) := by
  let M : Matrix (Fin d) (Fin e) ℝ := fun i k ↦ eval x (MatrixKernelSmoothing.meanMatrix μ a b F i
    k)
  let D := fun w ↦ schurField (B w) (F w)
  let t := fun i ↦ schurTest M i
  have he := kernelPSDMatrix_separable_eval μ a D (schurField_integrable_variable μ a F B ha hB hF)
    (schurBasis b (MatrixKernelSmoothing.meanMatrix μ a b F)) x (fun i ↦ eval x (b i)) t
    (schurBasis_eval b (MatrixKernelSmoothing.meanMatrix μ a b F) x) u v
  have hcoef : ∀w, (∑i, a w i*eval x (b i))^2=eval x (rootPolynomial a b w)^2 := by
    intro w
    simp [rootPolynomial]
  simp_rw [hcoef] at he
  have hentry (p q : Fin d ⊕ Fin e) : Integrable
      (fun w ↦ (eval x (rootPolynomial a b w)^2 • D w) p q) μ := by
    exact root_square_mul_integrable μ a b _
      (fun i j ↦ schurField_integrable_variable μ a F B ha hB hF i j p q) x
  have hi := entryIntegral_bilinear μ (fun w ↦ eval x (rootPolynomial a b w)^2 • D w) hentry (t u)
    (t v)
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul] at hi
  change eval x (certificate μ a b F B u v)=_ at he
  rw [he,←hi]
  rw [show entryIntegral μ (fun w ↦ eval x (rootPolynomial a b w)^2 • D w)=
      schurField (Real.sqrt (eval x (topPolynomial μ a b B))) M from
        normalized_schur_integral_variable μ a b F B hB hF x hmass]
  rw [schurTest_contraction,Real.sq_sqrt (topPolynomial_nonnegative μ a b B hB x)]
  dsimp only [M]
  ring

theorem exists_weighted_matrix_sphereSOS {n d e s : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (hb : ∀ i, (b i).totalDegree ≤ s) (F : Ω → Matrix (Fin d) (Fin e) ℝ)
    (B : Ω → ℝ) (hBnonneg : ∀ w, 0 ≤ B w) (hnorm : ∀ w, ‖F w‖ ≤ B w)
    (ha : ∀ i j, Integrable (fun w ↦ a w i * a w j) μ)
    (hB : ∀ i j, Integrable (fun w ↦ a w i * a w j * (B w) ^ 2) μ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ)
    (hmass : ∀ x ∈ Foundation.unitSphere n, (∫ w, eval x (rootPolynomial a b w) ^ 2 ∂μ) = 1) :
    ∃ N : Matrix (Fin d) (Fin d) (P n), FiniteMatrixVariance.BoundedMatrixSOS (3*s) N ∧
      ∀x∈Foundation.unitSphere n,∀u v,eval x (N u v)=
        eval x (topPolynomial μ a b B)*(if u=v then 1 else 0)-
          ∑k,eval x (MatrixKernelSmoothing.meanMatrix μ a b F u k)*
            eval x (MatrixKernelSmoothing.meanMatrix μ a b F v k) := by
  exact ⟨certificate μ a b F B,certificate_boundedMatrixSOS μ a b hb F B hBnonneg hnorm ha hB hF,
    fun x hx u v ↦ certificate_eval μ a b F B ha hB hF x (hmass x hx) u v⟩

end WeightedMatrixKernelSmoothing
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
