import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.MatrixSmoothing
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.HomogeneousSOSFromSphere

/-! Polynomial kernel means and the actual finite matrix-SOS smoothing
certificate. Sphere moment identities will be supplied by the normalized
sphere moment modules. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace MatrixKernelSmoothing

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory Matrix MvPolynomial
open MatrixSmoothing

abbrev P (n : ℕ) := Foundation.Polynomial n

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

def rootPolynomial {n : ℕ} (a : Ω → I→ℝ) (b : I → P n) (w : Ω) : P n :=
  ∑i, C (a w i)*b i

def weightedPolynomial {n : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (g : Ω → ℝ) : P n :=
  ∑i,∑j, C (∫w, a w i*a w j*g w ∂μ)*b i*b j

omit [DecidableEq I] in
theorem weightedPolynomial_degree {n s : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (hb : ∀ i, (b i).totalDegree ≤ s) (g : Ω → ℝ) :
    (weightedPolynomial μ a b g).totalDegree≤2*s := by
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  apply (totalDegree_mul _ _).trans
  have hi : (C (∫w, a w i*a w j*g w ∂μ)*b i).totalDegree≤s :=
    (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using hb i)
  simpa only [two_mul] using Nat.add_le_add hi (hb j)

omit [DecidableEq I] in
theorem weightedPolynomial_eval {n : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (g : Ω → ℝ)
    (hg : ∀ i j, Integrable (fun w ↦ a w i * a w j * g w) μ) (x : Fin n → ℝ) :
    eval x (weightedPolynomial μ a b g)=
      ∫w, eval x (rootPolynomial a b w)^2*g w ∂μ := by
  have he := entryIntegral_polynomialMatrix_eval μ
    (fun w i j ↦ a w i*a w j*g w) hg (fun i (_ : Fin 1) ↦ b i) x 0 0
  change eval x (weightedPolynomial μ a b g)=_ at he
  rw [he]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  simp only [rootPolynomial,eval_sum,eval_mul,eval_C,pow_two,Fintype.sum_mul_sum,Finset.sum_mul]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def meanMatrix {n d e : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ) (b : I → P n)
    (F : Ω → Matrix (Fin d) (Fin e) ℝ) : Matrix (Fin d) (Fin e) (P n) :=
  fun u v ↦ weightedPolynomial μ a b (fun w ↦ F w u v)

omit [DecidableEq I] in
theorem meanMatrix_degree {n d e s : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (hb : ∀ i, (b i).totalDegree ≤ s)
    (F : Ω → Matrix (Fin d) (Fin e) ℝ) (u : Fin d) (v : Fin e) :
    (meanMatrix μ a b F u v).totalDegree≤2*s := weightedPolynomial_degree μ a b hb _

omit [DecidableEq I] in
theorem meanMatrix_eval {n d e : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ) (b : I → P n)
    (F : Ω → Matrix (Fin d) (Fin e) ℝ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ)
    (x : Fin n → ℝ) (u : Fin d) (v : Fin e) :
    eval x (meanMatrix μ a b F u v)=
      ∫w, eval x (rootPolynomial a b w)^2*F w u v ∂μ :=
  weightedPolynomial_eval μ a b _ (fun i j ↦ hF i j u v) x

def schurBasis {n d e : ℕ} (b : I → P n) (M : Matrix (Fin d) (Fin e) (P n)) :
    I→(Fin d ⊕ Fin e)→Fin d→P n :=
  fun i p u ↦ Sum.elim (fun j ↦ if j=u then b i else 0) (fun k ↦ -b i*M u k) p

omit [Fintype I] [DecidableEq I] in
theorem schurBasis_degree {n d e s : ℕ} (b : I → P n)
    (hb : ∀ i, (b i).totalDegree ≤ s) (M : Matrix (Fin d) (Fin e) (P n))
    (hM : ∀ u k, (M u k).totalDegree ≤ 2 * s) (i : I) (p : Fin d ⊕ Fin e) (u : Fin d) :
    (schurBasis b M i p u).totalDegree≤3*s := by
  cases p with
  | inl j =>
    change (if j=u then b i else 0).totalDegree≤3*s
    split_ifs
    · exact (hb i).trans (by omega)
    · simp
  | inr k =>
    change (-b i*M u k).totalDegree≤3*s
    have hneg : (-b i).totalDegree≤s := by simpa using hb i
    exact (totalDegree_mul _ _).trans (by have hh := Nat.add_le_add hneg (hM u k);omega)

section BilinearIdentities

variable {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem bilinear_congruence (A : Matrix J I ℝ) (D : Matrix J J ℝ) (z w : I → ℝ) :
    dotProduct z ((A.transpose*D*A)*ᵥw)=dotProduct (A*ᵥz) (D*ᵥ(A*ᵥw)) := by
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

omit [DecidableEq I] in
theorem coefficientLift_mulVec (a b : I → ℝ) (t : J → ℝ) :
    MatrixSmoothing.coefficientLift a *ᵥ(fun p : I×J ↦ b p.1*t p.2)=
      (∑i, a i*b i) • t := by
  funext u
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,MatrixSmoothing.coefficientLift,
    Pi.smul_apply,smul_eq_mul]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

def schurTest {d e : ℕ} (M : Matrix (Fin d) (Fin e) ℝ) (u : Fin d) : Fin d ⊕ Fin e→ℝ :=
  Sum.elim (fun j ↦ if j=u then 1 else 0) (fun k ↦ -M u k)

omit [Fintype I] [DecidableEq I] in
theorem schurBasis_eval {n d e : ℕ} (b : I → P n) (M : Matrix (Fin d) (Fin e) (P n))
    (x : Fin n → ℝ) (i : I) (p : Fin d ⊕ Fin e) (u : Fin d) :
    eval x (schurBasis b M i p u)=eval x (b i)*schurTest (fun j k ↦ eval x (M j k)) u p := by
  cases p with
  | inl j => by_cases h:j=u <;> simp [schurBasis,schurTest,h]
  | inr k => simp [schurBasis,schurTest]

theorem schurTest_contraction {d e : ℕ} (B : ℝ) (F M : Matrix (Fin d) (Fin e) ℝ)
    (u v : Fin d) :
    dotProduct (schurTest M u) (MatrixSmoothing.schurField B F *ᵥ schurTest M v)=
      B^2*(if u=v then 1 else 0)-
        (∑k, F u k*M v k)-(∑k, M u k*F v k)+(∑k, M u k*M v k) := by
  simp [dotProduct,Matrix.mulVec,Fintype.sum_sum_type,MatrixSmoothing.schurField,
    schurTest,Matrix.fromBlocks,Matrix.smul_apply,Matrix.one_apply,
    Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    eq_comm,mul_comm,mul_left_comm,mul_assoc]
  simp only [mul_add,Finset.sum_add_distrib,mul_neg,Finset.sum_neg_distrib]
  simp only [mul_comm]
  ring

end BilinearIdentities

section KernelCertificate

variable {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq I] in
theorem kernelPSDMatrix_separable_eval {n d : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (D : Ω → Matrix J J ℝ)
    (hD : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * D w u v) μ)
    (b : I → J → Fin d → P n) (x : Fin n → ℝ) (c : I → ℝ) (t : Fin d → J→ℝ)
    (hsep : ∀ i j u, eval x (b i j u) = c i * t u j) (u v : Fin d) :
    eval x (kernelPSDMatrix μ a D b u v)=
      ∫w, (∑i, a w i*c i)^2*dotProduct (t u) (D w *ᵥ t v) ∂μ := by
  let A := fun w ↦ MatrixSmoothing.coefficientLift (J:=J) (a w)
  have hentry (p q : I×J) : Integrable (fun w ↦ ((A w).transpose*D w*A w) p q) μ := by
    rcases p with ⟨i,j⟩
    rcases q with ⟨k,l⟩
    simpa only [A,coefficientLift_entry] using hD i k j l
  have he := entryIntegral_polynomialMatrix_eval μ _ hentry (fun p ↦ b p.1 p.2) x u v
  change eval x (kernelPSDMatrix μ a D b u v)=_ at he
  rw [he]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  dsimp only
  have hsum : (∑p : I×J,∑q : I×J,
      ((A w).transpose*D w*A w) p q*eval x (b p.1 p.2 u)*eval x (b q.1 q.2 v))=
      dotProduct (fun p : I×J ↦ eval x (b p.1 p.2 u))
        (((A w).transpose*D w*A w)*ᵥ(fun p : I×J ↦ eval x (b p.1 p.2 v))) := by
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hsum,bilinear_congruence]
  simp only [hsep,A,coefficientLift_mulVec,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,
    smul_eq_mul,pow_two]
  ring

omit [Fintype I] [DecidableEq I] in
theorem schurField_integrable {d e : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (F : Ω → Matrix (Fin d) (Fin e) ℝ) (B : ℝ)
    (ha : ∀ i j, Integrable (fun w ↦ a w i * a w j) μ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ)
    (i j : I) (p q : Fin d ⊕ Fin e) :
    Integrable (fun w ↦ a w i*a w j*MatrixSmoothing.schurField B (F w) p q) μ := by
  cases p with
  | inl u =>
    cases q with
    | inl v =>
      simpa only [MatrixSmoothing.schurField,Matrix.fromBlocks_apply₁₁] using
        (ha i j).mul_const ((B^2 • (1:Matrix (Fin d) (Fin d) ℝ)) u v)
    | inr v => exact hF i j u v
  | inr u =>
    cases q with
    | inl v => exact hF i j v u
    | inr v =>
      simpa only [MatrixSmoothing.schurField,Matrix.fromBlocks_apply₂₂] using
        (ha i j).mul_const ((1:Matrix (Fin e) (Fin e) ℝ) u v)

def smoothingCertificate {n d e : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (F : Ω → Matrix (Fin d) (Fin e) ℝ) (B : ℝ) :
    Matrix (Fin d) (Fin d) (P n) :=
  kernelPSDMatrix μ a (fun w ↦ MatrixSmoothing.schurField B (F w))
    (schurBasis b (meanMatrix μ a b F))

theorem smoothingCertificate_boundedMatrixSOS {n d e s : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (hb : ∀ i, (b i).totalDegree ≤ s) (F : Ω → Matrix (Fin d) (Fin e) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hnorm : ∀ w, ‖F w‖ ≤ B)
    (ha : ∀ i j, Integrable (fun w ↦ a w i * a w j) μ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ) :
    FiniteMatrixVariance.BoundedMatrixSOS (3*s) (smoothingCertificate μ a b F B) := by
  apply kernelPSDMatrix_boundedMatrixSOS
  · exact schurField_integrable μ a F B ha hF
  · intro w
    exact schurField_posSemidef (F w) hB (hnorm w)
  · exact schurBasis_degree b hb _ (meanMatrix_degree μ a b hb F)

omit [DecidableEq I] in
theorem root_square_mul_integrable {n : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (g : Ω → ℝ)
    (hg : ∀ i j, Integrable (fun w ↦ a w i * a w j * g w) μ) (x : Fin n → ℝ) :
    Integrable (fun w ↦ eval x (rootPolynomial a b w)^2*g w) μ := by
  have hterm (i j : I) : Integrable
      (fun w ↦ a w i*a w j*g w*eval x (b i)*eval x (b j)) μ :=
    ((hg i j).mul_const _).mul_const _
  have hinner (i : I) : Integrable
      (fun w ↦ ∑j, a w i*a w j*g w*eval x (b i)*eval x (b j)) μ :=
    integrable_finsetSum _ fun j _ ↦ hterm i j
  have hs := integrable_finsetSum Finset.univ (fun i _ ↦ hinner i)
  convert hs using 1
  funext w
  simp only [rootPolynomial,eval_sum,eval_mul,eval_C,pow_two,Fintype.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq J] in
theorem entryIntegral_bilinear (μ : Measure Ω) (D : Ω → Matrix J J ℝ)
    (hD : ∀ i j, Integrable (fun w ↦ D w i j) μ) (z v : J → ℝ) :
    dotProduct z (entryIntegral μ D *ᵥ v)=∫w, dotProduct z (D w *ᵥ v) ∂μ := by
  have hterm (i j : J) : Integrable (fun w ↦ z i*(D w i j*v j)) μ :=
    ((hD i j).mul_const (v j)).const_mul (z i)
  have hinner (i : J) : Integrable (fun w ↦ ∑j, z i*(D w i j*v j)) μ :=
    integrable_finsetSum _ fun j _ ↦ hterm i j
  simp only [dotProduct,Matrix.mulVec,entryIntegral]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hinner i)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hterm _ j),integral_const_mul,integral_mul_const]

omit [DecidableEq I] in
theorem normalized_schur_integral {n d e : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (F : Ω → Matrix (Fin d) (Fin e) ℝ) (B : ℝ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ)
    (x : Fin n → ℝ) (hmass : (∫ w, eval x (rootPolynomial a b w) ^ 2 ∂μ) = 1) :
    entryIntegral μ (fun w ↦ eval x (rootPolynomial a b w)^2 • MatrixSmoothing.schurField B (F w))=
      MatrixSmoothing.schurField B (fun u v ↦ eval x (meanMatrix μ a b F u v)) := by
  apply Matrix.ext
  intro p q
  cases p with
  | inl u =>
    cases q with
    | inl v =>
      change (∫w, eval x (rootPolynomial a b w)^2*((B^2 • (1:Matrix (Fin d) (Fin d) ℝ)) u v) ∂μ)=_
      rw [integral_mul_const,hmass,one_mul]
      rfl
    | inr v =>
      exact (meanMatrix_eval μ a b F hF x u v).symm
  | inr u =>
    cases q with
    | inl v => exact (meanMatrix_eval μ a b F hF x v u).symm
    | inr v =>
      change (∫w, eval x (rootPolynomial a b w)^2*((1:Matrix (Fin e) (Fin e) ℝ) u v) ∂μ)=_
      rw [integral_mul_const,hmass,one_mul]
      rfl

omit [DecidableEq I] in
/-- Exact normalized smoothing inequality as an actual finite polynomial
matrix SOS on every normalization point. Its roots have degree at most3s. -/
theorem smoothingCertificate_eval {n d e : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (F : Ω → Matrix (Fin d) (Fin e) ℝ) (B : ℝ)
    (ha : ∀ i j, Integrable (fun w ↦ a w i * a w j) μ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ)
    (x : Fin n → ℝ) (hmass : (∫ w, eval x (rootPolynomial a b w) ^ 2 ∂μ) = 1)
    (u v : Fin d) :
    eval x (smoothingCertificate μ a b F B u v)=
      B^2*(if u=v then 1 else 0)-
        ∑k, eval x (meanMatrix μ a b F u k)*eval x (meanMatrix μ a b F v k) := by
  let M : Matrix (Fin d) (Fin e) ℝ := fun i k ↦ eval x (meanMatrix μ a b F i k)
  let D := fun w ↦ MatrixSmoothing.schurField B (F w)
  let t := fun i ↦ schurTest M i
  have he := kernelPSDMatrix_separable_eval μ a D (schurField_integrable μ a F B ha hF)
    (schurBasis b (meanMatrix μ a b F)) x (fun i ↦ eval x (b i)) t
    (schurBasis_eval b (meanMatrix μ a b F) x) u v
  have hcoef : ∀w, (∑i, a w i*eval x (b i))^2=eval x (rootPolynomial a b w)^2 := by
    intro w
    simp [rootPolynomial]
  simp_rw [hcoef] at he
  have hentry (p q : Fin d ⊕ Fin e) : Integrable
      (fun w ↦ (eval x (rootPolynomial a b w)^2 • D w) p q) μ := by
    exact root_square_mul_integrable μ a b _ (fun i j ↦ schurField_integrable μ a F B ha hF i j p
      q) x
  have hi := entryIntegral_bilinear μ (fun w ↦ eval x (rootPolynomial a b w)^2 • D w) hentry (t u)
    (t v)
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul] at hi
  change eval x (smoothingCertificate μ a b F B u v)=_ at he
  rw [he,←hi]
  rw [show entryIntegral μ (fun w ↦ eval x (rootPolynomial a b w)^2 • D w)=
    MatrixSmoothing.schurField B M from normalized_schur_integral μ a b F B hF x hmass]
  rw [schurTest_contraction]
  dsimp only [M]
  ring

theorem exists_smoothed_matrix_sphereSOS {n d e s : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (b : I → P n) (hb : ∀ i, (b i).totalDegree ≤ s) (F : Ω → Matrix (Fin d) (Fin e) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hnorm : ∀ w, ‖F w‖ ≤ B)
    (ha : ∀ i j, Integrable (fun w ↦ a w i * a w j) μ)
    (hF : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * F w u v) μ)
    (hmass : ∀ x ∈ Foundation.unitSphere n, (∫ w, eval x (rootPolynomial a b w) ^ 2 ∂μ) = 1) :
    ∃ N : Matrix (Fin d) (Fin d) (P n), FiniteMatrixVariance.BoundedMatrixSOS (3*s) N ∧
      ∀x∈Foundation.unitSphere n,∀u v,eval x (N u v)=
        B^2*(if u=v then 1 else 0)-
          ∑k, eval x (meanMatrix μ a b F u k)*eval x (meanMatrix μ a b F v k) := by
  exact ⟨smoothingCertificate μ a b F B,
    smoothingCertificate_boundedMatrixSOS μ a b hb F hB hnorm ha hF,
    fun x hx u v ↦ smoothingCertificate_eval μ a b F B ha hF x (hmass x hx) u v⟩

end KernelCertificate

end MatrixKernelSmoothing
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
