import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.WeightedQuadraticSelection
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.FiniteMatrixVariance

/-! Actual finite Gram compression of polynomial matrix square integrals.
Integrability is stated explicitly; the square family and its finite
compressed roots are constructed, rather than supplied as an SOS premise. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace MatrixSmoothing

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open MeasureTheory Matrix MvPolynomial
open FiniteMatrixVariance

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

def coefficientGram (μ : Measure Ω) (f : Ω → I→ℝ) : Matrix I I ℝ :=
  fun i j ↦ ∫w, f w i*f w j ∂μ

omit [DecidableEq I] in
theorem coefficientGram_quadratic (μ : Measure Ω) (f : Ω → I→ℝ)
    (hf : ∀ i j, Integrable (fun w ↦ f w i * f w j) μ) (z : I → ℝ) :
    dotProduct (star z) (coefficientGram μ f *ᵥ z)=
      ∫w, (∑i, z i*f w i)^2 ∂μ := by
  have hterm (i j : I) : Integrable (fun w ↦ (z i*f w i)*(z j*f w j)) μ := by
    have hh := ((hf i j).const_mul (z i)).mul_const (z j)
    convert hh using 1
    ext w
    ring
  have hinner (i : I) : Integrable (fun w ↦ ∑j, (z i*f w i)*(z j*f w j)) μ :=
    integrable_finsetSum _ fun j _ ↦ hterm i j
  simp only [pow_two,Fintype.sum_mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hinner i)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hterm _ j)]
  simp only [dotProduct,Pi.star_apply,star_trivial,Matrix.mulVec,coefficientGram]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have heq : (fun w ↦ (z i*f w i)*(z j*f w j))=
      (fun w ↦ z i*(f w i*f w j)*z j) := by funext w;ring
  rw [heq,integral_mul_const,integral_const_mul]
  ring

omit [DecidableEq I] in
theorem coefficientGram_posSemidef (μ : Measure Ω) (f : Ω → I→ℝ)
    (hf : ∀ i j, Integrable (fun w ↦ f w i * f w j) μ) :
    (coefficientGram μ f).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    change (∫w, f w j*f w i ∂μ)=∫w, f w i*f w j ∂μ
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w ↦ mul_comm _ _
  · intro z
    rw [coefficientGram_quadratic μ f hf]
    exact integral_nonneg fun w ↦ sq_nonneg _

abbrev P (n : ℕ) := Foundation.Polynomial n

def gramPolynomialMatrix {n d : ℕ} (G : Matrix I I ℝ)
    (b : I → Fin d → P n) : Matrix (Fin d) (Fin d) (P n) :=
  fun u v ↦ ∑i, ∑j, C (G i j)*b i u*b j v

def compressedRoot {n d : ℕ} (H : Matrix I I ℝ)
    (b : I → Fin d → P n) (k : I) : Fin d→P n :=
  fun u ↦ ∑i, C (H i k)*b i u

omit [DecidableEq I] in
theorem gramPolynomial_factor {n d : ℕ} (G H : Matrix I I ℝ)
    (hG : G = H * H.transpose) (b : I → Fin d → P n) :
    gramPolynomialMatrix G b=∑k, outer (compressedRoot H b k) := by
  apply Matrix.ext
  intro u v
  simp only [gramPolynomialMatrix,hG,Matrix.mul_apply,Matrix.transpose_apply,
    map_sum,map_mul,Matrix.sum_apply,outer,compressedRoot]
  simp_rw [Finset.sum_mul]
  rw [triple_sum_cycle]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq I] in
theorem compressedRoot_degree {n d r : ℕ} (H : Matrix I I ℝ)
    (b : I → Fin d → P n) (hb : ∀ i u, (b i u).totalDegree ≤ r) (k : I) (u : Fin d) :
    (compressedRoot H b k u).totalDegree≤r := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using hb i u)

/-- Constant PSD coefficient Gram matrices are actually factored into
finite polynomial vector roots with the original degree bound. -/
theorem gramPolynomial_boundedMatrixSOS {n d r : ℕ} (G : Matrix I I ℝ)
    (hG : G.PosSemidef) (b : I → Fin d → P n) (hb : ∀ i u, (b i u).totalDegree ≤ r) :
    BoundedMatrixSOS r (gramPolynomialMatrix G b) := by
  let H := CFC.sqrt G
  have ht : H.transpose=H := by
    simpa only [H,Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg G).posSemidef.isHermitian.eq
  have hfactor : G=H*H.transpose := by
    rw [ht]
    exact (CFC.sqrt_mul_sqrt_self G hG.nonneg).symm
  rw [gramPolynomial_factor G H hfactor]
  exact BoundedMatrixSOS.of_family _ (compressedRoot_degree H b hb)

def squareIntegralMatrix {n d : ℕ} (μ : Measure Ω) (f : Ω → I→ℝ)
    (b : I → Fin d → P n) : Matrix (Fin d) (Fin d) (P n) :=
  gramPolynomialMatrix (coefficientGram μ f) b

omit [DecidableEq I] in
theorem squareIntegralMatrix_eval {n d : ℕ} (μ : Measure Ω) (f : Ω → I→ℝ)
    (hf : ∀ i j, Integrable (fun w ↦ f w i * f w j) μ)
    (b : I → Fin d → P n) (x : Fin n → ℝ) (u v : Fin d) :
    eval x (squareIntegralMatrix μ f b u v)=
      ∫w, (∑i, f w i*eval x (b i u))*(∑j, f w j*eval x (b j v)) ∂μ := by
  have hterm (i j : I) : Integrable
      (fun w ↦ (f w i*eval x (b i u))*(f w j*eval x (b j v))) μ := by
    have hh := ((hf i j).mul_const (eval x (b i u))).mul_const (eval x (b j v))
    convert hh using 1
    ext w
    ring
  have hinner (i : I) : Integrable
      (fun w ↦ ∑j, (f w i*eval x (b i u))*(f w j*eval x (b j v))) μ :=
    integrable_finsetSum _ fun j _ ↦ hterm i j
  simp only [Fintype.sum_mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hinner i)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hterm _ j)]
  simp only [squareIntegralMatrix,gramPolynomialMatrix,eval_sum,eval_mul,eval_C,coefficientGram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have heq : (fun w ↦ (f w i*eval x (b i u))*(f w j*eval x (b j v)))=
      (fun w ↦ (f w i*f w j)*eval x (b i u)*eval x (b j v)) := by funext w;ring
  rw [heq,integral_mul_const,integral_mul_const]

/-- An integral of an actual polynomial vector square has an actual finite
polynomial matrix SOS certificate. The measurable field is compressed via
its genuine finite PSD coefficient Gram matrix, without cubature. -/
theorem squareIntegralMatrix_boundedMatrixSOS {n d r : ℕ} (μ : Measure Ω) (f : Ω → I→ℝ)
    (hf : ∀ i j, Integrable (fun w ↦ f w i * f w j) μ)
    (b : I → Fin d → P n) (hb : ∀ i u, (b i u).totalDegree ≤ r) :
    BoundedMatrixSOS r (squareIntegralMatrix μ f b) :=
  gramPolynomial_boundedMatrixSOS _ (coefficientGram_posSemidef μ f hf) b hb

def entryIntegral (μ : Measure Ω) (D : Ω → Matrix I I ℝ) : Matrix I I ℝ :=
  fun i j ↦ ∫w, D w i j ∂μ

omit [DecidableEq I] in
theorem entryIntegral_quadratic (μ : Measure Ω) (D : Ω → Matrix I I ℝ)
    (hD : ∀ i j, Integrable (fun w ↦ D w i j) μ) (z : I → ℝ) :
    dotProduct (star z) (entryIntegral μ D *ᵥ z)=
      ∫w, dotProduct (star z) (D w *ᵥ z) ∂μ := by
  have hterm (i j : I) : Integrable (fun w ↦ z i*(D w i j*z j)) μ :=
    ((hD i j).mul_const (z j)).const_mul (z i)
  have hinner (i : I) : Integrable (fun w ↦ ∑j, z i*(D w i j*z j)) μ :=
    integrable_finsetSum _ fun j _ ↦ hterm i j
  simp only [dotProduct,Pi.star_apply,star_trivial,Matrix.mulVec,entryIntegral]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hinner i)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hterm _ j)]
  simp_rw [integral_const_mul,integral_mul_const]

omit [DecidableEq I] in
theorem entryIntegral_posSemidef (μ : Measure Ω) (D : Ω → Matrix I I ℝ)
    (hD : ∀ i j, Integrable (fun w ↦ D w i j) μ)
    (hPSD : ∀ w, (D w).PosSemidef) : (entryIntegral μ D).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    change (∫w, D w j i ∂μ)=∫w, D w i j ∂μ
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w ↦ by
      simpa only [star_trivial] using (hPSD w).isHermitian.apply i j
  · intro z
    rw [entryIntegral_quadratic μ D hD]
    exact integral_nonneg fun w ↦ (hPSD w).dotProduct_mulVec_nonneg z

theorem entryIntegral_polynomialMatrix_boundedMatrixSOS {n d r : ℕ}
    (μ : Measure Ω) (D : Ω → Matrix I I ℝ)
    (hD : ∀ i j, Integrable (fun w ↦ D w i j) μ)
    (hPSD : ∀ w, (D w).PosSemidef)
    (b : I → Fin d → P n) (hb : ∀ i u, (b i u).totalDegree ≤ r) :
    BoundedMatrixSOS r (gramPolynomialMatrix (entryIntegral μ D) b) :=
  gramPolynomial_boundedMatrixSOS _ (entryIntegral_posSemidef μ D hD hPSD) b hb

omit [DecidableEq I] in
theorem entryIntegral_polynomialMatrix_eval {n d : ℕ}
    (μ : Measure Ω) (D : Ω → Matrix I I ℝ)
    (hD : ∀ i j, Integrable (fun w ↦ D w i j) μ)
    (b : I → Fin d → P n) (x : Fin n → ℝ) (u v : Fin d) :
    eval x (gramPolynomialMatrix (entryIntegral μ D) b u v)=
      ∫w, ∑i, ∑j, D w i j*eval x (b i u)*eval x (b j v) ∂μ := by
  have hterm (i j : I) : Integrable
      (fun w ↦ D w i j*eval x (b i u)*eval x (b j v)) μ :=
    ((hD i j).mul_const _).mul_const _
  have hinner (i : I) : Integrable
      (fun w ↦ ∑j, D w i j*eval x (b i u)*eval x (b j v)) μ :=
    integrable_finsetSum _ fun j _ ↦ hterm i j
  rw [integral_finsetSum _ (fun i _ ↦ hinner i)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hterm _ j)]
  simp only [gramPolynomialMatrix,entryIntegral,eval_sum,eval_mul,eval_C,
    integral_mul_const]

section LiftedFields

variable {J : Type*} [Fintype J] [DecidableEq J]

def coefficientLift (a : I → ℝ) : Matrix J (I×J) ℝ :=
  fun u p ↦ if u=p.2 then a p.1 else 0

omit [Fintype I] [DecidableEq I] in
theorem coefficientLift_entry (a : I → ℝ) (D : Matrix J J ℝ) (i j : I) (u v : J) :
    ((coefficientLift (J:=J) a).transpose*D*coefficientLift (J:=J) a) (i,u) (j,v)=a i*a j*D u v :=
      by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,coefficientLift]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_ite,mul_zero]
  ring

def liftedGram (μ : Measure Ω) (a : Ω → I→ℝ) (D : Ω → Matrix J J ℝ) : Matrix (I×J) (I×J) ℝ :=
  entryIntegral μ (fun w ↦ (coefficientLift (J:=J) (a w)).transpose*D w*coefficientLift (J:=J) (a
    w))

omit [Fintype I] [DecidableEq I] in
theorem liftedGram_entry (μ : Measure Ω) (a : Ω → I→ℝ) (D : Ω → Matrix J J ℝ)
    (i j : I) (u v : J) :
    liftedGram μ a D (i,u) (j,v)=∫w, a w i*a w j*D w u v ∂μ := by
  simp only [liftedGram,entryIntegral,coefficientLift_entry]

omit [DecidableEq I] in
theorem liftedGram_posSemidef (μ : Measure Ω) (a : Ω → I→ℝ) (D : Ω → Matrix J J ℝ)
    (hD : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * D w u v) μ)
    (hPSD : ∀ w, (D w).PosSemidef) : (liftedGram μ a D).PosSemidef := by
  apply entryIntegral_posSemidef
  · intro p q
    rcases p with ⟨i,u⟩
    rcases q with ⟨j,v⟩
    simpa only [coefficientLift_entry] using hD i j u v
  · intro w
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hPSD w).conjTranspose_mul_mul_same (coefficientLift (J:=J) (a w))

def kernelPSDMatrix {n d : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (D : Ω → Matrix J J ℝ) (b : I → J → Fin d → P n) : Matrix (Fin d) (Fin d) (P n) :=
  gramPolynomialMatrix (liftedGram μ a D) (fun p ↦ b p.1 p.2)

theorem kernelPSDMatrix_boundedMatrixSOS {n d r : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (D : Ω → Matrix J J ℝ)
    (hD : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * D w u v) μ)
    (hPSD : ∀ w, (D w).PosSemidef) (b : I → J → Fin d → P n)
    (hb : ∀ i j u, (b i j u).totalDegree ≤ r) :
    BoundedMatrixSOS r (kernelPSDMatrix μ a D b) :=
  gramPolynomial_boundedMatrixSOS _ (liftedGram_posSemidef μ a D hD hPSD) _ fun p ↦ hb p.1 p.2

omit [DecidableEq I] in
theorem kernelPSDMatrix_eval {n d : ℕ} (μ : Measure Ω) (a : Ω → I→ℝ)
    (D : Ω → Matrix J J ℝ)
    (hD : ∀ i j u v, Integrable (fun w ↦ a w i * a w j * D w u v) μ)
    (b : I → J → Fin d → P n) (x : Fin n → ℝ) (u v : Fin d) :
    eval x (kernelPSDMatrix μ a D b u v)=
      ∫w, ∑i : I×J,∑j : I×J, a w i.1*a w j.1*D w i.2 j.2*
        eval x (b i.1 i.2 u)*eval x (b j.1 j.2 v) ∂μ := by
  have hentry (p q : I×J) : Integrable
      (fun w ↦ ((coefficientLift (J:=J) (a w)).transpose*D w*coefficientLift (J:=J) (a w)) p q) μ
        := by
    rcases p with ⟨i,u⟩
    rcases q with ⟨j,v⟩
    simpa only [coefficientLift_entry] using hD i j u v
  have he := entryIntegral_polynomialMatrix_eval μ _ hentry (fun p ↦ b p.1 p.2) x u v
  simp only [Fintype.sum_prod_type,coefficientLift_entry] at he ⊢
  exact he

end LiftedFields

section MatrixNormSlack

omit [MeasurableSpace Ω] [Fintype I] [DecidableEq I] in
theorem real_dot_norm_square {K : Type*} [Fintype K] (z : K → ℝ) :
    dotProduct z z=‖(WithLp.equiv 2 (K→ℝ)).symm z‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [dotProduct,WithLp.equiv_symm_apply, PiLp.toLp_apply,Real.norm_eq_abs,sq_abs,←pow_two]

theorem operator_slack_posSemidef {d e : ℕ} (F : Matrix (Fin d) (Fin e) ℝ)
    {B : ℝ} (_hB : 0 ≤ B) (hF : ‖F‖ ≤ B) :
    (B^2 • (1:Matrix (Fin d) (Fin d) ℝ)-F*F.transpose).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · have hdiag : (B^2 • (1:Matrix (Fin d) (Fin d) ℝ)).IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      simp [Matrix.smul_apply,Matrix.one_apply,eq_comm]
    have hgram : (F*F.transpose).IsHermitian := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (Matrix.posSemidef_self_mul_conjTranspose F).isHermitian
    exact hdiag.sub hgram
  · intro z
    have hprod : dotProduct z ((F*F.transpose)*ᵥz)=dotProduct (F.transpose*ᵥz) (F.transpose*ᵥz) :=
      by
      rw [←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose]
    have hid : dotProduct z ((B^2 • (1:Matrix (Fin d) (Fin d) ℝ))*ᵥz)=B^2*dotProduct z z := by
      rw [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
      rfl
    simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub]
    rw [hid,hprod]
    rw [real_dot_norm_square,real_dot_norm_square]
    let x : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 ((Fin d)→ℝ)).symm z
    have ht : ‖F.transpose‖=‖F‖ := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.l2_opNorm_conjTranspose F
    have hn : ‖(WithLp.equiv 2 ((Fin e)→ℝ)).symm (F.transpose*ᵥz)‖≤B*‖x‖ := by
      have hh := Matrix.l2_opNorm_mulVec F.transpose x
      rw [ht] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hF (norm_nonneg x))
    nlinarith [norm_nonneg ((WithLp.equiv 2 ((Fin e)→ℝ)).symm (F.transpose*ᵥz)),norm_nonneg x]

def schurField {d e : ℕ} (B : ℝ) (F : Matrix (Fin d) (Fin e) ℝ) :
    Matrix (Fin d ⊕ Fin e) (Fin d ⊕ Fin e) ℝ :=
  Matrix.fromBlocks (B^2 • (1:Matrix (Fin d) (Fin d) ℝ)) F F.transpose 1

theorem schurField_posSemidef {d e : ℕ} (F : Matrix (Fin d) (Fin e) ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ‖F‖ ≤ B) : (schurField B F).PosSemidef := by
  have hslack := operator_slack_posSemidef F hB hF
  letI : Invertible (1:Matrix (Fin e) (Fin e) ℝ) := ⟨1,by simp,by simp⟩
  have h := (Matrix.PosDef.fromBlocks₂₂ (B^2 • (1:Matrix (Fin d) (Fin d) ℝ)) F
    (Matrix.PosDef.one : (1:Matrix (Fin e) (Fin e) ℝ).PosDef)).mpr (by simpa using hslack)
  simpa only [schurField,Matrix.conjTranspose_eq_transpose_of_trivial] using h

end MatrixNormSlack

end MatrixSmoothing
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
