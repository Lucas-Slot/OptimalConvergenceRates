import Mathlib.Analysis.Matrix.Order
import OptimalConvergenceRates.SphereDimensionBounds.ChebyshevSOSKernel
import Mathlib.Data.Matrix.Mul

/-! Finite polynomial matrix variance with explicit outer-product roots.
Kernel normalization, cubature, and a measurable matrix field are not assumed
or constructed here. The unnormalized weight sum is retained exactly. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.FiniteMatrixVariance

open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open MvPolynomial ChebyshevSOSKernel

abbrev P (n : ℕ) := OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n

def outer {n d : ℕ} (v : Fin d → P n) : Matrix (Fin d) (Fin d) (P n) :=
  fun i j => v i*v j

def BoundedMatrixSOS {n d : ℕ} (r : ℕ) (M : Matrix (Fin d) (Fin d) (P n)) : Prop :=
  ∃ m : ℕ, ∃ v : Fin m → Fin d → P n,
    (∀ k i,(v k i).totalDegree≤r) ∧ M=∑ k,outer (v k)

theorem BoundedMatrixSOS.of_family {n d r : ℕ} {I : Type*} [Fintype I]
    (v : I → Fin d → P n) (hv : ∀ k i, (v k i).totalDegree ≤ r) :
    BoundedMatrixSOS r (∑ k,outer (v k)) := by
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I,fun k => v (e.symm k),fun k i => hv _ i,?_⟩
  exact (e.symm.sum_comp (fun k => outer (v k))).symm

theorem BoundedMatrixSOS.mono {n d r t : ℕ} {M : Matrix (Fin d) (Fin d) (P n)}
    (hM : BoundedMatrixSOS r M) (hrt : r ≤ t) : BoundedMatrixSOS t M := by
  obtain ⟨m,v,hv,hid⟩ := hM
  exact ⟨m,v,fun k i => (hv k i).trans hrt,hid⟩

theorem BoundedMatrixSOS.add {n d r : ℕ} {M N : Matrix (Fin d) (Fin d) (P n)}
    (hM : BoundedMatrixSOS r M) (hN : BoundedMatrixSOS r N) :
    BoundedMatrixSOS r (M+N) := by
  classical
  obtain ⟨a,u,hu,rfl⟩ := hM
  obtain ⟨b,v,hv,rfl⟩ := hN
  have hid : (∑ k,outer (u k))+(∑ k,outer (v k))=
      ∑ k : Fin a ⊕ Fin b,outer (Sum.elim u v k) := by simp [Fintype.sum_sum_type]
  rw [hid]
  apply BoundedMatrixSOS.of_family
  intro k i
  cases k with
  | inl j => exact hu j i
  | inr j => exact hv j i

def quadraticForm {n d : ℕ} (M : Matrix (Fin d) (Fin d) (P n))
    (x : Fin d → P n) : P n := ∑ i,∑ j,x i*M i j*x j

theorem quadraticForm_outer {n d : ℕ} (v x : Fin d → P n) :
    quadraticForm (outer v) x=(∑ i,v i*x i)^2 := by
  simp only [quadraticForm,outer,pow_two,Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring_nf

theorem triple_sum_cycle {I J K R : Type*} [Fintype I] [Fintype J] [Fintype K]
    [AddCommMonoid R] (f : I → J → K → R) :
    (∑ i,∑ j,∑ k,f i j k)=∑ k,∑ i,∑ j,f i j k := by
  calc
    (∑ i,∑ j,∑ k,f i j k)=(∑ i,∑ k,∑ j,f i j k) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _=_ := Finset.sum_comm

/-- Contraction by an actual polynomial vector gives actual bounded scalar
SOS roots. The degree of that vector is included. -/
theorem BoundedMatrixSOS.contract {n d r t : ℕ}
    {M : Matrix (Fin d) (Fin d) (P n)} (hM : BoundedMatrixSOS r M)
    (x : Fin d → P n) (hx : ∀ i, (x i).totalDegree ≤ t) :
    BoundedSOS (r+t) (quadraticForm M x) := by
  obtain ⟨m,v,hv,rfl⟩ := hM
  have hid : quadraticForm (∑ k,outer (v k)) x=∑ k,(∑ i,v k i*x i)^2 := by
    simp only [quadraticForm,Matrix.sum_apply,Finset.mul_sum,Finset.sum_mul]
    rw [triple_sum_cycle]
    apply Finset.sum_congr rfl
    intro k hk
    exact quadraticForm_outer (v k) x
  rw [hid]
  apply BoundedSOS.of_family
  intro k
  apply totalDegree_finsetSum_le
  intro i hi
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (hv k i) (hx i))

theorem finite_weighted_bilinear_variance {I R : Type*} [Fintype I] [CommRing R]
    (w f g : I → R) :
    2*((∑ i,w i)*(∑ i,w i*f i*g i)-(∑ i,w i*f i)*(∑ i,w i*g i))=
      ∑ i,∑ j,w i*w j*(f i-f j)*(g i-g j) := by
  have hpoint (i j : I) : w i*w j*(f i-f j)*(g i-g j)=
      (w i*f i*g i)*w j+(w j*f j*g j)*w i-
        (w i*f i)*(w j*g j)-(w i*g i)*(w j*f j) := by ring_nf
  simp_rw [hpoint]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  ring_nf

def constantMatrix {n d e : ℕ} (F : Matrix (Fin d) (Fin e) ℝ) :
    Matrix (Fin d) (Fin e) (P n) := fun i j => C (F i j)

def weightSum {n : ℕ} {I : Type*} [Fintype I] (a : I → P n) : P n := ∑ i,a i^2

def meanMatrix {n d e : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (F : I → Matrix (Fin d) (Fin e) ℝ) :
    Matrix (Fin d) (Fin e) (P n) := fun u v => ∑ i,a i^2*C (F i u v)

def secondMatrix {n d e : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (F : I → Matrix (Fin d) (Fin e) ℝ) :
    Matrix (Fin d) (Fin d) (P n) :=
  fun u v => ∑ k : Fin e,∑ i,a i^2*C (F i u k)*C (F i v k)

def varianceMatrix {n d e : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (F : I → Matrix (Fin d) (Fin e) ℝ) :
    Matrix (Fin d) (Fin d) (P n) :=
  (weightSum a) • secondMatrix a F-meanMatrix a F*(meanMatrix a F).transpose

def differenceRoot {n d e : ℕ} {I : Type*} (a : I → P n)
    (F : I → Matrix (Fin d) (Fin e) ℝ) (z : I × I × Fin e) : Fin d → P n :=
  fun u => C (Real.sqrt (1/2:ℝ))*a z.1*a z.2.1*C (F z.1 u z.2.2-F z.2.1 u z.2.2)

theorem differenceRoot_degree {n d e s : ℕ} {I : Type*} (a : I → P n)
    (ha : ∀ i, (a i).totalDegree ≤ s) (F : I → Matrix (Fin d) (Fin e) ℝ)
    (z : I × I × Fin e) (u : Fin d) : (differenceRoot a F z u).totalDegree≤2*s := by
  unfold differenceRoot
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C,add_zero]
  apply (totalDegree_mul _ _).trans
  have hfirst : (C (Real.sqrt (1/2:ℝ))*a z.1).totalDegree≤s :=
    (totalDegree_mul _ _).trans (by simpa using ha z.1)
  simpa only [two_mul] using Nat.add_le_add hfirst (ha z.2.1)

/-- The half of all ordered pairs is realized by the constant square root
sqrt(1/2), so the right side is a literal finite polynomial matrix SOS. -/
theorem finite_matrix_variance_identity {n d e : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (F : I → Matrix (Fin d) (Fin e) ℝ) :
    varianceMatrix a F=∑ z : I × I × Fin e,outer (differenceRoot a F z) := by
  apply Matrix.ext
  intro u v
  have hsqrt : (C (Real.sqrt (1/2:ℝ)) : P n)^2=C (1/2:ℝ) := by
    rw [←map_pow,Real.sq_sqrt (by norm_num)]
  have hroot (z : I × I × Fin e) :
      outer (differenceRoot a F z) u v=C (1/2:ℝ)*a z.1^2*a z.2.1^2*
        (C (F z.1 u z.2.2)-C (F z.2.1 u z.2.2))*
        (C (F z.1 v z.2.2)-C (F z.2.1 v z.2.2)) := by
    unfold outer differenceRoot
    simp only [map_sub]
    linear_combination a z.1^2*a z.2.1^2*
      (C (F z.1 u z.2.2)-C (F z.2.1 u z.2.2))*
      (C (F z.1 v z.2.2)-C (F z.2.1 v z.2.2))*hsqrt
  simp only [Matrix.sum_apply,hroot,Fintype.sum_prod_type]
  rw [triple_sum_cycle]
  simp only [varianceMatrix,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    secondMatrix,meanMatrix,Matrix.mul_apply,Matrix.transpose_apply,weightSum]
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hv := finite_weighted_bilinear_variance (fun i => a i^2)
    (fun i => C (F i u k)) (fun i => C (F i v k))
  have hhalf : (C (1/2:ℝ) : P n)*2=1 := by
    change C (1/2:ℝ)*C (2:ℝ)=1
    rw [←map_mul]
    norm_num
  calc
    (∑ i,a i^2)*(∑ i,a i^2*C (F i u k)*C (F i v k))-
        (∑ i,a i^2*C (F i u k))*(∑ i,a i^2*C (F i v k))=
      C (1/2:ℝ)*(2*((∑ i,a i^2)*(∑ i,a i^2*C (F i u k)*C (F i v k))-
        (∑ i,a i^2*C (F i u k))*(∑ i,a i^2*C (F i v k)))) := by rw [←mul_assoc,hhalf,one_mul]
    _=_ := by rw [hv]; simp only [Finset.mul_sum]; ring_nf

theorem finite_matrix_variance_boundedSOS {n d e s : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (ha : ∀ i, (a i).totalDegree ≤ s)
    (F : I → Matrix (Fin d) (Fin e) ℝ) :
    BoundedMatrixSOS (2*s) (varianceMatrix a F) := by
  rw [finite_matrix_variance_identity]
  exact BoundedMatrixSOS.of_family _ (differenceRoot_degree a ha F)

theorem real_psd_factor {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ) (hD : D.PosSemidef) :
    ∃ G : Matrix (Fin d) (Fin d) ℝ,D=G*G.transpose := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hD.nonneg
  refine ⟨B.transpose,?_⟩
  simpa only [Matrix.star_eq_conjTranspose, Matrix.transpose_transpose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hB

def weightedPSDMatrix {n d : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (D : I → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) (P n) := (weightSum a) • meanMatrix a D

def slackRoot {n d : ℕ} {I : Type*} (a : I → P n)
    (G : I → Matrix (Fin d) (Fin d) ℝ) (z : I × I × Fin d) : Fin d → P n :=
  fun u => a z.1*a z.2.1*C (G z.1 u z.2.2)

theorem slackRoot_degree {n d s : ℕ} {I : Type*} (a : I → P n)
    (ha : ∀ i, (a i).totalDegree ≤ s) (G : I → Matrix (Fin d) (Fin d) ℝ)
    (z : I × I × Fin d) (u : Fin d) : (slackRoot a G z u).totalDegree≤2*s := by
  unfold slackRoot
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C,add_zero]
  exact (totalDegree_mul _ _).trans (by simpa [two_mul] using Nat.add_le_add (ha z.1) (ha z.2.1))

/-- Every supplied constant PSD slack is genuinely factored in Lean; the
finite weight sum is kept rather than assumed to be one. -/
theorem finite_psd_slack_boundedSOS {n d s : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (ha : ∀ i, (a i).totalDegree ≤ s)
    (D : I → Matrix (Fin d) (Fin d) ℝ) (hD : ∀ i, (D i).PosSemidef) :
    BoundedMatrixSOS (2*s) (weightedPSDMatrix a D) := by
  choose G hG using fun i => real_psd_factor (D i) (hD i)
  have hid : weightedPSDMatrix a D=∑ z : I × I × Fin d,outer (slackRoot a G z) := by
    apply Matrix.ext
    intro u v
    simp only [weightedPSDMatrix,Matrix.smul_apply,smul_eq_mul,meanMatrix,weightSum,
      Matrix.sum_apply,Fintype.sum_prod_type]
    simp_rw [hG,Matrix.mul_apply,Matrix.transpose_apply,map_sum,map_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [outer,slackRoot]
    ring_nf
  rw [hid]
  exact BoundedMatrixSOS.of_family _ (slackRoot_degree a ha G)

theorem meanMatrix_add {n d e : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (D E : I → Matrix (Fin d) (Fin e) ℝ) :
    meanMatrix a (fun i => D i+E i)=meanMatrix a D+meanMatrix a E := by
  apply Matrix.ext
  intro u v
  simp [meanMatrix,Matrix.add_apply,map_add,mul_add,Finset.sum_add_distrib]

theorem secondMatrix_eq_mean_gram {n d e : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (F : I → Matrix (Fin d) (Fin e) ℝ) :
    secondMatrix a F=meanMatrix a (fun i => F i*(F i).transpose) := by
  apply Matrix.ext
  intro u v
  simp only [secondMatrix,meanMatrix,Matrix.mul_apply,Matrix.transpose_apply,map_sum,map_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring_nf

/-- Variance plus the supplied PSD slack gives a polynomial matrix SOS
bound. Pointwise operator bounds may be used to prove hD separately. -/
theorem finite_matrix_slack_bound {n d e s : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (ha : ∀ i, (a i).totalDegree ≤ s)
    (F : I → Matrix (Fin d) (Fin e) ℝ)
    (D : I → Matrix (Fin d) (Fin d) ℝ) (hD : ∀ i, (D i).PosSemidef) :
    BoundedMatrixSOS (2*s)
      ((weightSum a) • meanMatrix a (fun i => D i+F i*(F i).transpose)-
        meanMatrix a F*(meanMatrix a F).transpose) := by
  have hvariance := finite_matrix_variance_boundedSOS a ha F
  have hslack := finite_psd_slack_boundedSOS a ha D hD
  have hsum := hslack.add hvariance
  rw [meanMatrix_add]
  convert hsum using 1
  simp only [weightedPSDMatrix,varianceMatrix,smul_add,secondMatrix_eq_mean_gram]
  abel

theorem meanMatrix_scalar_identity {n d : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (c : I → ℝ) :
    meanMatrix a (fun i => c i • (1 : Matrix (Fin d) (Fin d) ℝ))=
      (∑ i,a i^2*C (c i)) • (1 : Matrix (Fin d) (Fin d) (P n)) := by
  apply Matrix.ext
  intro u v
  by_cases huv : u=v
  · subst v
    simp [meanMatrix,Matrix.smul_apply,smul_eq_mul]
  · simp [meanMatrix,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,huv]

/-- A pointwise constant matrix PSD bound yields an actual finite matrix
SOS bound. Turning an operator norm estimate into hPSD is separate. -/
theorem finite_matrix_bound_boundedSOS {n d e s : ℕ} {I : Type*} [Fintype I]
    (a : I → P n) (ha : ∀ i, (a i).totalDegree ≤ s)
    (F : I → Matrix (Fin d) (Fin e) ℝ) (c : I → ℝ)
    (hPSD : ∀ i, (c i • (1 : Matrix (Fin d) (Fin d) ℝ) - F i * (F i).transpose).PosSemidef) :
    BoundedMatrixSOS (2*s)
      ((weightSum a*(∑ i,a i^2*C (c i))) • (1 : Matrix (Fin d) (Fin d) (P n))-
        meanMatrix a F*(meanMatrix a F).transpose) := by
  have h := finite_matrix_slack_bound a ha F
    (fun i => c i • (1 : Matrix (Fin d) (Fin d) ℝ)-F i*(F i).transpose) hPSD
  simp only [sub_add_cancel,meanMatrix_scalar_identity,smul_smul] at h
  exact h

end OptimalConvergenceRates.SphereDimensionBounds.FiniteMatrixVariance
