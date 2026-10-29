import OptimalConvergenceRates.BasicNotions.ClosedConeImage
/-
  OptimalConvergenceRates/BasicNotions/SoSConeClosed.lean

  Coefficient-topology infrastructure for closedness of fixed-degree SOS cones.
-/
import OptimalConvergenceRates.BasicNotions.CoefficientNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Funext

open MvPolynomial Finset Filter
open scoped BigOperators Topology MatrixOrder

noncomputable section

namespace OptimalConvergenceRates

local instance matrixNormedAddCommGroup {m n : Type*} [Fintype m] [Fintype n] :
    NormedAddCommGroup (Matrix m n ℝ) := Matrix.normedAddCommGroup

local instance matrixNormedSpace {m n : Type*} [Fintype m] [Fintype n] :
    NormedSpace ℝ (Matrix m n ℝ) := Matrix.normedSpace

/-- Total degree of a finitely supported exponent vector. -/
def expDegree {n : ℕ} (α : Fin n →₀ ℕ) : ℕ :=
  α.sum fun _ e => e

/-- Exponent vectors of total degree at most `d`. -/
def ExpLE (n d : ℕ) :=
  {α : Fin n →₀ ℕ // expDegree α ≤ d}

namespace ExpLE

@[simp] theorem val_mk {n d : ℕ} (α : Fin n →₀ ℕ) (hα : expDegree α ≤ d) :
    (⟨α, hα⟩ : ExpLE n d).1 = α := rfl

end ExpLE

lemma exp_apply_le_expDegree {n : ℕ} (α : Fin n →₀ ℕ) (i : Fin n) :
    α i ≤ expDegree α := by
  classical
  unfold expDegree
  by_cases hi : i ∈ α.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  · have hzero : α i = 0 := by
      simpa [Finsupp.mem_support_iff] using hi
    rw [hzero]
    exact Nat.zero_le _

noncomputable instance expLEFintype (n d : ℕ) : Fintype (ExpLE n d) := by
  classical
  let f : ExpLE n d → (Fin n → Fin (d + 1)) :=
    fun α i => ⟨α.1 i, Nat.lt_succ_of_le ((exp_apply_le_expDegree α.1 i).trans α.2)⟩
  letI : Finite (ExpLE n d) :=
    Finite.of_injective f (by
      intro α β h
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      exact Fin.ext_iff.mp (congrFun h i))
  exact Fintype.ofFinite _

/-- Coefficients of a polynomial on monomials of total degree at most `d`. -/
def coeffVec {n : ℕ} (d : ℕ) (P : MvPolynomial (Fin n) ℝ) : ExpLE n d → ℝ :=
  fun α => P.coeff α.1

/-- Reconstruct a polynomial from a finite coefficient vector. -/
noncomputable def polyOfVec {n : ℕ} (d : ℕ) (c : ExpLE n d → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ α : ExpLE n d, MvPolynomial.monomial α.1 (c α)

@[simp] lemma coeffVec_polyOfVec {n d : ℕ} (c : ExpLE n d → ℝ) :
    coeffVec d (polyOfVec d c) = c := by
  classical
  funext α
  unfold coeffVec polyOfVec
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single α]
  · simp
  · intro β _ hβα
    have hval : β.1 ≠ α.1 := by
      intro h
      exact hβα (Subtype.ext h)
    simp [MvPolynomial.coeff_monomial, hval]
  · intro hα
    simp at hα

lemma expDegree_of_mem_support_le_totalDegree {n : ℕ} {P : MvPolynomial (Fin n) ℝ}
    {α : Fin n →₀ ℕ} (hα : α ∈ P.support) :
    expDegree α ≤ P.totalDegree := by
  classical
  unfold expDegree
  simpa [MvPolynomial.totalDegree] using Finset.le_sup (s := P.support)
    (f := fun α => α.sum fun _ e => e) hα

lemma coeff_eq_zero_of_totalDegree_lt_expDegree {n : ℕ} {P : MvPolynomial (Fin n) ℝ}
    {α : Fin n →₀ ℕ} (hα : P.totalDegree < expDegree α) :
    P.coeff α = 0 := by
  classical
  by_contra hne
  have hmem : α ∈ P.support := by
    simpa [MvPolynomial.mem_support_iff] using hne
  have := expDegree_of_mem_support_le_totalDegree (P := P) hmem
  omega

lemma polyOfVec_coeffVec {n d : ℕ} {P : MvPolynomial (Fin n) ℝ}
    (hP : P.totalDegree ≤ d) :
    polyOfVec d (coeffVec d P) = P := by
  classical
  ext α
  by_cases hα : expDegree α ≤ d
  · have hcoeff := congrFun (coeffVec_polyOfVec (n := n) (d := d) (coeffVec d P)) ⟨α, hα⟩
    simpa [coeffVec] using hcoeff
  · have hgt : d < expDegree α := Nat.lt_of_not_ge hα
    have hz : P.coeff α = 0 :=
      coeff_eq_zero_of_totalDegree_lt_expDegree (P := P) (lt_of_le_of_lt hP hgt)
    rw [hz]
    unfold polyOfVec
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro β _
    have hne : (β.1 : Fin n →₀ ℕ) ≠ α := by
      intro hb
      have : expDegree α ≤ d := by simpa [hb] using β.2
      exact hα this
    simp [MvPolynomial.coeff_monomial, hne]

lemma eq_of_coeffVec_eq {n d : ℕ} {P Q : MvPolynomial (Fin n) ℝ}
    (hP : P.totalDegree ≤ d) (hQ : Q.totalDegree ≤ d)
    (hcoeff : coeffVec d P = coeffVec d Q) :
    P = Q := by
  rw [← polyOfVec_coeffVec hP, ← polyOfVec_coeffVec hQ, hcoeff]


/-- Monomial indices for degree-bounded square roots. -/
abbrev RootExp (n r : ℕ) := ExpLE n r

/-- Monomial indices for degree-bounded SOS output polynomials. -/
abbrev OutputExp (n r : ℕ) := ExpLE n (2 * r)

lemma expDegree_add {n : ℕ} (α β : Fin n →₀ ℕ) :
    expDegree (α + β) = expDegree α + expDegree β := by
  classical
  unfold expDegree
  rw [Finsupp.sum_add_index]
  · intro a ha
    simp
  · intro a ha b c
    simp

lemma polyOfVec_totalDegree_le {n d : ℕ} (c : ExpLE n d → ℝ) :
    (polyOfVec d c).totalDegree ≤ d := by
  classical
  unfold polyOfVec
  apply MvPolynomial.totalDegree_finsetSum_le
  intro α _
  exact (MvPolynomial.totalDegree_monomial_le α.1 (c α)).trans α.2

/-- Polynomial represented by a Gram matrix on monomials of degree at most `r`. -/
noncomputable def gramPoly {n r : ℕ}
    (Q : Matrix (RootExp n r) (RootExp n r) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ α : RootExp n r,
    ∑ β : RootExp n r,
      MvPolynomial.monomial (α.1 + β.1) (Q α β)

/-- Coefficient vector of the Gram polynomial. -/
noncomputable def gramMap {n r : ℕ}
    (Q : Matrix (RootExp n r) (RootExp n r) ℝ) :
    OutputExp n r → ℝ :=
  coeffVec (2 * r) (gramPoly Q)

lemma gramPoly_totalDegree_le {n r : ℕ}
    (Q : Matrix (RootExp n r) (RootExp n r) ℝ) :
    (gramPoly Q).totalDegree ≤ 2 * r := by
  classical
  unfold gramPoly
  apply MvPolynomial.totalDegree_finsetSum_le
  intro α _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro β _
  calc
    (MvPolynomial.monomial (α.1 + β.1) (Q α β)).totalDegree
        ≤ expDegree (α.1 + β.1) := MvPolynomial.totalDegree_monomial_le _ _
    _ = expDegree α.1 + expDegree β.1 := expDegree_add α.1 β.1
    _ ≤ r + r := Nat.add_le_add α.2 β.2
    _ = 2 * r := by omega



lemma gramPoly_sum {n r N : ℕ}
    (A : Fin N → Matrix (RootExp n r) (RootExp n r) ℝ) :
    gramPoly (∑ i : Fin N, A i) = ∑ i : Fin N, gramPoly (A i) := by
  classical
  ext γ
  unfold gramPoly
  simp only [Matrix.sum_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  calc
    (∑ x : RootExp n r, ∑ y : RootExp n r,
      if x.1 + y.1 = γ then ∑ c : Fin N, A c x y else 0)
        = ∑ x : RootExp n r, ∑ y : RootExp n r,
            ∑ c : Fin N, if x.1 + y.1 = γ then A c x y else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          by_cases h : x.1 + y.1 = γ <;> simp [h]
    _ = ∑ x : RootExp n r, ∑ c : Fin N, ∑ y : RootExp n r,
          if x.1 + y.1 = γ then A c x y else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ c : Fin N, ∑ x : RootExp n r, ∑ y : RootExp n r,
          if x.1 + y.1 = γ then A c x y else 0 := by
          rw [Finset.sum_comm]

lemma gramPoly_vecMulVec {n r : ℕ} (c : RootExp n r → ℝ) :
    gramPoly (Matrix.vecMulVec c (star c)) = (polyOfVec r c) ^ 2 := by
  classical
  unfold gramPoly polyOfVec
  rw [pow_two]
  rw [Finset.sum_mul_sum]
  simp [MvPolynomial.monomial_mul_monomial, Matrix.vecMulVec]

/-- A degree-bounded SOS polynomial is equivalently represented by a PSD Gram matrix. -/
theorem degreeBoundedSOS_iff_exists_psd_gram {n r : ℕ}
    {S : MvPolynomial (Fin n) ℝ} :
    Nonempty (DegreeBoundedSOS S r) ↔
      ∃ Q : Matrix (RootExp n r) (RootExp n r) ℝ,
        Q.PosSemidef ∧ gramPoly Q = S := by
  classical
  constructor
  · rintro ⟨w⟩
    let c : Fin w.N → RootExp n r → ℝ := fun i => coeffVec r (w.P i)
    let Q : Matrix (RootExp n r) (RootExp n r) ℝ :=
      ∑ i : Fin w.N, Matrix.vecMulVec (c i) (star (c i))
    refine ⟨Q, ?_, ?_⟩
    · unfold Q
      rw [Matrix.posSemidef_iff_eq_sum_vecMulVec]
      exact ⟨w.N, c, rfl⟩
    · unfold Q c
      rw [gramPoly_sum]
      simp_rw [gramPoly_vecMulVec]
      calc
        (∑ i : Fin w.N, polyOfVec r (coeffVec r (w.P i)) ^ 2)
            = ∑ i : Fin w.N, (w.P i) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [polyOfVec_coeffVec (w.degree i)]
        _ = S := w.decomp.symm
  · rintro ⟨Q, hQ, rfl⟩
    rw [Matrix.posSemidef_iff_eq_sum_vecMulVec] at hQ
    rcases hQ with ⟨m, v, hQ⟩
    refine ⟨⟨m, ?_, ?_, ?_⟩⟩
    · exact fun i => polyOfVec r (v i)
    · rw [hQ, gramPoly_sum]
      simp_rw [gramPoly_vecMulVec]
    · intro i
      exact polyOfVec_totalDegree_le _

lemma DegreeBoundedSOS.totalDegree_le {n r : ℕ} {S : MvPolynomial (Fin n) ℝ}
    (w : DegreeBoundedSOS S r) :
    S.totalDegree ≤ 2 * r :=
  w.totalDegree_le_two_mul

lemma totalDegree_le_of_nonempty_degreeBoundedSOS {n r : ℕ}
    {S : MvPolynomial (Fin n) ℝ} (hS : Nonempty (DegreeBoundedSOS S r)) :
    S.totalDegree ≤ 2 * r := by
  rcases hS with ⟨w⟩
  exact w.totalDegree_le

lemma coeffL1Distance_nonneg {n : ℕ} (P S : MvPolynomial (Fin n) ℝ) :
    0 ≤ coeffL1Distance P S := by
  unfold coeffL1Distance
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma abs_coeff_sub_le_coeffL1Distance {n : ℕ}
    (P S : MvPolynomial (Fin n) ℝ) (α : Fin n →₀ ℕ) :
    |(P - S).coeff α| ≤ coeffL1Distance P S := by
  classical
  unfold coeffL1Distance
  by_cases hα : α ∈ (P - S).support
  · exact Finset.single_le_sum
      (fun β _ => abs_nonneg ((P - S).coeff β)) hα
  · have hz : (P - S).coeff α = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hα
    rw [hz, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)


lemma norm_coeffVec_sub_le_coeffL1Distance {n d : ℕ}
    (P S : MvPolynomial (Fin n) ℝ) :
    ‖coeffVec d P - coeffVec d S‖ ≤ coeffL1Distance P S := by
  classical
  rw [Pi.norm_def]
  let D : NNReal := ⟨coeffL1Distance P S, coeffL1Distance_nonneg P S⟩
  change (↑(Finset.univ.sup fun b ↦ ‖(coeffVec d P - coeffVec d S) b‖₊) : ℝ) ≤ ↑D
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro α _
  apply NNReal.coe_le_coe.mp
  change ‖(coeffVec d P - coeffVec d S) α‖ ≤ coeffL1Distance P S
  simp only [Pi.sub_apply, coeffVec, Real.norm_eq_abs]
  calc |P.coeff α.1 - S.coeff α.1|
      = |(P - S).coeff α.1| := by simp
    _ ≤ coeffL1Distance P S := abs_coeff_sub_le_coeffL1Distance P S α.1

/-- Zero as a degree-bounded SOS polynomial. -/
def zeroDegreeBoundedSOS (n r : ℕ) :
    DegreeBoundedSOS (0 : MvPolynomial (Fin n) ℝ) r where
  N := 1
  P := fun _ => 0
  decomp := by simp
  degree := by simp

/-! ## Finite-dimensional Gram-matrix closedness -/

lemma gramPoly_add {n r : ℕ}
    (A B : Matrix (RootExp n r) (RootExp n r) ℝ) :
    gramPoly (A + B) = gramPoly A + gramPoly B := by
  classical
  ext γ
  unfold gramPoly
  simp only [Matrix.add_apply, MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_monomial]
  calc
    (∑ x : RootExp n r, ∑ y : RootExp n r,
      if x.1 + y.1 = γ then A x y + B x y else 0)
        = ∑ x : RootExp n r, ∑ y : RootExp n r,
            ((if x.1 + y.1 = γ then A x y else 0) +
              (if x.1 + y.1 = γ then B x y else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          by_cases h : x.1 + y.1 = γ <;> simp [h]
    _ = (∑ x : RootExp n r, ∑ y : RootExp n r,
            if x.1 + y.1 = γ then A x y else 0) +
          (∑ x : RootExp n r, ∑ y : RootExp n r,
            if x.1 + y.1 = γ then B x y else 0) := by
          simp [Finset.sum_add_distrib]

lemma gramPoly_smul {n r : ℕ} (a : ℝ)
    (A : Matrix (RootExp n r) (RootExp n r) ℝ) :
    gramPoly (a • A) = a • gramPoly A := by
  classical
  ext γ
  unfold gramPoly
  simp only [Matrix.smul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_monomial]
  calc
    (∑ x : RootExp n r, ∑ y : RootExp n r,
      if x.1 + y.1 = γ then a * A x y else 0)
        = ∑ x : RootExp n r, ∑ y : RootExp n r,
            a * (if x.1 + y.1 = γ then A x y else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          by_cases h : x.1 + y.1 = γ <;> simp [h]
    _ = a * (∑ x : RootExp n r, ∑ y : RootExp n r,
            if x.1 + y.1 = γ then A x y else 0) := by
          simp [Finset.mul_sum]


/-- The vector of monomial evaluations up to degree `r`. -/
def monomialVec {n r : ℕ} (x : Fin n → ℝ) : RootExp n r → ℝ :=
  fun α => α.1.prod fun i e => x i ^ e


lemma monomialVec_add_exp {n : ℕ} (x : Fin n → ℝ)
    (α β : Fin n →₀ ℕ) :
    (α + β).prod (fun i e => x i ^ e) =
      α.prod (fun i e => x i ^ e) * β.prod (fun i e => x i ^ e) := by
  rw [Finsupp.prod_add_index]
  · simp
  · intro i a b
    simp [pow_add]

/-- One row of the Gram matrix, interpreted as a polynomial in the root monomial basis. -/
noncomputable def gramRowPoly {n r : ℕ}
    (Q : Matrix (RootExp n r) (RootExp n r) ℝ) (α : RootExp n r) :
    MvPolynomial (Fin n) ℝ :=
  ∑ β : RootExp n r, MvPolynomial.monomial β.1 (Q α β)

lemma eval_gramRowPoly {n r : ℕ}
    (Q : Matrix (RootExp n r) (RootExp n r) ℝ) (α : RootExp n r)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (gramRowPoly Q α) = (Q.mulVec (monomialVec x)) α := by
  classical
  unfold gramRowPoly monomialVec Matrix.mulVec dotProduct
  simp [MvPolynomial.eval_monomial]

lemma eval_gramPoly {n r : ℕ}
    (Q : Matrix (RootExp n r) (RootExp n r) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (gramPoly Q) =
      star (monomialVec x) ⬝ᵥ Q.mulVec (monomialVec x) := by
  classical
  unfold gramPoly monomialVec Matrix.mulVec dotProduct
  simp only [MvPolynomial.eval_monomial, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [monomialVec_add_exp x α.1 β.1]
  simp [mul_left_comm]

lemma coeff_gramRowPoly {n r : ℕ}
    (Q : Matrix (RootExp n r) (RootExp n r) ℝ) (α β : RootExp n r) :
    (gramRowPoly Q α).coeff β.1 = Q α β := by
  classical
  unfold gramRowPoly
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single β]
  · simp
  · intro γ _ hγβ
    have hne : γ.1 ≠ β.1 := by
      intro h
      exact hγβ (Subtype.ext h)
    simp [MvPolynomial.coeff_monomial, hne]
  · intro hβ
    simp at hβ

lemma psd_eq_zero_of_gramMap_eq_zero {n r : ℕ}
    {Q : Matrix (RootExp n r) (RootExp n r) ℝ}
    (hQ : Q.PosSemidef) (hmap : gramMap Q = 0) :
    Q = 0 := by
  classical
  have hpoly : gramPoly Q = 0 := by
    apply eq_of_coeffVec_eq (gramPoly_totalDegree_le Q) (by simp)
    have hzero : coeffVec (2 * r) (0 : MvPolynomial (Fin n) ℝ) = 0 := by
      funext α
      simp [coeffVec]
    rw [hzero]
    simpa [gramMap] using hmap
  have hmul : ∀ x : Fin n → ℝ, Q.mulVec (monomialVec x) = 0 := by
    intro x
    apply ((hQ.dotProduct_mulVec_zero_iff)).mp
    rw [← eval_gramPoly Q x, hpoly]
    simp
  ext α β
  let p : MvPolynomial (Fin n) ℝ := gramRowPoly Q α
  have hp_eval : ∀ x : Fin n → ℝ, MvPolynomial.eval x p = 0 := by
    intro x
    have h := congrFun (hmul x) α
    simpa [p, eval_gramRowPoly] using h
  have hp_zero : p = 0 := by
    apply MvPolynomial.funext
    intro x
    simp [hp_eval x]
  have hcoeff := congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff β.1) hp_zero
  simpa [p, coeff_gramRowPoly] using hcoeff

/-- The Gram coefficient map as a continuous linear map. -/
noncomputable def gramMapCLM (n r : ℕ) :
    Matrix (RootExp n r) (RootExp n r) ℝ →L[ℝ] (OutputExp n r → ℝ) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := gramMap
       map_add' := by
        intro A B
        funext γ
        simp [gramMap, coeffVec, gramPoly_add]
       map_smul' := by
        intro a A
        funext γ
        simp [gramMap, coeffVec, gramPoly_smul] } :
      Matrix (RootExp n r) (RootExp n r) ℝ →ₗ[ℝ] (OutputExp n r → ℝ))

@[simp] lemma gramMapCLM_apply {n r : ℕ}
    (A : Matrix (RootExp n r) (RootExp n r) ℝ) :
    gramMapCLM n r A = gramMap A := rfl

/-- The PSD Gram-image cone in finite coefficient space. -/
def gramSOSCoeffCone (n r : ℕ) : Set (OutputExp n r → ℝ) :=
  {c | ∃ Q : Matrix (RootExp n r) (RootExp n r) ℝ, Q.PosSemidef ∧ gramMap Q = c}

lemma exists_cone_lower_bound_of_compact_unit
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (K : Set E)
    (hKclosed : IsClosed K)
    (hKsmul : ∀ {a : ℝ} {x : E}, 0 ≤ a → x ∈ K → a • x ∈ K)
    (hker : ∀ x ∈ K, L x = 0 → x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, C * ‖x‖ ≤ ‖L x‖ := by
  obtain ⟨C, hC, hbound⟩ := ClosedConeImage.cone_norm_bound K hKclosed
    (fun x hx a ha ↦ hKsmul ha.le hx) L hker
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro x hx
  exact (inv_mul_le_iff₀ hC).mpr (hbound x hx)

lemma isClosed_image_of_closed_cone_with_lower_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (K : Set E)
    (hKclosed : IsClosed K)
    (hKsmul : ∀ {a : ℝ} {x : E}, 0 ≤ a → x ∈ K → a • x ∈ K)
    (hker : ∀ x ∈ K, L x = 0 → x = 0) :
    IsClosed (L '' K) :=
  ClosedConeImage.isClosed_image_of_conic_trivial_kernel K hKclosed
    (fun x hx a ha ↦ hKsmul ha.le hx) L hker

/-- The degree-bounded SOS cone as a subset of finite coefficient space. -/
def degreeBoundedSOSCoeffCone (n r : ℕ) : Set (OutputExp n r → ℝ) :=
  {c | ∃ S : MvPolynomial (Fin n) ℝ,
    Nonempty (DegreeBoundedSOS S r) ∧ coeffVec (2 * r) S = c}

lemma degreeBoundedSOSCoeffCone_eq_gramSOSCoeffCone (n r : ℕ) :
    degreeBoundedSOSCoeffCone n r = gramSOSCoeffCone n r := by
  classical
  ext c
  constructor
  · rintro ⟨S, hS, rfl⟩
    rcases degreeBoundedSOS_iff_exists_psd_gram.mp hS with ⟨Q, hQ, rfl⟩
    exact ⟨Q, hQ, rfl⟩
  · rintro ⟨Q, hQ, hQc⟩
    refine ⟨gramPoly Q, degreeBoundedSOS_iff_exists_psd_gram.mpr ⟨Q, hQ, rfl⟩, ?_⟩
    exact hQc


/-- Public finite-dimensional closedness theorem for the fixed-degree SOS cone.

This reusable theorem supplies the fixed-degree closedness input used later; the
Choi-Lam specialization is `n = 4`, `r = 2` plus the elementary `sInf` argument below. -/
theorem isClosed_degreeBoundedSOSCoeffCone (n r : ℕ) :
    IsClosed (degreeBoundedSOSCoeffCone n r) := by
  classical
  let K : Set (Matrix (RootExp n r) (RootExp n r) ℝ) := {Q | Q.PosSemidef}
  have hgramImage : gramSOSCoeffCone n r = (gramMapCLM n r) '' K := by
    ext c
    constructor
    · rintro ⟨Q, hQ, hQc⟩
      exact ⟨Q, hQ, by simpa [gramMapCLM_apply] using hQc⟩
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩
  rw [degreeBoundedSOSCoeffCone_eq_gramSOSCoeffCone, hgramImage]
  apply isClosed_image_of_closed_cone_with_lower_bound (L := gramMapCLM n r) (K := K)
  · have hHerm : IsClosed {Q : Matrix (RootExp n r) (RootExp n r) ℝ | Q.IsHermitian} := by
      simp only [Matrix.IsHermitian.ext_iff]
      rw [show {Q : Matrix (RootExp n r) (RootExp n r) ℝ |
          ∀ i j, star (Q j i) = Q i j} =
          ⋂ i, ⋂ j, {Q : Matrix (RootExp n r) (RootExp n r) ℝ |
            star (Q j i) = Q i j} by
        ext Q
        simp]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro j
      apply isClosed_eq
      · fun_prop
      · fun_prop
    have hQuad : IsClosed
        {Q : Matrix (RootExp n r) (RootExp n r) ℝ |
          ∀ x : RootExp n r → ℝ, 0 ≤ star x ⬝ᵥ Q.mulVec x} := by
      rw [show {Q : Matrix (RootExp n r) (RootExp n r) ℝ |
          ∀ x : RootExp n r → ℝ, 0 ≤ star x ⬝ᵥ Q.mulVec x} =
          ⋂ x : RootExp n r → ℝ,
            {Q : Matrix (RootExp n r) (RootExp n r) ℝ | 0 ≤ star x ⬝ᵥ Q.mulVec x} by
        ext Q
        simp]
      apply isClosed_iInter
      intro x
      apply isClosed_le
      · fun_prop
      · unfold Matrix.mulVec dotProduct
        fun_prop
    have hK : K =
        {Q : Matrix (RootExp n r) (RootExp n r) ℝ | Q.IsHermitian} ∩
          {Q : Matrix (RootExp n r) (RootExp n r) ℝ |
            ∀ x : RootExp n r → ℝ, 0 ≤ star x ⬝ᵥ Q.mulVec x} := by
      ext Q
      simp [K, Matrix.posSemidef_iff_dotProduct_mulVec]
    rw [hK]
    exact hHerm.inter hQuad
  · intro a Q ha hQ
    exact hQ.smul ha
  · intro Q hQ hmap
    change gramMap Q = 0 at hmap
    exact psd_eq_zero_of_gramMap_eq_zero hQ hmap

/-- Closedness of the degree-bounded SOS cone in coefficient `L1` topology.

This is the general fixed-degree closedness form used by the four-variable quartic case. -/
theorem degreeBoundedSOSCone_closed_coeffL1
    {n r : ℕ} {P : MvPolynomial (Fin n) ℝ}
    (hPdeg : P.totalDegree ≤ 2 * r)
    (hdist : sInf {d | ∃ S : MvPolynomial (Fin n) ℝ,
      Nonempty (DegreeBoundedSOS S r) ∧ d = coeffL1Distance P S} = 0) :
    Nonempty (DegreeBoundedSOS P r) := by
  classical
  let A : Set ℝ := {d | ∃ S : MvPolynomial (Fin n) ℝ,
    Nonempty (DegreeBoundedSOS S r) ∧ d = coeffL1Distance P S}
  have hA_nonempty : A.Nonempty := by
    refine ⟨coeffL1Distance P 0, ?_⟩
    exact ⟨0, ⟨zeroDegreeBoundedSOS n r⟩, rfl⟩
  have hnear : coeffVec (2 * r) P ∈ closure (degreeBoundedSOSCoeffCone n r) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hinf : sInf A < ε := by
      simpa [A, hdist] using hε
    obtain ⟨d, hdA, hdlt⟩ := exists_lt_of_csInf_lt hA_nonempty hinf
    rcases hdA with ⟨S, hS, rfl⟩
    refine ⟨coeffVec (2 * r) S, ⟨S, hS, rfl⟩, ?_⟩
    calc dist (coeffVec (2 * r) P) (coeffVec (2 * r) S)
        = ‖coeffVec (2 * r) P - coeffVec (2 * r) S‖ := dist_eq_norm _ _
      _ ≤ coeffL1Distance P S := norm_coeffVec_sub_le_coeffL1Distance P S
      _ < ε := hdlt
  have hmem : coeffVec (2 * r) P ∈ degreeBoundedSOSCoeffCone n r := by
    simpa [isClosed_degreeBoundedSOSCoeffCone n r |>.closure_eq] using hnear
  rcases hmem with ⟨T, hT, hcoeff⟩
  have hTdeg : T.totalDegree ≤ 2 * r := totalDegree_le_of_nonempty_degreeBoundedSOS hT
  have hPT : P = T := eq_of_coeffVec_eq hPdeg hTdeg hcoeff.symm
  simpa [hPT] using hT

end OptimalConvergenceRates

end
