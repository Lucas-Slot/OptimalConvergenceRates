import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.SelectorCentering
import OptimalConvergenceRates.SphereDimensionBounds.TensorMomentFunctional

/-! The finite selector functional and its positivity on quadratic squares. -/
noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.SelectorFunctional
open scoped BigOperators Matrix
open MvPolynomial
open SelectorCentering
variable {I : Type*} [Fintype I]

abbrev P (n : ℕ) := MvPolynomial (Fin n) ℝ

def transverse {n : ℕ} : P n →ₐ[ℝ] P (n+1) := rename Fin.succ

def s (n : ℕ) : P (n+1) := X 0

/-- Substitute the actual transverse point while keeping the scalar variable. -/
def sliceAt {n : ℕ} (x : Fin n → ℝ) : P (n+1) →ₐ[ℝ] Polynomial ℝ :=
  aeval (Fin.cases Polynomial.X (fun i => Polynomial.C (x i)))

def coefficientEvaluation {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : P (n+1) →ₗ[ℝ] ℝ :=
  (Polynomial.lcoeff ℝ k).comp (sliceAt x).toLinearMap

@[simp] theorem sliceAt_C {n : ℕ} (x : Fin n → ℝ) (a : ℝ) :
    sliceAt x (C a) = Polynomial.C a := by simp [sliceAt]

@[simp] theorem sliceAt_s {n : ℕ} (x : Fin n → ℝ) :
    sliceAt x (s n) = Polynomial.X := by simp [sliceAt,s]

@[simp] theorem sliceAt_transverse {n : ℕ} (x : Fin n → ℝ) (p : P n) :
    sliceAt x (transverse p) = Polynomial.C (eval x p) := by
  simp only [sliceAt, transverse, aeval_rename]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p i hp => simp [map_mul,hp]

/-- The raw actual coefficient functional. -/
def rawFunctional {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) : P (n+1) →ₗ[ℝ] ℝ :=
  ∑ t, ((Z t 0 0) • coefficientEvaluation (h t) 4
    + (Z t 0 1) • coefficientEvaluation (h t) 3
    + (Z t 1 1) • coefficientEvaluation (h t) 2
    + (Z t 1 2) • coefficientEvaluation (h t) 1
    + (Z t 2 2) • coefficientEvaluation (h t) 0)

/-- Degree-four filtering gives a genuine full-polynomial linear functional. -/
def functional {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) : P (n+1) →ₗ[ℝ] ℝ :=
  (rawFunctional h Z).comp (homogeneousComponent 4)

theorem functional_of_homogeneous {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (p : P (n + 1)) (hp : p.IsHomogeneous 4) :
    functional h Z p = rawFunctional h Z p := by
  simp [functional,homogeneousComponent_of_mem hp]

/-- An actual quadratic with the distinguished scalar coordinate separated. -/
def quadratic {n : ℕ} (a : ℝ) (l Q : P n) : P (n+1) :=
  C a * s n ^ 2 + s n * transverse l + transverse Q

@[simp] theorem sliceAt_quadratic {n : ℕ} (x : Fin n → ℝ) (a : ℝ) (l Q : P n) :
    sliceAt x (quadratic a l Q) =
      Polynomial.C a * Polynomial.X^2 + Polynomial.X * Polynomial.C (eval x l)
        + Polynomial.C (eval x Q) := by
  simp [quadratic]

theorem quadratic_homogeneous {n : ℕ} (a : ℝ) (l Q : P n)
    (hl : l.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2) :
    (quadratic a l Q).IsHomogeneous 2 := by
  have hs : (s n).IsHomogeneous 1 := isHomogeneous_X ℝ 0
  exact (((hs.pow 2).C_mul a).add (hs.mul (hl.rename_isHomogeneous))).add (hQ.rename_isHomogeneous)

private theorem univariate_square_expansion (a b c : ℝ) :
    (Polynomial.C a * Polynomial.X^2 + Polynomial.X * Polynomial.C b + Polynomial.C c)^2 =
      Polynomial.C (a^2)*Polynomial.X^4 + Polynomial.C (2*a*b)*Polynomial.X^3 +
      Polynomial.C (b^2+2*a*c)*Polynomial.X^2 + Polynomial.C (2*b*c)*Polynomial.X +
      Polynomial.C (c^2) := by
  simp only [map_pow,map_mul,map_add,map_ofNat]
  ring

theorem rawFunctional_quadratic_square {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (a : ℝ) (l Q : P n) :
    rawFunctional h Z ((quadratic a l Q)^2) =
      ∑ t, (Z t 0 0*a^2 + Z t 0 1*(2*a*eval (h t) l)
        + Z t 1 1*((eval (h t) l)^2+2*a*eval (h t) Q)
        + Z t 1 2*(2*eval (h t) l*eval (h t) Q)
        + Z t 2 2*(eval (h t) Q)^2) := by
  simp only [rawFunctional, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, coefficientEvaluation,
    LinearMap.comp_apply, Polynomial.lcoeff_apply, AlgHom.toLinearMap_apply,
    map_pow, sliceAt_quadratic]
  simp_rw [univariate_square_expansion]
  norm_num only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  simp only [ite_true,ite_false,add_zero,zero_add,mul_zero]


/-- Exact coordinate Hankel consistency, without a sphere normalization premise. -/
def CoordinateConsistency {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j, (∑ t, (Z t 0 2-Z t 1 1)*(h t i*h t j)) = 0

theorem consistency_eval_quadratic {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hcons : CoordinateConsistency h Z)
    (Q : P n) (hQ : Q.IsHomogeneous 2) :
    (∑ t, (Z t 0 2-Z t 1 1)*eval (h t) Q) = 0 := by
  obtain ⟨c,rfl⟩ := TensorMomentFunctional.exists_quadraticPolynomial Q hQ
  rw [TensorMomentFunctional.quadraticPolynomial_apply]
  simp only [map_sum,map_mul,eval_C,eval_X]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro ij _
  calc
    _ = c ij * ∑ t, (Z t 0 2-Z t 1 1)*(h t ij.1*h t ij.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = 0 := by rw [hcons ij.1 ij.2,mul_zero]

/-- The exact quadratic-form evaluation at a real finite three-vector. -/
theorem psd_three_nonneg (G : Matrix (Fin 3) (Fin 3) ℝ)
    (hG : G.PosSemidef) (a b c : ℝ) :
    0 ≤ G 0 0*a^2+2*G 0 1*a*b+2*G 0 2*a*c+
      G 1 1*b^2+2*G 1 2*b*c+G 2 2*c^2 := by
  have hsym (i j : Fin 3) : G j i = G i j := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using congrFun (congrFun hG.1 i) j
  have hg := hG.dotProduct_mulVec_nonneg ![a,b,c]
  norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hg
  rw [hsym 0 1, hsym 0 2, hsym 1 2] at hg
  convert hg using 1; ring

/-- Positivity is proved for actual separated homogeneous quadratic roots. -/
theorem rawFunctional_quadratic_square_nonneg {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (hcons : CoordinateConsistency h Z) (a : ℝ) (l Q : P n)
    (hQ : Q.IsHomogeneous 2) :
    0 ≤ rawFunctional h Z ((quadratic a l Q)^2) := by
  rw [rawFunctional_quadratic_square]
  have heq : (∑ t, (Z t 0 0*a^2 + Z t 0 1*(2*a*eval (h t) l)
      + Z t 1 1*((eval (h t) l)^2+2*a*eval (h t) Q)
      + Z t 1 2*(2*eval (h t) l*eval (h t) Q)
      + Z t 2 2*(eval (h t) Q)^2)) =
    (∑ t, (Z t 0 0*a^2 + 2*Z t 0 1*a*eval (h t) l
      + 2*Z t 0 2*a*eval (h t) Q + Z t 1 1*(eval (h t) l)^2
      + 2*Z t 1 2*eval (h t) l*eval (h t) Q
      + Z t 2 2*(eval (h t) Q)^2)) := by
    have hc := consistency_eval_quadratic h Z hcons Q hQ
    have hid : (∑ t, (Z t 0 0*a^2 + Z t 0 1*(2*a*eval (h t) l)
        + Z t 1 1*((eval (h t) l)^2+2*a*eval (h t) Q)
        + Z t 1 2*(2*eval (h t) l*eval (h t) Q)
        + Z t 2 2*(eval (h t) Q)^2)) =
      (∑ t, (Z t 0 0*a^2 + 2*Z t 0 1*a*eval (h t) l
        + 2*Z t 0 2*a*eval (h t) Q + Z t 1 1*(eval (h t) l)^2
        + 2*Z t 1 2*eval (h t) l*eval (h t) Q
        + Z t 2 2*(eval (h t) Q)^2))
      - 2*a*∑ t, (Z t 0 2-Z t 1 1)*eval (h t) Q := by
      rw [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [hid,hc,mul_zero,sub_zero]
  rw [heq]
  exact Finset.sum_nonneg fun t _ => psd_three_nonneg (Z t) (hZ t) a
    (eval (h t) l) (eval (h t) Q)

/-- Every actual homogeneous quadratic has the scalar/linear/quadratic split. -/
theorem exists_quadratic_decomposition {n : ℕ} (q : P (n + 1))
    (hq : q.IsHomogeneous 2) :
    ∃ a : ℝ, ∃ l Q : P n, l.IsHomogeneous 1 ∧ Q.IsHomogeneous 2 ∧
      q = quadratic a l Q := by
  obtain ⟨c,rfl⟩ := TensorMomentFunctional.exists_quadraticPolynomial q hq
  let l : P n := (∑ i, C (c (0,i.succ))*X i) + (∑ i, C (c (i.succ,0))*X i)
  let Q : P n := ∑ i, ∑ j, C (c (i.succ,j.succ))*X i*X j
  have hl : l.IsHomogeneous 1 := by
    apply IsHomogeneous.add <;> apply IsHomogeneous.sum <;> intro i _
    · exact (isHomogeneous_X ℝ i).C_mul _
    · exact (isHomogeneous_X ℝ i).C_mul _
  have hQ : Q.IsHomogeneous 2 := by
    apply IsHomogeneous.sum
    intro i _
    apply IsHomogeneous.sum
    intro j _
    simpa using ((isHomogeneous_X ℝ i).C_mul (c (i.succ,j.succ))).mul
      (isHomogeneous_X ℝ j)
  refine ⟨c (0,0),l,Q,hl,hQ,?_⟩
  simp only [TensorMomentFunctional.quadraticPolynomial_apply,Fintype.sum_prod_type,
    Fin.sum_univ_succ,quadratic,transverse,s,l,Q,map_add,map_sum,map_mul,
    rename_C,rename_X]
  simp_rw [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
  simp only [mul_comm,mul_left_comm,mul_assoc,pow_two]
  ring


/-- Positivity on EVERY actual homogeneous quadratic square. -/
theorem rawFunctional_homogeneous_square_nonneg {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (hcons : CoordinateConsistency h Z) (q : P (n + 1)) (hq : q.IsHomogeneous 2) :
    0 ≤ rawFunctional h Z (q^2) := by
  obtain ⟨a,l,Q,_,hQ,rfl⟩ := exists_quadratic_decomposition q hq
  exact rawFunctional_quadratic_square_nonneg h Z hZ hcons a l Q hQ

theorem functional_homogeneous_square_nonneg {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (hcons : CoordinateConsistency h Z) (q : P (n + 1)) (hq : q.IsHomogeneous 2) :
    0 ≤ functional h Z (q^2) := by
  rw [functional_of_homogeneous h Z _ (by simpa using hq.pow 2)]
  exact rawFunctional_homogeneous_square_nonneg h Z hZ hcons q hq

theorem functional_homogeneous_zero {n d : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hd : d ≠ 4)
    (p : P (n + 1)) (hp : p.IsHomogeneous d) : functional h Z p = 0 := by
  simp [functional,homogeneousComponent_of_mem hp,Ne.symm hd]

/-- Filtering removes lower homogeneous components, so positivity holds for
all roots of total degree at most two as well. -/
theorem functional_square_nonneg {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (hcons : CoordinateConsistency h Z) (q : P (n + 1)) (hq : q.totalDegree ≤ 2) :
    0 ≤ functional h Z (q^2) := by
  let a := homogeneousComponent 0 q
  let b := homogeneousComponent 1 q
  let c := homogeneousComponent 2 q
  have ha : a.IsHomogeneous 0 := homogeneousComponent_isHomogeneous _ _
  have hb : b.IsHomogeneous 1 := homogeneousComponent_isHomogeneous _ _
  have hc : c.IsHomogeneous 2 := homogeneousComponent_isHomogeneous _ _
  have hdec : q = a+b+c := TensorMomentFunctional.decomposition_two q hq
  have hexp : q^2 = a^2+b^2+c^2+C 2*(a*b)+C 2*(a*c)+C 2*(b*c) := by
    rw [hdec,map_ofNat]
    ring
  have h0 := functional_homogeneous_zero h Z (by decide : 0 ≠ 4) _
    (by simpa using ha.pow 2)
  have h2 := functional_homogeneous_zero h Z (by decide : 2 ≠ 4) _
    (by simpa using hb.pow 2)
  have hab := functional_homogeneous_zero h Z (by decide : 1 ≠ 4) _
    (by simpa using ha.mul hb)
  have hac := functional_homogeneous_zero h Z (by decide : 2 ≠ 4) _
    (by simpa using ha.mul hc)
  have hbc := functional_homogeneous_zero h Z (by decide : 3 ≠ 4) _
    (by simpa using hb.mul hc)
  rw [hexp]
  simp only [map_add,TensorMomentFunctional.linearMap_C_mul,h0,h2,hab,hac,hbc,
    mul_zero,zero_add,add_zero]
  exact functional_homogeneous_square_nonneg h Z hZ hcons c hc

/-- All raw scalar/transverse marginals are actual coefficient identities. -/
theorem rawFunctional_s_pow_transverse {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (k : ℕ) (p : P n) :
    rawFunctional h Z (s n^k*transverse p) =
      ∑ t, ((if 4=k then Z t 0 0*eval (h t) p else 0)
        + (if 3=k then Z t 0 1*eval (h t) p else 0)
        + (if 2=k then Z t 1 1*eval (h t) p else 0)
        + (if 1=k then Z t 1 2*eval (h t) p else 0)
        + (if 0=k then Z t 2 2*eval (h t) p else 0)) := by
  simp only [rawFunctional,LinearMap.sum_apply,LinearMap.add_apply,LinearMap.smul_apply,
    smul_eq_mul,coefficientEvaluation,LinearMap.comp_apply,Polynomial.lcoeff_apply,
    AlgHom.toLinearMap_apply,map_mul,map_pow,sliceAt_s,sliceAt_transverse,
    Polynomial.coeff_mul_C,Polynomial.coeff_X_pow]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> ring


section TensorBridge
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem quarticApply_smul_zero
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (a b c d : E) (r : ℝ) :
    quarticApply A (r • a) b c d = r * quarticApply A a b c d := by
  have hh := A.map_update_smul ![(0:E),b,c,d] (0:Fin 4) r a
  simpa only [quarticApply,quarticTuple_update0,smul_eq_mul] using hh

theorem quarticApply_smul_one
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (a b c d : E) (r : ℝ) :
    quarticApply A a (r • b) c d = r * quarticApply A a b c d := by
  have hh := A.map_update_smul ![a,(0:E),c,d] (1:Fin 4) r b
  simpa only [quarticApply,quarticTuple_update1,smul_eq_mul] using hh

theorem quarticApply_smul_two
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (a b c d : E) (r : ℝ) :
    quarticApply A a b (r • c) d = r * quarticApply A a b c d := by
  have hh := A.map_update_smul ![a,b,(0:E),d] (2:Fin 4) r c
  simpa only [quarticApply,quarticTuple_update2,smul_eq_mul] using hh

set_option maxHeartbeats 1000000 in
theorem quarticDiagonal_add (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hA : SymmetricQuarticForm A) (a b : E) :
    quarticDiagonal A (a+b) = quarticDiagonal A a + 4*quarticApply A a a a b
      + 6*quarticApply A a a b b + 4*quarticApply A a b b b + quarticDiagonal A b := by
  simp only [quarticDiagonal,quarticApply_add0,quarticApply_add1,
    quarticApply_add2,quarticApply_add3]
  simp only [quarticApply_swap0 A hA,quarticApply_swap1 A hA,quarticApply_swap2 A hA]
  ring

theorem quarticDiagonal_smul_add
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hA : SymmetricQuarticForm A) (a b : E) (r : ℝ) :
    quarticDiagonal A (r • a+b) = r^4*quarticDiagonal A a
      + r^3*(4*quarticApply A a a a b) + r^2*(6*quarticApply A a a b b)
      + r*(4*quarticApply A a b b b) + quarticDiagonal A b := by
  rw [quarticDiagonal_add A hA]
  simp only [quarticDiagonal,quarticApply_smul_zero,quarticApply_smul_one,
    quarticApply_smul_two,SelectorCentering.quarticApply_smul_last]
  ring
end TensorBridge

/-- Distinguished actual Euclidean scalar axis. -/
def axis (n : ℕ) : SelectorCentering.EP (n+1) :=
  (WithLp.equiv 2 (Fin (n+1) → ℝ)).symm (Fin.cons 1 (fun _ => 0))

/-- Actual Euclidean inclusion of a transverse coordinate tuple. -/
def embed {n : ℕ} (x : Fin n → ℝ) : SelectorCentering.EP (n+1) :=
  (WithLp.equiv 2 (Fin (n+1) → ℝ)).symm (Fin.cons 0 x)

@[simp] theorem axis_zero (n : ℕ) : axis n 0 = 1 := rfl
@[simp] theorem axis_succ {n : ℕ} (i : Fin n) : axis n i.succ = 0 := rfl
@[simp] theorem embed_zero {n : ℕ} (x : Fin n → ℝ) : embed x 0 = 0 := rfl
@[simp] theorem embed_succ {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : embed x i.succ = x i := rfl

theorem sliceAt_eval {n : ℕ} (x : Fin n → ℝ) (p : P (n + 1)) (r : ℝ) :
    Polynomial.eval r (sliceAt x p) = eval (Fin.cases r x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p i hp =>
      simp only [map_mul,Polynomial.eval_mul]
      change Polynomial.eval r (sliceAt x p) * Polynomial.eval r (sliceAt x (X i)) =
        eval (Fin.cases r x) p * eval (Fin.cases r x) (X i)
      rw [hp]
      congr 1
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [sliceAt]

theorem eval_axis_embed {n : ℕ} (x : Fin n → ℝ) (p : P (n + 1)) (r : ℝ) :
    euclideanPolynomialEval p (r • axis n+embed x) = eval (Fin.cases r x) p := by
  have hpoint : (fun i => (r • axis n+embed x) i) = Fin.cases r x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [PiLp.add_apply,PiLp.smul_apply]
  exact congrArg (fun z => eval z p) hpoint

/-- The actual univariate slice coefficients of every homogeneous quartic. -/
theorem sliceAt_homogeneous_quartic {n : ℕ} (x : Fin n → ℝ)
    (p : P (n + 1)) (hp : p.IsHomogeneous 4) :
    sliceAt x p =
      Polynomial.C (quarticDiagonal (homogeneousQuarticForm p) (axis n))*Polynomial.X^4
      + Polynomial.C (4*quarticApply (homogeneousQuarticForm p)
          (axis n) (axis n) (axis n) (embed x))*Polynomial.X^3
      + Polynomial.C (6*quarticApply (homogeneousQuarticForm p)
          (axis n) (axis n) (embed x) (embed x))*Polynomial.X^2
      + Polynomial.C (4*quarticApply (homogeneousQuarticForm p)
          (axis n) (embed x) (embed x) (embed x))*Polynomial.X
      + Polynomial.C (quarticDiagonal (homogeneousQuarticForm p) (embed x)) := by
  apply Polynomial.funext
  intro r
  rw [sliceAt_eval,← eval_axis_embed,← homogeneousQuarticForm_diagonal p hp]
  rw [← quarticDiagonal_eq (homogeneousQuarticForm p) (r • axis n+embed x)]
  rw [quarticDiagonal_smul_add _ (homogeneousQuarticForm_symmetric p)]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_X]
  ring

/-- Equality with the frozen polarization-defined finite functional on every
actual homogeneous quartic, in the explicit scalar/transverse coordinate split. -/
theorem rawFunctional_eq_polynomialMarginalFunctional {n : ℕ}
    (h : I → Fin n → ℝ) (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (p : P (n + 1)) (hp : p.IsHomogeneous 4) :
    rawFunctional h Z p =
      SelectorCentering.polynomialMarginalFunctional (axis n) (fun t => embed (h t)) Z p := by
  rw [SelectorCentering.polynomialMarginalFunctional_homogeneous p hp,
    SelectorCentering.tensorMarginalFunctional_apply]
  simp only [rawFunctional,LinearMap.sum_apply,LinearMap.add_apply,
    LinearMap.smul_apply,smul_eq_mul,coefficientEvaluation,LinearMap.comp_apply,
    AlgHom.toLinearMap_apply,Polynomial.lcoeff_apply]
  simp_rw [sliceAt_homogeneous_quartic _ p hp]
  norm_num only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  simp only [ite_true,ite_false,add_zero,zero_add,mul_zero]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The frozen finite polarization functional is therefore positive on every
actual homogeneous quadratic square. -/
theorem polynomialMarginalFunctional_homogeneous_square_nonneg {n : ℕ}
    (h : I → Fin n → ℝ) (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (hZ : ∀ t, (Z t).PosSemidef) (hcons : CoordinateConsistency h Z)
    (q : P (n + 1)) (hq : q.IsHomogeneous 2) :
    0 ≤ SelectorCentering.polynomialMarginalFunctional
      (axis n) (fun t => embed (h t)) Z (q^2) := by
  rw [← rawFunctional_eq_polynomialMarginalFunctional h Z _ (by simpa using hq.pow 2)]
  exact rawFunctional_homogeneous_square_nonneg h Z hZ hcons q hq


/-- Homogeneous degree-four scalar/transverse marginals of the filtered functional. -/
theorem functional_s_pow_transverse {n d : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (k : ℕ) (p : P n)
    (hp : p.IsHomogeneous d) (hdegree : k + d = 4) :
    functional h Z (s n^k*transverse p) =
      ∑ t, ((if 4=k then Z t 0 0*eval (h t) p else 0)
        + (if 3=k then Z t 0 1*eval (h t) p else 0)
        + (if 2=k then Z t 1 1*eval (h t) p else 0)
        + (if 1=k then Z t 1 2*eval (h t) p else 0)
        + (if 0=k then Z t 2 2*eval (h t) p else 0)) := by
  have hs : (s n).IsHomogeneous 1 := isHomogeneous_X ℝ 0
  have htrans : (transverse p).IsHomogeneous d := hp.rename_isHomogeneous
  have hhom : (s n^k*transverse p).IsHomogeneous 4 := by
    simpa only [Nat.one_mul,hdegree] using (hs.pow k).mul htrans
  rw [functional_of_homogeneous h Z _ hhom]
  exact rawFunctional_s_pow_transverse h Z k p

theorem functional_scalar_four {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) :
    functional h Z (s n^4) = diagonalMass Z 0 := by
  have hc := functional_s_pow_transverse h Z 4 (1:P n) (isHomogeneous_one (Fin n) ℝ) (by decide)
  simpa [transverse,diagonalMass] using hc

theorem functional_s3_linear {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (l : P n) (hl : l.IsHomogeneous 1) :
    functional h Z (s n^3*transverse l) = ∑ t, Z t 0 1*eval (h t) l := by
  simpa using functional_s_pow_transverse h Z 3 l hl (by decide)

theorem functional_s2_quadratic {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (Q : P n) (hQ : Q.IsHomogeneous 2) :
    functional h Z (s n^2*transverse Q) = ∑ t, Z t 1 1*eval (h t) Q := by
  simpa using functional_s_pow_transverse h Z 2 Q hQ (by decide)

theorem functional_s1_cubic {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (B : P n) (hB : B.IsHomogeneous 3) :
    functional h Z (s n*transverse B) = ∑ t, Z t 1 2*eval (h t) B := by
  simpa using functional_s_pow_transverse h Z 1 B hB (by decide)

theorem functional_transverse_quartic {n : ℕ} (h : I → Fin n → ℝ)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (F : P n) (hF : F.IsHomogeneous 4) :
    functional h Z (transverse F) = ∑ t, Z t 2 2*eval (h t) F := by
  simpa using functional_s_pow_transverse h Z 0 F hF (by decide)

/-- The actual transverse radius polynomial. -/
def radius (n : ℕ) : P n := ∑ i, X i^2

theorem radius_homogeneous (n : ℕ) : (radius n).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  simpa using (isHomogeneous_X ℝ i).pow 2

@[simp] theorem radius_eval {n : ℕ} (x : Fin n → ℝ) :
    eval x (radius n) = ∑ i, x i^2 := by simp [radius]

theorem functional_s2_radius {n : ℕ} (h : I → Fin n → ℝ)
    (hh : ∀ t, (∑ i, h t i ^ 2) = 1) (Z : I → Matrix (Fin 3) (Fin 3) ℝ) :
    functional h Z (s n^2*transverse (radius n)) = diagonalMass Z 1 := by
  rw [functional_s2_quadratic h Z _ (radius_homogeneous n)]
  simp only [radius_eval,hh,mul_one,diagonalMass]

theorem functional_radius_four {n : ℕ} (h : I → Fin n → ℝ)
    (hh : ∀ t, (∑ i, h t i ^ 2) = 1) (Z : I → Matrix (Fin 3) (Fin 3) ℝ) :
    functional h Z ((transverse (radius n))^2) = diagonalMass Z 2 := by
  rw [← map_pow, functional_transverse_quartic h Z _
    (by simpa using (radius_homogeneous n).pow 2)]
  simp only [map_pow,radius_eval,hh,one_pow,mul_one,diagonalMass]

/-- Actual centered transverse linear coordinate. -/
def centeredCoordinate {n : ℕ} (mu : Fin n → ℝ) (i : Fin n) : P (n+1) :=
  X i.succ-C (mu i)*s n

theorem functional_centered_third_moment_of_relation {n : ℕ}
    (h : I → Fin n → ℝ) (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (mu : Fin n → ℝ) (hmu : ∀ i, (∑ t, Z t 0 1 * h t i) = mu i * diagonalMass Z 0)
    (i : Fin n) : functional h Z (s n^3*centeredCoordinate mu i)=0 := by
  have hid : s n^3*centeredCoordinate mu i =
      s n^3*transverse (X i)-C (mu i)*s n^4 := by
    simp only [centeredCoordinate,transverse,rename_X]
    ring
  rw [hid,map_sub,TensorMomentFunctional.linearMap_C_mul,
    functional_s3_linear h Z _ (isHomogeneous_X ℝ i),functional_scalar_four]
  simp only [eval_X,hmu,sub_self]

theorem functional_centered_third_moment {n : ℕ}
    (h : I → SelectorCentering.EP n) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (i : Fin n) : functional (fun t j => h t j) Z
      (s n^3*centeredCoordinate (fun j => centeringVector h Z j) i)=0 := by
  apply functional_centered_third_moment_of_relation
  intro j
  have hv := leadingMass_smul_centeringVector_of_psd h hh Z hZ
  have hc := congrArg (EuclideanSpace.proj j) hv
  simpa [thirdMomentVector,map_sum,map_smul,smul_eq_mul,mul_comm] using hc.symm


/-- The actual squared radius of a finite family of polynomial coordinates. -/
def sumSquares {m k : ℕ} (v : Fin k → P m) : P m := ∑ i, v i^2

theorem sumSquares_degree {m k : ℕ} (v : Fin k → P m)
    (hv : ∀ i, (v i).totalDegree ≤ 1) : (sumSquares v).totalDegree ≤ 2 := by
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro i _
  have hvi := hv i
  exact (totalDegree_pow _ _).trans (by omega)

/-- A product of two sums of squares of linear roots has nonnegative value. -/
theorem product_sumSquares_nonneg {m k l : ℕ} (E : P m →ₗ[ℝ] ℝ)
    (hE : ∀ q, q.totalDegree ≤ 2 → 0 ≤ E (q ^ 2))
    (v : Fin k → P m) (z : Fin l → P m)
    (hv : ∀ i, (v i).totalDegree ≤ 1) (hz : ∀ j, (z j).totalDegree ≤ 1) :
    0 ≤ E (sumSquares v*sumSquares z) := by
  have hid : sumSquares v*sumSquares z = ∑ i, ∑ j, (v i*z j)^2 := by
    simp only [sumSquares,Finset.sum_mul,Finset.mul_sum,mul_pow]
    rw [Finset.sum_comm]
  rw [hid,map_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [map_sum]
  apply Finset.sum_nonneg
  intro j _
  apply hE
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (hv i) (hz j))

/-- The fourth-power vector triangle estimate is proved with actual polynomial
squares, rather than inferred from a pointwise nonnegative quartic. -/
theorem fourthRadius_triangle {m k : ℕ} (E : P m →ₗ[ℝ] ℝ)
    (hE : ∀ q, q.totalDegree ≤ 2 → 0 ≤ E (q ^ 2))
    (v z : Fin k → P m) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (hz : ∀ i, (z i).totalDegree ≤ 1) :
    E ((sumSquares (fun i => v i-z i))^2) ≤
      8*(E ((sumSquares v)^2)+E ((sumSquares z)^2)) := by
  let plus := sumSquares (fun i => v i+z i)
  let minus := sumSquares (fun i => v i-z i)
  have hplusdeg : plus.totalDegree ≤ 2 := sumSquares_degree _ fun i =>
    (totalDegree_add _ _).trans (max_le (hv i) (hz i))
  have hdiffdeg : (sumSquares v-sumSquares z).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le (sumSquares_degree v hv) (sumSquares_degree z hz))
  have hprod : 0 ≤ E (plus*minus) := product_sumSquares_nonneg E hE _ _
    (fun i => (totalDegree_add _ _).trans (max_le (hv i) (hz i)))
    (fun i => (totalDegree_sub _ _).trans (max_le (hv i) (hz i)))
  have hsum : plus+minus=2*(sumSquares v+sumSquares z) := by
    dsimp [plus,minus,sumSquares]
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i, 2*(v i^2+z i^2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
  have hid : C (8:ℝ)*((sumSquares v)^2+(sumSquares z)^2)-minus^2 =
      C 4*(sumSquares v-sumSquares z)^2+C 2*(plus*minus)+plus^2 := by
    have hp : plus=2*(sumSquares v+sumSquares z)-minus := by linear_combination hsum
    rw [hp,map_ofNat,map_ofNat,map_ofNat]
    ring
  have heq := congrArg E hid
  simp only [map_sub,map_add,TensorMomentFunctional.linearMap_C_mul] at heq
  have hp := hE plus hplusdeg
  have hd := hE _ hdiffdeg
  dsimp [minus] at heq
  linarith

theorem euclidean_norm_sq {n : ℕ} (x : SelectorCentering.EP n) :
    ‖x‖^2=∑ i, x i^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs,sq_abs]

theorem functional_centered_radius_four {n : ℕ}
    (h : I → SelectorCentering.EP n) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (hcons : SelectorCentering.QuadraticConsistency h Z) :
    functional (fun t j => h t j) Z
      ((sumSquares (fun i => centeredCoordinate (fun j => centeringVector h Z j) i))^2)
      ≤ 16*diagonalMass Z 2 := by
  let hc : I → Fin n → ℝ := fun t i => h t i
  let mu := centeringVector h Z
  let v : Fin n → P (n+1) := fun i => X i.succ
  let z : Fin n → P (n+1) := fun i => C (mu i)*s n
  have hcoord : CoordinateConsistency hc Z := hcons
  have hE := functional_square_nonneg hc Z hZ hcoord
  have hv (i : Fin n) : (v i).totalDegree ≤ 1 := (isHomogeneous_X ℝ i.succ).totalDegree_le
  have hz (i : Fin n) : (z i).totalDegree ≤ 1 := by
    exact ((isHomogeneous_X ℝ (0:Fin (n+1))).C_mul (mu i)).totalDegree_le
  have htri := fourthRadius_triangle (functional hc Z) hE v z hv hz
  have hunit (t : I) : (∑ i, hc t i^2)=1 := by
    rw [← euclidean_norm_sq,hh t,one_pow]
  have hva : sumSquares v=transverse (radius n) := by
    simp only [sumSquares,v,transverse,radius,map_sum,map_pow,rename_X]
  have hza : sumSquares z=C (∑ i, mu i^2)*s n^2 := by
    dsimp [sumSquares,z]
    calc
      _ = ∑ i, C (mu i^2)*s n^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_pow,map_pow]
      _ = _ := by rw [← Finset.sum_mul,← map_sum]
  have hzsq : (sumSquares z)^2=C (‖mu‖^4)*s n^4 := by
    rw [hza,← euclidean_norm_sq,mul_pow,← map_pow]
    have hpow : (‖mu‖^2)^2=‖mu‖^4 := by ring
    have hsquare : (s n^2)^2=s n^4 := by ring
    rw [hpow,hsquare]
  have hfirst : functional hc Z ((sumSquares v)^2)=diagonalMass Z 2 := by
    rw [hva,functional_radius_four hc hunit Z]
  have hsecond : functional hc Z ((sumSquares z)^2)=‖mu‖^4*diagonalMass Z 0 := by
    rw [hzsq,TensorMomentFunctional.linearMap_C_mul,functional_scalar_four]
  have hmass := (centeringVector_bounds h hh Z hZ
    (traceConsistency_of_quadraticConsistency h hh Z hcons)).1
  rw [hfirst,hsecond] at htri
  change functional hc Z ((sumSquares (fun i => v i-z i))^2) ≤ 16*diagonalMass Z 2
  linarith


/-- The filtered actual functional agrees with the frozen polarization functional
on every homogeneous quartic. -/
theorem functional_eq_polynomialMarginalFunctional {n : ℕ}
    (h : I → Fin n → ℝ) (Z : I → Matrix (Fin 3) (Fin 3) ℝ)
    (p : P (n + 1)) (hp : p.IsHomogeneous 4) :
    functional h Z p =
      SelectorCentering.polynomialMarginalFunctional (axis n) (fun t => embed (h t)) Z p := by
  rw [functional_of_homogeneous h Z p hp]
  exact rawFunctional_eq_polynomialMarginalFunctional h Z p hp

/-- The same actual functional has both quadratic-square positivity and the
actual centered-quartic `332/3` estimate; no separate functional is substituted. -/
theorem functional_pullback_abs_le {n : ℕ} (hn : 0 < n)
    (p : P n) (hp : p.IsHomogeneous 4) (q : P (n + 1)) (hq : q.IsHomogeneous 4)
    (L : SelectorCentering.EP (n + 1) →L[ℝ] SelectorCentering.EP n)
    (hpull : ∀ x, euclideanPolynomialEval q x = euclideanPolynomialEval p (L x))
    (h : I → SelectorCentering.EP n) (hh : ∀ t, ‖h t‖ = 1)
    (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (hZ : ∀ t, (Z t).PosSemidef)
    (hcons : SelectorCentering.QuadraticConsistency h Z)
    (he : L (axis n) = -centeringVector h Z)
    (hv : ∀ t, L (embed (fun i => h t i)) = h t) :
    |functional (fun t i => h t i) Z q| ≤
      (332/3 : ℝ)*OptimalConvergenceRates.SphereDimensionBounds.Foundation.sphereSupNorm p*diagonalMass Z 2 := by
  rw [functional_eq_polynomialMarginalFunctional _ Z q hq]
  exact SelectorCentering.polynomialMarginalFunctional_pullback_abs_le_of_consistency
    hn p hp q hq L hpull (axis n) (fun t => embed (fun i => h t i)) h hh Z hZ hcons he hv

end OptimalConvergenceRates.SphereDimensionBounds.SelectorFunctional
