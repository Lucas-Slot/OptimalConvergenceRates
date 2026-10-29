import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.BivariateTaylorPolynomial
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SphereZonalPolynomialRange

/-! Joint homogeneity gives the exact same-degree range for an averaged
polynomial in both the output point and the integration point. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace BivariateZonalRange

open scoped BigOperators InnerProductSpace
open MeasureTheory MvPolynomial SphereMeasure SphereMoments SphereZonalPolynomialRange
  BivariateTaylorPolynomial

abbrev Poly (n : ℕ) := Foundation.Polynomial n

def leftExponent {n : ℕ} (a : Fin n ⊕ Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  (Finsupp.sumFinsuppEquivProdFinsupp a).1
def rightExponent {n : ℕ} (a : Fin n ⊕ Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  (Finsupp.sumFinsuppEquivProdFinsupp a).2

theorem degree_fintype {ι : Type*} [Fintype ι] (a : ι →₀ ℕ) : a.degree=∑ i,a i := by
  exact Finsupp.degree_eq_sum a

theorem split_degree {n : ℕ} (a : Fin n ⊕ Fin n →₀ ℕ) :
    a.degree=(leftExponent a).degree+(rightExponent a).degree := by
  rw [degree_fintype,degree_fintype,degree_fintype,Fintype.sum_sum_type]
  rfl

theorem eval_monomial_fintype {ι : Type*} [Fintype ι] (a : ι →₀ ℕ) (c : ℝ) (x : ι → ℝ) :
    eval x (monomial a c)=c*∏ i,x i^a i := by
  rw [eval_monomial,Finsupp.prod_fintype]
  intro i
  exact pow_zero _

theorem eval_monomial_split {n : ℕ} (a : Fin n ⊕ Fin n →₀ ℕ) (c : ℝ)
    (x y : Fin n → ℝ) :
    eval (Sum.elim x y) (monomial a c)=
      c*eval x (monomial (leftExponent a) (1:ℝ))*eval y (monomial (rightExponent a) (1:ℝ)) := by
  rw [eval_monomial_fintype,eval_monomial_fintype,eval_monomial_fintype,Fintype.prod_sum_type]
  simp only [one_mul,Sum.elim_inl,Sum.elim_inr,leftExponent,rightExponent,
    Finsupp.fst_sumFinsuppEquivProdFinsupp,Finsupp.snd_sumFinsuppEquivProdFinsupp]
  ring

def bivariateAverage {n : ℕ} (B : Joint n) (P : Polynomial ℝ) (x : E n) : ℝ :=
  ∫ y : Sphere n,eval (Sum.elim (fun i ↦ x i) (fun i ↦ y.1 i)) B*P.eval ⟪x,y.1⟫_ℝ ∂surface n

theorem exists_homogeneous_bivariate_range {n d : ℕ} (hn : 0 < n)
    (B : Joint n) (hB : B.IsHomogeneous d) (P : Polynomial ℝ) :
    ∃ q : Poly n,q.IsHomogeneous d ∧ ∀ x : Sphere n,
      eval (fun i ↦ x.1 i) q=bivariateAverage B P x.1 := by
  classical
  let w : (Fin n⊕Fin n →₀ ℕ) → Poly n := fun a ↦ Classical.choose
    (exists_homogeneous_zonal_polynomial hn (monomial (rightExponent a) (1:ℝ))
      (isHomogeneous_monomial (1:ℝ) rfl) P)
  have hwhom (a : Fin n⊕Fin n →₀ ℕ) : (w a).IsHomogeneous (rightExponent a).degree :=
    (Classical.choose_spec (exists_homogeneous_zonal_polynomial hn
      (monomial (rightExponent a) (1:ℝ)) (isHomogeneous_monomial (1:ℝ) rfl) P)).1
  have hweval (a : Fin n⊕Fin n →₀ ℕ) (x : Sphere n) :
      eval (fun i ↦ x.1 i) (w a)=zonalAverage (monomial (rightExponent a) (1:ℝ)) P x.1 :=
    (Classical.choose_spec (exists_homogeneous_zonal_polynomial hn
      (monomial (rightExponent a) (1:ℝ)) (isHomogeneous_monomial (1:ℝ) rfl) P)).2 x
  refine ⟨∑ a∈B.support,C (coeff a B)*monomial (leftExponent a) (1:ℝ)*w a,?_,?_⟩
  · apply IsHomogeneous.sum
    intro a ha
    have hdeg : a.degree=d := by
      simpa only [Finsupp.degree_apply,Finsupp.weight_apply,Pi.one_apply,
        smul_eq_mul,mul_one,Finsupp.sum] using hB (mem_support_iff.mp ha)
    have hh := ((isHomogeneous_monomial (1:ℝ) (rfl : (leftExponent a).degree=(leftExponent
      a).degree)).mul
      (hwhom a)).C_mul (coeff a B)
    simpa only [mul_assoc,←split_degree,hdeg] using hh
  · intro x
    simp only [eval_sum,eval_mul,eval_C]
    simp_rw [hweval]
    change (∑ a∈B.support,coeff a B*eval (fun i ↦ x.1 i) (monomial (leftExponent a) (1:ℝ))*
      ∫ y : Sphere n,eval (fun i ↦ y.1 i) (monomial (rightExponent a) (1:ℝ))*P.eval ⟪x.1,y.1⟫_ℝ
        ∂surface n)=_
    calc
      _=∫ y : Sphere n,∑ a∈B.support,
          (coeff a B*eval (fun i ↦ x.1 i) (monomial (leftExponent a) (1:ℝ)))*
            (eval (fun i ↦ y.1 i) (monomial (rightExponent a) (1:ℝ))*P.eval ⟪x.1,y.1⟫_ℝ) ∂surface
              n := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro a ha
          exact (integral_const_mul _ _).symm
        · intro a ha
          exact (integrable_zonalAverage hn (monomial (rightExponent a) (1:ℝ)) P x.1).const_mul _
      _=bivariateAverage B P x.1 := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro y
        dsimp only
        have heval := congrArg (eval (Sum.elim (fun i ↦ x.1 i) (fun i ↦ y.1 i))) B.as_sum
        rw [eval_sum] at heval
        rw [heval,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        rw [eval_monomial_split]
        ring

/-- The actual averaged cubic Taylor operator has the same homogeneous
degree as its input, independently of the scalar kernel degree. -/
theorem exists_homogeneous_cubicTaylor_range {n d : ℕ} (hn : 0 < n)
    (p : Poly n) (hp : p.IsHomogeneous d) (P : Polynomial ℝ) :
    ∃ q : Poly n,q.IsHomogeneous d ∧ ∀ x : Sphere n,
      eval (fun i ↦ x.1 i) q=
        ∫ y : Sphere n,DegreeTaylorBounds.evalForm (CubicTaylorBounds.cubicModel y.1 p) (x.1-y.1)*
          P.eval ⟪x.1,y.1⟫_ℝ ∂surface n := by
  obtain ⟨q,hq,hqe⟩ := exists_homogeneous_bivariate_range hn (bivariateTaylor p)
    (bivariateTaylor_homogeneous p hp) P
  refine ⟨q,hq,?_⟩
  intro x
  rw [hqe]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  rw [bivariateTaylor_eval]

end BivariateZonalRange
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
