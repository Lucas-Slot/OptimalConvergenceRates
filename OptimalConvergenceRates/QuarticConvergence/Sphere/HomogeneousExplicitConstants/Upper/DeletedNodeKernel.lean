import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.GegenbauerSpectralMoments
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.JacobiTwoBlockLocalization

/-! A monic polynomial deleting two indexed quadrature nodes. Concentration
uses actual positive angular square norms and nonnegative spectral weights;
no simplicity or ordering of the whole spectrum is assumed. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace DeletedNodeKernel

open scoped BigOperators
open Polynomial GegenbauerJacobi GegenbauerSpectralMoments FiniteSpectralMeasure
  JacobiSpectralSupport AngularPolynomialPositivity

def omittedSet {ell : ℕ} (i j : Fin ell) : Finset (Fin ell) :=
  (Finset.univ.erase i).erase j

def deletedPolynomial {ell : ℕ} (nodes : Fin ell → ℝ) (i j : Fin ell) : Polynomial ℝ :=
  ∏ k ∈ omittedSet i j,(X-C (nodes k))

theorem omittedSet_card {ell : ℕ} (i j : Fin ell) (hij : i ≠ j) :
    (omittedSet i j).card=ell-2 := by
  unfold omittedSet
  rw [Finset.card_erase_of_mem (by simp [hij.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp only [Finset.card_univ,Fintype.card_fin]
  omega

theorem deletedPolynomial_monic {ell : ℕ} (nodes : Fin ell → ℝ) (i j : Fin ell) :
    (deletedPolynomial nodes i j).Monic := monic_prod_X_sub_C nodes _

theorem deletedPolynomial_ne_zero {ell : ℕ} (nodes : Fin ell → ℝ) (i j : Fin ell) :
    deletedPolynomial nodes i j ≠ 0 := (deletedPolynomial_monic nodes i j).ne_zero

theorem deletedPolynomial_degree {ell : ℕ} (nodes : Fin ell → ℝ) (i j : Fin ell)
    (hij : i ≠ j) : (deletedPolynomial nodes i j).natDegree=ell-2 := by
  rw [deletedPolynomial,natDegree_finsetProd_X_sub_C_eq_card,omittedSet_card i j hij]

theorem deletedPolynomial_eval_zero {ell : ℕ} (nodes : Fin ell → ℝ) (i j k : Fin ell)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (deletedPolynomial nodes i j).eval (nodes k)=0 := by
  rw [deletedPolynomial,eval_prod]
  apply Finset.prod_eq_zero (i:=k)
  · simp [omittedSet,hki,hkj]
  · simp

/-- The concentration step has the exact quadrature formula as an
explicit intermediate premise. The final supplier instantiates it with
the actual Gegenbauer matrix. -/
theorem ratio_bound_of_quadrature {N ell : ℕ} (hell : 2 ≤ ell)
    (hquad : ∀ p : Polynomial ℝ,p.natDegree ≤ 2*ell-2 →
      normalizedZonalFunctional (N-2) p=
        ∑ k : Fin ell,p.eval ((jacobi_hermitian N ell).eigenvalues k)*
          weight (jacobi_hermitian N ell) (initialVector (by omega : 0 < ell)) k)
    (i j : Fin ell) (hij : i ≠ j) (c : ℝ)
    (hci : c ≤ (jacobi_hermitian N ell).eigenvalues i)
    (hcj : c ≤ (jacobi_hermitian N ell).eigenvalues j)
    (hupper : ∀ k : Fin ell,(jacobi_hermitian N ell).eigenvalues k ≤ 1) :
    let chi := deletedPolynomial (fun k ↦ (jacobi_hermitian N ell).eigenvalues k) i j
    4*normalizedZonalFunctional (N-2) ((1-X)^2*chi^2)/
      normalizedZonalFunctional (N-2) (chi^2) ≤ 4*(1-c)^2 := by
  intro chi
  let nodes : Fin ell→ℝ := fun k ↦ (jacobi_hermitian N ell).eigenvalues k
  let weights : Fin ell→ℝ := fun k ↦
    weight (jacobi_hermitian N ell) (initialVector (by omega : 0 < ell)) k
  have hdeg : chi.natDegree=ell-2 := deletedPolynomial_degree nodes i j hij
  have hmass : 0 < normalizedZonalFunctional (N-2) (chi^2) :=
    zonal_square_pos _ _ (deletedPolynomial_ne_zero nodes i j)
  have hsqdeg : (chi^2).natDegree ≤ 2*ell-2 := by
    have hd := natDegree_pow_le (p:=chi) (n:=2)
    rw [hdeg] at hd
    omega
  have hnumdeg : ((1-X)^2*chi^2).natDegree ≤ 2*ell-2 := by
    have hd := natDegree_mul_le (p:=(1-X)^2) (q:=chi^2)
    have hc := natDegree_pow_le (p:=chi) (n:=2)
    have he : ((1-X:Polynomial ℝ)^2).natDegree ≤ 2 := by
      exact (natDegree_pow_le (p:=(1-X:Polynomial ℝ)) (n:=2)).trans (by
        have hx := natDegree_sub_le (1:Polynomial ℝ) X
        norm_num at hx ⊢
        omega)
    rw [hdeg] at hc
    omega
  have hsum : normalizedZonalFunctional (N-2) ((1-X)^2*chi^2) ≤
      (1-c)^2*normalizedZonalFunctional (N-2) (chi^2) := by
    rw [hquad _ hnumdeg,hquad _ hsqdeg,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    change (((1-X)^2*chi^2).eval (nodes k))*weights k ≤
      (1-c)^2*((chi^2).eval (nodes k)*weights k)
    simp only [eval_mul,eval_pow,eval_sub,eval_one,eval_X]
    by_cases hki : k=i
    · subst k
      have hdiff : (1-nodes i)^2 ≤ (1-c)^2 := by
        have hu := hupper i
        change nodes i ≤ 1 at hu
        change c ≤ nodes i at hci
        nlinarith [sq_nonneg (nodes i-c)]
      have hnonneg : 0 ≤ (chi.eval (nodes i))^2*weights i :=
        mul_nonneg (sq_nonneg _) (weight_nonnegative _ _ _)
      nlinarith [mul_le_mul_of_nonneg_right hdiff hnonneg]
    · by_cases hkj : k=j
      · subst k
        have hdiff : (1-nodes j)^2 ≤ (1-c)^2 := by
          have hu := hupper j
          change nodes j ≤ 1 at hu
          change c ≤ nodes j at hcj
          nlinarith [sq_nonneg (nodes j-c)]
        have hnonneg : 0 ≤ (chi.eval (nodes j))^2*weights j :=
          mul_nonneg (sq_nonneg _) (weight_nonnegative _ _ _)
        nlinarith [mul_le_mul_of_nonneg_right hdiff hnonneg]
      · have hz : chi.eval (nodes k)=0 := deletedPolynomial_eval_zero nodes i j k hki hkj
        rw [hz]
        simp
  apply (div_le_iff₀ hmass).mpr
  nlinarith

end DeletedNodeKernel
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
