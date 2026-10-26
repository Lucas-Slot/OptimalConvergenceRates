import OptimalConvergenceRates.SphereDimensionBounds.JacobiSpectralSupport
import OptimalConvergenceRates.SphereDimensionBounds.CyclicSpectralMeasure

/-! Exact polynomial spectral moments from the finite Gegenbauer Krylov
identity. The identity is an explicit input of these intermediate lemmas;
its actual construction is supplied in the finite-coordinate module. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.GegenbauerSpectralMoments

open scoped BigOperators InnerProductSpace
open Polynomial Matrix GegenbauerNorms GegenbauerGram GegenbauerJacobi
  FiniteSpectralMeasure JacobiSpectralSupport

abbrev Vector (ell : ℕ) := EuclideanSpace ℝ (Fin ell)

def initialVector {ell : ℕ} (hell : 0 < ell) : Vector ell :=
  EuclideanSpace.single ⟨0,hell⟩ 1

theorem initial_norm {ell : ℕ} (hell : 0 < ell) : ‖initialVector hell‖=1 := by
  simp [initialVector]

theorem initial_polynomialMap (N : ℕ) {ell : ℕ} (hell : 0 < ell) :
    polynomialMap N ell (fun i => initialVector hell i)=1 := by
  have hs : (fun i => initialVector hell i)=Pi.single ⟨0,hell⟩ 1 := by
    funext i
    simp [initialVector,PiLp.single_apply,Pi.single_apply]
  rw [hs,polynomialMap_single,normalized_zero]

theorem pair_vectorMap {N ell : ℕ} (hN : 3 ≤ N) (v w : Vector ell) :
    pair (N-2) (polynomialMap N ell (fun i => v i))
      (polynomialMap N ell (fun i => w i))=⟪v,w⟫_ℝ := by
  rw [pair_polynomialMap hN,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.inner_apply,conj_trivial]
  ring

theorem exact_power_of_krylov {N ell : ℕ} (hN : 3 ≤ N) (hell : 0 < ell)
    (hpower : ∀ k : ℕ,k < ell → polynomialMap N ell
      (fun i => iterateVector (jacobi N ell) k (initialVector hell) i)=X^k)
    (k : ℕ) (hk : k ≤ 2*ell-2) :
    normalizedZonalFunctional (N-2) (X^k)=
      ∑ i : Fin ell,((jacobi_hermitian N ell).eigenvalues i)^k*
        weight (jacobi_hermitian N ell) (initialVector hell) i := by
  let a := k/2
  let b := k-a
  have hab : a+b=k := by dsimp [a,b];omega
  have ha : a < ell := by dsimp [a];omega
  have hb : b < ell := by dsimp [a,b];omega
  calc
    _=pair (N-2) (X^a) (X^b) := by unfold pair;rw [←pow_add,hab]
    _=pair (N-2)
        (polynomialMap N ell (fun i => iterateVector (jacobi N ell) a (initialVector hell) i))
        (polynomialMap N ell (fun i => iterateVector (jacobi N ell) b (initialVector hell) i)) := by
      rw [hpower a ha,hpower b hb]
    _=⟪iterateVector (jacobi N ell) a (initialVector hell),
        iterateVector (jacobi N ell) b (initialVector hell)⟫_ℝ := pair_vectorMap hN _ _
    _=_ := by rw [inner_iterates (jacobi_hermitian N ell),hab]

theorem exact_polynomial_of_krylov {N ell : ℕ} (hN : 3 ≤ N) (hell : 0 < ell)
    (hpower : ∀ k : ℕ,k < ell → polynomialMap N ell
      (fun i => iterateVector (jacobi N ell) k (initialVector hell) i)=X^k)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ 2*ell-2) :
    normalizedZonalFunctional (N-2) p=
      ∑ i : Fin ell,p.eval ((jacobi_hermitian N ell).eigenvalues i)*
        weight (jacobi_hermitian N ell) (initialVector hell) i := by
  have hexp := p.as_sum_range_C_mul_X_pow
  have heval (i : Fin ell) : p.eval ((jacobi_hermitian N ell).eigenvalues i)=
      ∑ k ∈ Finset.range (p.natDegree+1),p.coeff k*((jacobi_hermitian N ell).eigenvalues i)^k := by
    conv_lhs => rw [hexp]
    simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  calc
    _=∑ k ∈ Finset.range (p.natDegree+1),p.coeff k*
        normalizedZonalFunctional (N-2) (X^k) := by
      conv_lhs => rw [hexp]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul]
    _=∑ k ∈ Finset.range (p.natDegree+1),p.coeff k*
        ∑ i : Fin ell,((jacobi_hermitian N ell).eigenvalues i)^k*
          weight (jacobi_hermitian N ell) (initialVector hell) i := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ 2*ell-2 := by have hm := Finset.mem_range.mp hk;omega
      rw [exact_power_of_krylov hN hell hpower k hk']
    _=_ := by
      simp_rw [heval,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem cyclic_of_krylov {N ell : ℕ} (hN : 3 ≤ N) (hell : 0 < ell)
    (hpower : ∀ k : ℕ,k < ell → polynomialMap N ell
      (fun i => iterateVector (jacobi N ell) k (initialVector hell) i)=X^k)
    (hdegree : ∀ w : Vector ell,
      (polynomialMap N ell (fun i => w i)).natDegree < ell) :
    CyclicSpectralMeasure.IsCyclic (jacobi N ell) (initialVector hell) := by
  intro w hw
  let p := polynomialMap N ell (fun i => w i)
  have horth (k : ℕ) (hk : k < ell) : pair (N-2) p (X^k)=0 := by
    rw [←hpower k hk]
    exact (pair_vectorMap hN w _).trans (hw k)
  have hself : pair (N-2) p p=0 := by
    calc
      _=pair (N-2) p (∑ k ∈ Finset.range (p.natDegree+1),C (p.coeff k)*X^k) :=
        congrArg (pair (N-2) p) p.as_sum_range_C_mul_X_pow
      _=∑ k ∈ Finset.range (p.natDegree+1),p.coeff k*pair (N-2) p (X^k) := by
        unfold pair
        rw [Finset.mul_sum,map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [show p*(C (p.coeff k)*X^k)=C (p.coeff k)*(p*X^k) by ring,
          ←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul]
      _=0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hk' : k < ell := by
          have hm := Finset.mem_range.mp hk
          have hd := hdegree w
          change p.natDegree < ell at hd
          omega
        rw [horth k hk',mul_zero]
  have hnorm : ‖w‖^2=0 := by
    rw [←real_inner_self_eq_norm_sq,←pair_vectorMap hN]
    exact hself
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

end OptimalConvergenceRates.SphereDimensionBounds.GegenbauerSpectralMoments
