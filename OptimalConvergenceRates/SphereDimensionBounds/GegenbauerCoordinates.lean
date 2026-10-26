import OptimalConvergenceRates.SphereDimensionBounds.GegenbauerGram

/-! Exact finite coordinates for the actual orthonormal Gegenbauer
polynomials, and compressed multiplication without boundary-term algebra. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.GegenbauerCoordinates

open scoped BigOperators
open Polynomial Matrix GegenbauerNorms GegenbauerJacobi GegenbauerGram

def polynomialLinear (N ell : ℕ) : (Fin ell → ℝ) →ₗ[ℝ] Polynomial ℝ where
  toFun := polynomialMap N ell
  map_add' v w := by simp [polynomialMap,add_mul,Finset.sum_add_distrib]
  map_smul' a v := by
    simp [polynomialMap,Polynomial.smul_eq_C_mul,Finset.mul_sum,mul_assoc]

theorem polynomialMap_mem_degreeLT (N ell : ℕ) (v : Fin ell → ℝ) :
    polynomialMap N ell v∈Polynomial.degreeLT ℝ ell := by
  unfold polynomialMap
  apply (Polynomial.degreeLT ℝ ell).sum_mem
  intro i hi
  apply Polynomial.mem_degreeLT.mpr
  have hnat : (C (v i)*normalized N i.val).natDegree ≤ i.val :=
    Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C,zero_add] using normalized_natDegree_le N i.val)
  calc
    (C (v i)*normalized N i.val).degree ≤ (C (v i)*normalized N i.val).natDegree := Polynomial.degree_le_natDegree
    _ < ell := WithBot.coe_lt_coe.mpr (hnat.trans_lt i.isLt)

theorem polynomialMap_degree_lt (N ell : ℕ) (v : Fin ell → ℝ) :
    (polynomialMap N ell v).degree < ell :=
  Polynomial.mem_degreeLT.mp (polynomialMap_mem_degreeLT N ell v)

theorem pair_polynomialMap_normalized {N ell : ℕ} (hN : 3 ≤ N) (v : Fin ell → ℝ) (i : Fin ell) :
    pair (N-2) (polynomialMap N ell v) (normalized N i.val)=v i := by
  classical
  rw [←polynomialMap_single N ell i,pair_polynomialMap hN]
  simp [Pi.single_apply]

theorem pair_normalized_polynomialMap {N ell : ℕ} (hN : 3 ≤ N) (v : Fin ell → ℝ) (i : Fin ell) :
    pair (N-2) (normalized N i.val) (polynomialMap N ell v)=v i := by
  rw [pair_comm,pair_polynomialMap_normalized hN]

theorem polynomialMap_injective {N ell : ℕ} (hN : 3 ≤ N) : Function.Injective (polynomialMap N ell) := by
  intro v w hvw
  funext i
  have h := congrArg (fun p => pair (N-2) p (normalized N i.val)) hvw
  simpa only [pair_polynomialMap_normalized hN] using h

def truncatedPolynomialLinear (N ell : ℕ) : (Fin ell → ℝ) →ₗ[ℝ] Polynomial.degreeLT ℝ ell :=
  (polynomialLinear N ell).codRestrict _ (polynomialMap_mem_degreeLT N ell)

def coordinateEnd (N ell : ℕ) : Module.End ℝ (Fin ell → ℝ) :=
  (Polynomial.degreeLTEquiv ℝ ell).toLinearMap.comp (truncatedPolynomialLinear N ell)

theorem truncatedPolynomialLinear_injective {N ell : ℕ} (hN : 3 ≤ N) :
    Function.Injective (truncatedPolynomialLinear N ell) := by
  intro v w hvw
  exact polynomialMap_injective hN (congrArg Subtype.val hvw)

theorem coordinateEnd_injective {N ell : ℕ} (hN : 3 ≤ N) : Function.Injective (coordinateEnd N ell) :=
  (Polynomial.degreeLTEquiv ℝ ell).injective.comp (truncatedPolynomialLinear_injective hN)

/-- Every polynomial below the truncation degree has actual finite
orthonormal Gegenbauer coordinates. No leading-coefficient premise. -/
theorem exists_coordinates {N ell : ℕ} (hN : 3 ≤ N) (p : Polynomial ℝ) (hp : p.degree < ell) :
    ∃ v : Fin ell → ℝ,polynomialMap N ell v=p := by
  have honto : Function.Surjective (coordinateEnd N ell) :=
    LinearMap.surjective_of_injective (coordinateEnd_injective hN)
  let pp : Polynomial.degreeLT ℝ ell := ⟨p,Polynomial.mem_degreeLT.mpr hp⟩
  obtain ⟨v,hv⟩ := honto (Polynomial.degreeLTEquiv ℝ ell pp)
  have heq : truncatedPolynomialLinear N ell v=pp := (Polynomial.degreeLTEquiv ℝ ell).injective hv
  exact ⟨v,congrArg Subtype.val heq⟩

theorem truncatedPolynomialLinear_surjective {N ell : ℕ} (hN : 3 ≤ N) :
    Function.Surjective (truncatedPolynomialLinear N ell) := by
  intro p
  obtain ⟨v,hv⟩ := exists_coordinates hN p.1 (Polynomial.mem_degreeLT.mp p.2)
  exact ⟨v,Subtype.ext hv⟩

def coordinateEquiv {N ell : ℕ} (hN : 3 ≤ N) : (Fin ell → ℝ) ≃ₗ[ℝ] Polynomial.degreeLT ℝ ell :=
  LinearEquiv.ofBijective (truncatedPolynomialLinear N ell)
    ⟨truncatedPolynomialLinear_injective hN,truncatedPolynomialLinear_surjective hN⟩

theorem jacobi_dot_symmetric (N ell : ℕ) (v w : Fin ell → ℝ) :
    dotProduct v (jacobi N ell*ᵥw)=dotProduct w (jacobi N ell*ᵥv) := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hsym := congrFun (congrFun (jacobi_symmetric N ell) i) j
  change jacobi N ell j i=jacobi N ell i j at hsym
  rw [hsym]
  ring

/-- The actual compressed Jacobi action equals multiplication by X as
soon as the multiplied polynomial still lies below the truncation degree. -/
theorem polynomialMap_jacobi {N ell : ℕ} (hN : 3 ≤ N) (v : Fin ell → ℝ)
    (hdegree : (X * polynomialMap N ell v).degree < (ell : WithBot ℕ)) :
    polynomialMap N ell (jacobi N ell*ᵥv)=X*polynomialMap N ell v := by
  classical
  obtain ⟨w,hw⟩ := exists_coordinates hN (X*polynomialMap N ell v) hdegree
  have hdot (z : Fin ell → ℝ) : dotProduct w z=dotProduct z (jacobi N ell*ᵥv) := by
    calc
      dotProduct w z=pair (N-2) (polynomialMap N ell w) (polynomialMap N ell z) :=
        (pair_polynomialMap hN w z).symm
      _=pair (N-2) (X*polynomialMap N ell v) (polynomialMap N ell z) := by rw [hw]
      _=dotProduct v (jacobi N ell*ᵥz) := multiplication_gram hN v z
      _=dotProduct z (jacobi N ell*ᵥv) := jacobi_dot_symmetric N ell v z
  have hwj : w=jacobi N ell*ᵥv := by
    funext i
    simpa [dotProduct,Pi.single_apply] using hdot (Pi.single i 1)
  rw [←hwj]
  exact hw

end OptimalConvergenceRates.SphereDimensionBounds.GegenbauerCoordinates
