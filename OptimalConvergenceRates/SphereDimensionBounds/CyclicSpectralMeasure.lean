import OptimalConvergenceRates.SphereDimensionBounds.FiniteSpectralMeasure

/-! A cyclic real symmetric matrix has positive spectral weights and
pairwise distinct eigenvalues. These are consequences of cyclicity,
rather than assumptions on the finite spectral measure. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.CyclicSpectralMeasure

open scoped BigOperators InnerProductSpace
open Matrix FiniteSpectralMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsCyclic (M : Mat (ι := ι)) (v : Point (ι := ι)) : Prop :=
  ∀ w : Point (ι:=ι),
    (∀ k : ℕ, ⟪w,iterateVector M k v⟫_ℝ=0) → w=0

theorem weight_pos {M : Mat (ι := ι)} (hM : M.IsHermitian)
    (v : Point (ι := ι)) (hcyc : IsCyclic M v) (i : ι) :
    0 < weight hM v i := by
  apply sq_pos_of_ne_zero
  intro hzero
  have hbzero := hcyc (hM.eigenvectorBasis i) (by
    intro k
    rw [eigenmode_iterate hM,hzero,mul_zero])
  have hnorm := hM.eigenvectorBasis.orthonormal.norm_eq_one i
  rw [hbzero,norm_zero] at hnorm
  norm_num at hnorm

theorem eigenvalues_injective {M : Mat (ι := ι)} (hM : M.IsHermitian)
    (v : Point (ι := ι)) (hcyc : IsCyclic M v) :
    Function.Injective hM.eigenvalues := by
  intro i j hij
  by_contra hne
  let b := hM.eigenvectorBasis
  let ai : ℝ := ⟪b i,v⟫_ℝ
  let aj : ℝ := ⟪b j,v⟫_ℝ
  have haj : aj ≠ 0 := by
    have hp := weight_pos hM v hcyc j
    change 0 < aj^2 at hp
    exact (sq_pos_iff).mp hp
  have hz : aj • b i-ai • b j=0 := hcyc _ (by
    intro k
    rw [inner_sub_left,real_inner_smul_left,real_inner_smul_left]
    change aj*⟪hM.eigenvectorBasis i,iterateVector M k v⟫_ℝ-
      ai*⟪hM.eigenvectorBasis j,iterateVector M k v⟫_ℝ=0
    rw [eigenmode_iterate hM,eigenmode_iterate hM,hij]
    change aj*((hM.eigenvalues j)^k*ai)-ai*((hM.eigenvalues j)^k*aj)=0
    ring)
  have hi := congrArg (fun w : Point (ι:=ι) => ⟪b i,w⟫_ℝ) hz
  rw [inner_sub_right,real_inner_smul_right,real_inner_smul_right,
    b.inner_eq_zero hne,inner_zero_right] at hi
  have hself : ⟪b i,b i⟫_ℝ=1 := by
    rw [real_inner_self_eq_norm_sq,b.norm_eq_one,one_pow]
  exact haj (by simpa [hself] using hi)

end OptimalConvergenceRates.SphereDimensionBounds.CyclicSpectralMeasure
