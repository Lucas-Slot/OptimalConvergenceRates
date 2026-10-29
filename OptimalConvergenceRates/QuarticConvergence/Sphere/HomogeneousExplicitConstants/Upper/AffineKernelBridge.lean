import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.KernelAbsorption

/-! Actual affine translation of bounded SOS roots, followed by kernel
absorption at the same original sphere level. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace AffineKernelBridge

open scoped BigOperators
open MvPolynomial Foundation ChebyshevSOSKernel KernelAbsorption

theorem affine_substitution_degree {n m : ℕ} (f : Fin n → Foundation.Polynomial m)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : Foundation.Polynomial n) :
    ((eval₂Hom C f) p).totalDegree ≤ p.totalDegree := by
  classical
  have heq := congrArg (eval₂Hom C f) p.as_sum
  rw [map_sum] at heq
  rw [heq]
  apply totalDegree_finsetSum_le
  intro a ha
  rw [eval₂Hom_monomial]
  change (C (p.coeff a)*a.prod (fun i e ↦ f i^e)).totalDegree ≤ p.totalDegree
  have hp : (a.prod (fun i e ↦ f i^e)).totalDegree ≤ a.sum (fun _ e ↦ e) := by
    change (∏ i ∈ a.support, f i^(a i)).totalDegree ≤ ∑ i ∈ a.support, a i
    apply (totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (a i) (hf i))
  exact (totalDegree_mul _ _).trans (by simpa using hp.trans (le_totalDegree ha))

theorem boundedSOS_affine_substitution {n m d : ℕ}
    (f : Fin n → Foundation.Polynomial m) (hf : ∀ i, (f i).totalDegree ≤ 1)
    {p : Foundation.Polynomial n} (hp : BoundedSOS d p) :
    BoundedSOS d ((eval₂Hom C f) p) := by
  rcases hp.exists_squares with ⟨k,h,hh,hid⟩
  apply BoundedSOS.of_squares (fun i ↦ (eval₂Hom C f) (h i))
    (fun i ↦ (affine_substitution_degree f hf (h i)).trans (hh i))
  rw [hid,map_sum]
  simp only [map_pow]

def translation (n : ℕ) (y : Fin n → ℝ) :
    Foundation.Polynomial n →+* Foundation.Polynomial n :=
  eval₂Hom C (fun i ↦ X i-C (y i))

@[simp] theorem translation_C {n : ℕ} (y : Fin n → ℝ) (c : ℝ) :
    translation n y (C c)=C c := by simp [translation]

theorem translation_degree {n : ℕ} (y : Fin n → ℝ) (p : Foundation.Polynomial n) :
    (translation n y p).totalDegree ≤ p.totalDegree := by
  apply affine_substitution_degree
  intro i
  exact (totalDegree_sub _ _).trans (by simp)

theorem boundedSOS_translation {n d : ℕ} (y : Fin n → ℝ)
    {p : Foundation.Polynomial n} (hp : BoundedSOS d p) :
    BoundedSOS d (translation n y p) := by
  apply boundedSOS_affine_substitution _ _ hp
  intro i
  exact (totalDegree_sub _ _).trans (by simp)

theorem translation_radius {n : ℕ} (y : Fin n → ℝ) :
    translation n y (radiusPolynomial n)=chordPole y := by
  simp [translation, radiusPolynomial, SphereBallTransfers.sphereQuadratic, chordPole]

def translatedLocal {n : ℕ} (y : Fin n → ℝ) (v : Foundation.Polynomial n)
    (c : ℝ) : Foundation.Polynomial n :=
  translation n y v+C c*(chordPole y)^2

theorem translatedLocal_degree {n : ℕ} (y : Fin n → ℝ) (v : Foundation.Polynomial n)
    (hv : v.totalDegree ≤ 3) (c : ℝ) : (translatedLocal y v c).totalDegree ≤ 4 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (translation_degree y v).trans (by omega)
  · apply (totalDegree_mul _ _).trans
    have hc := (totalDegree_pow (chordPole y) 2).trans
      (Nat.mul_le_mul_left 2 (chordPole_degree y))
    simpa using hc

theorem translated_kernel_feasible {n ell : ℕ} (y : Fin n → ℝ)
    (hy : ∑ i, y i ^ 2 = 1) (v chi : Foundation.Polynomial n)
    (hv : v.totalDegree ≤ 3) (hchi : chi.totalDegree ≤ ell - 2)
    (hell : 2 ≤ ell) (m : ℕ) (c : ℝ)
    (hlocal : BoundedSOS (2 * m + 2)
      ((radiusPolynomial n) ^ (2 * m) * (v + C c * (radiusPolynomial n) ^ 2))) :
    Feasible (3*m+ell)
      (kernelNumerator (dotPole y) chi m^2*translatedLocal y v c) 0 := by
  have htranslated := boundedSOS_translation y hlocal
  have hlocal' : BoundedSOS (2*m+2) ((chordPole y)^(2*m)*translatedLocal y v c) := by
    simpa only [map_mul,map_add,map_pow,translation_radius,translation_C,
      translatedLocal] using htranslated
  exact kernel_absorption_feasible y hy chi (translatedLocal y v c) hchi
    (translatedLocal_degree y v hv c) hell m hlocal'

end AffineKernelBridge
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
