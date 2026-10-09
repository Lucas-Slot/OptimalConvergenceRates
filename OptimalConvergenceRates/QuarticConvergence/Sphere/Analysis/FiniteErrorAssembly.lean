/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/FiniteErrorAssembly.lean

  Algebraic and pointwise assembly of finitely many filtered square roots.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Assembly

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- A finite family of polynomials with uniformly bounded degree gives an
ordinary degree-bounded SOS. -/
def DegreeBoundedSOS.ofFinSquares {n N r : ℕ}
    (P : Fin N → MvPolynomial (Fin n) ℝ)
    (hdegree : ∀ i, (P i).totalDegree ≤ r) :
    DegreeBoundedSOS (∑ i, (P i) ^ 2) r where
  N := N
  P := P
  decomp := rfl
  degree := hdegree

/-- The exact error identity used after applying the Boolean filter to each
retained smooth square root. -/
theorem finite_square_error_identity {n N : ℕ}
    (F : MvPolynomial (Fin n) ℝ)
    (a e : Fin N → MvPolynomial (Fin n) ℝ) :
    (∑ i, (a i + e i) ^ 2) - F =
      2 * (∑ i, a i * e i) + (∑ i, (e i) ^ 2) -
        (F - ∑ i, (a i) ^ 2) := by
  simp_rw [add_sq, Finset.sum_add_distrib, mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- Real-valued form of the finite-square error identity, used pointwise for
smooth retained roots. -/
theorem real_finite_square_error_identity {N : ℕ}
    (F : ℝ) (a e : Fin N → ℝ) :
    (∑ i, (a i + e i) ^ 2) - F =
      2 * (∑ i, a i * e i) + (∑ i, (e i) ^ 2) -
        (F - ∑ i, (a i) ^ 2) := by
  simp_rw [add_sq, Finset.sum_add_distrib, mul_assoc]
  rw [← Finset.mul_sum]
  ring


/-- If the discarded remainder, the root-error cross term, and the squared
root errors are bounded pointwise, their finite sum has the corresponding
sphere sup-norm bound. This is the polynomial-independent summation step in
the finite-resolution approximation argument. -/
theorem finite_square_approximation_bound {n N : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ)
    (a e : Fin N → MvPolynomial (Fin n) ℝ)
    (crossErr squareErr remainderErr : ℝ)
    (hcross : ∀ x ∈ sphereSet n,
      ∑ i, |MvPolynomial.eval x (a i) * MvPolynomial.eval x (e i)| ≤ crossErr)
    (hsquare : ∀ x ∈ sphereSet n,
      ∑ i, (MvPolynomial.eval x (e i)) ^ 2 ≤ squareErr)
    (hremainder : ∀ x ∈ sphereSet n,
      |MvPolynomial.eval x (F - ∑ i, (a i) ^ 2)| ≤ remainderErr) :
    sphereSupNorm (F - ∑ i, (a i + e i) ^ 2) ≤
      2 * crossErr + squareErr + remainderErr := by
  apply sphereSupNorm_le_of_bound hn
  intro x hx
  have hcrossAbs :
      |∑ i, MvPolynomial.eval x (a i) * MvPolynomial.eval x (e i)| ≤
        crossErr :=
    (abs_sum_le_sum_abs _ _).trans (hcross x hx)
  have hsquareNonneg :
      0 ≤ ∑ i, (MvPolynomial.eval x (e i)) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  calc
    |MvPolynomial.eval x (F - ∑ i, (a i + e i) ^ 2)| =
        |MvPolynomial.eval x ((∑ i, (a i + e i) ^ 2) - F)| := by
          rw [map_sub, map_sub, abs_sub_comm]
    _ = |MvPolynomial.eval x
          (2 * (∑ i, a i * e i) + (∑ i, (e i) ^ 2) -
            (F - ∑ i, (a i) ^ 2))| := by
          rw [finite_square_error_identity]
    _ = |2 * (∑ i, MvPolynomial.eval x (a i) * MvPolynomial.eval x (e i)) +
          (∑ i, (MvPolynomial.eval x (e i)) ^ 2) -
          MvPolynomial.eval x (F - ∑ i, (a i) ^ 2)| := by
          simp only [map_sub, map_sum, map_pow, map_add, map_mul]
          norm_num
    _ ≤ |2 * (∑ i, MvPolynomial.eval x (a i) * MvPolynomial.eval x (e i))| +
          |∑ i, (MvPolynomial.eval x (e i)) ^ 2| +
          |MvPolynomial.eval x (F - ∑ i, (a i) ^ 2)| := by
          apply (abs_sub _ _).trans
          exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 2 * crossErr + squareErr + remainderErr := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_nonneg hsquareNonneg]
          exact add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hcrossAbs (by norm_num))
              (hsquare x hx))
            (hremainder x hx)

/-- The preceding pointwise estimate, packaged with its explicit finite SOS
witness and root-degree bound. -/
theorem finite_square_approximation {n N r : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ)
    (a e : Fin N → MvPolynomial (Fin n) ℝ)
    (crossErr squareErr remainderErr : ℝ)
    (hdegree : ∀ i, (a i + e i).totalDegree ≤ r)
    (hcross : ∀ x ∈ sphereSet n,
      ∑ i, |MvPolynomial.eval x (a i) * MvPolynomial.eval x (e i)| ≤ crossErr)
    (hsquare : ∀ x ∈ sphereSet n,
      ∑ i, (MvPolynomial.eval x (e i)) ^ 2 ≤ squareErr)
    (hremainder : ∀ x ∈ sphereSet n,
      |MvPolynomial.eval x (F - ∑ i, (a i) ^ 2)| ≤ remainderErr) :
    ∃ Q : MvPolynomial (Fin n) ℝ,
      Nonempty (DegreeBoundedSOS Q r) ∧
        sphereSupNorm (F - Q) ≤
          2 * crossErr + squareErr + remainderErr := by
  refine ⟨∑ i, (a i + e i) ^ 2,
    ⟨DegreeBoundedSOS.ofFinSquares (fun i ↦ a i + e i) hdegree⟩, ?_⟩
  exact finite_square_approximation_bound hn F a e
    crossErr squareErr remainderErr hcross hsquare hremainder

/-- Finite error assembly for retained-root estimates: the retained roots
are arbitrary real-valued functions, while only their filtered approximants are
polynomials. -/
theorem finite_filtered_square_approximation_bound {n N : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ)
    (a : Fin N → ((Fin n → ℝ) → ℝ))
    (p : Fin N → MvPolynomial (Fin n) ℝ)
    (crossErr squareErr remainderErr : ℝ)
    (hcross : ∀ x ∈ sphereSet n,
      ∑ i, |a i x * (MvPolynomial.eval x (p i) - a i x)| ≤ crossErr)
    (hsquare : ∀ x ∈ sphereSet n,
      ∑ i, (MvPolynomial.eval x (p i) - a i x) ^ 2 ≤ squareErr)
    (hremainder : ∀ x ∈ sphereSet n,
      |MvPolynomial.eval x F - ∑ i, (a i x) ^ 2| ≤ remainderErr) :
    sphereSupNorm (F - ∑ i, (p i) ^ 2) ≤
      2 * crossErr + squareErr + remainderErr := by
  apply sphereSupNorm_le_of_bound hn
  intro x hx
  let e : Fin N → ℝ := fun i ↦ MvPolynomial.eval x (p i) - a i x
  have hcrossAbs : |∑ i, a i x * e i| ≤ crossErr :=
    (abs_sum_le_sum_abs _ _).trans (hcross x hx)
  have hsquareNonneg : 0 ≤ ∑ i, (e i) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hscalar :=
    real_finite_square_error_identity
      (MvPolynomial.eval x F) (fun i ↦ a i x) e
  have hp (i : Fin N) : MvPolynomial.eval x (p i) = a i x + e i := by
    dsimp [e]
    ring
  calc
    |MvPolynomial.eval x (F - ∑ i, (p i) ^ 2)| =
        |MvPolynomial.eval x F - ∑ i, (MvPolynomial.eval x (p i)) ^ 2| := by
          simp only [map_sub, map_sum, map_pow]
    _ = |(∑ i, (a i x + e i) ^ 2) - MvPolynomial.eval x F| := by
          rw [abs_sub_comm]
          apply congrArg abs
          apply congrArg (fun z : ℝ ↦ z - MvPolynomial.eval x F)
          apply Finset.sum_congr rfl
          intro i _
          rw [hp]
    _ = |2 * (∑ i, a i x * e i) + (∑ i, (e i) ^ 2) -
          (MvPolynomial.eval x F - ∑ i, (a i x) ^ 2)| := by rw [hscalar]
    _ ≤ |2 * (∑ i, a i x * e i)| + |∑ i, (e i) ^ 2| +
          |MvPolynomial.eval x F - ∑ i, (a i x) ^ 2| := by
          apply (abs_sub _ _).trans
          exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 2 * crossErr + squareErr + remainderErr := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_nonneg hsquareNonneg]
          exact add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hcrossAbs (by norm_num))
              (hsquare x hx))
            (hremainder x hx)

/-- Smooth retained roots and polynomial filtered roots satisfying the three
finite-error estimates produce an ordinary degree-bounded SOS approximation. -/
theorem finite_filtered_square_approximation {n N r : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ)
    (a : Fin N → ((Fin n → ℝ) → ℝ))
    (p : Fin N → MvPolynomial (Fin n) ℝ)
    (crossErr squareErr remainderErr : ℝ)
    (hdegree : ∀ i, (p i).totalDegree ≤ r)
    (hcross : ∀ x ∈ sphereSet n,
      ∑ i, |a i x * (MvPolynomial.eval x (p i) - a i x)| ≤ crossErr)
    (hsquare : ∀ x ∈ sphereSet n,
      ∑ i, (MvPolynomial.eval x (p i) - a i x) ^ 2 ≤ squareErr)
    (hremainder : ∀ x ∈ sphereSet n,
      |MvPolynomial.eval x F - ∑ i, (a i x) ^ 2| ≤ remainderErr) :
    ∃ Q : MvPolynomial (Fin n) ℝ,
      Nonempty (DegreeBoundedSOS Q r) ∧
        sphereSupNorm (F - Q) ≤
          2 * crossErr + squareErr + remainderErr := by
  refine ⟨∑ i, (p i) ^ 2,
    ⟨DegreeBoundedSOS.ofFinSquares p hdegree⟩, ?_⟩
  exact finite_filtered_square_approximation_bound hn F a p
    crossErr squareErr remainderErr hcross hsquare hremainder

end QuarticConvergence
end OptimalConvergenceRates

end
