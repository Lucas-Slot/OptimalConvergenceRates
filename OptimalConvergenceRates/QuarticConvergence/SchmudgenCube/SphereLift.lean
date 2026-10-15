/-
  Polynomial lift from the hypercube to a sphere with `2*n+1` coordinates.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.QuarticRate
import Mathlib.Analysis.MeanInequalities

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Named coordinates: one spare coordinate and two coordinates for each
cube variable. -/
abbrev CubeSphereVar (n : ℕ) := Option (Fin n × Bool)

/-- The named sphere coordinates identified with the `Fin` coordinates used
by the existing sphere development. -/
noncomputable def cubeSphereEquiv (n : ℕ) : CubeSphereVar n ≃ Fin (2 * n + 1) :=
  (Fintype.equivFin (CubeSphereVar n)).trans
    (Equiv.cast (by
      congr 1
      simp [CubeSphereVar]
      omega))

/-- The first coordinate in the block belonging to `i`. -/
def cubeSphereFirst (n : ℕ) (i : Fin n) : Fin (2 * n + 1) :=
  cubeSphereEquiv n (some (i, false))

/-- The second coordinate in the block belonging to `i`. -/
def cubeSphereSecond (n : ℕ) (i : Fin n) : Fin (2 * n + 1) :=
  cubeSphereEquiv n (some (i, true))

/-- The squared mass of the `i`-th coordinate block, scaled by `n`. -/
def cubeSphereBlockMass (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin (2 * n + 1)) ℝ :=
  MvPolynomial.C (n : ℝ) *
    (X (cubeSphereFirst n i) ^ 2 + X (cubeSphereSecond n i) ^ 2)

/-- The `i`-th coordinate of the polynomial map from the sphere to the cube. -/
def cubeSphereCoordinate (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin (2 * n + 1)) ℝ :=
  MvPolynomial.C (Real.sqrt n) * X (cubeSphereFirst n i) *
    ((MvPolynomial.C (2 * n + 1 : ℝ) - cubeSphereBlockMass n i) *
      MvPolynomial.C ((2 * n : ℝ)⁻¹)) ^ n

/-- Pull a cube polynomial back along the polynomial sphere-to-cube map. -/
def cubeSphereLift (n : ℕ) :
    MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin (2 * n + 1)) ℝ :=
  MvPolynomial.aeval (cubeSphereCoordinate n)

@[simp] theorem cubeSphereLift_X (n : ℕ) (i : Fin n) :
    cubeSphereLift n (X i) = cubeSphereCoordinate n i := by
  simp [cubeSphereLift]

@[simp] theorem cubeSphereLift_C (n : ℕ) (c : ℝ) :
    cubeSphereLift n (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [cubeSphereLift]

theorem cubeSphereBlockMass_totalDegree_le_two (n : ℕ) (i : Fin n) :
    (cubeSphereBlockMass n i).totalDegree ≤ 2 := by
  let x₀ : MvPolynomial (Fin (2 * n + 1)) ℝ := X (cubeSphereFirst n i)
  let x₁ : MvPolynomial (Fin (2 * n + 1)) ℝ := X (cubeSphereSecond n i)
  have hx₀ : (x₀ ^ 2).totalDegree ≤ 2 := by
    simp [x₀, MvPolynomial.totalDegree_X_pow]
  have hx₁ : (x₁ ^ 2).totalDegree ≤ 2 := by
    simp [x₁, MvPolynomial.totalDegree_X_pow]
  have hsum : (x₀ ^ 2 + x₁ ^ 2).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le hx₀ hx₁)
  have hconstant :
      (MvPolynomial.C (n : ℝ) :
        MvPolynomial (Fin (2 * n + 1)) ℝ).totalDegree ≤ 0 := by
    exact le_of_eq (MvPolynomial.totalDegree_C (n : ℝ))
  unfold cubeSphereBlockMass
  change ((MvPolynomial.C (n : ℝ) : MvPolynomial (Fin (2 * n + 1)) ℝ) *
    (x₀ ^ 2 + x₁ ^ 2)).totalDegree ≤ 2
  calc
    ((MvPolynomial.C (n : ℝ) : MvPolynomial (Fin (2 * n + 1)) ℝ) *
        (x₀ ^ 2 + x₁ ^ 2)).totalDegree
        ≤ (MvPolynomial.C (n : ℝ) : MvPolynomial (Fin (2 * n + 1)) ℝ).totalDegree +
          (x₀ ^ 2 + x₁ ^ 2).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + 2 := Nat.add_le_add hconstant hsum
    _ = 2 := by omega

theorem cubeSphereCoordinate_totalDegree_le (n : ℕ) (i : Fin n) :
    (cubeSphereCoordinate n i).totalDegree ≤ 2 * n + 1 := by
  let base : MvPolynomial (Fin (2 * n + 1)) ℝ :=
    (MvPolynomial.C (2 * n + 1 : ℝ) - cubeSphereBlockMass n i) *
      MvPolynomial.C ((2 * n : ℝ)⁻¹)
  have hlargeConstant :
      (MvPolynomial.C (2 * n + 1 : ℝ) :
        MvPolynomial (Fin (2 * n + 1)) ℝ).totalDegree ≤ 2 := by
    exact (le_of_eq (MvPolynomial.totalDegree_C (2 * n + 1 : ℝ))).trans (by omega)
  have hsub :
      (MvPolynomial.C (2 * n + 1 : ℝ) - cubeSphereBlockMass n i).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub _ _).trans
      (max_le hlargeConstant (cubeSphereBlockMass_totalDegree_le_two n i))
  have hconstant :
      (MvPolynomial.C ((2 * n : ℝ)⁻¹) :
        MvPolynomial (Fin (2 * n + 1)) ℝ).totalDegree ≤ 0 := by
    exact le_of_eq (MvPolynomial.totalDegree_C ((2 * n : ℝ)⁻¹))
  have hbase : base.totalDegree ≤ 2 := by
    dsimp [base]
    calc
      ((MvPolynomial.C (2 * n + 1 : ℝ) - cubeSphereBlockMass n i) *
          MvPolynomial.C ((2 * n : ℝ)⁻¹)).totalDegree ≤
          (MvPolynomial.C (2 * n + 1 : ℝ) - cubeSphereBlockMass n i).totalDegree +
            (MvPolynomial.C ((2 * n : ℝ)⁻¹) :
              MvPolynomial (Fin (2 * n + 1)) ℝ).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 + 0 := Nat.add_le_add hsub hconstant
      _ = 2 := by omega
  let prefactor : MvPolynomial (Fin (2 * n + 1)) ℝ :=
    MvPolynomial.C (Real.sqrt n) * X (cubeSphereFirst n i)
  have hprefactor : prefactor.totalDegree ≤ 1 := by
    dsimp [prefactor]
    have hc :
        (MvPolynomial.C (Real.sqrt n) :
          MvPolynomial (Fin (2 * n + 1)) ℝ).totalDegree ≤ 0 := by
      exact le_of_eq (MvPolynomial.totalDegree_C (Real.sqrt n))
    calc
      (MvPolynomial.C (Real.sqrt n) * X (cubeSphereFirst n i)).totalDegree ≤
          (MvPolynomial.C (Real.sqrt n) :
            MvPolynomial (Fin (2 * n + 1)) ℝ).totalDegree +
            (X (cubeSphereFirst n i) :
              MvPolynomial (Fin (2 * n + 1)) ℝ).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 1 := Nat.add_le_add hc (by simp)
      _ = 1 := by omega
  unfold cubeSphereCoordinate
  change (prefactor * base ^ n).totalDegree ≤ _
  calc
    (prefactor * base ^ n).totalDegree ≤ prefactor.totalDegree +
        (base ^ n).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + n * 2 := Nat.add_le_add hprefactor
      ((MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left n hbase))
    _ = 2 * n + 1 := by omega

/-- General degree bound for substitution by polynomials of uniformly bounded
degree. -/
theorem totalDegree_aeval_le_mul {m n d : ℕ}
    (f : Fin n → MvPolynomial (Fin m) ℝ) (hf : ∀ i, (f i).totalDegree ≤ d)
    (p : MvPolynomial (Fin n) ℝ) :
    (MvPolynomial.aeval f p).totalDegree ≤ d * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro exponent hexponent
  rw [MvPolynomial.aeval_monomial]
  calc
    (algebraMap ℝ (MvPolynomial (Fin m) ℝ) (legacyMvCoeff exponent p) *
        exponent.prod fun i k ↦ f i ^ k).totalDegree ≤
        (algebraMap ℝ (MvPolynomial (Fin m) ℝ)
          (legacyMvCoeff exponent p)).totalDegree +
          (exponent.prod fun i k ↦ f i ^ k).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (exponent.prod fun i k ↦ f i ^ k).totalDegree := by
      rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C]
      simp
    _ ≤ ∑ i ∈ exponent.support, (f i ^ exponent i).totalDegree := by
      simp only [Finsupp.prod]
      exact MvPolynomial.totalDegree_finsetProd exponent.support _
    _ ≤ ∑ i ∈ exponent.support, d * exponent i := by
      apply Finset.sum_le_sum
      intro i _
      calc
        (f i ^ exponent i).totalDegree ≤ exponent i * (f i).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ ≤ exponent i * d := Nat.mul_le_mul_left _ (hf i)
        _ = d * exponent i := Nat.mul_comm _ _
    _ = d * exponent.sum (fun _ e ↦ e) := by
      simp only [Finsupp.sum, Finset.mul_sum]
    _ ≤ d * p.totalDegree := Nat.mul_le_mul_left d
      (Finset.le_sup (f := fun s ↦ s.sum fun _ e ↦ e) hexponent)

theorem cubeSphereLift_totalDegree_le (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (cubeSphereLift n p).totalDegree ≤ (2 * n + 1) * p.totalDegree := by
  exact totalDegree_aeval_le_mul (cubeSphereCoordinate n)
    (cubeSphereCoordinate_totalDegree_le n) p

/-- Evaluation of the lift is evaluation of the original polynomial at the
polynomial sphere-to-cube map. -/
theorem eval_cubeSphereLift (n : ℕ) (z : Fin (2 * n + 1) → ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval z (cubeSphereLift n p) =
      MvPolynomial.eval (fun i ↦ MvPolynomial.eval z (cubeSphereCoordinate n i)) p := by
  change MvPolynomial.eval z
      (MvPolynomial.eval₂
        (algebraMap ℝ (MvPolynomial (Fin (2 * n + 1)) ℝ)) (cubeSphereCoordinate n) p) = _
  rw [MvPolynomial.eval_eval₂]
  have hcoeff :
      (MvPolynomial.eval z).comp
          (algebraMap ℝ (MvPolynomial (Fin (2 * n + 1)) ℝ)) = RingHom.id ℝ := by
    ext c
    simp [MvPolynomial.algebraMap_eq]
  rw [hcoeff, MvPolynomial.eval₂_id]

end QuarticConvergence
end OptimalConvergenceRates

end
