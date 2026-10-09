/-
  Polynomial substitution from the lifted sphere coordinates to a product of circles.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SphereLiftSection

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers


/-- The paired variables `(x_i, y_i)` used on the product of unit circles. -/
abbrev CubeCircleVar (n : ℕ) := Fin n × Bool

/-- The product of unit circles in paired coordinates. -/
def ProductCircle (n : ℕ) : Set (CubeCircleVar n → ℝ) :=
  {z | ∀ i, z (i, false) ^ 2 + z (i, true) ^ 2 = 1}

/-- The scaled inclusion of paired circle coordinates into the named sphere coordinates. -/
def productCircleSpherePointNamed (n : ℕ) (z : CubeCircleVar n → ℝ) :
    CubeSphereVar n → ℝ
  | none => 0
  | some ib => z ib / Real.sqrt n

/-- The scaled inclusion expressed in the `Fin` coordinates of the sphere development. -/
def productCircleSpherePoint (n : ℕ) (z : CubeCircleVar n → ℝ) :
    Fin (2 * n + 1) → ℝ :=
  fun j ↦ productCircleSpherePointNamed n z ((cubeSphereEquiv n).symm j)

@[simp] theorem productCircleSpherePoint_first (n : ℕ) (z : CubeCircleVar n → ℝ)
    (i : Fin n) :
    productCircleSpherePoint n z (cubeSphereFirst n i) = z (i, false) / Real.sqrt n := by
  simp [productCircleSpherePoint, productCircleSpherePointNamed, cubeSphereFirst]

@[simp] theorem productCircleSpherePoint_second (n : ℕ) (z : CubeCircleVar n → ℝ)
    (i : Fin n) :
    productCircleSpherePoint n z (cubeSphereSecond n i) = z (i, true) / Real.sqrt n := by
  simp [productCircleSpherePoint, productCircleSpherePointNamed, cubeSphereSecond]

/-- The scaled inclusion sends the product of circles to the unit sphere. -/
theorem productCircleSpherePoint_mem_sphere {n : ℕ} (hn : 0 < n)
    {z : CubeCircleVar n → ℝ} (hz : z ∈ ProductCircle n) :
    productCircleSpherePoint n z ∈ sphereSet (2 * n + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpair (i : Fin n) :
      (z (i, false) / Real.sqrt n) ^ 2 +
          (z (i, true) / Real.sqrt n) ^ 2 = 1 / (n : ℝ) := by
    rw [div_pow, div_pow, Real.sq_sqrt hnR.le]
    rw [← add_div, show z (i, false) ^ 2 + z (i, true) ^ 2 = 1 from hz i]
  change MvPolynomial.eval (productCircleSpherePoint n z)
      (sphereQuadratic (2 * n + 1)) = 1
  simp only [sphereQuadratic, map_sum, map_pow, eval_X]
  rw [← (cubeSphereEquiv n).sum_comp (fun j ↦ productCircleSpherePoint n z j ^ 2)]
  simp only [productCircleSpherePoint, Equiv.symm_apply_apply]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [productCircleSpherePointNamed, OfNat.ofNat, Fintype.sum_bool]
  calc
    (0 : ℝ) ^ 2 +
        ∑ i : Fin n,
          ((z (i, true) / Real.sqrt n) ^ 2 + (z (i, false) / Real.sqrt n) ^ 2) =
        ∑ i : Fin n,
          ((z (i, true) / Real.sqrt n) ^ 2 + (z (i, false) / Real.sqrt n) ^ 2) := by
      norm_num
    _ = ∑ _i : Fin n, (1 / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [add_comm, hpair i]
    _ = 1 := by simp [hn.ne']

/-- The linear polynomial substitution associated with the scaled inclusion. -/
def productCircleSubstitution (n : ℕ) :
    MvPolynomial (Fin (2 * n + 1)) ℝ →ₐ[ℝ] MvPolynomial (CubeCircleVar n) ℝ :=
  MvPolynomial.aeval fun j ↦
    match (cubeSphereEquiv n).symm j with
    | none => 0
    | some ib => MvPolynomial.C ((Real.sqrt n)⁻¹) * X ib

/-- Evaluating after the polynomial substitution is evaluation at the scaled inclusion. -/
theorem eval_productCircleSubstitution (n : ℕ) (z : CubeCircleVar n → ℝ)
    (p : MvPolynomial (Fin (2 * n + 1)) ℝ) :
    MvPolynomial.eval z (productCircleSubstitution n p) =
      MvPolynomial.eval (productCircleSpherePoint n z) p := by
  change MvPolynomial.eval z
      (MvPolynomial.eval₂
        (algebraMap ℝ (MvPolynomial (CubeCircleVar n) ℝ))
        (fun j ↦
          match (cubeSphereEquiv n).symm j with
          | none => 0
          | some ib => MvPolynomial.C ((Real.sqrt n)⁻¹) * X ib)
        p) = _
  rw [MvPolynomial.eval_eval₂]
  have hcoeff :
      (MvPolynomial.eval z).comp
          (algebraMap ℝ (MvPolynomial (CubeCircleVar n) ℝ)) = RingHom.id ℝ := by
    ext c
    simp [MvPolynomial.algebraMap_eq]
  rw [hcoeff, MvPolynomial.eval₂_id]
  have hpoint :
      (fun j ↦ MvPolynomial.eval z
        (match (cubeSphereEquiv n).symm j with
        | none => (0 : MvPolynomial (CubeCircleVar n) ℝ)
        | some ib => MvPolynomial.C ((Real.sqrt n)⁻¹) * X ib)) =
        productCircleSpherePoint n z := by
    funext j
    rcases h : (cubeSphereEquiv n).symm j with _ | ib
    · simp [productCircleSpherePoint, productCircleSpherePointNamed, h]
    · simp [productCircleSpherePoint, productCircleSpherePointNamed, h, div_eq_mul_inv,
        mul_comm]
  rw [hpoint]

/-- General total-degree bound for substitution by polynomials of uniformly bounded degree. -/
theorem totalDegree_aeval_le_mul_general {σ τ : Type*} {d : ℕ}
    (f : σ → MvPolynomial τ ℝ) (hf : ∀ i, (f i).totalDegree ≤ d)
    (p : MvPolynomial σ ℝ) :
    (MvPolynomial.aeval f p).totalDegree ≤ d * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro exponent hexponent
  rw [MvPolynomial.aeval_monomial]
  calc
    (algebraMap ℝ (MvPolynomial τ ℝ) (MvPolynomial.coeff exponent p) *
        exponent.prod fun i k ↦ f i ^ k).totalDegree ≤
        (algebraMap ℝ (MvPolynomial τ ℝ)
          (MvPolynomial.coeff exponent p)).totalDegree +
          (exponent.prod fun i k ↦ f i ^ k).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (exponent.prod fun i k ↦ f i ^ k).totalDegree := by
      rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C]
      simp
    _ ≤ ∑ i ∈ exponent.support, (f i ^ exponent i).totalDegree := by
      simp only [Finsupp.prod]
      exact MvPolynomial.totalDegree_finset_prod exponent.support _
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
      (Finset.le_sup (f := fun e ↦ e.sum fun _ k ↦ k) hexponent)

/-- The product-circle substitution does not increase total degree. -/
theorem productCircleSubstitution_totalDegree_le (n : ℕ)
    (p : MvPolynomial (Fin (2 * n + 1)) ℝ) :
    (productCircleSubstitution n p).totalDegree ≤ p.totalDegree := by
  have hvar : ∀ j,
      (match (cubeSphereEquiv n).symm j with
        | none => (0 : MvPolynomial (CubeCircleVar n) ℝ)
        | some ib => MvPolynomial.C ((Real.sqrt n)⁻¹) * X ib).totalDegree ≤ 1 := by
    intro j
    rcases (cubeSphereEquiv n).symm j with _ | ib
    · simp
    · calc
        (MvPolynomial.C ((Real.sqrt n)⁻¹) *
            (X ib : MvPolynomial (CubeCircleVar n) ℝ)).totalDegree ≤
            (MvPolynomial.C ((Real.sqrt n)⁻¹) :
              MvPolynomial (CubeCircleVar n) ℝ).totalDegree +
              (X ib : MvPolynomial (CubeCircleVar n) ℝ).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ 1 := by simp
  unfold productCircleSubstitution
  have hdegree := totalDegree_aeval_le_mul_general _ hvar p
  rw [one_mul] at hdegree
  exact hdegree

/-- The substituted sphere relation vanishes at every product-circle point. -/
theorem eval_productCircleSubstitution_sphereRelation {n : ℕ} (hn : 0 < n)
    {z : CubeCircleVar n → ℝ} (hz : z ∈ ProductCircle n) :
    MvPolynomial.eval z
      (productCircleSubstitution n (sphereRelation (2 * n + 1))) = 0 := by
  rw [eval_productCircleSubstitution]
  exact eval_sphereRelation_of_mem (productCircleSpherePoint_mem_sphere hn hz)

/-- On the product of circles, the polynomial sphere map retracts to the first coordinates. -/
theorem eval_productCircleSubstitution_cubeSphereCoordinate {n : ℕ} (hn : 0 < n)
    {z : CubeCircleVar n → ℝ} (hz : z ∈ ProductCircle n) (i : Fin n) :
    MvPolynomial.eval z (productCircleSubstitution n (cubeSphereCoordinate n i)) =
      z (i, false) := by
  rw [eval_productCircleSubstitution, eval_cubeSphereCoordinate,
    productCircleSpherePoint_first, productCircleSpherePoint_second]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
  have hmass :
      (n : ℝ) * ((z (i, false) / Real.sqrt n) ^ 2 +
        (z (i, true) / Real.sqrt n) ^ 2) = 1 := by
    rw [div_pow, div_pow, Real.sq_sqrt hnR.le, ← add_div]
    rw [show z (i, false) ^ 2 + z (i, true) ^ 2 = 1 from hz i]
    field_simp
  rw [hmass]
  have hratio : ((2 * n + 1 : ℝ) - 1) / (2 * n) = 1 := by
    field_simp
    ring
  rw [hratio, one_pow]
  field_simp

/-- The lifted polynomial restricts to the original polynomial on the product of circles. -/
theorem eval_productCircleSubstitution_cubeSphereLift {n : ℕ} (hn : 0 < n)
    {z : CubeCircleVar n → ℝ} (hz : z ∈ ProductCircle n)
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval z (productCircleSubstitution n (cubeSphereLift n p)) =
      MvPolynomial.eval (fun i ↦ z (i, false)) p := by
  rw [eval_productCircleSubstitution, eval_cubeSphereLift_eq_map]
  have hmap :
      cubeSphereMap n (productCircleSpherePoint n z) = fun i ↦ z (i, false) := by
    funext i
    rw [cubeSphereMap]
    rw [← eval_productCircleSubstitution]
    exact eval_productCircleSubstitution_cubeSphereCoordinate hn hz i
  rw [hmap]

end QuarticConvergence
end OptimalConvergenceRates

end
