import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.CertificateScaling

/-!
# Explicit nonempty feasible sets for the quartic construction

A sum of quadratic squares minus `c * x_t^4`, where `c ≥ 0`, has feasible
value `-c` already at order two on the original full unit sphere.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators

/-- A finite family of squares may be indexed by any finite type; this lemma
converts it to the `Fin m` representation in the definition of `Feasible`. -/
theorem feasible_of_fintype_sos {n r : ℕ} {p : Polynomial n} {lam : ℝ}
    {I : Type*} [Fintype I] (h : I → Polynomial n) (g : Polynomial n)
    (hh : ∀ j, (h j).totalDegree ≤ r)
    (hg : g.totalDegree ≤ 2 * r - 2)
    (hid : p - MvPolynomial.C lam =
      (∑ j : I, h j ^ 2) + (1 - radiusPolynomial n) * g) :
    Feasible r p lam := by
  classical
  let e := (Fintype.equivFin I).symm
  apply feasible_of_squares (fun j ↦ h (e j)) g (fun j ↦ hh (e j)) hg
  rw [e.sum_comp (fun j ↦ h j ^ 2)]
  exact hid

theorem radiusPolynomial_totalDegree_le (n : ℕ) :
    (radiusPolynomial n).totalDegree ≤ 2 := by
  classical
  dsimp only [radiusPolynomial, SphereBallTransfers.sphereQuadratic]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  simp

/-- Expanding the squared radius gives a sum over all ordered coordinate pairs. -/
theorem radius_squared_pair_sos (n : ℕ) :
    (radiusPolynomial n) ^ 2 =
      ∑ k : Fin n × Fin n,
        ((MvPolynomial.X k.1 : Polynomial n) * MvPolynomial.X k.2) ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  dsimp only [radiusPolynomial, SphereBallTransfers.sphereQuadratic]
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum, ← mul_pow]

/-- A quadratic root for every ordered pair, omitting the single pair `(t,t)`. -/
def coordinateComplementRoot {n : ℕ} (t : Fin n) (k : Fin n × Fin n) : Polynomial n :=
  if k = (t, t) then 0 else MvPolynomial.X k.1 * MvPolynomial.X k.2

theorem coordinateComplementRoot_totalDegree_le {n : ℕ} (t : Fin n)
    (k : Fin n × Fin n) : (coordinateComplementRoot t k).totalDegree ≤ 2 := by
  classical
  unfold coordinateComplementRoot
  split_ifs
  · simp
  · calc
      ((MvPolynomial.X k.1 : Polynomial n) * MvPolynomial.X k.2).totalDegree ≤
          (MvPolynomial.X k.1 : Polynomial n).totalDegree +
            (MvPolynomial.X k.2 : Polynomial n).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = 2 := by simp

/-- The complement of one fourth power in the squared radius is SOS. -/
theorem radius_coordinate_complement_sos {n : ℕ} (t : Fin n) :
    (radiusPolynomial n) ^ 2 - (MvPolynomial.X t : Polynomial n) ^ 4 =
      ∑ k : Fin n × Fin n, coordinateComplementRoot t k ^ 2 := by
  classical
  have hdiag : ((MvPolynomial.X t : Polynomial n) * MvPolynomial.X t) ^ 2 =
      (MvPolynomial.X t : Polynomial n) ^ 4 := by ring
  have hsplit :
      (∑ k : Fin n × Fin n,
        ((MvPolynomial.X k.1 : Polynomial n) * MvPolynomial.X k.2) ^ 2) =
      (MvPolynomial.X t : Polynomial n) ^ 4 +
        ∑ k : Fin n × Fin n, coordinateComplementRoot t k ^ 2 := by
    calc
      (∑ k : Fin n × Fin n,
          ((MvPolynomial.X k.1 : Polynomial n) * MvPolynomial.X k.2) ^ 2) =
          ∑ k : Fin n × Fin n,
            ((if k = (t, t) then
                ((MvPolynomial.X k.1 : Polynomial n) * MvPolynomial.X k.2) ^ 2
              else 0) + coordinateComplementRoot t k ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hkt : k = (t, t) <;> simp [coordinateComplementRoot, hkt]
      _ = (∑ k : Fin n × Fin n,
            if k = (t, t) then
              ((MvPolynomial.X k.1 : Polynomial n) * MvPolynomial.X k.2) ^ 2
            else 0) +
          ∑ k : Fin n × Fin n, coordinateComplementRoot t k ^ 2 :=
        Finset.sum_add_distrib
      _ = (MvPolynomial.X t : Polynomial n) ^ 4 +
          ∑ k : Fin n × Fin n, coordinateComplementRoot t k ^ 2 := by
        simp [hdiag]
  rw [radius_squared_pair_sos, hsplit]
  ring

/-- An explicit order-two certificate for an SOS quartic minus one coordinate
fourth power. No Positivstellensatz or SDP attainment theorem is required. -/
theorem feasible_two_of_sos_sub_coordinate_fourth {n m : ℕ}
    {p : Polynomial n} {c : ℝ} (t : Fin n) (hc : 0 ≤ c)
    (h : Fin m → Polynomial n) (hh : ∀ j, (h j).totalDegree ≤ 2)
    (hp : p = (∑ j : Fin m, h j ^ 2) -
      MvPolynomial.C c * (MvPolynomial.X t : Polynomial n) ^ 4) :
    Feasible 2 p (-c) := by
  classical
  let H : (Fin m ⊕ (Fin n × Fin n)) → Polynomial n :=
    Sum.elim h (fun k ↦ MvPolynomial.C (Real.sqrt c) * coordinateComplementRoot t k)
  let g : Polynomial n := MvPolynomial.C c * (1 + radiusPolynomial n)
  have hsqrt : (MvPolynomial.C (Real.sqrt c) : Polynomial n) ^ 2 =
      MvPolynomial.C c := by
    rw [← MvPolynomial.C_pow, Real.sq_sqrt hc]
  have hscaled :
      (∑ k : Fin n × Fin n,
          (MvPolynomial.C (Real.sqrt c) * coordinateComplementRoot t k) ^ 2) =
        MvPolynomial.C c *
          (∑ k : Fin n × Fin n, coordinateComplementRoot t k ^ 2) := by
    simp_rw [mul_pow, hsqrt]
    rw [Finset.mul_sum]
  have hsum : (∑ j : Fin m ⊕ (Fin n × Fin n), H j ^ 2) =
      (∑ j : Fin m, h j ^ 2) +
        MvPolynomial.C c *
          ((radiusPolynomial n) ^ 2 - (MvPolynomial.X t : Polynomial n) ^ 4) := by
    simp only [Fintype.sum_sum_type, H, Sum.elim_inl, Sum.elim_inr]
    rw [hscaled, radius_coordinate_complement_sos]
  apply feasible_of_fintype_sos H g
  · intro j
    cases j with
    | inl j => simpa [H] using hh j
    | inr k =>
        change (MvPolynomial.C (Real.sqrt c) * coordinateComplementRoot t k).totalDegree ≤ 2
        calc
          (MvPolynomial.C (Real.sqrt c) * coordinateComplementRoot t k).totalDegree ≤
              (MvPolynomial.C (Real.sqrt c) : Polynomial n).totalDegree +
                (coordinateComplementRoot t k).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ = (coordinateComplementRoot t k).totalDegree := by simp
          _ ≤ 2 := coordinateComplementRoot_totalDegree_le t k
  · change (MvPolynomial.C c * (1 + radiusPolynomial n)).totalDegree ≤ 2
    have hplus : (1 + radiusPolynomial n).totalDegree ≤ 2 := by
      calc
        (1 + radiusPolynomial n).totalDegree ≤
            max (1 : Polynomial n).totalDegree (radiusPolynomial n).totalDegree :=
          MvPolynomial.totalDegree_add _ _
        _ ≤ 2 := max_le (by simp) (radiusPolynomial_totalDegree_le n)
    calc
      (MvPolynomial.C c * (1 + radiusPolynomial n)).totalDegree ≤
          (MvPolynomial.C c : Polynomial n).totalDegree +
            (1 + radiusPolynomial n).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = (1 + radiusPolynomial n).totalDegree := by simp
      _ ≤ 2 := hplus
  · rw [hp, hsum, MvPolynomial.C_neg]
    dsimp [g]
    ring

/-- The same feasible value works at every sphere relaxation order `r ≥ 2`. -/
theorem feasible_of_sos_sub_coordinate_fourth {n m r : ℕ}
    {p : Polynomial n} {c : ℝ} (t : Fin n) (hc : 0 ≤ c) (hr : 2 ≤ r)
    (h : Fin m → Polynomial n) (hh : ∀ j, (h j).totalDegree ≤ 2)
    (hp : p = (∑ j : Fin m, h j ^ 2) -
      MvPolynomial.C c * (MvPolynomial.X t : Polynomial n) ^ 4) :
    Feasible r p (-c) := by
  exact feasible_mono hr (feasible_two_of_sos_sub_coordinate_fourth t hc h hh hp)

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
