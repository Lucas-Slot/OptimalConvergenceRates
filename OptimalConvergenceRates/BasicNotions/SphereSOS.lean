/-
  OptimalConvergenceRates/BasicNotions/SphereSOS.lean

  Sum-of-squares certificates modulo the equation of the unit sphere.
-/
import OptimalConvergenceRates.BasicNotions.SOS

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace SphereBallTransfers

/-! ## Generic SOS certificates modulo the unit-sphere equation -/

/-- The quadratic form `x_0^2 + ... + x_{m-1}^2`. -/
def sphereQuadratic (m : ℕ) : MvPolynomial (Fin m) ℝ :=
  ∑ i : Fin m, (X i) ^ 2

/-- The defining polynomial for the unit sphere: `sum_i x_i^2 - 1`. -/
def sphereRelation (m : ℕ) : MvPolynomial (Fin m) ℝ :=
  sphereQuadratic m - 1

/-- The unit sphere as a subset of coordinate space. -/
def sphereSet (m : ℕ) : Set (Fin m → ℝ) :=
  {x | MvPolynomial.eval x (sphereQuadratic m) = 1}

/-- A degree-`k` SOS certificate for `p` modulo the unit-sphere equation.

The degree bound is on the square roots. The multiplier of the sphere relation
is intentionally left unbounded. -/
def SphereSOSMod {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (k : ℕ) : Prop :=
  ∃ (N : ℕ) (q : Fin N → MvPolynomial (Fin m) ℝ) (h : MvPolynomial (Fin m) ℝ),
    p = (∑ j : Fin N, (q j) ^ 2) + sphereRelation m * h ∧
    ∀ j : Fin N, (q j).totalDegree ≤ k

/-- The explicit data carried by a degree-`k` sphere SOS certificate. -/
structure SphereSOSWitness {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (k : ℕ) where
  N : ℕ
  q : Fin N → MvPolynomial (Fin m) ℝ
  h : MvPolynomial (Fin m) ℝ
  decomp : p = (∑ j : Fin N, (q j) ^ 2) + sphereRelation m * h
  degree : ∀ j : Fin N, (q j).totalDegree ≤ k

/-- Forget the structured witness into the existential predicate. -/
theorem SphereSOSWitness.toSphereSOSMod {m : ℕ} {p : MvPolynomial (Fin m) ℝ} {k : ℕ}
    (w : SphereSOSWitness p k) : SphereSOSMod p k :=
  ⟨w.N, w.q, w.h, w.decomp, w.degree⟩

/-- Repackage the existential predicate as an explicit witness. -/
theorem sphereSOSMod_iff_nonempty_witness {m : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (k : ℕ) : SphereSOSMod p k ↔ Nonempty (SphereSOSWitness p k) := by
  constructor
  · rintro ⟨N, q, h, hdecomp, hdeg⟩
    exact ⟨⟨N, q, h, hdecomp, hdeg⟩⟩
  · rintro ⟨w⟩
    exact w.toSphereSOSMod

/-- A degree-bounded ordinary SOS is a sphere SOS certificate with zero multiplier. -/
theorem DegreeBoundedSOS.toSphereSOSMod {m : ℕ} {p : MvPolynomial (Fin m) ℝ} {k : ℕ}
    (hp : DegreeBoundedSOS p k) : SphereSOSMod p k := by
  exact ⟨hp.N, hp.P, 0, by simp [hp.decomp], hp.degree⟩

/-- The zero polynomial has a sphere SOS certificate at every order. -/
theorem sphereSOSMod_zero (m k : ℕ) :
    SphereSOSMod (0 : MvPolynomial (Fin m) ℝ) k := by
  refine ⟨0, Fin.elim0, 0, ?_, fun j ↦ Fin.elim0 j⟩
  simp

/-- A nonnegative constant has a degree-zero sphere SOS certificate. -/
theorem sphereSOSMod_const {m k : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    SphereSOSMod (MvPolynomial.C c : MvPolynomial (Fin m) ℝ) k := by
  refine ⟨1, fun _ ↦ MvPolynomial.C (Real.sqrt c), 0, ?_, ?_⟩
  · simp only [Fin.sum_univ_one, pow_two, add_zero, mul_zero]
    rw [← map_mul, Real.mul_self_sqrt hc]
  · intro j
    simp

/-- Sphere SOS certificates are closed under addition without increasing the order. -/
theorem SphereSOSMod.add {m k : ℕ} {p q : MvPolynomial (Fin m) ℝ}
    (hp : SphereSOSMod p k) (hq : SphereSOSMod q k) : SphereSOSMod (p + q) k := by
  classical
  obtain ⟨Np, qp, hpRel, hpDecomp, hpDeg⟩ := hp
  obtain ⟨Nq, qq, hqRel, hqDecomp, hqDeg⟩ := hq
  let roots : Fin (Np + Nq) → MvPolynomial (Fin m) ℝ := Fin.addCases qp qq
  refine ⟨Np + Nq, roots, hpRel + hqRel, ?_, ?_⟩
  · rw [hpDecomp, hqDecomp]
    simp only [roots, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
    ring
  · intro j
    exact Fin.addCases (fun i ↦ by simpa [roots] using hpDeg i)
      (fun i ↦ by simpa [roots] using hqDeg i) j

/-- Increasing the root-degree bound preserves a sphere SOS certificate. -/
theorem SphereSOSMod.mono {m : ℕ} {p : MvPolynomial (Fin m) ℝ} {k l : ℕ}
    (hkl : k ≤ l) (hp : SphereSOSMod p k) : SphereSOSMod p l := by
  obtain ⟨N, q, h, hdecomp, hdeg⟩ := hp
  exact ⟨N, q, h, hdecomp, fun j ↦ (hdeg j).trans hkl⟩
/-- Multiplying a sphere SOS certificate by a polynomial square adds the degree of that
polynomial to the root-degree bound. -/
theorem SphereSOSMod.mul_sq {m k : ℕ} {p : MvPolynomial (Fin m) ℝ}
    (hp : SphereSOSMod p k) (a : MvPolynomial (Fin m) ℝ) :
    SphereSOSMod (p * a ^ 2) (k + a.totalDegree) := by
  obtain ⟨N, q, h, hdecomp, hdeg⟩ := hp
  refine ⟨N, fun j ↦ q j * a, h * a ^ 2, ?_, ?_⟩
  · rw [hdecomp]
    simp only [add_mul, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · ring
  · intro j
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hdeg j) le_rfl)

/-- Sphere SOS certificates are closed under multiplication by a nonnegative scalar. -/
theorem SphereSOSMod.nonneg_scale {m k : ℕ} {p : MvPolynomial (Fin m) ℝ}
    (hp : SphereSOSMod p k) {c : ℝ} (hc : 0 ≤ c) :
    SphereSOSMod (MvPolynomial.C c * p) k := by
  have h := hp.mul_sq (MvPolynomial.C (Real.sqrt c))
  convert h using 1
  · rw [← MvPolynomial.C_pow, Real.sq_sqrt hc]
    ring
  · simp


/-- Adding a multiple of the sphere relation changes only the relation multiplier. -/
theorem SphereSOSMod.add_relation_mul {m k : ℕ} {p : MvPolynomial (Fin m) ℝ}
    (hp : SphereSOSMod p k) (a : MvPolynomial (Fin m) ℝ) :
    SphereSOSMod (p + sphereRelation m * a) k := by
  obtain ⟨N, q, h, hdecomp, hdeg⟩ := hp
  refine ⟨N, q, h + a, ?_, hdeg⟩
  rw [hdecomp]
  ring
/-- A finite sum of sphere SOS certificates has the same root-degree bound. -/
theorem sphereSOSMod_finset_sum {m k : ℕ} {ι : Type*}
    (s : Finset ι) (p : ι → MvPolynomial (Fin m) ℝ)
    (hp : ∀ i ∈ s, SphereSOSMod (p i) k) :
    SphereSOSMod (∑ i ∈ s, p i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using sphereSOSMod_zero m k
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hp a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ hp i (Finset.mem_insert_of_mem hi))

/-- The product of two sphere SOS certificates is a sphere SOS certificate, with root
degrees adding. -/
theorem SphereSOSMod.mul {m k l : ℕ} {p q : MvPolynomial (Fin m) ℝ}
    (hp : SphereSOSMod p k) (hq : SphereSOSMod q l) :
    SphereSOSMod (p * q) (k + l) := by
  classical
  obtain ⟨N, roots, h, hdecomp, hdeg⟩ := hq
  have hterm (j : Fin N) : SphereSOSMod (p * roots j ^ 2) (k + l) := by
    exact (hp.mul_sq (roots j)).mono (Nat.add_le_add_left (hdeg j) k)
  have hsum : SphereSOSMod (∑ j : Fin N, p * roots j ^ 2) (k + l) := by
    simpa using sphereSOSMod_finset_sum Finset.univ
      (fun j : Fin N ↦ p * roots j ^ 2) (fun j _ ↦ hterm j)
  have hcert := hsum.add_relation_mul (p * h)
  convert hcert using 1
  rw [hdecomp, mul_add, Finset.mul_sum]
  ring


/-- Sphere SOS membership only depends on the polynomial modulo the sphere relation. -/
theorem sphereSOSMod_add_relation_mul_iff {m k : ℕ}
    (p a : MvPolynomial (Fin m) ℝ) :
    SphereSOSMod (p + sphereRelation m * a) k ↔ SphereSOSMod p k := by
  constructor
  · intro hp
    have h := hp.add_relation_mul (-a)
    convert h using 1
    all_goals ring
  · intro hp
    exact hp.add_relation_mul a

/-- Evaluation of the sphere relation vanishes on the unit sphere. -/
@[simp] theorem eval_sphereRelation_of_mem {m : ℕ} {x : Fin m → ℝ}
    (hx : x ∈ sphereSet m) : MvPolynomial.eval x (sphereRelation m) = 0 := by
  rw [sphereRelation, map_sub, hx]
  simp

/-- A sphere SOS certificate evaluates nonnegatively on the unit sphere. -/
theorem SphereSOSMod.nonnegOnSphere {m k : ℕ} {p : MvPolynomial (Fin m) ℝ}
    (hp : SphereSOSMod p k) {x : Fin m → ℝ} (hx : x ∈ sphereSet m) :
    0 ≤ MvPolynomial.eval x p := by
  obtain ⟨N, q, h, hdecomp, -⟩ := hp
  rw [hdecomp]
  simp only [map_add, map_mul, map_sum, map_pow, eval_sphereRelation_of_mem hx, zero_mul,
    add_zero]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

end SphereBallTransfers
end OptimalConvergenceRates

end
