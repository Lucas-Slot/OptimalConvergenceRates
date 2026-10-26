import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Hierarchy
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Compactness
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.SphereCurve

/-!
# Relabeling a finite sphere without changing its hierarchy

`FiniteSphereCertificate` is the ordinary certificate identity for an arbitrary
finite variable type. Its specialization to `Fin n` is definitionally equivalent
to the project's `Feasible` predicate, as proved below.
-/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

def reindexedPoint {σ τ : Type*} (e : σ ≃ τ) (x : σ → ℝ) : τ → ℝ := x ∘ e.symm

theorem reindexedPoint_sum_sq {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (x : σ → ℝ) :
    (∑ j : τ, reindexedPoint e x j ^ 2) = ∑ i : σ, x i ^ 2 := by
  exact e.symm.sum_comp (fun i => x i ^ 2)

theorem eval_reindexedPoint {σ τ : Type*} (e : σ ≃ τ)
    (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    MvPolynomial.eval (reindexedPoint e x) (MvPolynomial.rename e p) =
      MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_rename]
  have hpoint : reindexedPoint e x ∘ e = x := by
    funext i
    simp [reindexedPoint]
  rw [hpoint]

theorem totalDegree_reindex {σ τ : Type*} (e : σ ≃ τ) (p : MvPolynomial σ ℝ) :
    (MvPolynomial.rename e p).totalDegree = p.totalDegree :=
  MvPolynomial.totalDegree_renameEquiv e p

theorem genericRadius_reindex {σ τ : Type*} [Fintype σ] [Fintype τ] (e : σ ≃ τ) :
    MvPolynomial.rename e (genericRadius (σ := σ)) = genericRadius (σ := τ) := by
  classical
  simp only [genericRadius, map_sum, map_pow, MvPolynomial.rename_X]
  exact e.sum_comp (fun j => (MvPolynomial.X j : MvPolynomial τ ℝ) ^ 2)

/-- The standard finite-sphere certificate, with the same exact degree bounds. -/
def FiniteSphereCertificate {σ : Type*} [Fintype σ]
    (r : ℕ) (p : MvPolynomial σ ℝ) (lam : ℝ) : Prop :=
  ∃ (m : ℕ) (h : Fin m → MvPolynomial σ ℝ) (g : MvPolynomial σ ℝ),
    (∀ j, (h j).totalDegree ≤ r) ∧ g.totalDegree ≤ 2 * r - 2 ∧
      p - MvPolynomial.C lam = (∑ j : Fin m, h j ^ 2) + (1 - genericRadius) * g

theorem finiteSphereCertificate_fin_iff {n r : ℕ} {p : Polynomial n} {lam : ℝ} :
    FiniteSphereCertificate r p lam ↔ Feasible r p lam := Iff.rfl

theorem FiniteSphereCertificate.rename_equiv {σ τ : Type*} [Fintype σ] [Fintype τ]
    {r : ℕ} {p : MvPolynomial σ ℝ} {lam : ℝ}
    (hcert : FiniteSphereCertificate r p lam) (e : σ ≃ τ) :
    FiniteSphereCertificate r (MvPolynomial.rename e p) lam := by
  classical
  rcases hcert with ⟨m, h, g, hh, hg, hid⟩
  refine ⟨m, fun j => MvPolynomial.rename e (h j), MvPolynomial.rename e g, ?_, ?_, ?_⟩
  · intro j
    exact (MvPolynomial.totalDegree_rename_le e (h j)).trans (hh j)
  · exact (MvPolynomial.totalDegree_rename_le e g).trans hg
  · have he := congrArg (MvPolynomial.rename e) hid
    simpa only [map_sub, MvPolynomial.rename_C, map_sum, map_pow, map_add, map_mul,
      map_one, genericRadius_reindex] using he

theorem finiteSphereCertificate_reindex {σ : Type*} [Fintype σ] {n r : ℕ}
    {p : MvPolynomial σ ℝ} {lam : ℝ} (e : σ ≃ Fin n)
    (hcert : FiniteSphereCertificate r p lam) :
    Feasible r (MvPolynomial.rename e p) lam :=
  finiteSphereCertificate_fin_iff.mp (hcert.rename_equiv e)

theorem Feasible.rename_equiv {n m r : ℕ} {p : Polynomial n} {lam : ℝ}
    (hcert : Feasible r p lam) (e : Fin n ≃ Fin m) :
    Feasible r (MvPolynomial.rename e p) lam :=
  finiteSphereCertificate_reindex e (finiteSphereCertificate_fin_iff.mpr hcert)

theorem feasible_rename_equiv_iff {n m r : ℕ} (e : Fin n ≃ Fin m)
    (p : Polynomial n) (lam : ℝ) :
    Feasible r (MvPolynomial.rename e p) lam ↔ Feasible r p lam := by
  constructor
  · intro h
    have hback := h.rename_equiv e.symm
    simpa only [MvPolynomial.rename_rename, e.symm_comp_self,
      MvPolynomial.rename_id_apply] using hback
  · intro h
    exact h.rename_equiv e

theorem isSphereMinimum_reindex {σ : Type*} [Fintype σ] {n : ℕ}
    (e : σ ≃ Fin n) (p : MvPolynomial σ ℝ) (mu : ℝ)
    (hlower : ∀ x : σ → ℝ, (∑ i : σ, x i ^ 2) = 1 → mu ≤ MvPolynomial.eval x p)
    (hattained : ∃ x : σ → ℝ, (∑ i : σ, x i ^ 2) = 1 ∧ MvPolynomial.eval x p = mu) :
    IsSphereMinimum (MvPolynomial.rename e p) mu := by
  constructor
  · intro y hy
    rw [MvPolynomial.eval_rename]
    apply hlower
    have hsum := e.sum_comp (fun j => y j ^ 2)
    exact hsum.trans hy
  · obtain ⟨x, hx, hvalue⟩ := hattained
    refine ⟨reindexedPoint e x, ?_, ?_⟩
    · change (∑ j : Fin n, reindexedPoint e x j ^ 2) = 1
      rw [reindexedPoint_sum_sq, hx]
    · rw [eval_reindexedPoint, hvalue]

theorem sphereSupNorm_reindex_eq {σ : Type*} [Fintype σ] {n : ℕ}
    (e : σ ≃ Fin n) (p : MvPolynomial σ ℝ) (B : ℝ)
    (hbound : ∀ x : σ → ℝ, (∑ i : σ, x i ^ 2) = 1 → |MvPolynomial.eval x p| ≤ B)
    (hattained : ∃ x : σ → ℝ, (∑ i : σ, x i ^ 2) = 1 ∧ |MvPolynomial.eval x p| = B) :
    sphereSupNorm (MvPolynomial.rename e p) = B := by
  obtain ⟨x, hx, hvalue⟩ := hattained
  have hy : reindexedPoint e x ∈ unitSphere n := by
    change (∑ j : Fin n, reindexedPoint e x j ^ 2) = 1
    rw [reindexedPoint_sum_sq, hx]
  have heval : |MvPolynomial.eval (reindexedPoint e x) (MvPolynomial.rename e p)| = B := by
    rw [eval_reindexedPoint, hvalue]
  apply le_antisymm
  · apply csSup_le (s := {v : ℝ | ∃ y ∈ unitSphere n,
      |MvPolynomial.eval y (MvPolynomial.rename e p)| = v})
      ⟨B, reindexedPoint e x, hy, heval⟩
    rintro v ⟨y, hysphere, rfl⟩
    rw [MvPolynomial.eval_rename]
    exact hbound (y ∘ e) ((e.sum_comp (fun j => y j ^ 2)).trans hysphere)
  · exact le_csSup (sphereNormValues_bddAbove _)
      ⟨reindexedPoint e x, hy, heval⟩

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
