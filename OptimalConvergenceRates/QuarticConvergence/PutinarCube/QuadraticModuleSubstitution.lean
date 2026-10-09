/-
  Degree-tracked substitutions of box quadratic-module certificates.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.OrderConventions
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ProductCircle
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n m d r s : ℕ}

/-! ## Closure lemmas used by substitution -/

/-- Polynomial substitution preserves sums of squares. -/
theorem isSOS_aeval {p : MvPolynomial (Fin n) ℝ}
    (hp : IsSOS p) (f : Fin n → MvPolynomial (Fin m) ℝ) :
    IsSOS (MvPolynomial.aeval f p) := by
  obtain ⟨N, q, rfl⟩ := hp
  exact ⟨N, fun i ↦ MvPolynomial.aeval f (q i), by
    simp only [map_sum, map_pow]⟩

/-- An SOS polynomial belongs to the box quadratic module as its free term. -/
theorem isSOS_mem_BoxQuadraticModule {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : IsSOS p) (hdegree : p.totalDegree ≤ r) :
    p ∈ BoxQuadraticModule n r := by
  refine ⟨p, 0, hp, fun _ ↦ IsSOS_zero, hdegree, fun _ ↦ by simp, ?_⟩
  simp

/-- A single SOS multiple of one box generator is a quadratic-module term. -/
theorem sos_mul_boxSemialgebraicGenerator_mem_BoxQuadraticModule
    (i : Fin n) (p : MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hp : IsSOS p)
    (hdegree : (p * BoxSemialgebraicGenerator i).totalDegree ≤ r) :
    p * BoxSemialgebraicGenerator i ∈ BoxQuadraticModule n r := by
  classical
  refine ⟨0, Function.update 0 i p, IsSOS_zero, ?_, by simp, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa using hp
    · rw [Function.update_of_ne hji]
      exact IsSOS_zero
  · intro j
    by_cases hji : j = i
    · subst j
      simpa using hdegree
    · rw [Function.update_of_ne hji]
      simp
  · rw [zero_add, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Function.update_of_ne hji]
      simp
    · simp

/-- A finite sum of certificates at one common order is again a certificate at
that order. -/
theorem BoxQuadraticModule_sum {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hp : ∀ i, p i ∈ BoxQuadraticModule n r) :
    ∑ i, p i ∈ BoxQuadraticModule n r := by
  classical
  apply Finset.sum_induction _ (· ∈ BoxQuadraticModule n r)
      (fun _ _ ha hb ↦ BoxQuadraticModule_add ha hb)
      (zero_mem_BoxQuadraticModule n r)
  intro i _
  exact hp i

/-- Multiplication by an SOS polynomial preserves the box quadratic module and
adds the SOS total degree to the certificate order. -/
theorem BoxQuadraticModule_sos_mul
    {p q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : IsSOS p) (hq : q ∈ BoxQuadraticModule n r) :
    p * q ∈ BoxQuadraticModule n (r + p.totalDegree) := by
  obtain ⟨τ0, τ, hsos0, hsos, hdegree0, hdegree, hq⟩ := hq
  refine ⟨p * τ0, fun i ↦ p * τ i, IsSOS_mul hp hsos0,
    fun i ↦ IsSOS_mul hp (hsos i), ?_, ?_, ?_⟩
  · calc
      (p * τ0).totalDegree ≤ p.totalDegree + τ0.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ p.totalDegree + r := Nat.add_le_add_left hdegree0 _
      _ = r + p.totalDegree := Nat.add_comm _ _
  · intro i
    calc
      (p * τ i * BoxSemialgebraicGenerator i).totalDegree =
          (p * (τ i * BoxSemialgebraicGenerator i)).totalDegree := by ring_nf
      _ ≤ p.totalDegree + (τ i * BoxSemialgebraicGenerator i).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ p.totalDegree + r := Nat.add_le_add_left (hdegree i) _
      _ = r + p.totalDegree := Nat.add_comm _ _
  · rw [hq, mul_add, Finset.mul_sum]
    simp only [mul_assoc]

/-! ## Substitution through arbitrary generator certificates -/

/-- A source box generator is nonzero. -/
theorem boxSemialgebraicGenerator_ne_zero (i : Fin n) :
    BoxSemialgebraicGenerator i ≠ (0 : MvPolynomial (Fin n) ℝ) := by
  intro hzero
  have heval := congrArg (MvPolynomial.eval fun _ : Fin n ↦ (0 : ℝ)) hzero
  simp [BoxSemialgebraicGenerator] at heval

/-- The degree of an SOS multiplier in a box quadratic-module term is bounded
by the degree of that term. -/
theorem totalDegree_le_of_mul_boxSemialgebraicGenerator_totalDegree_le
    {p : MvPolynomial (Fin n) ℝ} (i : Fin n) {r : ℕ}
    (hdegree : (p * BoxSemialgebraicGenerator i).totalDegree ≤ r) :
    p.totalDegree ≤ r := by
  by_cases hp : p = 0
  · simp [hp]
  · have hmul := MvPolynomial.totalDegree_mul_of_isDomain hp
      (boxSemialgebraicGenerator_ne_zero i)
    rw [hmul] at hdegree
    omega

/-- Substitute a bounded-degree polynomial for every source variable. If the
image of every source box generator already has a target box quadratic-module
certificate of order `s`, a source order-`r` certificate maps to target order
`s + d * r`.

This deliberately states the generator hypothesis as target module membership:
it can express localized identities more general than a single target
generator factor. -/
theorem aeval_mem_BoxQuadraticModule_of_generator_mem
    (f : Fin n → MvPolynomial (Fin m) ℝ)
    (hfdegree : ∀ i, (f i).totalDegree ≤ d)
    (hgenerator : ∀ i,
      MvPolynomial.aeval f (BoxSemialgebraicGenerator i) ∈
        BoxQuadraticModule m s)
    {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ BoxQuadraticModule n r) :
    MvPolynomial.aeval f p ∈ BoxQuadraticModule m (s + d * r) := by
  obtain ⟨σ0, σ, hsos0, hsos, hdegree0, hdegree, hp⟩ := hp
  have hmap_degree (q : MvPolynomial (Fin n) ℝ) (hq : q.totalDegree ≤ r) :
      (MvPolynomial.aeval f q).totalDegree ≤ d * r :=
    (totalDegree_aeval_le_mul_general f hfdegree q).trans
      (Nat.mul_le_mul_left d hq)
  have hfree : MvPolynomial.aeval f σ0 ∈ BoxQuadraticModule m (s + d * r) :=
    isSOS_mem_BoxQuadraticModule (isSOS_aeval hsos0 f)
      ((hmap_degree σ0 hdegree0).trans (by omega))
  have hterm (i : Fin n) :
      MvPolynomial.aeval f (σ i) *
          MvPolynomial.aeval f (BoxSemialgebraicGenerator i) ∈
        BoxQuadraticModule m (s + d * r) := by
    have hsigma_degree : (σ i).totalDegree ≤ r :=
      totalDegree_le_of_mul_boxSemialgebraicGenerator_totalDegree_le i (hdegree i)
    have hmapped_degree : (MvPolynomial.aeval f (σ i)).totalDegree ≤ d * r :=
      hmap_degree (σ i) hsigma_degree
    exact BoxQuadraticModule_mono (by omega)
      (BoxQuadraticModule_sos_mul (isSOS_aeval (hsos i) f) (hgenerator i))
  rw [hp]
  simpa only [map_add, map_sum, map_mul] using
    BoxQuadraticModule_add hfree (BoxQuadraticModule_sum _ hterm)

/-! ## The sharp single-generator factorization case -/

/-- A sharper substitution theorem for the common case in which every source
box generator maps exactly to an SOS multiple of one selected target box
generator. Because each complete source term is mapped before its degree is
estimated, no extra additive generator order is lost: the target order is
`d * r`. The selected target coordinates need not be distinct. -/
theorem aeval_mem_BoxQuadraticModule_of_generator_sos_mul
    (f : Fin n → MvPolynomial (Fin m) ℝ)
    (hfdegree : ∀ i, (f i).totalDegree ≤ d)
    (target : Fin n → Fin m)
    (multiplier : Fin n → MvPolynomial (Fin m) ℝ)
    (hmultiplier : ∀ i, IsSOS (multiplier i))
    (hgenerator : ∀ i,
      MvPolynomial.aeval f (BoxSemialgebraicGenerator i) =
        multiplier i * BoxSemialgebraicGenerator (target i))
    {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ BoxQuadraticModule n r) :
    MvPolynomial.aeval f p ∈ BoxQuadraticModule m (d * r) := by
  obtain ⟨σ0, σ, hsos0, hsos, hdegree0, hdegree, hp⟩ := hp
  have hmap_degree (q : MvPolynomial (Fin n) ℝ) (hq : q.totalDegree ≤ r) :
      (MvPolynomial.aeval f q).totalDegree ≤ d * r :=
    (totalDegree_aeval_le_mul_general f hfdegree q).trans
      (Nat.mul_le_mul_left d hq)
  have hfree : MvPolynomial.aeval f σ0 ∈ BoxQuadraticModule m (d * r) :=
    isSOS_mem_BoxQuadraticModule (isSOS_aeval hsos0 f) (hmap_degree σ0 hdegree0)
  have hterm (i : Fin n) :
      MvPolynomial.aeval f (σ i) *
          MvPolynomial.aeval f (BoxSemialgebraicGenerator i) ∈
        BoxQuadraticModule m (d * r) := by
    rw [hgenerator i]
    rw [← mul_assoc]
    apply sos_mul_boxSemialgebraicGenerator_mem_BoxQuadraticModule
    · exact IsSOS_mul (isSOS_aeval (hsos i) f) (hmultiplier i)
    · rw [mul_assoc, ← hgenerator i, ← map_mul]
      exact hmap_degree _ (hdegree i)
  rw [hp]
  simpa only [map_add, map_sum, map_mul] using
    BoxQuadraticModule_add hfree (BoxQuadraticModule_sum _ hterm)

/-! ## Coordinate and selected-univariate substitutions -/

/-- Substitute the target coordinate `target i` for source coordinate `i`.
Injectivity is not required; identifying source coordinates is allowed. -/
def boxCoordinateSubstitution (target : Fin n → Fin m) :
    Fin n → MvPolynomial (Fin m) ℝ :=
  fun i ↦ X (target i)

/-- Coordinate substitution preserves the canonical box quadratic-module
order exactly. -/
theorem aeval_boxCoordinateSubstitution_mem_BoxQuadraticModule
    (target : Fin n → Fin m) {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ BoxQuadraticModule n r) :
    MvPolynomial.aeval (boxCoordinateSubstitution target) p ∈
      BoxQuadraticModule m r := by
  simpa using aeval_mem_BoxQuadraticModule_of_generator_sos_mul
    (d := 1) (r := r) (boxCoordinateSubstitution target)
    (fun i ↦ by simp [boxCoordinateSubstitution]) target
    (fun _ ↦ (1 : MvPolynomial (Fin m) ℝ))
    (fun _ ↦ by simpa using IsSOS_sq (1 : MvPolynomial (Fin m) ℝ)) (fun i ↦ by
      simp [boxCoordinateSubstitution, BoxSemialgebraicGenerator]) hp

/-- Substitute a univariate polynomial into a selected target coordinate. -/
def selectedUnivariateSubstitution
    (target : Fin n → Fin m) (q : Fin n → Polynomial ℝ) :
    Fin n → MvPolynomial (Fin m) ℝ :=
  fun i ↦ embedUnivariate (target i) (q i)

/-- Selected-coordinate univariate substitution with explicit box-generator
factorizations. The factorization hypothesis is exactly the algebraic condition
needed for Putinar localization: `1 - q_i(X)^2` must be an SOS multiple of the
selected target generator. -/
theorem aeval_selectedUnivariateSubstitution_mem_BoxQuadraticModule
    (target : Fin n → Fin m) (q : Fin n → Polynomial ℝ)
    (hqdegree : ∀ i, (q i).natDegree ≤ d)
    (multiplier : Fin n → MvPolynomial (Fin m) ℝ)
    (hmultiplier : ∀ i, IsSOS (multiplier i))
    (hfactor : ∀ i,
      1 - (embedUnivariate (target i) (q i)) ^ 2 =
        multiplier i * BoxSemialgebraicGenerator (target i))
    {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ BoxQuadraticModule n r) :
    MvPolynomial.aeval (selectedUnivariateSubstitution target q) p ∈
      BoxQuadraticModule m (d * r) := by
  apply aeval_mem_BoxQuadraticModule_of_generator_sos_mul
      (selectedUnivariateSubstitution target q) ?_ target multiplier hmultiplier ?_ hp
  · intro i
    exact (totalDegree_embedUnivariate (target i) (q i)).trans (hqdegree i)
  · intro i
    simpa [selectedUnivariateSubstitution, BoxSemialgebraicGenerator] using hfactor i

end QuarticConvergence
end OptimalConvergenceRates

end
