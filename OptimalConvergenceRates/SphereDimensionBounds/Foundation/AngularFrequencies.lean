import OptimalConvergenceRates.SphereDimensionBounds.Foundation.WeightedComplex
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Degree-sensitive finite frequencies of angular polynomial evaluation

Integer-frequency polynomials are represented by the ordinary additive monoid
algebra `AddMonoidAlgebra ℂ ℤ`. Its convolution product adds frequencies.
-/

open scoped Pointwise

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

abbrev FrequencyPolynomial := AddMonoidAlgebra ℂ ℤ

/-- All frequencies lie in the indicated symmetric integer interval. -/
def FrequencyBand (r : ℕ) (p : FrequencyPolynomial) : Prop :=
  ∀ k ∈ p.coeff.support, -(r : ℤ) ≤ k ∧ k ≤ (r : ℤ)

def frequencyExpHom (z : ℂ) : Multiplicative ℤ →* ℂ where
  toFun k := Complex.exp ((k.toAdd : ℂ) * z * Complex.I)
  map_one' := by simp
  map_mul' a b := by
    change Complex.exp (((a.toAdd + b.toAdd : ℤ) : ℂ) * z * Complex.I) =
      Complex.exp ((a.toAdd : ℂ) * z * Complex.I) *
        Complex.exp ((b.toAdd : ℂ) * z * Complex.I)
    simp only [Int.cast_add, add_mul, Complex.exp_add]

def evalFrequency (z : ℂ) : FrequencyPolynomial →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ ℤ (frequencyExpHom z)

theorem evalFrequency_eq_sum (z : ℂ) (p : FrequencyPolynomial) :
    evalFrequency z p =
      ∑ k ∈ p.coeff.support, Complex.exp ((k : ℂ) * z * Complex.I) * p.coeff k := by
  rw [evalFrequency, AddMonoidAlgebra.lift_apply]
  simp only [Finsupp.sum, frequencyExpHom, MonoidHom.coe_mk, OneHom.coe_mk,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  change p.coeff k * Complex.exp ((k : ℂ) * z * Complex.I) =
    Complex.exp ((k : ℂ) * z * Complex.I) * p.coeff k
  exact mul_comm _ _

@[simp]
theorem evalFrequency_single (z : ℂ) (k : ℤ) (c : ℂ) :
    evalFrequency z (AddMonoidAlgebra.single k c) = c * Complex.exp ((k : ℂ) * z * Complex.I) := by
  simp [evalFrequency, AddMonoidAlgebra.lift_single, frequencyExpHom, smul_eq_mul]

theorem frequencyBand_zero (r : ℕ) : FrequencyBand r 0 := by
  simp [FrequencyBand]

theorem frequencyBand_single {r : ℕ} (k : ℤ) (c : ℂ)
    (hk : -(r : ℤ) ≤ k ∧ k ≤ (r : ℤ)) :
    FrequencyBand r (AddMonoidAlgebra.single k c) := by
  intro j hj
  have hjs : j ∈ ({k} : Finset ℤ) := Finsupp.support_single_subset hj
  simpa only [Finset.mem_singleton.mp hjs] using hk

theorem frequencyBand_mono {r t : ℕ} (hrt : r ≤ t) {p : FrequencyPolynomial}
    (hp : FrequencyBand r p) : FrequencyBand t p := by
  intro k hk
  have h := hp k hk
  constructor <;> omega

theorem frequencyBand_add {r : ℕ} {p q : FrequencyPolynomial}
    (hp : FrequencyBand r p) (hq : FrequencyBand r q) : FrequencyBand r (p + q) := by
  intro k hk
  rcases Finset.mem_union.mp (Finsupp.support_add hk) with hk | hk
  · exact hp k hk
  · exact hq k hk

theorem frequencyBand_mul {r t : ℕ} {p q : FrequencyPolynomial}
    (hp : FrequencyBand r p) (hq : FrequencyBand t q) : FrequencyBand (r + t) (p * q) := by
  intro k hk
  rcases Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset p q hk) with ⟨i, hi, j, hj, rfl⟩
  have hpi := hp i hi
  have hqj := hq j hj
  constructor <;> push_cast <;> omega

theorem frequencyBand_one : FrequencyBand 0 (1 : FrequencyPolynomial) := by
  change FrequencyBand 0 (AddMonoidAlgebra.single 0 1)
  exact frequencyBand_single 0 1 (by norm_num)

theorem frequencyBand_pow {r : ℕ} {p : FrequencyPolynomial} (hp : FrequencyBand r p)
    (n : ℕ) : FrequencyBand (r * n) (p ^ n) := by
  induction n with
  | zero => simpa using frequencyBand_one
  | succ n ih => simpa only [pow_succ, Nat.mul_succ] using frequencyBand_mul ih hp

theorem frequencyBand_finset_sum {ι : Type*} (s : Finset ι) (p : ι → FrequencyPolynomial)
    (r : ℕ) (hp : ∀ i ∈ s, FrequencyBand r (p i)) : FrequencyBand r (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using frequencyBand_zero r
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact frequencyBand_add (hp i (by simp)) (ih (fun j hj => hp j (by simp [hj])))

theorem frequencyBand_finset_prod {ι : Type*} (s : Finset ι) (p : ι → FrequencyPolynomial)
    (r : ι → ℕ) (hp : ∀ i ∈ s, FrequencyBand (r i) (p i)) :
    FrequencyBand (∑ i ∈ s, r i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using frequencyBand_one
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      exact frequencyBand_mul (hp i (by simp)) (ih (fun j hj => hp j (by simp [hj])))

/-- Substitution of bandwidth-one expressions into a polynomial has bandwidth
at most its actual total degree. The statement is uniform in the variable type. -/
theorem frequencyBand_eval₂
    {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R)
    (c : R →+* FrequencyPolynomial) (v : σ → FrequencyPolynomial)
    (hc : ∀ a : R, FrequencyBand 0 (c a))
    (hv : ∀ i : σ, FrequencyBand 1 (v i)) :
    FrequencyBand p.totalDegree (p.eval₂ c v) := by
  classical
  have heval : p.eval₂ c v = ∑ d ∈ p.support,
      c (p.coeff d) * d.prod (fun i e => v i ^ e) := by
    conv_lhs => rw [p.as_sum]
    simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial]
  rw [heval]
  apply frequencyBand_finset_sum
  intro d hd
  have hprod : FrequencyBand (d.sum (fun _ e => e)) (d.prod (fun i e => v i ^ e)) := by
    simpa only [Finsupp.sum, Finsupp.prod, one_mul] using
      frequencyBand_finset_prod d.support (fun i => v i ^ d i) (fun i => d i)
        (fun i _ => by simpa only [one_mul] using frequencyBand_pow (hv i) (d i))
  have hmon := frequencyBand_mul (hc (p.coeff d)) hprod
  exact frequencyBand_mono (MvPolynomial.le_totalDegree hd) (by simpa using hmon)

def sinFrequency : FrequencyPolynomial :=
  AddMonoidAlgebra.single (-1) (Complex.I / 2) + AddMonoidAlgebra.single 1 (-Complex.I / 2)

def cosFrequency : FrequencyPolynomial :=
  AddMonoidAlgebra.single 1 (1 / 2) + AddMonoidAlgebra.single (-1) (1 / 2)

theorem frequencyBand_sin : FrequencyBand 1 sinFrequency := by
  apply frequencyBand_add
  · exact frequencyBand_single (-1) _ (by norm_num)
  · exact frequencyBand_single 1 _ (by norm_num)

theorem frequencyBand_cos : FrequencyBand 1 cosFrequency := by
  apply frequencyBand_add
  · exact frequencyBand_single 1 _ (by norm_num)
  · exact frequencyBand_single (-1) _ (by norm_num)

@[simp]
theorem evalFrequency_sin (z : ℂ) : evalFrequency z sinFrequency = Complex.sin z := by
  simp only [sinFrequency, map_add, evalFrequency_single, Int.cast_neg, Int.cast_one,
    neg_one_mul, one_mul, Complex.sin]
  ring

@[simp]
theorem evalFrequency_cos (z : ℂ) : evalFrequency z cosFrequency = Complex.cos z := by
  simp only [cosFrequency, map_add, evalFrequency_single, Int.cast_neg, Int.cast_one,
    neg_one_mul, one_mul, Complex.cos]
  ring

def angularCoefficientHom : ℝ →+* FrequencyPolynomial :=
  AddMonoidAlgebra.singleZeroRingHom.comp Complex.ofRealHom

def angularFrequencyVariable {σ : Type*} (y : σ → ℝ) : Option σ → FrequencyPolynomial
  | none => cosFrequency
  | some i => angularCoefficientHom (y i) * sinFrequency

/-- `none` is the padding coordinate; `some i` is the original coordinate. -/
def angularCoordinate {σ : Type*} (y : σ → ℝ) (z : ℂ) : Option σ → ℂ
  | none => Complex.cos z
  | some i => Complex.sin z * (y i : ℂ)

def angularFrequencyPolynomial {σ : Type*} (p : MvPolynomial (Option σ) ℝ) (y : σ → ℝ) :
    FrequencyPolynomial := p.eval₂ angularCoefficientHom (angularFrequencyVariable y)

theorem frequencyBand_angularCoefficient (a : ℝ) :
    FrequencyBand 0 (angularCoefficientHom a) := by
  change FrequencyBand 0 (AddMonoidAlgebra.single 0 (a : ℂ))
  exact frequencyBand_single 0 _ (by norm_num)

theorem frequencyBand_angularVariable {σ : Type*} (y : σ → ℝ) (i : Option σ) :
    FrequencyBand 1 (angularFrequencyVariable y i) := by
  cases i with
  | none => exact frequencyBand_cos
  | some i =>
      exact frequencyBand_mul (frequencyBand_angularCoefficient (y i)) frequencyBand_sin

theorem frequencyBand_angularPolynomial {σ : Type*} (p : MvPolynomial (Option σ) ℝ)
    (y : σ → ℝ) : FrequencyBand p.totalDegree (angularFrequencyPolynomial p y) :=
  frequencyBand_eval₂ p angularCoefficientHom (angularFrequencyVariable y)
    frequencyBand_angularCoefficient (frequencyBand_angularVariable y)

@[simp]
theorem evalFrequency_angularCoefficient (a : ℝ) (z : ℂ) :
    evalFrequency z (angularCoefficientHom a) = (a : ℂ) := by
  change evalFrequency z (AddMonoidAlgebra.single 0 (a : ℂ)) = (a : ℂ)
  simp

@[simp]
theorem evalFrequency_angularVariable {σ : Type*} (y : σ → ℝ) (z : ℂ) (i : Option σ) :
    evalFrequency z (angularFrequencyVariable y i) = angularCoordinate y z i := by
  cases i with
  | none => exact evalFrequency_cos z
  | some i => simp [angularFrequencyVariable, angularCoordinate, mul_comm]

theorem evalFrequency_angularPolynomial {σ : Type*} (p : MvPolynomial (Option σ) ℝ)
    (y : σ → ℝ) (z : ℂ) :
    evalFrequency z (angularFrequencyPolynomial p y) =
      p.eval₂ Complex.ofRealHom (angularCoordinate y z) := by
  change (evalFrequency z).toRingHom
    (p.eval₂ angularCoefficientHom (angularFrequencyVariable y)) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hcoeff : (evalFrequency z).toRingHom.comp angularCoefficientHom = Complex.ofRealHom := by
    ext a
    change evalFrequency z (AddMonoidAlgebra.single 0 (a : ℂ)) = (a : ℂ)
    simp
  rw [hcoeff]
  apply congrArg (fun v : Option σ → ℂ => p.eval₂ Complex.ofRealHom v)
  funext i
  exact evalFrequency_angularVariable y z i

/-- Complete scalar frequency conversion for a real polynomial in the original
coordinates and one padding coordinate. No norm condition on `y` is needed. -/
theorem angular_polynomial_frequency_representation
    {σ : Type*} (p : MvPolynomial (Option σ) ℝ) (y : σ → ℝ) (r : ℕ)
    (hdegree : p.totalDegree ≤ r) :
    ∃ c : FrequencyPolynomial, FrequencyBand r c ∧ ∀ z : ℂ,
      p.eval₂ Complex.ofRealHom (angularCoordinate y z) =
        ∑ k ∈ c.coeff.support, Complex.exp ((k : ℂ) * z * Complex.I) * c.coeff k := by
  refine ⟨angularFrequencyPolynomial p y,
    frequencyBand_mono hdegree (frequencyBand_angularPolynomial p y), ?_⟩
  intro z
  rw [← evalFrequency_angularPolynomial p y z]
  exact evalFrequency_eq_sum z _

/-- A common integer interval may be used in place of the individual support. -/
theorem evalFrequency_eq_sum_Icc {r : ℕ} {p : FrequencyPolynomial}
    (hp : FrequencyBand r p) (z : ℂ) :
    evalFrequency z p =
      ∑ k ∈ Finset.Icc (-(r : ℤ)) (r : ℤ), Complex.exp ((k : ℂ) * z * Complex.I) * p.coeff k := by
  classical
  rw [evalFrequency_eq_sum]
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_Icc.2 (hp k hk)
  · intro k hk hnot
    have hzero : p.coeff k = 0 := Finsupp.notMem_support_iff.1 hnot
    simp only [hzero, mul_zero]

def angularVector {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (y : σ → ℝ) (z : ℂ) : EuclideanSpace ℂ J :=
  (WithLp.equiv 2 (J → ℂ)).symm
    (fun j => (p j).eval₂ Complex.ofRealHom (angularCoordinate y z))

def angularFrequencyVector {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (y : σ → ℝ) (k : ℤ) : EuclideanSpace ℂ J :=
  (WithLp.equiv 2 (J → ℂ)).symm (fun j => (angularFrequencyPolynomial (p j) y).coeff k)

@[simp]
theorem angularVector_apply {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (y : σ → ℝ) (z : ℂ) (j : J) :
    angularVector p y z j = (p j).eval₂ Complex.ofRealHom (angularCoordinate y z) := rfl

@[simp]
theorem angularFrequencyVector_apply {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial (Option σ) ℝ) (y : σ → ℝ) (k : ℤ) (j : J) :
    angularFrequencyVector p y k j = (angularFrequencyPolynomial (p j) y).coeff k := rfl

/-- All squares in a finite certificate have a simultaneous frequency
representation in the Euclidean codomain. The index type may be empty. -/
theorem angularVector_frequency_representation
    {σ J : Type*} [Fintype J] (p : J → MvPolynomial (Option σ) ℝ)
    (y : σ → ℝ) (r : ℕ) (hdegree : ∀ j : J, (p j).totalDegree ≤ r) (z : ℂ) :
    angularVector p y z =
      ∑ k ∈ Finset.Icc (-(r : ℤ)) (r : ℤ),
        Complex.exp ((k : ℂ) * z * Complex.I) • angularFrequencyVector p y k := by
  apply PiLp.ext
  intro j
  rw [angularVector_apply]
  change (p j).eval₂ Complex.ofRealHom (angularCoordinate y z) =
    (PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : J => ℂ) j)
      (∑ k ∈ Finset.Icc (-(r : ℤ)) (r : ℤ),
        Complex.exp ((k : ℂ) * z * Complex.I) • angularFrequencyVector p y k)
  simp only [map_sum, map_smul, PiLp.proj_apply, angularFrequencyVector_apply, smul_eq_mul]
  rw [← evalFrequency_angularPolynomial (p j) y z]
  exact evalFrequency_eq_sum_Icc
    (frequencyBand_mono (hdegree j) (frequencyBand_angularPolynomial (p j) y)) z

/-- The exact weighted complex estimate for the angular restriction of a
finite polynomial certificate. The result uses the Euclidean norm and its
constant is independent of the number of certificate squares. -/
theorem angularVector_weighted_complex_bound
    {σ J : Type*} [Fintype J] (p : J → MvPolynomial (Option σ) ℝ)
    (y : σ → ℝ) {r : ℕ} (hr : 0 < r)
    (hdegree : ∀ j : J, (p j).totalDegree ≤ r) {a : ℝ}
    (hreal : ∀ t : ℝ, ‖angularVector p y (t : ℂ)‖ ≤ a + t ^ 2) (z : ℂ) :
    ‖angularVector p y z‖ ≤ (a + (r : ℝ)⁻¹ ^ 2) *
      (1 + (r : ℝ) * ‖z‖) ^ 2 * Real.exp ((r : ℝ) * |z.im|) := by
  have hrepr (w : ℂ) : angularVector p y w =
      ∑ k ∈ Finset.Icc (-(r : ℤ)) (r : ℤ),
        Complex.exp (((k : ℝ) : ℂ) * w * Complex.I) • angularFrequencyVector p y k := by
    simpa only [Complex.ofReal_intCast] using angularVector_frequency_representation p y r hdegree w
  have hfreq : ∀ k ∈ Finset.Icc (-(r : ℤ)) (r : ℤ),
      -(r : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ (r : ℝ) := by
    intro k hk
    exact_mod_cast Finset.mem_Icc.1 hk
  have hreal' : ∀ t : ℝ,
      ‖∑ k ∈ Finset.Icc (-(r : ℤ)) (r : ℤ),
        Complex.exp (((k : ℝ) : ℂ) * (t : ℂ) * Complex.I) • angularFrequencyVector p y k‖ ≤
          a + t ^ 2 := by
    intro t
    rw [← hrepr (t : ℂ)]
    exact hreal t
  have hbound := weighted_complex_bound_of_finite_frequencies
    (Finset.Icc (-(r : ℤ)) (r : ℤ)) (fun k : ℤ => (k : ℝ)) (angularFrequencyVector p y)
    (show (0 : ℝ) < (r : ℝ) by exact_mod_cast hr) hfreq hreal' z
  rw [← hrepr z] at hbound
  exact hbound

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
