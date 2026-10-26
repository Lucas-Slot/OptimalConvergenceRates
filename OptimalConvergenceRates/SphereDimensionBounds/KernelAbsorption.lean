import OptimalConvergenceRates.SphereDimensionBounds.ChebyshevSOSKernel
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.CertificateScaling
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.ExplicitFeasibility
import Mathlib.Algebra.Ring.GeomSum

/-! Exact absorption of a radial local multiplier by a polynomial kernel.
The local bounded SOS is an explicit hypothesis; no kernel moment bound or
existence of local certificates is asserted in this algebraic component. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.KernelAbsorption

open scoped BigOperators
open MvPolynomial OptimalConvergenceRates.SphereDimensionBounds.Foundation ChebyshevSOSKernel

abbrev P (n : ℕ) := OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n

def radialProxy {n : ℕ} (t : P n) : P n := 2*(1-t)
def kernelNumerator {n : ℕ} (t chi : P n) (m : ℕ) : P n := (1-t^2)^m*chi
def remainderRoot {n : ℕ} (t chi : P n) (m : ℕ) : P n :=
  C ((1/2:ℝ)^m)*(1+t)^m*chi

theorem kernel_absorption_identity {n : ℕ} (t chi : P n) (m : ℕ) :
    kernelNumerator t chi m^2=(radialProxy t)^(2*m)*remainderRoot t chi m^2 := by
  have hbase : (1-t^2)=radialProxy t*(C (1/2:ℝ)*(1+t)) := by
    have htwo : (2:P n)*C (1/2:ℝ)=1 := by
      change C (2:ℝ)*C (1/2:ℝ)=1
      rw [←map_mul]
      norm_num
    unfold radialProxy
    calc
      1-t^2=((2:P n)*C (1/2:ℝ))*(1-t)*(1+t) := by rw [htwo]; ring
      _=_ := by ring
  have hb : remainderRoot t chi m=(C (1/2:ℝ)*(1+t))^m*chi := by
    simp only [remainderRoot,mul_pow,←map_pow]
  rw [kernelNumerator,hbase,mul_pow,hb,mul_pow,mul_pow]
  rw [←pow_mul,←pow_mul]
  rw [show m*2=2*m by omega]
  ring

theorem radialProxy_degree {n : ℕ} (t : P n) (ht : t.totalDegree ≤ 1) :
    (radialProxy t).totalDegree≤1 := by
  apply (totalDegree_mul _ _).trans
  change (C (2:ℝ) : P n).totalDegree+(1-t).totalDegree≤1
  simp only [totalDegree_C,zero_add]
  exact (totalDegree_sub _ _).trans (max_le (by simp) ht)

theorem remainderRoot_degree {n ell : ℕ} (t chi : P n) (ht : t.totalDegree ≤ 1)
    (hchi : chi.totalDegree ≤ ell - 2) (m : ℕ) :
    (remainderRoot t chi m).totalDegree≤ m+(ell-2) := by
  have hplus : (1+t).totalDegree≤1 := (totalDegree_add _ _).trans (max_le (by simp) ht)
  have hpow : ((1+t)^m).totalDegree≤ m :=
    (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left m hplus)
  unfold remainderRoot
  apply (totalDegree_mul _ _).trans
  have hfirst : (C ((1/2:ℝ)^m)*(1+t)^m).totalDegree≤ m :=
    (totalDegree_mul _ _).trans (by simpa using hpow)
  exact Nat.add_le_add hfirst hchi

/-- The complete physical root budget includes all three copies of m. -/
theorem absorption_root_budget (m ell : ℕ) (hell : 2 ≤ ell) :
    (2*m+2)+(m+(ell-2))=3*m+ell := by omega

theorem boundedSOS_absorbed {n ell : ℕ} (t chi localRadius p : P n)
    (ht : t.totalDegree ≤ 1) (hchi : chi.totalDegree ≤ ell - 2) (hell : 2 ≤ ell) (m : ℕ)
    (hlocal : BoundedSOS (2 * m + 2) (localRadius ^ (2 * m) * p)) :
    BoundedSOS (3*m+ell) ((localRadius^(2*m)*p)*remainderRoot t chi m^2) := by
  have hs := BoundedSOS.square (remainderRoot t chi m) (remainderRoot_degree t chi ht hchi m)
  simpa only [absorption_root_budget m ell hell] using hlocal.mul hs

def dotPole {n : ℕ} (y : Fin n → ℝ) : P n := ∑ i,C (y i)*X i
def chordPole {n : ℕ} (y : Fin n → ℝ) : P n := ∑ i,(X i-C (y i))^2

theorem dotPole_degree {n : ℕ} (y : Fin n → ℝ) : (dotPole y).totalDegree≤1 := by
  apply totalDegree_finsetSum_le
  intro i hi
  exact (totalDegree_mul _ _).trans (by simp)

theorem chordPole_degree {n : ℕ} (y : Fin n → ℝ) : (chordPole y).totalDegree≤2 := by
  apply totalDegree_finsetSum_le
  intro i hi
  apply (totalDegree_pow _ _).trans
  have h : (X i-C (y i) : P n).totalDegree≤1 :=
    (totalDegree_sub _ _).trans (by simp)
  exact (Nat.mul_le_mul_left 2 h).trans (by omega)

theorem unit_pole_chord_identity {n : ℕ} (y : Fin n → ℝ) (hy : ∑ i, y i ^ 2 = 1) :
    chordPole y=radialProxy (dotPole y)-(1-radiusPolynomial n) := by
  classical
  have hexpand : chordPole y=radiusPolynomial n+C (∑ i,y i^2)-2*dotPole y := by
    unfold chordPole radiusPolynomial dotPole
    calc
      (∑ i,(X i-C (y i))^2)=
          ∑ i,((X i)^2+(C (y i))^2-2*(C (y i)*X i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _=_ := by
        simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,
          ←map_pow,←map_sum]
  rw [hexpand,hy]
  simp only [map_one,radialProxy]
  ring

def powerDifferenceSum {n : ℕ} (a b : P n) (k : ℕ) : P n :=
  ∑ i ∈ Finset.range k,a^i*b^(k-1-i)

theorem powerDifferenceSum_identity {n : ℕ} (a b : P n) (k : ℕ) :
    (a-b)*powerDifferenceSum a b k=a^k-b^k := by
  exact (Commute.all a b).mul_geom_sum₂ k

theorem powerDifferenceSum_degree {n : ℕ} (a b : P n)
    (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (k : ℕ) :
    (powerDifferenceSum a b k).totalDegree≤2*k-2 := by
  apply totalDegree_finsetSum_le
  intro i hi
  have hik : i<k := Finset.mem_range.mp hi
  apply (totalDegree_mul _ _).trans
  have h1 := (totalDegree_pow a i).trans (Nat.mul_le_mul_left i ha)
  have h2 := (totalDegree_pow b (k-1-i)).trans (Nat.mul_le_mul_left (k-1-i) hb)
  omega

def absorptionMultiplier {n : ℕ} (y : Fin n → ℝ) (chi p : P n) (m : ℕ) : P n :=
  powerDifferenceSum (radialProxy (dotPole y)) (chordPole y) (2*m)*
    remainderRoot (dotPole y) chi m^2*p

/-- The sphere equality is accounted for by an explicit polynomial, with no
appeal to an unbounded ideal-divisibility theorem. -/
theorem absorbed_sphere_identity {n : ℕ} (y : Fin n → ℝ) (hy : ∑ i, y i ^ 2 = 1)
    (chi p : P n) (m : ℕ) :
    kernelNumerator (dotPole y) chi m^2*p=
      (chordPole y^(2*m)*p)*remainderRoot (dotPole y) chi m^2+
        (1-radiusPolynomial n)*absorptionMultiplier y chi p m := by
  rw [kernel_absorption_identity]
  have hchord := unit_pole_chord_identity y hy
  have hdiff : radialProxy (dotPole y)-chordPole y=1-radiusPolynomial n := by
    rw [hchord]
    ring
  have hsum := powerDifferenceSum_identity (radialProxy (dotPole y)) (chordPole y) (2*m)
  rw [hdiff] at hsum
  unfold absorptionMultiplier
  linear_combination -(remainderRoot (dotPole y) chi m^2*p)*hsum

theorem absorptionMultiplier_degree {n ell : ℕ} (y : Fin n → ℝ) (chi p : P n)
    (hchi : chi.totalDegree ≤ ell - 2) (hp : p.totalDegree ≤ 4) (hell : 2 ≤ ell) (m : ℕ) :
    (absorptionMultiplier y chi p m).totalDegree≤2*(3*m+ell)-2 := by
  by_cases hm : m=0
  · simp [hm,absorptionMultiplier,powerDifferenceSum]
  · have hmpos : 1≤ m := by omega
    have hsum := powerDifferenceSum_degree (radialProxy (dotPole y)) (chordPole y)
      ((radialProxy_degree _ (dotPole_degree y)).trans (by omega)) (chordPole_degree y) (2*m)
    have hb := remainderRoot_degree (dotPole y) chi (dotPole_degree y) hchi m
    have hb2 := (totalDegree_pow (remainderRoot (dotPole y) chi m) 2).trans
      (Nat.mul_le_mul_left 2 hb)
    unfold absorptionMultiplier
    apply (totalDegree_mul _ _).trans
    have hmul := (totalDegree_mul
      (powerDifferenceSum (radialProxy (dotPole y)) (chordPole y) (2*m))
      (remainderRoot (dotPole y) chi m^2)).trans (Nat.add_le_add hsum hb2)
    omega

/-- Actual original-sphere feasibility at root degree 3m+ell, conditional
only on the supplied local bounded-SOS certificate and polynomial budgets. -/
theorem kernel_absorption_feasible {n ell : ℕ} (y : Fin n → ℝ)
    (hy : ∑ i, y i ^ 2 = 1) (chi p : P n) (hchi : chi.totalDegree ≤ ell - 2)
    (hp : p.totalDegree ≤ 4) (hell : 2 ≤ ell) (m : ℕ)
    (hlocal : BoundedSOS (2 * m + 2) (chordPole y ^ (2 * m) * p)) :
    Feasible (3*m+ell) (kernelNumerator (dotPole y) chi m^2*p) 0 := by
  obtain ⟨a,h,hh,hid⟩ := boundedSOS_absorbed (dotPole y) chi (chordPole y) p
    (dotPole_degree y) hchi hell m hlocal
  refine ⟨a,h,absorptionMultiplier y chi p m,hh,
    absorptionMultiplier_degree y chi p hchi hp hell m,?_⟩
  simpa only [map_zero,sub_zero,hid] using absorbed_sphere_identity y hy chi p m

/-- Kernel normalization is a nonnegative scalar and preserves the same
original relaxation order. Its moment estimate is a separate obligation. -/
theorem normalized_kernel_absorption_feasible {n ell : ℕ} (y : Fin n → ℝ)
    (hy : ∑ i, y i ^ 2 = 1) (chi p : P n) (hchi : chi.totalDegree ≤ ell - 2)
    (hp : p.totalDegree ≤ 4) (hell : 2 ≤ ell) (m : ℕ)
    (hlocal : BoundedSOS (2 * m + 2) (chordPole y ^ (2 * m) * p))
    (Z : ℝ) (hZ : 0 < Z) :
    Feasible (3*m+ell) (C Z⁻¹*(kernelNumerator (dotPole y) chi m^2*p)) 0 := by
  simpa only [mul_zero] using
    (kernel_absorption_feasible y hy chi p hchi hp hell m hlocal).scale (inv_nonneg.mpr hZ.le)

end OptimalConvergenceRates.SphereDimensionBounds.KernelAbsorption
