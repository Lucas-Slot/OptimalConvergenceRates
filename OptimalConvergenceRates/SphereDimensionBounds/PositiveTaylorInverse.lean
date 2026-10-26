import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-! The finite-dimensional inverse step for the linear Taylor operator.
No preservation-of-constants hypothesis is used. The concrete operator,
its kernel estimates and its SOS image must be supplied separately. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.PositiveTaylorInverse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem near_identity_injective (A : V →ₗ[ℝ] V) {t : ℝ} (ht : t < 1)
    (hnear : ∀ v, ‖v - A v‖ ≤ t * ‖v‖) : Function.Injective A := by
  intro x y hxy
  by_contra hne
  have hzero : A (x-y)=0 := by rw [map_sub,hxy,sub_self]
  have hb := hnear (x-y)
  rw [hzero,sub_zero] at hb
  have hp : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hs : t*‖x-y‖ < ‖x-y‖ := by nlinarith
  exact (not_lt_of_ge hb) hs

theorem positive_preimage [FiniteDimensional ℝ V] {Ω : Type*}
    (E : V →ₗ[ℝ] (Ω → ℝ)) (e : V)
    (he : ∀ x, E e x = 1) (hen : ‖e‖ ≤ 1)
    (heval : ∀ v x, |E v x| ≤ ‖v‖)
    (A : V →ₗ[ℝ] V) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4)
    (hnear : ∀ v, ‖v - A v‖ ≤ t*‖v‖)
    (F : V) (hFn : ‖F‖ ≤ 1) (hF : ∀ x, 0 ≤ E F x) :
    ∃ H, A H=F+(2*t) • e ∧ ‖H‖≤2 ∧ ∀ x, 0≤E H x := by
  have ht1 : t<1 := by linarith
  have honto : Function.Surjective A :=
    LinearMap.surjective_of_injective (near_identity_injective A ht1 hnear)
  obtain ⟨H,hH⟩ := honto (F+(2*t) • e)
  have htarget : ‖F+(2*t) • e‖≤1+2*t := by
    calc
      ‖F+(2*t) • e‖≤‖F‖+‖(2*t) • e‖ := norm_add_le _ _
      _ = ‖F‖+(2*t)*‖e‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      _ ≤ 1+(2*t)*1 := add_le_add hFn (mul_le_mul_of_nonneg_left hen (by positivity))
      _ = 1+2*t := by ring
  have hsum : ‖H‖≤t*‖H‖+(1+2*t) := by
    calc
      ‖H‖=‖(H-A H)+A H‖ := by congr 1; abel
      _ ≤ ‖H-A H‖+‖A H‖ := norm_add_le _ _
      _ ≤ t*‖H‖+(1+2*t) := add_le_add (hnear H) (by rw [hH]; exact htarget)
  have htn := mul_le_mul_of_nonneg_right ht (norm_nonneg H)
  have hHn : ‖H‖≤2 := by nlinarith
  have herr : ‖H-(F+(2*t) • e)‖≤2*t := by
    rw [←hH]
    exact (hnear H).trans (by nlinarith)
  refine ⟨H,hH,hHn,?_⟩
  intro x
  have hval := (abs_le.mp ((heval (H-(F+(2*t) • e)) x).trans herr)).1
  simp only [map_sub,map_add,map_smul,Pi.sub_apply,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul,he,mul_one] at hval
  linarith [hF x]

/-- Algebraic repair of the Taylor image. This conditional component is
independent of a concrete polynomial kernel or SOS construction. -/
theorem certificate_of_positive_images [FiniteDimensional ℝ V] {Ω : Type*}
    (E : V →ₗ[ℝ] (Ω → ℝ)) (e : V)
    (he : ∀ x, E e x = 1) (hen : ‖e‖ ≤ 1) (heval : ∀ v x, |E v x| ≤ ‖v‖)
    (K : Set V) (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hconst : ∀ c:ℝ, 0≤c → c • e∈K)
    (A : V →ₗ[ℝ] V) {t q : ℝ} (ht0 : 0≤t) (ht : t≤1/4) (hq : 0≤q)
    (hnear : ∀ v, ‖v-A v‖≤t*‖v‖)
    (himage : ∀ v, (∀ x, 0≤E v x) → A v+(q*‖v‖) • e∈K)
    (F : V) (hFn : ‖F‖≤1) (hF : ∀ x, 0≤E F x) :
    F+(2*(t+q)) • e∈K := by
  obtain ⟨H,hH,hHn,hpos⟩ := positive_preimage E e he hen heval A ht0 ht hnear F hFn hF
  have hres : 0≤q*(2-‖H‖) := mul_nonneg hq (sub_nonneg.mpr hHn)
  have hs := hadd _ (himage H hpos) _ (hconst _ hres)
  rw [hH] at hs
  convert hs using 1; module

end OptimalConvergenceRates.SphereDimensionBounds.PositiveTaylorInverse
