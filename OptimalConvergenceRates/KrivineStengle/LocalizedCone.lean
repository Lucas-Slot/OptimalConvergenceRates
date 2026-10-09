/-
  OptimalConvergenceRates/KrivineStengle/LocalizedCone.lean

  The division-free cone in the localization away from the polynomial being certified.
-/
import OptimalConvergenceRates.KrivineStengle.Preordering
import OptimalConvergenceRates.KrivineStengle.SquareCone
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.Ring

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

variable {B : Type*} [CommRing B]

/-- The localization cone attached to a square cone `T` and an element `p`.

The equation is written after clearing an even power of the localization denominator. -/
def localizationCone (T : Set B) (p : B) : Set (Localization.Away p) :=
  {b | ∃ N : ℕ, ∃ U ∈ T, ∃ V ∈ T,
    (algebraMap B (Localization.Away p) p) ^ (2 * N) * b =
      algebraMap B (Localization.Away p) (U - p * V)}

theorem localizationCone_map_mem {T : Set B} (hT : IsSquareCone T) (p : B)
    {q : B} (hq : q ∈ T) :
    algebraMap B (Localization.Away p) q ∈ localizationCone T p := by
  refine ⟨0, q, hq, 0, hT.zero_mem, ?_⟩
  simp

theorem localizationCone_neg_algebraMap_self {T : Set B} (hT : IsSquareCone T) (p : B) :
    -(algebraMap B (Localization.Away p) p) ∈ localizationCone T p := by
  refine ⟨0, 0, hT.zero_mem, 1, hT.one_mem, ?_⟩
  simp

private theorem even_power_mem {T : Set B} (hT : IsSquareCone T) (p : B) (N : ℕ) :
    p ^ (2 * N) ∈ T := by
  have h := hT.sq_mem (p ^ N)
  simpa [pow_two, ← pow_add, two_mul] using h

/-- The localization cone is a possibly improper square cone. -/
theorem localizationCone_isSquareCone (T : Set B) (hT : IsSquareCone T) (p : B) :
    IsSquareCone (localizationCone T p) := by
  let P : Localization.Away p := algebraMap B (Localization.Away p) p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨0, 0, hT.zero_mem, 0, hT.zero_mem, ?_⟩
    simp
  · refine ⟨0, 1, hT.one_mem, 0, hT.zero_mem, ?_⟩
    simp
  · rintro x y ⟨N, U, hU, V, hV, hx⟩ ⟨M, U', hU', V', hV', hy⟩
    let U'' := p ^ (2 * M) * U + p ^ (2 * N) * U'
    let V'' := p ^ (2 * M) * V + p ^ (2 * N) * V'
    have hU'' : U'' ∈ T := hT.add_mem
      (hT.mul_mem (even_power_mem hT p M) hU)
      (hT.mul_mem (even_power_mem hT p N) hU')
    have hV'' : V'' ∈ T := hT.add_mem
      (hT.mul_mem (even_power_mem hT p M) hV)
      (hT.mul_mem (even_power_mem hT p N) hV')
    refine ⟨N + M, U'', hU'', V'', hV'', ?_⟩
    change P ^ (2 * (N + M)) * (x + y) = _
    have hexp : 2 * (N + M) = 2 * N + 2 * M := by omega
    rw [hexp, pow_add]
    calc
      (P ^ (2 * N) * P ^ (2 * M)) * (x + y) =
          P ^ (2 * M) * (P ^ (2 * N) * x) +
            P ^ (2 * N) * (P ^ (2 * M) * y) := by ring
      _ = P ^ (2 * M) * algebraMap B (Localization.Away p) (U - p * V) +
            P ^ (2 * N) * algebraMap B (Localization.Away p) (U' - p * V') := by
              rw [hx, hy]
      _ = algebraMap B (Localization.Away p) (U'' - p * V'') := by
        simp only [U'', V'', map_add, map_sub, map_mul, map_pow]
        ring
  · rintro x y ⟨N, U, hU, V, hV, hx⟩ ⟨M, U', hU', V', hV', hy⟩
    let U'' := U * U' + p ^ 2 * (V * V')
    let V'' := U * V' + V * U'
    have hU'' : U'' ∈ T := hT.add_mem (hT.mul_mem hU hU')
      (hT.mul_mem (hT.sq_mem p) (hT.mul_mem hV hV'))
    have hV'' : V'' ∈ T := hT.add_mem (hT.mul_mem hU hV') (hT.mul_mem hV hU')
    refine ⟨N + M, U'', hU'', V'', hV'', ?_⟩
    change P ^ (2 * (N + M)) * (x * y) = _
    have hexp : 2 * (N + M) = 2 * N + 2 * M := by omega
    rw [hexp, pow_add]
    calc
      (P ^ (2 * N) * P ^ (2 * M)) * (x * y) =
          (P ^ (2 * N) * x) * (P ^ (2 * M) * y) := by ring
      _ = algebraMap B (Localization.Away p) (U - p * V) *
            algebraMap B (Localization.Away p) (U' - p * V') := by rw [hx, hy]
      _ = algebraMap B (Localization.Away p) (U'' - p * V'') := by
        simp only [U'', V'', map_add, map_sub, map_mul, map_pow]
        ring
  · intro x
    obtain ⟨N, a, ha⟩ := IsLocalization.Away.surj p x
    refine ⟨N, a ^ 2, hT.sq_mem a, 0, hT.zero_mem, ?_⟩
    change P ^ (2 * N) * x ^ 2 = _
    have hexp : 2 * N = N + N := by omega
    rw [hexp, pow_add]
    calc
      (P ^ N * P ^ N) * x ^ 2 = (x * P ^ N) ^ 2 := by ring
      _ = (algebraMap B (Localization.Away p) a) ^ 2 := by rw [ha]
      _ = algebraMap B (Localization.Away p) (a ^ 2 - p * 0) := by simp

variable [IsDomain B]

/-- Impropriety of the localization cone clears denominators to the normalized
Krivine--Stengle identity, with a positive exponent. -/
theorem localizationCone_extract {T : Set B} (hT : IsSquareCone T) {p : B} (hp : p ≠ 0)
    (himproper : (-1 : Localization.Away p) ∈ localizationCone T p) :
    ∃ (k : ℕ), 1 ≤ k ∧ ∃ S ∈ T, ∃ U ∈ T, p * S = p ^ (2 * k) + U := by
  obtain ⟨N, U, hU, V, hV, hneg⟩ := himproper
  have hinj : Function.Injective (algebraMap B (Localization.Away p)) :=
    IsLocalization.injective (Localization.Away p)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hp)
  have hbase : -(p ^ (2 * N)) = U - p * V := by
    apply hinj
    simpa [map_pow] using hneg
  have hpV : p * V = p ^ (2 * N) + U := by
    calc
      p * V = U - (-(p ^ (2 * N))) := by rw [hbase]; ring
      _ = p ^ (2 * N) + U := by ring
  refine ⟨N + 1, by omega, p ^ 2 * V, hT.mul_mem (hT.sq_mem p) hV,
    p ^ 2 * U, hT.mul_mem (hT.sq_mem p) hU, ?_⟩
  calc
    p * (p ^ 2 * V) = p ^ 2 * (p * V) := by ring
    _ = p ^ 2 * (p ^ (2 * N) + U) := by rw [hpV]
    _ = p ^ (2 * (N + 1)) + p ^ 2 * U := by
      rw [show 2 * (N + 1) = 2 * N + 2 by omega, pow_add]
      ring

open MvPolynomial

variable {n m : ℕ}

/-- The repository preordering, regarded as a possibly improper square cone. -/
theorem preorderingMem_isSquareCone (g : Fin m → MvPolynomial (Fin n) ℝ) :
    IsSquareCone {q | PreorderingMem g q} where
  zero_mem := preorderingMem_zero g
  one_mem := preorderingMem_one g
  add_mem := preorderingMem_add
  mul_mem := preorderingMem_mul
  sq_mem := preorderingMem_sq g

/-- The localization cone used for the polynomial certificate theorem. -/
def localizedCertificateCone (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) : Set (Localization.Away p) :=
  localizationCone {q | PreorderingMem g q} p

theorem localizedCertificateCone_isSquareCone
    (g : Fin m → MvPolynomial (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ) :
    IsSquareCone (localizedCertificateCone g p) :=
  localizationCone_isSquareCone _ (preorderingMem_isSquareCone g) p

theorem localizedCertificateCone_generator
    (g : Fin m → MvPolynomial (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ) (i : Fin m) :
    algebraMap _ (Localization.Away p) (g i) ∈ localizedCertificateCone g p :=
  localizationCone_map_mem (preorderingMem_isSquareCone g) p (preorderingMem_generator g i)

theorem localizedCertificateCone_neg_self
    (g : Fin m → MvPolynomial (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ) :
    -(algebraMap _ (Localization.Away p) p) ∈ localizedCertificateCone g p :=
  localizationCone_neg_algebraMap_self (preorderingMem_isSquareCone g) p

/-- Polynomial specialization of denominator extraction. -/
theorem localizedCertificateCone_extract
    {g : Fin m → MvPolynomial (Fin n) ℝ} {p : MvPolynomial (Fin n) ℝ} (hp : p ≠ 0)
    (himproper : (-1 : Localization.Away p) ∈ localizedCertificateCone g p) :
    Nonempty (KSWitness g p) := by
  obtain ⟨k, hk, S, hS, T, hT, hid⟩ :=
    localizationCone_extract (preorderingMem_isSquareCone g) hp himproper
  exact ⟨⟨k, hk, S, T, hS, hT, hid⟩⟩

end OptimalConvergenceRates.KrivineStengle

end
