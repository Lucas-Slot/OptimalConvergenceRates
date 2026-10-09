/-
  OptimalConvergenceRates/KrivineStengle/RateSeed.lean

  Algebraic interface from a fixed Krivine--Stengle witness to perturbation refutations,
  together with the explicit seed used by the sharp example.
-/
import OptimalConvergenceRates.KrivineStengle.ConditionalNonnegative
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

variable {n m : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
  {p : MvPolynomial (Fin n) ℝ}

/-- The additional generator asserting that `p` is at most `-ε`. -/
def perturbationGenerator (p : MvPolynomial (Fin n) ℝ) (ε : ℝ) :
    MvPolynomial (Fin n) ℝ :=
  -p - C ε

/-- The polynomial identity underlying the fixed-seed refutation. -/
theorem KSWitness.perturbation_identity (w : KSWitness g p) (ε : ℝ) :
    -(C (ε ^ (2 * w.k))) =
      w.T + (C ε + perturbationGenerator p ε) * w.S +
        ((C ε + perturbationGenerator p ε) ^ (2 * w.k) - C (ε ^ (2 * w.k))) := by
  simp only [perturbationGenerator, C_pow]
  have hnegpow : (-p) ^ (2 * w.k) = p ^ (2 * w.k) := by
    calc
      (-p) ^ (2 * w.k) = ((-p) ^ 2) ^ w.k := by rw [pow_mul]
      _ = (p ^ 2) ^ w.k := by ring
      _ = p ^ (2 * w.k) := by rw [pow_mul]
  rw [show C ε + (-p - C ε) = -p by ring, hnegpow]
  symm
  calc
    w.T + -p * w.S + (p ^ (2 * w.k) - C ε ^ (2 * w.k)) =
        (w.T + p ^ (2 * w.k) - p * w.S) - C ε ^ (2 * w.k) := by ring
    _ = -C ε ^ (2 * w.k) := by rw [w.identity]; ring

section SharpSeed

/-- Coordinates for the fixed three-variable matching example. -/
def sharpSeedA : MvPolynomial (Fin 3) ℝ := X 0
def sharpSeedB : MvPolynomial (Fin 3) ℝ := X 1
def sharpSeedZ : MvPolynomial (Fin 3) ℝ := X 2

/-- The nontrivial generator `z*a*b + z^5` in the matching example. -/
def sharpSeedW : MvPolynomial (Fin 3) ℝ :=
  sharpSeedZ * sharpSeedA * sharpSeedB + sharpSeedZ ^ 5

/-- The four generators of the matching example. -/
def sharpSeedGenerators : Fin 4 → MvPolynomial (Fin 3) ℝ :=
  ![sharpSeedA, sharpSeedB, sharpSeedW,
    1 - sharpSeedA ^ 2 - sharpSeedB ^ 2 - sharpSeedZ ^ 2]

/-- The explicit `k = 3` Krivine--Stengle seed for the matching example. -/
def sharpSeedWitness : KSWitness sharpSeedGenerators sharpSeedZ where
  k := 3
  k_pos := by omega
  S := sharpSeedW
  T := sharpSeedZ ^ 2 * sharpSeedA * sharpSeedB
  hS := by
    simpa [sharpSeedGenerators] using preorderingMem_generator sharpSeedGenerators (2 : Fin 4)
  hT := by
    exact preorderingMem_mul
      (preorderingMem_mul (preorderingMem_sq sharpSeedGenerators sharpSeedZ)
        (by simpa [sharpSeedGenerators] using
          preorderingMem_generator sharpSeedGenerators (0 : Fin 4)))
      (by simpa [sharpSeedGenerators] using
        preorderingMem_generator sharpSeedGenerators (1 : Fin 4))
  identity := by
    simp only [sharpSeedW, sharpSeedZ, sharpSeedA, sharpSeedB]
    ring

theorem sharpSeed_nonempty :
    Nonempty (KSWitness sharpSeedGenerators sharpSeedZ) :=
  ⟨sharpSeedWitness⟩

end SharpSeed

end OptimalConvergenceRates.KrivineStengle

end
