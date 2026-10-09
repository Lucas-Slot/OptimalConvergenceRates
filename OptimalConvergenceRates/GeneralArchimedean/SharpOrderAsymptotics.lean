/-
  Linear growth of the expanded sharp conversion order in the rational
  package degree.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpParameterBounds

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

set_option maxHeartbeats 800000 in
-- Expanding the nested order formula requires extra elaboration time.
/-- The fully expanded sharp conversion order is bounded by its value at
degree one times `L+1`.  The expanded order contains several nested maxima
and products, so this structural proof receives a larger heartbeat budget. -/
theorem sharpConversionRefutationOrderOfDegree_le_linear
    (L s d rSigma rA rB : ℕ) :
    sharpConversionRefutationOrderOfDegree L s d rSigma rA rB ≤
      (L + 1) *
        sharpConversionRefutationOrderOfDegree 1 s d rSigma rA rB := by
  let q := L + 1
  let A := max rA rB
  let FL := L * d
  let F₁ := 1 * d
  let RintL := A + (L + 3) * d
  let Rint₁ := A + (1 + 3) * d
  let RprodL := s * (RintL + FL)
  let Rprod₁ := s * (Rint₁ + F₁)
  let R₁L := max (rSigma + s * FL) (RprodL + d)
  let R₁₁ := max (rSigma + s * F₁) (Rprod₁ + d)
  let R₂L := max (R₁L + s * FL) (d + s * FL)
  let R₂₁ := max (R₁₁ + s * F₁) (d + s * F₁)
  let R₃L := max (R₂L + s * FL) (RprodL + (d + 2 * s * FL))
  let R₃₁ := max (R₂₁ + s * F₁) (Rprod₁ + (d + 2 * s * F₁))
  let R₄L := max (R₃L + s * FL) (d + 3 * s * FL)
  let R₄₁ := max (R₃₁ + s * F₁) (d + 3 * s * F₁)
  have hconst (a : ℕ) : a ≤ q * a := by
    exact Nat.le_mul_of_pos_left a (by simp [q])
  have hadd {a b a₁ b₁ : ℕ}
      (ha : a ≤ q * a₁) (hb : b ≤ q * b₁) :
      a + b ≤ q * (a₁ + b₁) := by
    calc
      a + b ≤ q * a₁ + q * b₁ := Nat.add_le_add ha hb
      _ = q * (a₁ + b₁) := (Nat.mul_add _ _ _).symm
  have hmax {a b a₁ b₁ : ℕ}
      (ha : a ≤ q * a₁) (hb : b ≤ q * b₁) :
      max a b ≤ q * max a₁ b₁ := by
    apply max_le
    · exact ha.trans (Nat.mul_le_mul_left q (le_max_left _ _))
    · exact hb.trans (Nat.mul_le_mul_left q (le_max_right _ _))
  have hF : FL ≤ q * F₁ := by
    dsimp [FL, F₁, q]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right d (Nat.le_succ L)
  have hshift : (L + 3) * d ≤ q * ((1 + 3) * d) := by
    have h : L + 3 ≤ q * (1 + 3) := by dsimp [q]; omega
    calc
      (L + 3) * d ≤ (q * (1 + 3)) * d := Nat.mul_le_mul_right d h
      _ = q * ((1 + 3) * d) := by simp [Nat.mul_assoc]
  have hRint : RintL ≤ q * Rint₁ := by
    dsimp [RintL, Rint₁]
    exact hadd (hconst A) hshift
  have hRprod : RprodL ≤ q * Rprod₁ := by
    have hinside : RintL + FL ≤ q * (Rint₁ + F₁) := hadd hRint hF
    dsimp [RprodL, Rprod₁]
    calc
      s * (RintL + FL) ≤ s * (q * (Rint₁ + F₁)) :=
        Nat.mul_le_mul_left s hinside
      _ = q * (s * (Rint₁ + F₁)) := by
        simp [Nat.mul_left_comm]
  have hsF : s * FL ≤ q * (s * F₁) := by
    calc
      s * FL ≤ s * (q * F₁) := Nat.mul_le_mul_left s hF
      _ = q * (s * F₁) := by
        simp [Nat.mul_left_comm]
  have hR₁ : R₁L ≤ q * R₁₁ := by
    dsimp [R₁L, R₁₁]
    exact hmax (hadd (hconst rSigma) hsF)
      (hadd hRprod (hconst d))
  have hR₂ : R₂L ≤ q * R₂₁ := by
    dsimp [R₂L, R₂₁]
    exact hmax (hadd hR₁ hsF) (hadd (hconst d) hsF)
  have htwo : 2 * s * FL ≤ q * (2 * s * F₁) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left 2 hsF
  have hR₃ : R₃L ≤ q * R₃₁ := by
    dsimp [R₃L, R₃₁]
    exact hmax (hadd hR₂ hsF)
      (hadd hRprod (hadd (hconst d) htwo))
  have hthree : 3 * s * FL ≤ q * (3 * s * F₁) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left 3 hsF
  have hRE : d + 3 * s * FL ≤ q * (d + 3 * s * F₁) :=
    hadd (hconst d) hthree
  have hR₄ : R₄L ≤ q * R₄₁ := by
    dsimp [R₄L, R₄₁]
    exact hmax (hadd hR₃ hsF) hRE
  have hExpansion : RprodL + (d + 2 * s * FL) ≤
      q * (Rprod₁ + (d + 2 * s * F₁)) :=
    hadd hRprod (hadd (hconst d) htwo)
  have hTerm :
      max (RprodL + (d + 2 * s * FL)) (max (d + 3 * s * FL) R₄L) ≤
        q * max (Rprod₁ + (d + 2 * s * F₁))
          (max (d + 3 * s * F₁) R₄₁) :=
    hmax hExpansion (hmax hRE hR₄)
  have hOdd := hmax hTerm hRE
  have hDenInside : (rA + FL) + FL ≤ q * ((rA + F₁) + F₁) :=
    hadd (hadd (hconst rA) hF) hF
  have hDen : s * ((rA + FL) + FL) ≤
      q * (s * ((rA + F₁) + F₁)) := by
    calc
      s * ((rA + FL) + FL) ≤ s * (q * ((rA + F₁) + F₁)) :=
        Nat.mul_le_mul_left s hDenInside
      _ = q * (s * ((rA + F₁) + F₁)) := by
        simp [Nat.mul_left_comm]
  simpa [sharpConversionRefutationOrderOfDegree, q, A, FL, F₁,
    RintL, Rint₁, RprodL, Rprod₁, R₁L, R₁₁, R₂L, R₂₁,
    R₃L, R₃₁, R₄L, R₄₁] using hmax hOdd hDen

/-- Real-valued form of the linear order estimate. -/
theorem sharpConversionRefutationOrderOfDegree_cast_le
    (L s d rSigma rA rB : ℕ) :
    (sharpConversionRefutationOrderOfDegree L s d rSigma rA rB : ℝ) ≤
      (sharpConversionRefutationOrderOfDegree 1 s d rSigma rA rB : ℝ) *
        ((L : ℝ) + 1) := by
  have h := sharpConversionRefutationOrderOfDegree_le_linear
    L s d rSigma rA rB
  have hcast :
      (sharpConversionRefutationOrderOfDegree L s d rSigma rA rB : ℝ) ≤
        (((L + 1) * sharpConversionRefutationOrderOfDegree
          1 s d rSigma rA rB : ℕ) : ℝ) := by exact_mod_cast h
  simpa [Nat.cast_mul, Nat.cast_add, mul_comm] using hcast

end OptimalConvergenceRates.GeneralArchimedean

end
