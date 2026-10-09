/-
  Scalar exponential arithmetic for the signed-moment tail.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.MomentObstruction

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

/-- If the effective coefficient/moment base is exponentially small in the
truncation order, every surviving shifted moment has Gaussian decay. -/
theorem sharpTailDecay_of_base_le
    {eta : Real} {D d : Nat}
    (heta : 0 <= eta) (hetaOne : eta <= 1)
    (hbase : (8 : Real) * (d : Real) ^ 2 * eta <=
      Real.exp (-((32 : Real) * (D : Real) + 32))) :
    SharpTailDecay eta D d
      (Real.exp (16 - 16 * (D : Real) ^ 2)) := by
  intro L s hDL hcut hs
  let B : Real := -((32 : Real) * (D : Real) + 32)
  have hbaseNonneg : 0 <= (8 : Real) * (d : Real) ^ 2 * eta := by
    positivity
  have hpow :
      ((8 : Real) * (d : Real) ^ 2 * eta) ^ L <=
        (Real.exp B) ^ L := by
    gcongr
  have hetaPow : eta ^ s <= 1 := pow_le_one₀ heta hetaOne
  have hmomentNonneg :
      0 <= Real.exp (4 * ((L + s : Nat) : Real) ^ 2) :=
    (Real.exp_pos _).le
  have hfactor :
      (8 : Real) ^ L * (d : Real) ^ (2 * L) * eta ^ (L + s) *
          Real.exp (4 * ((L + s : Nat) : Real) ^ 2) =
        (((8 : Real) * (d : Real) ^ 2 * eta) ^ L * eta ^ s) *
          Real.exp (4 * ((L + s : Nat) : Real) ^ 2) := by
    rw [pow_add]
    rw [show (d : Real) ^ (2 * L) = ((d : Real) ^ 2) ^ L by
      rw [pow_mul]]
    rw [mul_pow, mul_pow]
    ring
  rw [hfactor]
  calc
    (((8 : Real) * (d : Real) ^ 2 * eta) ^ L * eta ^ s) *
        Real.exp (4 * ((L + s : Nat) : Real) ^ 2)
        <= ((Real.exp B) ^ L * 1) *
          Real.exp (4 * ((L + s : Nat) : Real) ^ 2) := by
      gcongr
    _ = Real.exp
        ((L : Real) * B + 4 * ((L + s : Nat) : Real) ^ 2) := by
      rw [mul_one, ← Real.exp_nat_mul, ← Real.exp_add]
    _ <= Real.exp (16 - 16 * (D : Real) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hDLcast : (D : Real) <= (L : Real) := by exact_mod_cast hDL
      have hcutCast : ((L + s : Nat) : Real) <= 2 * (D : Real) := by
        exact_mod_cast hcut
      have hsq : ((L + s : Nat) : Real) ^ 2 <= (2 * (D : Real)) ^ 2 := by
        gcongr
      dsimp [B]
      nlinarith

end OptimalConvergenceRates.GeneralArchimedean

end
