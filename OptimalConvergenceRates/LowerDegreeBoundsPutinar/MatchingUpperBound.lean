/-
  OptimalConvergenceRates/LowerDegreeBoundsPutinar/MatchingUpperBound.lean

  Matching upper-bound construction for the corner polynomial using univariate SOS cutoffs.
-/
import OptimalConvergenceRates.LowerDegreeBoundsPutinar.GloballyNonnegativeModule
import OptimalConvergenceRates.MarkovLukacz.UnivariateSOS
import OptimalConvergenceRates.Chebyshev.ChebyshevGrowth
import Mathlib.Algebra.MvPolynomial.Funext

open MvPolynomial Finset Polynomial

noncomputable section

namespace OptimalConvergenceRates

/-! ## Univariate lifting -/

/-- Lift a univariate polynomial to coordinate `i` in two variables. -/
def liftUni (i : Fin 2) (p : Polynomial ℝ) : MvPolynomial (Fin 2) ℝ :=
  embedUnivariate i p

@[simp] theorem eval_liftUni (i : Fin 2) (p : Polynomial ℝ) (x : Fin 2 → ℝ) :
    MvPolynomial.eval x (liftUni i p) = p.eval (x i) := by
  simp [liftUni, eval_embedUnivariate]

theorem liftUni_totalDegree_le (i : Fin 2) (p : Polynomial ℝ) :
    (liftUni i p).totalDegree ≤ p.natDegree := by
  simpa [liftUni] using totalDegree_embedUnivariate i p

theorem liftUni_nonneg {i : Fin 2} {p : Polynomial ℝ}
    (hp : ∀ t : ℝ, 0 ≤ p.eval t) : IsNonnegOn (liftUni i p) Set.univ := by
  intro x _
  simpa using hp (x i)

/-- Lifting preserves univariate SOS witnesses. -/
theorem liftUni_isSOS {i : Fin 2} {p : Polynomial ℝ} (hp : IsSOSUni p) :
    IsSOS (liftUni i p) := by
  simpa [liftUni] using IsSOS_of_IsSOSUni i p hp

/-! ## Chebyshev-kernel ingredients -/

/-- The kernel parameter `δ = m⁻²`. -/
def delta (m : ℕ) : ℝ := 1 / (m : ℝ) ^ 2

/-- The second-kind endpoint kernel `A = δ U_{m-1}²`. -/
def endpointKernel (m : ℕ) : Polynomial ℝ :=
  Polynomial.C (delta m) * Polynomial.Chebyshev.U ℝ (m - 1 : ℤ) ^ 2

/-- The square repair piece `D = δ - g A`. -/
def DKernel (m : ℕ) : Polynomial ℝ :=
  Polynomial.C (delta m) - (1 - Polynomial.X ^ 2) * endpointKernel m

/-- The remaining one-variable repair piece `E = g(1 - A)`. -/
def EKernel (m : ℕ) : Polynomial ℝ :=
  (1 - Polynomial.X ^ 2) * (1 - endpointKernel m)

/-- The nonnegative repair polynomial `B = E + δ`. -/
def repairKernel (m : ℕ) : Polynomial ℝ :=
  EKernel m + Polynomial.C (delta m)

/-- The Chebyshev identity `T_{n+1}² + (1 - X²) U_n² = 1`. -/
theorem chebyshevT_sq_add_one_sub_X_sq_mul_U_sq (n : ℤ) :
    Polynomial.Chebyshev.T ℝ (n + 1) ^ 2 +
      (1 - Polynomial.X ^ 2) * Polynomial.Chebyshev.U ℝ n ^ 2 = 1 := by
  have hS : Polynomial.Chebyshev.U ℝ n ^ 2 + Polynomial.Chebyshev.U ℝ (n + 1) ^ 2 -
      (2 * Polynomial.X) * Polynomial.Chebyshev.U ℝ n * Polynomial.Chebyshev.U ℝ (n + 1) =
        1 := by
    have hS := congr_arg (fun p : Polynomial ℝ => p.comp (2 * Polynomial.X))
      (Polynomial.Chebyshev.S_sq_add_S_sq (R := ℝ) n)
    simpa [Polynomial.Chebyshev.S_comp_two_mul_X, mul_comm, mul_left_comm, mul_assoc] using hS
  have hU := Polynomial.Chebyshev.U_eq_X_mul_U_add_T (R := ℝ) n
  linear_combination (norm := ring_nf) hS -
    (Polynomial.Chebyshev.U ℝ (n + 1) - Polynomial.X * Polynomial.Chebyshev.U ℝ n +
      Polynomial.Chebyshev.T ℝ (n + 1)) * hU

/-- Chebyshev identity in the form needed for the kernel repair. -/
theorem DKernel_eq_delta_mul_chebyshevT_sq (m : ℕ) (_hm : 1 ≤ m) :
    DKernel m = Polynomial.C (delta m) * chebyshevT m ^ 2 := by
  let U : Polynomial ℝ := Polynomial.Chebyshev.U ℝ (m - 1 : ℤ)
  let T : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (m : ℤ)
  have hid0 := chebyshevT_sq_add_one_sub_X_sq_mul_U_sq ((m : ℤ) - 1)
  have hid : T ^ 2 + (1 - Polynomial.X ^ 2) * U ^ 2 = 1 := by
    dsimp [T, U]
    simpa [show ((m : ℤ) - 1 + 1) = (m : ℤ) by omega,
      show ((m : ℤ) - 1) = (m - 1 : ℤ) by omega] using hid0
  have hsub : 1 - (1 - Polynomial.X ^ 2) * U ^ 2 = T ^ 2 := by
    calc
      1 - (1 - Polynomial.X ^ 2) * U ^ 2 =
          (T ^ 2 + (1 - Polynomial.X ^ 2) * U ^ 2) -
            (1 - Polynomial.X ^ 2) * U ^ 2 := by rw [hid]
      _ = T ^ 2 := by ring
  unfold DKernel endpointKernel
  rw [chebyshevT_eq_T_nat m]
  dsimp [T, U] at hsub ⊢
  calc
    Polynomial.C (delta m) - (1 - Polynomial.X ^ 2) *
        (Polynomial.C (delta m) * Polynomial.Chebyshev.U ℝ (m - 1 : ℤ) ^ 2)
        = Polynomial.C (delta m) *
          (1 - (1 - Polynomial.X ^ 2) * Polynomial.Chebyshev.U ℝ (m - 1 : ℤ) ^ 2) := by
            ring_nf
    _ = Polynomial.C (delta m) * Polynomial.Chebyshev.T ℝ (m : ℤ) ^ 2 := by
        rw [hsub]

theorem endpointKernel_isSOSUni (m : ℕ) : IsSOSUni (endpointKernel m) := by
  let U : Polynomial ℝ := Polynomial.Chebyshev.U ℝ (m - 1 : ℤ)
  refine ⟨1, fun _ => Polynomial.C (Real.sqrt (delta m)) * U, ?_⟩
  have hd : 0 ≤ delta m := by
    unfold delta
    positivity
  simp only [Fin.sum_univ_one]
  unfold endpointKernel
  change Polynomial.C (delta m) * U ^ 2 = (Polynomial.C (Real.sqrt (delta m)) * U) ^ 2
  rw [pow_two, pow_two]
  calc
    Polynomial.C (delta m) * (U * U)
        = Polynomial.C (Real.sqrt (delta m) * Real.sqrt (delta m)) * (U * U) := by
            rw [Real.mul_self_sqrt hd]
    _ = (Polynomial.C (Real.sqrt (delta m)) * Polynomial.C (Real.sqrt (delta m))) *
          (U * U) := by
            rw [Polynomial.C_mul]
    _ = (Polynomial.C (Real.sqrt (delta m)) * U) *
          (Polynomial.C (Real.sqrt (delta m)) * U) := by
            ac_rfl

theorem chebyshevU_ge_nat_of_ge_one (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    (d + 1 : ℝ) ≤ (Polynomial.Chebyshev.U ℝ (d : ℤ)).eval x := by
  induction d with
  | zero => simp [Polynomial.Chebyshev.U_zero]
  | succ d ih =>
      have hrec : Polynomial.Chebyshev.U ℝ ((d + 1 : ℕ) : ℤ) =
          Polynomial.X * Polynomial.Chebyshev.U ℝ (d : ℤ) +
            Polynomial.Chebyshev.T ℝ ((d + 1 : ℕ) : ℤ) := by
        have h := Polynomial.Chebyshev.U_eq_X_mul_U_add_T (R := ℝ) (d : ℤ)
        simpa using h
      rw [hrec]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      have hT : 1 ≤ (Polynomial.Chebyshev.T ℝ ((d + 1 : ℕ) : ℤ)).eval x := by
        rw [← chebyshevT_eq_T_nat (d + 1)]
        exact chebyshevT_lower_bound_ge_one (d + 1) x hx
      have hxU : (d + 1 : ℝ) ≤ x * (Polynomial.Chebyshev.U ℝ (d : ℤ)).eval x := by
        calc (d + 1 : ℝ) = 1 * (d + 1 : ℝ) := by ring
          _ ≤ x * (Polynomial.Chebyshev.U ℝ (d : ℤ)).eval x := by
              exact mul_le_mul hx ih (by positivity) (by positivity)
      have hcast : ((d + 1 : ℕ) : ℝ) + 1 = (d + 1 : ℝ) + 1 := by norm_num
      linarith

/-- Outside `[-1,1]`, the second-kind Chebyshev polynomial has endpoint growth. -/
theorem chebyshevU_abs_ge_nat_of_one_le_abs (d : ℕ) (x : ℝ) (hx : 1 ≤ |x|) :
    (d + 1 : ℝ) ≤ |(Polynomial.Chebyshev.U ℝ (d : ℤ)).eval x| := by
  rcases le_or_gt 0 x with hx0 | hx0
  · have hx1 : 1 ≤ x := by rwa [abs_of_nonneg hx0] at hx
    exact le_trans (chebyshevU_ge_nat_of_ge_one d x hx1) (le_abs_self _)
  · have hy : 1 ≤ -x := by
      have hneg : |x| = -x := abs_of_neg hx0
      rwa [hneg] at hx
    have hge := chebyshevU_ge_nat_of_ge_one d (-x) hy
    have hneg_eval := Polynomial.Chebyshev.U_eval_neg (R := ℝ) d (-x)
    rw [← neg_neg x, hneg_eval]
    rw [abs_mul]
    have hunit : |((d : ℤ).negOnePow : ℝ)| = 1 := by
      exact abs_unit_intCast _
    rw [hunit, one_mul]
    exact le_trans hge (le_abs_self _)

theorem DKernel_isSOSUni (m : ℕ) (hm : 1 ≤ m) : IsSOSUni (DKernel m) := by
  rw [DKernel_eq_delta_mul_chebyshevT_sq m hm]
  let T : Polynomial ℝ := chebyshevT m
  refine ⟨1, fun _ => Polynomial.C (Real.sqrt (delta m)) * T, ?_⟩
  have hd : 0 ≤ delta m := by
    unfold delta
    positivity
  simp only [Fin.sum_univ_one]
  change Polynomial.C (delta m) * T ^ 2 = (Polynomial.C (Real.sqrt (delta m)) * T) ^ 2
  rw [pow_two, pow_two]
  calc
    Polynomial.C (delta m) * (T * T)
        = Polynomial.C (Real.sqrt (delta m) * Real.sqrt (delta m)) * (T * T) := by
            rw [Real.mul_self_sqrt hd]
    _ = (Polynomial.C (Real.sqrt (delta m)) * Polynomial.C (Real.sqrt (delta m))) *
          (T * T) := by
            rw [Polynomial.C_mul]
    _ = (Polynomial.C (Real.sqrt (delta m)) * T) *
          (Polynomial.C (Real.sqrt (delta m)) * T) := by
            ac_rfl

/-- The repair piece `E` is globally nonnegative. -/
theorem EKernel_nonneg (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    0 ≤ (EKernel m).eval t := by
  let Uval : ℝ := (Polynomial.Chebyshev.U ℝ (m - 1 : ℤ)).eval t
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  unfold EKernel endpointKernel
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  by_cases ht : |t| ≤ 1
  · have hg : 0 ≤ 1 - t ^ 2 := by
      have ht_sq : t ^ 2 ≤ 1 := by rwa [sq_le_one_iff_abs_le_one]
      nlinarith
    have hU : |Uval| ≤ (m : ℝ) := by
      dsimp [Uval]
      exact chebyshevU_abs_le m t (abs_le.mp ht).1 (abs_le.mp ht).2
    have hA : delta m * Uval ^ 2 ≤ 1 := by
      unfold delta
      have hUsq_abs : |Uval| ^ 2 ≤ (m : ℝ) ^ 2 :=
        sq_le_sq' (by linarith [abs_nonneg Uval, hmpos.le]) hU
      have hUsq : Uval ^ 2 ≤ (m : ℝ) ^ 2 := by simpa [sq_abs] using hUsq_abs
      have hm2pos : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hmpos
      calc (1 / (m : ℝ) ^ 2) * Uval ^ 2 ≤ (1 / (m : ℝ) ^ 2) * (m : ℝ) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hUsq (by positivity)
        _ = 1 := by field_simp [ne_of_gt hm2pos]
    have h1A : 0 ≤ 1 - delta m * Uval ^ 2 := by linarith
    exact mul_nonneg hg h1A
  · have houtside : 1 ≤ |t| := le_of_not_ge ht
    have hg : 1 - t ^ 2 ≤ 0 := by
      have ht_sq_abs : (1 : ℝ) ^ 2 ≤ |t| ^ 2 :=
        sq_le_sq' (by linarith [abs_nonneg t]) houtside
      have ht_sq : 1 ≤ t ^ 2 := by simpa [sq_abs] using ht_sq_abs
      nlinarith
    have hU : (m : ℝ) ≤ |Uval| := by
      have h := chebyshevU_abs_ge_nat_of_one_le_abs (m - 1) t houtside
      have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
        have : m - 1 + 1 = m := by omega
        exact_mod_cast this
      have hidx : ((m - 1 : ℕ) : ℤ) = (m - 1 : ℤ) := by omega
      simpa [Uval, hcast, hidx] using h
    have hA : 1 ≤ delta m * Uval ^ 2 := by
      unfold delta
      have hUsq_abs : (m : ℝ) ^ 2 ≤ |Uval| ^ 2 :=
        sq_le_sq' (by linarith [abs_nonneg Uval, hmpos.le]) hU
      have hUsq : (m : ℝ) ^ 2 ≤ Uval ^ 2 := by simpa [sq_abs] using hUsq_abs
      have hm2pos : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hmpos
      calc 1 = (1 / (m : ℝ) ^ 2) * (m : ℝ) ^ 2 := by field_simp [ne_of_gt hm2pos]
        _ ≤ (1 / (m : ℝ) ^ 2) * Uval ^ 2 := by
            exact mul_le_mul_of_nonneg_left hUsq (by positivity)
    have h1A : 1 - delta m * Uval ^ 2 ≤ 0 := by linarith
    exact mul_nonneg_of_nonpos_of_nonpos hg h1A

theorem EKernel_isSOSUni (m : ℕ) (hm : 1 ≤ m) : IsSOSUni (EKernel m) :=
  IsSOSUni_of_nonneg (EKernel m) (EKernel_nonneg m hm)

theorem repairKernel_isSOSUni (m : ℕ) (hm : 1 ≤ m) : IsSOSUni (repairKernel m) := by
  unfold repairKernel
  exact IsSOSUni_of_nonneg _ (by
    intro t
    have hE := EKernel_nonneg m hm t
    have hd : 0 ≤ delta m := by
      unfold delta
      positivity
    simpa using add_nonneg hE hd)


theorem one_sub_X_sq_natDegree_le :
    (1 - Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
  calc (1 - Polynomial.X ^ 2 : Polynomial ℝ).natDegree
      ≤ max (1 : Polynomial ℝ).natDegree (Polynomial.X ^ 2 : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ 2 := by
        rw [Polynomial.natDegree_one, Polynomial.natDegree_X_pow]
        norm_num

theorem endpointKernel_natDegree_le (m : ℕ) (hm : 1 ≤ m) :
    (endpointKernel m).natDegree ≤ 2 * m - 2 := by
  unfold endpointKernel
  let U : Polynomial ℝ := Polynomial.Chebyshev.U ℝ (m - 1 : ℤ)
  calc (Polynomial.C (delta m) * U ^ 2).natDegree
      ≤ (U ^ 2).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ 2 * U.natDegree := Polynomial.natDegree_pow_le
    _ = 2 * (m - 1) := by
        congr 1
        dsimp [U]
        rw [Polynomial.Chebyshev.natDegree_U]
        have hcast : ((m - 1 : ℤ) + 1).natAbs = m := by
          have h : (m - 1 : ℤ) + 1 = (m : ℤ) := by omega
          rw [h]
          exact Int.natAbs_natCast m
        rw [hcast]
    _ = 2 * m - 2 := by omega

theorem DKernel_natDegree_le (m : ℕ) (hm : 1 ≤ m) :
    (DKernel m).natDegree ≤ 2 * m := by
  rw [DKernel_eq_delta_mul_chebyshevT_sq m hm]
  let T : Polynomial ℝ := chebyshevT m
  calc (Polynomial.C (delta m) * T ^ 2).natDegree
      ≤ (T ^ 2).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ 2 * T.natDegree := Polynomial.natDegree_pow_le
    _ = 2 * m := by
        dsimp [T]
        rw [natDegree_chebyshevT]

theorem EKernel_natDegree_le (m : ℕ) (hm : 1 ≤ m) :
    (EKernel m).natDegree ≤ 2 * m := by
  unfold EKernel
  have hA := endpointKernel_natDegree_le m hm
  calc ((1 - Polynomial.X ^ 2 : Polynomial ℝ) * (1 - endpointKernel m)).natDegree
      ≤ (1 - Polynomial.X ^ 2 : Polynomial ℝ).natDegree +
          (1 - endpointKernel m).natDegree := Polynomial.natDegree_mul_le
    _ ≤ 2 + (2 * m - 2) := by
        apply Nat.add_le_add one_sub_X_sq_natDegree_le
        calc (1 - endpointKernel m).natDegree
            ≤ max (1 : Polynomial ℝ).natDegree (endpointKernel m).natDegree :=
              Polynomial.natDegree_sub_le _ _
          _ ≤ 2 * m - 2 := by
              rw [Polynomial.natDegree_one]
              exact max_le (by omega) hA
    _ = 2 * m := by omega

theorem repairKernel_natDegree_le (m : ℕ) (hm : 1 ≤ m) :
    (repairKernel m).natDegree ≤ 2 * m := by
  unfold repairKernel
  calc (EKernel m + Polynomial.C (delta m)).natDegree
      ≤ max (EKernel m).natDegree (Polynomial.C (delta m)).natDegree :=
        Polynomial.natDegree_add_le _ _
    _ ≤ 2 * m := by
        rw [Polynomial.natDegree_C]
        exact max_le (EKernel_natDegree_le m hm) (Nat.zero_le _)


theorem BoxSemialgebraicGenerator_totalDegree_le_two (i : Fin 2) :
    (BoxSemialgebraicGenerator i).totalDegree ≤ 2 := by
  unfold BoxSemialgebraicGenerator
  calc (1 - X i ^ 2 : MvPolynomial (Fin 2) ℝ).totalDegree
      ≤ max (1 : MvPolynomial (Fin 2) ℝ).totalDegree
          (X i ^ 2 : MvPolynomial (Fin 2) ℝ).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ 2 := by
        rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X_pow]
        norm_num

/-! ## Lifted certificate pieces -/

def Ax (m : ℕ) : MvPolynomial (Fin 2) ℝ := liftUni 0 (endpointKernel m)
def Ay (m : ℕ) : MvPolynomial (Fin 2) ℝ := liftUni 1 (endpointKernel m)
def Bx (m : ℕ) : MvPolynomial (Fin 2) ℝ := liftUni 0 (repairKernel m)
def By (m : ℕ) : MvPolynomial (Fin 2) ℝ := liftUni 1 (repairKernel m)
def Dx (m : ℕ) : MvPolynomial (Fin 2) ℝ := liftUni 0 (DKernel m)
def Dy (m : ℕ) : MvPolynomial (Fin 2) ℝ := liftUni 1 (DKernel m)
def Ex (m : ℕ) : MvPolynomial (Fin 2) ℝ := liftUni 0 (EKernel m)
def Ey (m : ℕ) : MvPolynomial (Fin 2) ℝ := liftUni 1 (EKernel m)

/-- First multiplier in the matching upper-bound certificate. -/
def sigma1Upper (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  Ax m * By m

/-- Second multiplier in the matching upper-bound certificate. -/
def sigma2Upper (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  Ay m * Bx m

/-- SOS residual in the matching upper-bound certificate. -/
def sigma0Upper (ε : ℝ) (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (ε - delta m ^ 2) + Ex m * Ey m + Dx m * Dy m

/-- Package the two generator multipliers as a `Fin 2` family. -/
def sigmaUpper (m : ℕ) : Fin 2 → MvPolynomial (Fin 2) ℝ
  | 0 => sigma1Upper m
  | 1 => sigma2Upper m

/-! ## SOS witnesses -/

theorem Ax_isSOS (m : ℕ) : IsSOS (Ax m) :=
  liftUni_isSOS (endpointKernel_isSOSUni m)

theorem Ay_isSOS (m : ℕ) : IsSOS (Ay m) :=
  liftUni_isSOS (endpointKernel_isSOSUni m)

theorem Bx_isSOS (m : ℕ) (hm : 1 ≤ m) : IsSOS (Bx m) :=
  liftUni_isSOS (repairKernel_isSOSUni m hm)

theorem By_isSOS (m : ℕ) (hm : 1 ≤ m) : IsSOS (By m) :=
  liftUni_isSOS (repairKernel_isSOSUni m hm)

theorem Dx_isSOS (m : ℕ) (hm : 1 ≤ m) : IsSOS (Dx m) :=
  liftUni_isSOS (DKernel_isSOSUni m hm)

theorem Dy_isSOS (m : ℕ) (hm : 1 ≤ m) : IsSOS (Dy m) :=
  liftUni_isSOS (DKernel_isSOSUni m hm)

theorem Ex_isSOS (m : ℕ) (hm : 1 ≤ m) : IsSOS (Ex m) :=
  liftUni_isSOS (EKernel_isSOSUni m hm)

theorem Ey_isSOS (m : ℕ) (hm : 1 ≤ m) : IsSOS (Ey m) :=
  liftUni_isSOS (EKernel_isSOSUni m hm)

theorem sigma1Upper_isSOS (m : ℕ) (hm : 1 ≤ m) : IsSOS (sigma1Upper m) := by
  unfold sigma1Upper
  exact IsSOS_mul (Ax_isSOS m) (By_isSOS m hm)

theorem sigma2Upper_isSOS (m : ℕ) (hm : 1 ≤ m) : IsSOS (sigma2Upper m) := by
  unfold sigma2Upper
  exact IsSOS_mul (Ay_isSOS m) (Bx_isSOS m hm)

theorem sigma0Upper_isSOS (ε : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hε : delta m ^ 2 ≤ ε) : IsSOS (sigma0Upper ε m) := by
  unfold sigma0Upper
  have hconst : IsSOS (MvPolynomial.C (ε - delta m ^ 2) : MvPolynomial (Fin 2) ℝ) :=
    IsSOS_C_nonneg _ (by linarith)
  have hE : IsSOS (Ex m * Ey m) := IsSOS_mul (Ex_isSOS m hm) (Ey_isSOS m hm)
  have hD : IsSOS (Dx m * Dy m) := IsSOS_mul (Dx_isSOS m hm) (Dy_isSOS m hm)
  exact IsSOS_add (IsSOS_add hconst hE) hD

/-! ## Identity and degree bookkeeping -/

theorem matchingUpperBound_identity (ε : ℝ) (m : ℕ) (_hm : 1 ≤ m) :
    f_eps ε =
      sigma0Upper ε m +
        sigma1Upper m * BoxSemialgebraicGenerator (0 : Fin 2) +
        sigma2Upper m * BoxSemialgebraicGenerator (1 : Fin 2) := by
  apply MvPolynomial.funext
  intro z
  rw [f_eps_eval]
  simp [sigma0Upper, sigma1Upper, sigma2Upper, Ax, Ay, Bx, By, Dx, Dy, Ex, Ey,
    endpointKernel, DKernel, EKernel, repairKernel, liftUni, eval_embedUnivariate,
    BoxSemialgebraicGenerator_eval, map_add, map_sub, map_mul, map_pow, MvPolynomial.eval_C]
  ring

theorem sigma0Upper_totalDegree_le (ε : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    (sigma0Upper ε m).totalDegree ≤ 4 * m := by
  have hEx : (Ex m).totalDegree ≤ 2 * m :=
    (liftUni_totalDegree_le 0 (EKernel m)).trans (EKernel_natDegree_le m hm)
  have hEy : (Ey m).totalDegree ≤ 2 * m :=
    (liftUni_totalDegree_le 1 (EKernel m)).trans (EKernel_natDegree_le m hm)
  have hDx : (Dx m).totalDegree ≤ 2 * m :=
    (liftUni_totalDegree_le 0 (DKernel m)).trans (DKernel_natDegree_le m hm)
  have hDy : (Dy m).totalDegree ≤ 2 * m :=
    (liftUni_totalDegree_le 1 (DKernel m)).trans (DKernel_natDegree_le m hm)
  have hEprod : (Ex m * Ey m).totalDegree ≤ 4 * m := by
    calc (Ex m * Ey m).totalDegree
        ≤ (Ex m).totalDegree + (Ey m).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * m + 2 * m := Nat.add_le_add hEx hEy
      _ = 4 * m := by omega
  have hDprod : (Dx m * Dy m).totalDegree ≤ 4 * m := by
    calc (Dx m * Dy m).totalDegree
        ≤ (Dx m).totalDegree + (Dy m).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * m + 2 * m := Nat.add_le_add hDx hDy
      _ = 4 * m := by omega
  unfold sigma0Upper
  calc (MvPolynomial.C (ε - delta m ^ 2) + Ex m * Ey m + Dx m * Dy m).totalDegree
      ≤ max (MvPolynomial.C (ε - delta m ^ 2) + Ex m * Ey m).totalDegree
          (Dx m * Dy m).totalDegree := MvPolynomial.totalDegree_add _ _
    _ ≤ 4 * m := by
        apply max_le
        · calc (MvPolynomial.C (ε - delta m ^ 2) + Ex m * Ey m).totalDegree
              ≤ max (MvPolynomial.C (ε - delta m ^ 2) : MvPolynomial (Fin 2) ℝ).totalDegree
                  (Ex m * Ey m).totalDegree := MvPolynomial.totalDegree_add _ _
            _ ≤ 4 * m := by
                rw [MvPolynomial.totalDegree_C]
                exact max_le (Nat.zero_le _) hEprod
        · exact hDprod

theorem sigma1Upper_mul_gen_totalDegree_le (m : ℕ) (hm : 1 ≤ m) :
    (sigma1Upper m * BoxSemialgebraicGenerator (0 : Fin 2)).totalDegree ≤ 4 * m := by
  have hA : (Ax m).totalDegree ≤ 2 * m - 2 :=
    (liftUni_totalDegree_le 0 (endpointKernel m)).trans (endpointKernel_natDegree_le m hm)
  have hB : (By m).totalDegree ≤ 2 * m :=
    (liftUni_totalDegree_le 1 (repairKernel m)).trans (repairKernel_natDegree_le m hm)
  unfold sigma1Upper
  calc (Ax m * By m * BoxSemialgebraicGenerator (0 : Fin 2)).totalDegree
      ≤ (Ax m * By m).totalDegree + (BoxSemialgebraicGenerator (0 : Fin 2)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ ((Ax m).totalDegree + (By m).totalDegree) + 2 := by
        exact Nat.add_le_add (MvPolynomial.totalDegree_mul _ _)
          (BoxSemialgebraicGenerator_totalDegree_le_two 0)
    _ ≤ ((2 * m - 2) + 2 * m) + 2 := by
        exact Nat.add_le_add (Nat.add_le_add hA hB) le_rfl
    _ = 4 * m := by omega

theorem sigma2Upper_mul_gen_totalDegree_le (m : ℕ) (hm : 1 ≤ m) :
    (sigma2Upper m * BoxSemialgebraicGenerator (1 : Fin 2)).totalDegree ≤ 4 * m := by
  have hA : (Ay m).totalDegree ≤ 2 * m - 2 :=
    (liftUni_totalDegree_le 1 (endpointKernel m)).trans (endpointKernel_natDegree_le m hm)
  have hB : (Bx m).totalDegree ≤ 2 * m :=
    (liftUni_totalDegree_le 0 (repairKernel m)).trans (repairKernel_natDegree_le m hm)
  unfold sigma2Upper
  calc (Ay m * Bx m * BoxSemialgebraicGenerator (1 : Fin 2)).totalDegree
      ≤ (Ay m * Bx m).totalDegree + (BoxSemialgebraicGenerator (1 : Fin 2)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ ((Ay m).totalDegree + (Bx m).totalDegree) + 2 := by
        exact Nat.add_le_add (MvPolynomial.totalDegree_mul _ _)
          (BoxSemialgebraicGenerator_totalDegree_le_two 1)
    _ ≤ ((2 * m - 2) + 2 * m) + 2 := by
        exact Nat.add_le_add (Nat.add_le_add hA hB) le_rfl
    _ = 4 * m := by omega

theorem sigmaUpper_isSOS (m : ℕ) (hm : 1 ≤ m) (i : Fin 2) :
    IsSOS (sigmaUpper m i) := by
  fin_cases i <;> simp [sigmaUpper, sigma1Upper_isSOS, sigma2Upper_isSOS, hm]

theorem sigmaUpper_mul_gen_totalDegree_le (m : ℕ) (hm : 1 ≤ m) (i : Fin 2) :
    (sigmaUpper m i * BoxSemialgebraicGenerator i).totalDegree ≤ 4 * m := by
  fin_cases i
  · simpa [sigmaUpper] using sigma1Upper_mul_gen_totalDegree_le m hm
  · simpa [sigmaUpper] using sigma2Upper_mul_gen_totalDegree_le m hm

theorem matchingUpperBound_sum_identity (ε : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    f_eps ε = sigma0Upper ε m +
      ∑ i : Fin 2, sigmaUpper m i * BoxSemialgebraicGenerator i := by
  rw [matchingUpperBound_identity ε m hm]
  simp [sigmaUpper]
  ring

/-! ## Relaxed and SOS module membership -/

theorem f_eps_mem_BoxNonnegQuadraticModule_of_m (ε : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hε : delta m ^ 2 ≤ ε) :
    f_eps ε ∈ BoxNonnegQuadraticModule 2 (4 * m) := by
  refine ⟨sigma0Upper ε m, sigmaUpper m, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsSOS_nonneg _ (sigma0Upper_isSOS ε m hm hε)
  · intro i
    exact IsSOS_nonneg _ (sigmaUpper_isSOS m hm i)
  · exact sigma0Upper_totalDegree_le ε m hm
  · exact sigmaUpper_mul_gen_totalDegree_le m hm
  · exact matchingUpperBound_sum_identity ε m hm

theorem f_eps_mem_BoxQuadraticModule_of_m (ε : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hε : delta m ^ 2 ≤ ε) :
    f_eps ε ∈ BoxQuadraticModule 2 (4 * m) := by
  refine ⟨sigma0Upper ε m, sigmaUpper m, ?_, ?_, ?_, ?_, ?_⟩
  · exact sigma0Upper_isSOS ε m hm hε
  · exact sigmaUpper_isSOS m hm
  · exact sigma0Upper_totalDegree_le ε m hm
  · exact sigmaUpper_mul_gen_totalDegree_le m hm
  · exact matchingUpperBound_sum_identity ε m hm

theorem one_le_ceil_rpow_neg_quarter (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ Nat.ceil (ε ^ (-(1 : ℝ) / 4)) := by
  set x : ℝ := ε ^ (-(1 : ℝ) / 4)
  have hx_ge_one : 1 ≤ x := by
    dsimp [x]
    rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring]
    rw [Real.rpow_neg hε.le]
    have hquarter : ε ^ ((1 : ℝ) / 4) ≤ 1 := by
      simpa using Real.rpow_le_rpow hε.le hε1 (show 0 ≤ (1 : ℝ) / 4 by norm_num)
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hε _)).mpr hquarter
  have hceil : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  exact_mod_cast le_trans hx_ge_one hceil

theorem delta_sq_le_of_ceil_rpow_neg_quarter (ε : ℝ) (hε : 0 < ε) :
    delta (Nat.ceil (ε ^ (-(1 : ℝ) / 4))) ^ 2 ≤ ε := by
  set x : ℝ := ε ^ (-(1 : ℝ) / 4)
  set m : ℕ := Nat.ceil x
  have hx_pos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos hε _
  have hm_ge_x : x ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil x
  have hx4 : x ^ 4 = ε⁻¹ := by
    dsimp [x]
    rw [← Real.rpow_natCast (ε ^ (-(1 : ℝ) / 4)) 4]
    rw [← Real.rpow_mul hε.le]
    norm_num
    rw [Real.rpow_neg hε.le]
    simp
  have hpow : x ^ 4 ≤ (m : ℝ) ^ 4 := by
    exact pow_le_pow_left₀ (le_of_lt hx_pos) hm_ge_x 4
  have hinv : 1 / (m : ℝ) ^ 4 ≤ ε := by
    have hle : ε⁻¹ ≤ (m : ℝ) ^ 4 := by simpa [hx4] using hpow
    have h := one_div_le_one_div_of_le (inv_pos.mpr hε) hle
    simpa [one_div] using h
  unfold delta
  rw [div_pow, one_pow]
  have hpoweq : ((m : ℝ) ^ 2) ^ 2 = (m : ℝ) ^ 4 := by ring
  rwa [hpoweq]

theorem four_mul_ceil_rpow_neg_quarter_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((4 * Nat.ceil (ε ^ (-(1 : ℝ) / 4)) : ℕ) : ℝ) ≤
      8 * ε ^ (-(1 : ℝ) / 4) := by
  set x : ℝ := ε ^ (-(1 : ℝ) / 4)
  have hx_pos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos hε _
  have hx_ge_one : 1 ≤ x := by
    dsimp [x]
    rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring]
    rw [Real.rpow_neg hε.le]
    have hquarter : ε ^ ((1 : ℝ) / 4) ≤ 1 := by
      simpa using Real.rpow_le_rpow hε.le hε1 (show 0 ≤ (1 : ℝ) / 4 by norm_num)
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hε _)).mpr hquarter
  have hceil_lt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one (le_of_lt hx_pos)
  have hceil_le : (Nat.ceil x : ℝ) ≤ 2 * x := by
    have htmp : (Nat.ceil x : ℝ) < 2 * x := by nlinarith
    exact le_of_lt htmp
  calc ((4 * Nat.ceil x : ℕ) : ℝ)
      = 4 * (Nat.ceil x : ℝ) := by norm_num
    _ ≤ 4 * (2 * x) := by nlinarith
    _ = 8 * ε ^ (-(1 : ℝ) / 4) := by dsimp [x]; ring

/-- Relaxed globally nonnegative multiplier upper bound with concrete constant `8`. -/
theorem f_eps_mem_BoxNonnegQuadraticModule_matching_upper
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 8 * ε ^ (-(1 : ℝ) / 4) ∧
      f_eps ε ∈ BoxNonnegQuadraticModule 2 r := by
  let m : ℕ := Nat.ceil (ε ^ (-(1 : ℝ) / 4))
  refine ⟨4 * m, ?_, ?_⟩
  · exact four_mul_ceil_rpow_neg_quarter_le ε hε hε1
  · exact f_eps_mem_BoxNonnegQuadraticModule_of_m ε m
      (one_le_ceil_rpow_neg_quarter ε hε hε1)
      (delta_sq_le_of_ceil_rpow_neg_quarter ε hε)

/-- Genuine Putinar/SOS upper bound matching the lower-bound exponent. -/
theorem f_eps_mem_BoxQuadraticModule_matching_upper
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 8 * ε ^ (-(1 : ℝ) / 4) ∧
      f_eps ε ∈ BoxQuadraticModule 2 r := by
  let m : ℕ := Nat.ceil (ε ^ (-(1 : ℝ) / 4))
  refine ⟨4 * m, ?_, ?_⟩
  · exact four_mul_ceil_rpow_neg_quarter_le ε hε hε1
  · exact f_eps_mem_BoxQuadraticModule_of_m ε m
      (one_le_ceil_rpow_neg_quarter ε hε hε1)
      (delta_sq_le_of_ceil_rpow_neg_quarter ε hε)

end OptimalConvergenceRates

end
