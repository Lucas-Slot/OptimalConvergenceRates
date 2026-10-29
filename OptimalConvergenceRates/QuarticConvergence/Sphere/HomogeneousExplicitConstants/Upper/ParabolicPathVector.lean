import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Exact positive parabolic path test vectors, replacing trigonometric
test vectors without changing the localization constant. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace ParabolicPathVector

open scoped BigOperators

def value (m k : ℕ) : ℝ := (k:ℝ)*((m:ℝ)-(k:ℝ))

theorem value_zero (m : ℕ) : value m 0=0 := by simp [value]
theorem value_end (m : ℕ) : value m m=0 := by simp [value]

theorem value_nonneg {m k : ℕ} (hk : k ≤ m) : 0≤value m k := by
  unfold value
  exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hk))

theorem value_pos {m k : ℕ} (hk : 0 < k) (hkm : k < m) : 0<value m k := by
  unfold value
  exact mul_pos (by exact_mod_cast hk) (sub_pos.mpr (by exact_mod_cast hkm))

theorem sum_first (m : ℕ) :
    (∑k∈Finset.range m,(k:ℝ))=(m:ℝ)*((m:ℝ)-1)/2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,ih];push_cast;ring

theorem sum_second (m : ℕ) :
    (∑k∈Finset.range m,(k:ℝ)^2)=(m:ℝ)*((m:ℝ)-1)*(2*(m:ℝ)-1)/6 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,ih];push_cast;ring

theorem sum_third (m : ℕ) :
    (∑k∈Finset.range m,(k:ℝ)^3)=((m:ℝ)*((m:ℝ)-1)/2)^2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,ih];push_cast;ring

theorem sum_fourth (m : ℕ) :
    (∑k∈Finset.range m,(k:ℝ)^4)=
      (m:ℝ)*((m:ℝ)-1)*(2*(m:ℝ)-1)*(3*(m:ℝ)^2-3*(m:ℝ)-1)/30 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,ih];push_cast;ring

def squareSum (m : ℕ) : ℝ := ∑k∈Finset.range m,(value m k)^2
def adjacentSum (m : ℕ) : ℝ := ∑k∈Finset.range m,value m k*value m (k+1)

theorem squareSum_eq (m : ℕ) : squareSum m=((m:ℝ)^5-(m:ℝ))/30 := by
  have h : squareSum m=
      (m:ℝ)^2*(∑k∈Finset.range m,(k:ℝ)^2)-
        2*(m:ℝ)*(∑k∈Finset.range m,(k:ℝ)^3)+∑k∈Finset.range m,(k:ℝ)^4 := by
    simp only [squareSum,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [value]
    ring
  rw [h,sum_second,sum_third,sum_fourth]
  ring

theorem adjacentSum_eq (m : ℕ) :
    adjacentSum m=((m:ℝ)^5-5*(m:ℝ)^3+4*(m:ℝ))/30 := by
  have h : adjacentSum m=
      ((m:ℝ)^2-(m:ℝ))*(∑k∈Finset.range m,(k:ℝ))+
        ((m:ℝ)^2-3*(m:ℝ)+1)*(∑k∈Finset.range m,(k:ℝ)^2)+
        (2-2*(m:ℝ))*(∑k∈Finset.range m,(k:ℝ)^3)+
        ∑k∈Finset.range m,(k:ℝ)^4 := by
    simp only [adjacentSum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [value,Nat.cast_add,Nat.cast_one]
    ring
  rw [h,sum_first,sum_second,sum_third,sum_fourth]
  ring

theorem squareSum_pos {m : ℕ} (hm : 2 ≤ m) : 0<squareSum m := by
  have hp : 0<(value m 1)^2 := sq_pos_of_pos (value_pos (by omega) (by omega))
  exact hp.trans_le (Finset.single_le_sum (fun k _ ↦ sq_nonneg (value m k))
    (show 1∈Finset.range m by simp;omega))

theorem adjacentSum_nonneg (m : ℕ) : 0≤adjacentSum m := by
  apply Finset.sum_nonneg
  intro k hk
  have hm : k<m := Finset.mem_range.mp hk
  exact mul_nonneg (value_nonneg (by omega)) (value_nonneg (by omega))

theorem adjacentSum_exact (m : ℕ) :
    adjacentSum m=(1-5/((m:ℝ)^2+1))*squareSum m := by
  rw [adjacentSum_eq,squareSum_eq]
  have hp : (m:ℝ)^2+1≠0 := by positivity
  field_simp
  ring

theorem adjacentSum_lower {m ell : ℕ} (hell : 0 < ell) (hsize : ell ≤ 3 * m) :
    (1-45/(ell:ℝ)^2)*squareSum m≤adjacentSum m := by
  have hE : 0<(ell:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hell)
  have hM : 0<(m:ℝ)^2+1 := by positivity
  have hs : (ell:ℝ)^2≤9*(m:ℝ)^2 := by
    have h := (sq_le_sq₀ (by positivity : 0≤(ell:ℝ)) (by positivity : 0≤3*(m:ℝ))).mpr
      (show (ell:ℝ)≤3*(m:ℝ) by exact_mod_cast hsize)
    nlinarith
  have hd : 5/((m:ℝ)^2+1)≤45/(ell:ℝ)^2 := by
    apply (div_le_div_iff₀ hM hE).mpr
    nlinarith
  rw [adjacentSum_exact]
  apply mul_le_mul_of_nonneg_right (by linarith)
  exact Finset.sum_nonneg (fun k _ ↦ sq_nonneg (value m k))

def start (ell : ℕ) : ℕ := ell/3
def length (ell : ℕ) : ℕ := (ell-start ell-1)/2

/-- The two length-L blocks start at J and J+L+1. The single unused
coordinate between them eliminates the Jacobi cross term exactly. -/
theorem block_parameters {ell : ℕ} (hell : 5 ≤ ell) :
    1≤length ell ∧ start ell+2*length ell+1≤ell ∧
      ell≤3*(length ell+1) ∧ ell≤3*(start ell+1) := by
  unfold length start
  omega

end ParabolicPathVector
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
