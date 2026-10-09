/-
  OptimalConvergenceRates/Chebyshev/GaussChebyshevQuadrature.lean

  Gauss-Chebyshev quadrature nodes and discrete Chebyshev orthogonality.
-/
import OptimalConvergenceRates.Chebyshev.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## Quadrature infrastructure for Property (P1) -/

/-- Gauss-Chebyshev quadrature nodes: y_j = cos((2j+1)π/(2(r+2))),
    the zeros of the Chebyshev polynomial T_{r+2}. -/
noncomputable def chebyNode (r : ℕ) (j : ℕ) : ℝ :=
  Real.cos ((2 * j + 1) * Real.pi / (2 * (r + 2 : ℝ)))

/-- Quadrature node multi-index set: {0,...,r+1}^n -/
noncomputable def quadratureNodes (n r : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun _ : Fin n => Finset.range (r + 2))

/-- Chebyshev nodes are in [-1,1] -/
theorem chebyNode_mem_Icc (r j : ℕ) : chebyNode r j ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- Chebyshev node vector is in Hypercube -/
theorem chebyNode_vec_mem_Hypercube (r : ℕ) (j : Fin n → ℕ) :
    (fun i => chebyNode r (j i)) ∈ Hypercube n :=
  fun _ _ => chebyNode_mem_Icc r _

/-! ## Trigonometric sum identity and discrete Chebyshev orthogonality -/

/-- Telescoping trigonometric sum identity: for 1 ≤ m ≤ 2N-1,
    ∑_{j=0}^{N-1} cos(m·(2j+1)·π/(2N)) = 0.
    Proof: multiply by 2·sin(mπ/(2N)), use sin(A+B)-sin(A-B)=2cos(A)sin(B)
    to get a telescoping sum that equals sin(mπ)-sin(0) = 0. -/
private theorem cos_sum_eq_zero (N : ℕ) (hN : 0 < N) (m : ℕ)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * N - 1) :
    ∑ j ∈ Finset.range N,
      Real.cos (↑m * (2 * ↑j + 1) * Real.pi / (2 * ↑N)) = 0 := by
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have h2N_ne : (2 * (↑N : ℝ)) ≠ 0 := ne_of_gt (by positivity)
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (by omega)
  -- sin(mπ/(2N)) > 0 since 0 < mπ/(2N) < π
  have hα_pos : 0 < ↑m * Real.pi / (2 * ↑N) := by positivity
  have hα_lt_pi : ↑m * Real.pi / (2 * (↑N : ℝ)) < Real.pi := by
    have h1 : (↑m : ℝ) / (2 * ↑N) < 1 := by
      rw [div_lt_one (by positivity : (0 : ℝ) < 2 * ↑N)]
      exact_mod_cast (by omega : m < 2 * N)
    calc ↑m * Real.pi / (2 * ↑N) = (↑m / (2 * ↑N)) * Real.pi := by ring
      _ < 1 * Real.pi := by exact mul_lt_mul_of_pos_right h1 Real.pi_pos
      _ = Real.pi := one_mul _
  have hsin_pos : 0 < Real.sin (↑m * Real.pi / (2 * ↑N)) :=
    Real.sin_pos_of_pos_of_lt_pi hα_pos hα_lt_pi
  -- Suffices: 2·sin(mπ/(2N))·S = 0, then S = 0
  suffices hkey : 2 * Real.sin (↑m * Real.pi / (2 * ↑N)) *
      ∑ j ∈ Finset.range N,
        Real.cos (↑m * (2 * ↑j + 1) * Real.pi / (2 * ↑N)) = 0 by
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h (by positivity)
    · exact h
  rw [Finset.mul_sum]
  -- Each term via sin(A+B) - sin(A-B) = 2cos(A)sin(B)
  have hterm : ∀ j ∈ Finset.range N,
      2 * Real.sin (↑m * Real.pi / (2 * ↑N)) *
        Real.cos (↑m * (2 * ↑j + 1) * Real.pi / (2 * ↑N)) =
      Real.sin (↑m * (↑j + 1) * Real.pi / ↑N) -
        Real.sin (↑m * ↑j * Real.pi / ↑N) := by
    intro j _
    have heq_add :
        ↑m * (2 * ↑j + 1) * Real.pi / (2 * ↑N) +
          ↑m * Real.pi / (2 * ↑N) =
        ↑m * (↑j + 1) * Real.pi / ↑N := by field_simp; ring
    have heq_sub :
        ↑m * (2 * ↑j + 1) * Real.pi / (2 * ↑N) -
          ↑m * Real.pi / (2 * ↑N) =
        ↑m * ↑j * Real.pi / ↑N := by field_simp; ring
    have h1 := Real.sin_add
      (↑m * (2 * ↑j + 1) * Real.pi / (2 * ↑N))
      (↑m * Real.pi / (2 * ↑N))
    have h2 := Real.sin_sub
      (↑m * (2 * ↑j + 1) * Real.pi / (2 * ↑N))
      (↑m * Real.pi / (2 * ↑N))
    rw [heq_add] at h1; rw [heq_sub] at h2; linarith
  rw [Finset.sum_congr rfl hterm]
  -- Telescope: ∑(f(j+1)-f(j)) = f(N)-f(0) via induction
  have htel : ∀ p : ℕ, ∑ j ∈ Finset.range p,
      (Real.sin (↑m * (↑j + 1) * Real.pi / ↑N) -
       Real.sin (↑m * ↑j * Real.pi / ↑N)) =
      Real.sin (↑m * ↑p * Real.pi / ↑N) := by
    intro p; induction p with
    | zero => simp
    | succ p ih => rw [Finset.sum_range_succ, ih]; push_cast; linarith
  rw [htel, show (↑m : ℝ) * ↑N * Real.pi / ↑N = ↑m * Real.pi from by field_simp]
  exact Real.sin_nat_mul_pi m

/-- Discrete Chebyshev orthogonality at Gauss-Chebyshev quadrature nodes.
    (1/(r+2)) ∑_j T_k(y_j) T_l(y_j) = δ_{kl} · (if k=0 then 1 else 1/2).
    Proved directly from the trigonometric sum identity. -/
theorem discrete_chebyshev_orthogonality (r : ℕ) (k l : ℕ)
    (hk : k ≤ r) (hl : l ≤ r) :
    (1 / (r + 2 : ℝ)) * ∑ j ∈ Finset.range (r + 2),
      (chebyshevT k).eval (chebyNode r j) *
        (chebyshevT l).eval (chebyNode r j) =
    if k ≠ l then 0
    else if k = 0 then 1
    else 1 / 2 := by
  have hN_pos : 0 < r + 2 := by omega
  have hN_cast_pos : (0 : ℝ) < ↑(r + 2) := Nat.cast_pos.mpr hN_pos
  have hN_cast_ne : (↑(r + 2) : ℝ) ≠ 0 := ne_of_gt hN_cast_pos
  -- Rewrite using chebyshevT_cos and chebyNode
  simp_rw [chebyNode, chebyshevT_cos]
  -- Now: (1/(r+2)) * ∑_j cos(k·θ_j)·cos(l·θ_j)
  -- where θ_j = (2j+1)·π/(2·(r+2))
  -- Note: after simp_rw, ↑(r+2) appears as ↑r + 2
  by_cases hkl : k = l
  · -- Case k = l
    subst hkl; simp only [ne_eq, not_true_eq_false, ite_false]
    by_cases hk0 : k = 0
    · -- k = l = 0: cos(0)² = 1
      subst hk0; simp only [ite_true]
      simp only [Nat.cast_zero, zero_mul, Real.cos_zero, one_mul]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast; field_simp
    · -- k = l ≥ 1: cos²(kθ) = (1 + cos(2kθ))/2
      simp only [hk0, ite_false]
      -- Product-to-sum: 2cos²(x) = 1 + cos(2x)
      have hprod : ∀ j ∈ Finset.range (r + 2),
          Real.cos (↑k * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2)))) *
          Real.cos (↑k * ((2 * ↑j + 1) * Real.pi /
            (2 * (↑r + 2)))) =
          1 / 2 + Real.cos (↑(2 * k) * (2 * ↑j + 1) * Real.pi /
            (2 * (↑r + 2))) / 2 := by
        intro j _
        have h := Real.two_mul_cos_mul_cos
          (↑k * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2))))
          (↑k * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2))))
        rw [sub_self, Real.cos_zero] at h
        have harg : ↑k * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2))) +
            ↑k * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2))) =
            ↑(2 * k) * (2 * ↑j + 1) * Real.pi /
              (2 * (↑r + 2)) := by push_cast; ring
        rw [harg] at h; linarith
      rw [Finset.sum_congr rfl hprod, Finset.sum_add_distrib]
      -- ∑ cos(2kθ)/2 = 0 by cos_sum_eq_zero
      -- Need: ↑r + 2 = ↑(r+2) for applying cos_sum_eq_zero
      have hcast_eq : (↑r : ℝ) + 2 = ↑(r + 2) := by push_cast; ring
      have hcos_zero : ∑ j ∈ Finset.range (r + 2),
          Real.cos (↑(2 * k) * (2 * ↑j + 1) * Real.pi /
            (2 * (↑r + 2))) / 2 = 0 := by
        rw [← Finset.sum_div]; simp_rw [hcast_eq]
        rw [cos_sum_eq_zero (r + 2) hN_pos (2 * k)
          (by omega) (by omega), zero_div]
      rw [hcos_zero, add_zero]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      -- (1/(r+2)) * ((r+2) * (1/2)) = 1/2
      push_cast; field_simp
  · -- Case k ≠ l
    simp only [ne_eq, hkl, not_false_eq_true, ite_true]
    suffices h : ∑ j ∈ Finset.range (r + 2),
        Real.cos (↑k * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2)))) *
        Real.cos (↑l * ((2 * ↑j + 1) * Real.pi /
          (2 * (↑r + 2)))) = 0 by
      rw [h, mul_zero]
    -- Multiply by 2, use product-to-sum, show both sums vanish
    have hcast_eq : (↑r : ℝ) + 2 = ↑(r + 2) := by push_cast; ring
    have h2sum : (2 : ℝ) * ∑ j ∈ Finset.range (r + 2),
        Real.cos (↑k * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2)))) *
        Real.cos (↑l * ((2 * ↑j + 1) * Real.pi /
          (2 * (↑r + 2)))) = 0 := by
      rw [Finset.mul_sum]
      have hprod : ∀ j ∈ Finset.range (r + 2),
          2 * (Real.cos (↑k * ((2 * ↑j + 1) * Real.pi /
            (2 * (↑r + 2)))) *
          Real.cos (↑l * ((2 * ↑j + 1) * Real.pi /
            (2 * (↑r + 2))))) =
          Real.cos ((↑k - ↑l) * ((2 * ↑j + 1) * Real.pi /
            (2 * (↑r + 2)))) +
          Real.cos ((↑k + ↑l) * ((2 * ↑j + 1) * Real.pi /
            (2 * (↑r + 2)))) := by
        intro j _
        have h := Real.two_mul_cos_mul_cos
          (↑k * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2))))
          (↑l * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2))))
        have h1 :
            ↑k * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2))) -
            ↑l * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2))) =
            (↑k - ↑l) * ((2 * ↑j + 1) * Real.pi /
              (2 * (↑r + 2))) := by ring
        have h2 :
            ↑k * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2))) +
            ↑l * ((2 * ↑j + 1) * Real.pi / (2 * (↑r + 2))) =
            (↑k + ↑l) * ((2 * ↑j + 1) * Real.pi /
              (2 * (↑r + 2))) := by ring
        rw [h1, h2] at h; linarith
      rw [Finset.sum_congr rfl hprod, Finset.sum_add_distrib]
      -- Both sums vanish
      have hsum_diff : ∑ j ∈ Finset.range (r + 2),
          Real.cos ((↑k - ↑l) * ((2 * ↑j + 1) * Real.pi /
            (2 * (↑r + 2)))) = 0 := by
        by_cases hkl_le : k ≤ l
        · -- k < l: use cos(-x) = cos(x)
          have hkl_lt : k < l := Nat.lt_of_le_of_ne hkl_le hkl
          have hconv : ∀ j ∈ Finset.range (r + 2),
              Real.cos ((↑k - ↑l) * ((2 * ↑j + 1) * Real.pi /
                (2 * (↑r + 2)))) =
              Real.cos (↑(l - k) * (2 * ↑j + 1) * Real.pi /
                (2 * ↑(r + 2))) := by
            intro j _
            have hc : (↑k : ℝ) - ↑l = -(↑(l - k) : ℝ) := by
              rw [Nat.cast_sub (Nat.le_of_lt hkl_lt)]; ring
            rw [show (↑k - ↑l) * ((2 * ↑j + 1) * Real.pi /
              (2 * (↑r + 2))) =
              -(↑(l - k) * (2 * ↑j + 1) * Real.pi /
                (2 * ↑(r + 2))) from by rw [hc, hcast_eq]; ring]
            exact Real.cos_neg _
          rw [Finset.sum_congr rfl hconv]
          exact cos_sum_eq_zero (r + 2) hN_pos (l - k)
            (by omega) (by omega)
        · -- k > l
          push_neg at hkl_le
          have hle : l ≤ k := Nat.le_of_lt hkl_le
          have hconv : ∀ j ∈ Finset.range (r + 2),
              Real.cos ((↑k - ↑l) * ((2 * ↑j + 1) * Real.pi /
                (2 * (↑r + 2)))) =
              Real.cos (↑(k - l) * (2 * ↑j + 1) * Real.pi /
                (2 * ↑(r + 2))) := by
            intro j _; congr 1
            rw [hcast_eq]; push_cast [Nat.cast_sub hle]; ring
          rw [Finset.sum_congr rfl hconv]
          exact cos_sum_eq_zero (r + 2) hN_pos (k - l)
            (by omega) (by omega)
      have hsum_add : ∑ j ∈ Finset.range (r + 2),
          Real.cos ((↑k + ↑l) * ((2 * ↑j + 1) * Real.pi /
            (2 * (↑r + 2)))) = 0 := by
        have hconv : ∀ j ∈ Finset.range (r + 2),
            Real.cos ((↑k + ↑l) * ((2 * ↑j + 1) * Real.pi /
              (2 * (↑r + 2)))) =
            Real.cos (↑(k + l) * (2 * ↑j + 1) * Real.pi /
              (2 * ↑(r + 2))) := by
          intro j _; congr 1; rw [hcast_eq]; push_cast; ring
        rw [Finset.sum_congr rfl hconv]
        exact cos_sum_eq_zero (r + 2) hN_pos (k + l)
          (by omega) (by omega)
      rw [hsum_diff, hsum_add, add_zero]
    linarith

end OptimalConvergenceRates

end
