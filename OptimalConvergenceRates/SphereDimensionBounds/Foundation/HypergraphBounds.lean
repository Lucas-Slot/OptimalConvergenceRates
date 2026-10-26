import OptimalConvergenceRates.SphereDimensionBounds.Foundation.BinomialBounds

/-! Numerical estimates for the expanding triple-system union bound. -/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

theorem containment_product_bound (a v : ℕ) (hv : v ≤ 2 * a)
    (q : ℝ) (hq : 0 < q) :
    (24 / q) ^ a * (3 / q) ^ v * (2 * q) ^ (3 * a) ≤
      (2048 : ℝ) ^ a * q ^ (2 * a - v) := by
  have hcancel : q ^ (3 * a) / (q ^ a * q ^ v) = q ^ (2 * a - v) := by
    apply (div_eq_iff (mul_ne_zero (pow_ne_zero _ hq.ne') (pow_ne_zero _ hq.ne'))).2
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have htwo : (2 : ℝ) ^ (3 * a) = (8 : ℝ) ^ a := by rw [pow_mul]; norm_num
  have hthree : (3 : ℝ) ^ v ≤ (9 : ℝ) ^ a := by
    calc
      (3 : ℝ) ^ v ≤ (3 : ℝ) ^ (2 * a) := pow_le_pow_right₀ (by norm_num) hv
      _ = (9 : ℝ) ^ a := by rw [pow_mul]; norm_num
  have heq : (24 / q) ^ a * (3 / q) ^ v * (2 * q) ^ (3 * a) =
      ((24 : ℝ) ^ a * (3 : ℝ) ^ v * (8 : ℝ) ^ a) * q ^ (2 * a - v) := by
    rw [div_pow, div_pow, mul_pow, htwo]
    calc
      (24 ^ a / q ^ a) * (3 ^ v / q ^ v) * (8 ^ a * q ^ (3 * a)) =
          (24 ^ a * 3 ^ v * 8 ^ a) * (q ^ (3 * a) / (q ^ a * q ^ v)) := by ring
      _ = _ := by rw [hcancel]
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq.le _)
  calc
    (24 : ℝ) ^ a * 3 ^ v * 8 ^ a ≤ 24 ^ a * 9 ^ a * 8 ^ a := by gcongr
    _ = (1728 : ℝ) ^ a := by rw [← mul_pow, ← mul_pow]; norm_num
    _ ≤ (2048 : ℝ) ^ a := pow_le_pow_left₀ (by norm_num) (by norm_num) a

theorem small_ratio_containment_bound (a v : ℕ) (hv : v ≤ 2 * a)
    (hvfour : 4 * v ≤ 7 * a) (q : ℝ) (hq : 0 ≤ q)
    (hqsmall : q ≤ 1 / (2 : ℝ) ^ 48) :
    (2048 : ℝ) ^ a * q ^ (2 * a - v) ≤ (1 / 2 : ℝ) ^ a := by
  have hqone : q ≤ 1 := by norm_num at hqsmall ⊢; linarith
  have he : a ≤ 4 * (2 * a - v) := by omega
  have hpower : q ^ (4 * (2 * a - v)) ≤ q ^ a := pow_le_pow_of_le_one hq hqone he
  have hfour : ((2048 : ℝ) ^ a * q ^ (2 * a - v)) ^ 4 ≤ ((1 / 2 : ℝ) ^ a) ^ 4 := by
    calc
      ((2048 : ℝ) ^ a * q ^ (2 * a - v)) ^ 4 =
          ((2048 : ℝ) ^ 4) ^ a * q ^ (4 * (2 * a - v)) := by
        rw [mul_pow]
        simp only [← pow_mul]
        congr 1 <;> congr 1 <;> omega
      _ ≤ ((2048 : ℝ) ^ 4) ^ a * q ^ a := by gcongr
      _ ≤ ((2048 : ℝ) ^ 4) ^ a * (1 / (2 : ℝ) ^ 48) ^ a := by gcongr
      _ = ((1 / 2 : ℝ) ^ a) ^ 4 := by
        rw [← mul_pow]
        norm_num
        rw [← pow_mul, Nat.mul_comm a 4, pow_mul]
        norm_num
  exact le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity) hfour

theorem small_support_union_bound (N a v : ℕ) (ha : 0 < a)
    (hav : a ≤ v) (hv : v ≤ 2 * a) (hvfour : 4 * v ≤ 7 * a)
    (hsmall : a * 2 ^ 48 ≤ N) (u : ℝ) (hu : 0 ≤ u)
    (huratio : u ≤ ((v : ℝ) / (N : ℝ)) ^ 3) :
    (((8 * N).choose a : ℝ) * (N.choose v : ℝ)) * u ^ a ≤ (1 / 2 : ℝ) ^ a := by
  have hN : 0 < N := by
    have : 0 < a * 2 ^ 48 := Nat.mul_pos ha (by positivity)
    omega
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hvpos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (show 0 < v by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have havR : (a : ℝ) ≤ (v : ℝ) := by exact_mod_cast hav
  have hvR : (v : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hv
  let q : ℝ := (a : ℝ) / (N : ℝ)
  have hq : 0 < q := div_pos hapos hNpos
  have hqsmall : q ≤ 1 / (2 : ℝ) ^ 48 := by
    apply (div_le_div_iff₀ hNpos (by positivity : (0 : ℝ) < (2 : ℝ) ^ 48)).mpr
    have hcast : (a : ℝ) * (2 : ℝ) ^ 48 ≤ (N : ℝ) := by exact_mod_cast hsmall
    simpa using hcast
  have hcA : ((8 * N).choose a : ℝ) ≤ (24 / q) ^ a := by
    calc
      ((8 * N).choose a : ℝ) ≤ (3 * ((8 * N : ℕ) : ℝ) / (a : ℝ)) ^ a :=
        binomial_le_three_mul_div_pow (8 * N) a ha
      _ = (24 / q) ^ a := by
        congr 1
        dsimp [q]
        push_cast
        field_simp
        ring
  have hden : 3 * (N : ℝ) / (v : ℝ) ≤ 3 * (N : ℝ) / (a : ℝ) := by
    apply (div_le_div_iff₀ hvpos hapos).mpr
    exact mul_le_mul_of_nonneg_left havR (by positivity)
  have hcV : (N.choose v : ℝ) ≤ (3 / q) ^ v := by
    calc
      (N.choose v : ℝ) ≤ (3 * (N : ℝ) / (v : ℝ)) ^ v :=
        binomial_le_three_mul_div_pow N v (by omega)
      _ ≤ (3 * (N : ℝ) / (a : ℝ)) ^ v := by gcongr
      _ = (3 / q) ^ v := by
        congr 1
        dsimp [q]
        field_simp
  have hvq : (v : ℝ) / (N : ℝ) ≤ 2 * q := by
    calc
      (v : ℝ) / (N : ℝ) ≤ (2 * (a : ℝ)) / (N : ℝ) := by gcongr
      _ = 2 * q := by dsimp [q]; ring
  have hp : u ^ a ≤ (2 * q) ^ (3 * a) := by
    calc
      u ^ a ≤ (((v : ℝ) / (N : ℝ)) ^ 3) ^ a := pow_le_pow_left₀ hu huratio a
      _ ≤ ((2 * q) ^ 3) ^ a := by gcongr
      _ = (2 * q) ^ (3 * a) := by rw [pow_mul]
  calc
    (((8 * N).choose a : ℝ) * (N.choose v : ℝ)) * u ^ a ≤
        (24 / q) ^ a * (3 / q) ^ v * (2 * q) ^ (3 * a) := by gcongr
    _ ≤ (2048 : ℝ) ^ a * q ^ (2 * a - v) := containment_product_bound a v hv q hq
    _ ≤ (1 / 2 : ℝ) ^ a := small_ratio_containment_bound a v hv hvfour q hq.le hqsmall

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
