/-
  The two-factor localized-product certificate used in the Putinar conversion.
-/
import OptimalConvergenceRates.LowerDegreeBoundsPutinar.MatchingUpperBound
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.QuadraticModuleSubstitution

open MvPolynomial Finset Polynomial

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n : ℕ}

/-! ## The localized Chebyshev factors -/

/-- The manuscript parameter `μ = k⁻²`. This is an alias for the kernel parameter
`delta` already used by the matching two-variable Putinar certificate. -/
def putinarPairMu (k : ℕ) : ℝ := delta k

/-- The second-kind Chebyshev factor `U_{k-1}(X_i)`. -/
def putinarPairU (k : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  embedUnivariate i (Polynomial.Chebyshev.U ℝ (k - 1 : ℤ))

/-- The normalized factor `q_i = k⁻¹ U_{k-1}(X_i)`. -/
def putinarPairQ (k : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C ((k : ℝ)⁻¹) * putinarPairU k i

/-- The localized generator factor
`a_i = μ (1-X_i²) U_{k-1}(X_i)² = (1-X_i²) q_i²`. -/
def putinarPairFactor (k : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (putinarPairMu k) *
    (BoxSemialgebraicGenerator i * putinarPairU k i ^ 2)

/-- The normalized and unnormalized presentations of the localized factor agree. -/
theorem putinarPairFactor_eq_generator_mul_q_sq (k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    putinarPairFactor k i = BoxSemialgebraicGenerator i * putinarPairQ k i ^ 2 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < k))
  simp only [putinarPairFactor, putinarPairQ, putinarPairMu, delta, pow_two]
  have hscalar : 1 / ((k : ℝ) * (k : ℝ)) = (k : ℝ)⁻¹ * (k : ℝ)⁻¹ := by
    field_simp
  rw [hscalar, MvPolynomial.C_mul]
  ring

/-! ## Pell factorization -/

/-- The Chebyshev Pell identity, lifted to one selected cube coordinate. -/
theorem one_sub_embed_chebyshevT_sq (k : ℕ) (_hk : 1 ≤ k) (i : Fin n) :
    1 - embedUnivariate i (chebyshevT k) ^ 2 =
      putinarPairU k i ^ 2 * BoxSemialgebraicGenerator i := by
  have hpell := chebyshevT_sq_add_one_sub_X_sq_mul_U_sq ((k : ℤ) - 1)
  have hpell' :
      chebyshevT k ^ 2 + (1 - Polynomial.X ^ 2) *
          Polynomial.Chebyshev.U ℝ (k - 1 : ℤ) ^ 2 = 1 := by
    rw [chebyshevT_eq_T_nat]
    simpa [show ((k : ℤ) - 1 + 1) = (k : ℤ) by omega,
      show ((k : ℤ) - 1) = (k - 1 : ℤ) by omega] using hpell
  have hlift := congrArg (embedUnivariate i) hpell'
  simp only [map_add, map_mul, map_one, map_pow] at hlift
  rw [embedUnivariate_one_sub_sq] at hlift
  unfold putinarPairU
  linear_combination -hlift

/-- The multiplier in the lifted Pell identity is an explicit square. -/
theorem putinarPairU_sq_isSOS (k : ℕ) (i : Fin n) :
    IsSOS (putinarPairU k i ^ 2) :=
  IsSOS_sq _

/-! ## The specialized two-variable template -/

/-- At `m = 1`, the matching two-variable certificate has no `E` repair term.
This explicit certificate avoids appealing to general univariate positivity-to-SOS. -/
theorem f_eps_one_mem_BoxQuadraticModule :
    f_eps 1 ∈ BoxQuadraticModule 2 4 := by
  let σ0 : MvPolynomial (Fin 2) ℝ := (X 0 * X 1) ^ 2
  let σ : Fin 2 → MvPolynomial (Fin 2) ℝ := fun _ ↦ 1
  refine ⟨σ0, σ, IsSOS_sq _, fun _ ↦ ?_, ?_, fun i ↦ ?_, ?_⟩
  · simpa [σ] using IsSOS_sq (1 : MvPolynomial (Fin 2) ℝ)
  · dsimp [σ0]
    calc
      ((X 0 * X 1) ^ 2 : MvPolynomial (Fin 2) ℝ).totalDegree
          ≤ 2 * (X 0 * X 1 : MvPolynomial (Fin 2) ℝ).totalDegree :=
        MvPolynomial.totalDegree_pow _ _
      _ ≤ 2 * ((X 0 : MvPolynomial (Fin 2) ℝ).totalDegree +
          (X 1 : MvPolynomial (Fin 2) ℝ).totalDegree) := by
        exact Nat.mul_le_mul_left 2 (MvPolynomial.totalDegree_mul _ _)
      _ = 4 := by simp
  · simp only [σ, one_mul]
    exact BoxSemialgebraicGenerator_totalDegree_le_two i |>.trans (by omega)
  · rw [f_eps_eq_gen_prod_add]
    simp only [σ0, σ, Fin.sum_univ_two]
    simp [BoxSemialgebraicGenerator]
    ring

/-! ## Substitution and the localized pair certificate -/

/-- Substitute `T_k` into two selected target coordinates. The selected coordinates need not
be distinct; the intended localized-product use has two distinct coordinates. -/
def putinarPairSubstitution (k : ℕ) (i j : Fin n) :
    Fin 2 → MvPolynomial (Fin n) ℝ
  | 0 => embedUnivariate i (chebyshevT k)
  | 1 => embedUnivariate j (chebyshevT k)

/-- Substituting `T_k` into the explicit `m = 1` template costs exactly a factor `k`
in canonical total-degree order. -/
theorem aeval_f_eps_one_putinarPairSubstitution_mem
    (k : ℕ) (hk : 1 ≤ k) (i j : Fin n) :
    MvPolynomial.aeval (putinarPairSubstitution k i j) (f_eps 1) ∈
      BoxQuadraticModule n (4 * k) := by
  let target : Fin 2 → Fin n := ![i, j]
  let q : Fin 2 → Polynomial ℝ := fun _ ↦ chebyshevT k
  let multiplier : Fin 2 → MvPolynomial (Fin n) ℝ :=
    fun t ↦ putinarPairU k (target t) ^ 2
  have hsub : putinarPairSubstitution k i j = selectedUnivariateSubstitution target q := by
    funext t
    fin_cases t <;> rfl
  rw [hsub]
  have hcert := aeval_selectedUnivariateSubstitution_mem_BoxQuadraticModule
    (d := k) (r := 4) target q (fun _ ↦ by simp [q, natDegree_chebyshevT]) multiplier
    (fun t ↦ putinarPairU_sq_isSOS k (target t))
    (fun t ↦ by
      simpa [q, multiplier] using one_sub_embed_chebyshevT_sq k hk (target t))
    f_eps_one_mem_BoxQuadraticModule
  simpa [Nat.mul_comm] using hcert

/-- Evaluation-free polynomial form of the substituted two-variable corner polynomial. -/
theorem aeval_f_eps_one_putinarPairSubstitution (k : ℕ) (hk : 1 ≤ k)
    (i j : Fin n) :
    MvPolynomial.aeval (putinarPairSubstitution k i j) (f_eps 1) =
      (BoxSemialgebraicGenerator i * putinarPairU k i ^ 2) *
        (BoxSemialgebraicGenerator j * putinarPairU k j ^ 2) + 1 := by
  rw [f_eps_eq_gen_prod_add]
  simp only [map_add, map_mul, map_one]
  simp only [BoxSemialgebraicGenerator, map_sub, map_one, map_pow, MvPolynomial.aeval_X,
    putinarPairSubstitution]
  rw [one_sub_embed_chebyshevT_sq k hk i, one_sub_embed_chebyshevT_sq k hk j]
  simp only [BoxSemialgebraicGenerator]
  ring

/-- The manuscript's `|J| = 2` localized-product certificate:

`a_i a_j + μ²` belongs to the canonical box quadratic module at order `4k`.

The proof starts from the explicit `m = 1` two-variable certificate, substitutes
Chebyshev `T_k` into the two selected coordinates, and scales by `μ²`. -/
theorem putinarPairFactor_mul_add_mu_sq_mem_BoxQuadraticModule
    (k : ℕ) (hk : 1 ≤ k) (i j : Fin n) :
    putinarPairFactor k i * putinarPairFactor k j +
        MvPolynomial.C (putinarPairMu k ^ 2) ∈
      BoxQuadraticModule n (4 * k) := by
  have hsub := aeval_f_eps_one_putinarPairSubstitution_mem k hk i j
  have hscaled := BoxQuadraticModule_nonneg_scale (putinarPairMu k ^ 2)
    (sq_nonneg (putinarPairMu k)) hsub
  rw [aeval_f_eps_one_putinarPairSubstitution k hk i j] at hscaled
  convert hscaled using 1
  simp only [putinarPairFactor]
  rw [MvPolynomial.C_pow]
  ring

/-- The same pair certificate in the manuscript's normalized notation
`a_i = (1-X_i²) q_i²`. -/
theorem generator_mul_putinarPairQ_sq_pair_add_mu_sq_mem_BoxQuadraticModule
    (k : ℕ) (hk : 1 ≤ k) (i j : Fin n) :
    (BoxSemialgebraicGenerator i * putinarPairQ k i ^ 2) *
          (BoxSemialgebraicGenerator j * putinarPairQ k j ^ 2) +
        MvPolynomial.C (putinarPairMu k ^ 2) ∈
      BoxQuadraticModule n (4 * k) := by
  rw [← putinarPairFactor_eq_generator_mul_q_sq k hk i,
    ← putinarPairFactor_eq_generator_mul_q_sq k hk j]
  exact putinarPairFactor_mul_add_mu_sq_mem_BoxQuadraticModule k hk i j

end QuarticConvergence
end OptimalConvergenceRates

end
