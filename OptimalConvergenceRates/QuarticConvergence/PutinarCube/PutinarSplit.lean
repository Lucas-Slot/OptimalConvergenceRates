/-
  The explicit one-variable Chebyshev splitting used by the Putinar conversion.

  The sum of squares is stored as a triangular double sum.  Thus the square
  with second-kind Chebyshev index `q` occurs exactly `k - 1 - q` times, which
  is the manuscript coefficient without introducing square roots of scalars.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarPair
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ConeWitnesses

open MvPolynomial Finset Polynomial
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n : ℕ}

/-! ## A finite univariate Chebyshev identity -/

/-- The prefix sum `∑_{q < k} U_q²`. -/
private def chebyshevUSqPrefix (k : ℕ) : Polynomial ℝ :=
  ∑ q ∈ Finset.range k, Polynomial.Chebyshev.U ℝ (q : ℤ) ^ 2

private theorem chebyshevUSqPrefix_succ (m : ℕ) :
    chebyshevUSqPrefix (m + 1) =
      chebyshevUSqPrefix m + Polynomial.Chebyshev.U ℝ (m : ℤ) ^ 2 := by
  simp [chebyshevUSqPrefix, Finset.sum_range_succ]

/-- The triangular square sum.  The term `U_q²` occurs once for each
`t` with `q ≤ t < k - 1`, hence with multiplicity `k - 1 - q`. -/
private def chebyshevSplitTriangularSum (k : ℕ) : Polynomial ℝ :=
  ∑ t ∈ Finset.range (k - 1), chebyshevUSqPrefix (t + 1)

/-- The determinant-one identity for two consecutive second-kind Chebyshev
polynomials. -/
private theorem chebyshevU_pair_pell (m : ℕ) :
    Polynomial.Chebyshev.U ℝ (m : ℤ) ^ 2 +
        Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1) ^ 2 -
      2 * Polynomial.X * Polynomial.Chebyshev.U ℝ (m : ℤ) *
        Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1) = 1 := by
  have hpell := chebyshevT_sq_add_one_sub_X_sq_mul_U_sq ((m : ℤ) - 1)
  have hTU := Polynomial.Chebyshev.T_eq_U_sub_X_mul_U (ℝ) (m : ℤ)
  rw [show (m : ℤ) - 1 + 1 = m by omega] at hpell
  rw [hTU] at hpell
  linear_combination (norm := ring_nf) hpell

/-- The first-difference identity driving the triangular square decomposition. -/
private theorem chebyshevU_sq_difference_add_prefix (m : ℕ) :
    Polynomial.Chebyshev.U ℝ (m : ℤ) ^ 2 -
        Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1) ^ 2 +
      4 * (1 - Polynomial.X ^ 2) * chebyshevUSqPrefix m =
        Polynomial.C ((2 * m + 1 : ℕ) : ℝ) := by
  induction m with
  | zero =>
      simp [chebyshevUSqPrefix, Polynomial.Chebyshev.U_zero,
        Polynomial.Chebyshev.U_neg_one]
  | succ m ih =>
      have hrec := Polynomial.Chebyshev.U_add_two (ℝ) ((m : ℤ) - 1)
      have hpell := chebyshevU_pair_pell m
      rw [show (m : ℤ) - 1 + 2 = (m + 1 : ℕ) by omega,
        show (m : ℤ) - 1 + 1 = m by omega] at hrec
      have hindex : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
      rw [chebyshevUSqPrefix_succ, hindex, hrec]
      have hconst :
          Polynomial.C (((2 * (m + 1) + 1 : ℕ) : ℝ)) =
            Polynomial.C (((2 * m + 1 : ℕ) : ℝ)) + 2 := by
        norm_num [Nat.cast_add, Nat.cast_mul, Polynomial.C_ofNat]
        ring
      rw [hconst]
      linear_combination (norm := ring_nf) ih + 2 * hpell

/-- Recurrence for the triangular sum. -/
private theorem chebyshevSplitTriangularSum_succ (k : ℕ) (hk : 1 ≤ k) :
    chebyshevSplitTriangularSum (k + 1) =
      chebyshevSplitTriangularSum k + chebyshevUSqPrefix k := by
  simp only [chebyshevSplitTriangularSum]
  change (∑ t ∈ Finset.range k, chebyshevUSqPrefix (t + 1)) =
    (∑ t ∈ Finset.range (k - 1), chebyshevUSqPrefix (t + 1)) +
      chebyshevUSqPrefix k
  rw [show k = (k - 1) + 1 by omega, Finset.sum_range_succ]
  simp [Nat.sub_add_cancel hk]

/-- Explicit finite square decomposition of `k² - U_{k-1}²`. -/
private theorem chebyshev_sq_sub_U_sq_eq_triangular (k : ℕ) (hk : 1 ≤ k) :
    Polynomial.C ((k : ℝ) ^ 2) -
        Polynomial.Chebyshev.U ℝ ((k - 1 : ℕ) : ℤ) ^ 2 =
      4 * (1 - Polynomial.X ^ 2) * chebyshevSplitTriangularSum k := by
  induction k, hk using Nat.le_induction with
  | base => simp [chebyshevSplitTriangularSum, Polynomial.Chebyshev.U_zero]
  | succ k hk ih =>
      have hdiff := chebyshevU_sq_difference_add_prefix k
      have htri := chebyshevSplitTriangularSum_succ k hk
      rw [htri]
      rw [show k + 1 - 1 = k by omega]
      have hkm1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
      rw [hkm1] at ih
      have hscalar : ((k + 1 : ℕ) : ℝ) ^ 2 =
          (k : ℝ) ^ 2 + ((2 * k + 1 : ℕ) : ℝ) := by
        norm_num [Nat.cast_add, Nat.cast_mul, Polynomial.C_ofNat]
        ring
      rw [hscalar, map_add]
      linear_combination (norm := ring_nf) ih - hdiff

/-! ## The multivariate split -/

/-- The normalized first-kind Chebyshev factor `c_i = k⁻¹ T_k(X_i)`. -/
def putinarSplitC (k : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C ((k : ℝ)⁻¹) * embedUnivariate i (chebyshevT k)

/-- The residual factor `s_i = g_i - a_i`. -/
def putinarSplitS (k : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  BoxSemialgebraicGenerator i - putinarPairFactor k i

/-- A root in the explicit triangular SOS decomposition of `s_i`. -/
def putinarSplitRoot (i : Fin n) (q : ℕ) : MvPolynomial (Fin n) ℝ :=
  BoxSemialgebraicGenerator i *
    embedUnivariate i (Polynomial.Chebyshev.U ℝ (q : ℤ))

/-- The explicit triangular sum of squares for the residual factor. -/
def putinarSplitSquareSum (k : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ t ∈ Finset.range (k - 1), ∑ q ∈ Finset.range (t + 1), putinarSplitRoot i q ^ 2

/-- The split is definitionally exhaustive: `g_i = s_i + a_i`. -/
theorem boxGenerator_eq_putinarSplitS_add_factor (k : ℕ) (i : Fin n) :
    BoxSemialgebraicGenerator i = putinarSplitS k i + putinarPairFactor k i := by
  simp [putinarSplitS]

/-- The complementary localized factor is the explicit square `c_i²`. -/
theorem putinarPairMu_sub_factor_eq_putinarSplitC_sq
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    MvPolynomial.C (putinarPairMu k) - putinarPairFactor k i =
      putinarSplitC k i ^ 2 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < k))
  have hpell := one_sub_embed_chebyshevT_sq k hk i
  simp only [putinarSplitC, putinarPairFactor, putinarPairMu, delta]
  have hscalar : 1 / (k : ℝ) ^ 2 = (k : ℝ)⁻¹ ^ 2 := by
    field_simp
  rw [hscalar]
  rw [show BoxSemialgebraicGenerator i * putinarPairU k i ^ 2 =
      1 - embedUnivariate i (chebyshevT k) ^ 2 by
        rw [hpell]
        ring]
  rw [MvPolynomial.C_pow]
  ring


private theorem embed_chebyshevSplitTriangularSum (k : ℕ) (i : Fin n) :
    embedUnivariate i (chebyshevSplitTriangularSum k) =
      ∑ t ∈ Finset.range (k - 1),
        ∑ q ∈ Finset.range (t + 1),
          embedUnivariate i (Polynomial.Chebyshev.U ℝ (q : ℤ)) ^ 2 := by
  simp [chebyshevSplitTriangularSum, chebyshevUSqPrefix]

/-- The triangular square sum is the generator square times the lifted
univariate triangular sum. -/
theorem putinarSplitSquareSum_eq_generator_sq_mul (k : ℕ) (i : Fin n) :
    putinarSplitSquareSum k i =
      BoxSemialgebraicGenerator i ^ 2 *
        embedUnivariate i (chebyshevSplitTriangularSum k) := by
  rw [embed_chebyshevSplitTriangularSum]
  unfold putinarSplitSquareSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  unfold putinarSplitRoot
  ring

/-- The residual has the explicit finite triangular SOS decomposition. -/
theorem putinarSplitS_eq_scaled_squareSum
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    putinarSplitS k i =
      MvPolynomial.C (4 * putinarPairMu k) * putinarSplitSquareSum k i := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < k))
  have huni := chebyshev_sq_sub_U_sq_eq_triangular k hk
  have hembedfour :
      embedUnivariate i (4 : Polynomial ℝ) = (4 : MvPolynomial (Fin n) ℝ) :=
    map_ofNat (embedUnivariate i) 4
  have hlift :
      MvPolynomial.C ((k : ℝ) ^ 2) -
          embedUnivariate i (Polynomial.Chebyshev.U ℝ ((k - 1 : ℕ) : ℤ)) ^ 2 =
        (4 : MvPolynomial (Fin n) ℝ) * BoxSemialgebraicGenerator i *
          embedUnivariate i (chebyshevSplitTriangularSum k) := by
    simpa [embedUnivariate_one_sub_sq, hembedfour] using congrArg (embedUnivariate i) huni
  have hscalar : (1 / (k : ℝ) ^ 2) * (k : ℝ) ^ 2 = 1 := by field_simp
  have hCscalar :
      (MvPolynomial.C (1 / (k : ℝ) ^ 2) : MvPolynomial (Fin n) ℝ) *
        MvPolynomial.C ((k : ℝ) ^ 2) = 1 := by
    rw [← MvPolynomial.C_mul, hscalar, MvPolynomial.C_1]
  have hCfour :
      (4 : MvPolynomial (Fin n) ℝ) * MvPolynomial.C (1 / (k : ℝ) ^ 2) =
        MvPolynomial.C (4 * (1 / (k : ℝ) ^ 2)) := by
    change MvPolynomial.C 4 * MvPolynomial.C (1 / (k : ℝ) ^ 2) = _
    rw [← MvPolynomial.C_mul]
  rw [putinarSplitSquareSum_eq_generator_sq_mul]
  simp only [putinarSplitS, putinarPairFactor, putinarPairMu, delta]
  unfold putinarPairU
  calc
    BoxSemialgebraicGenerator i -
        MvPolynomial.C (1 / (k : ℝ) ^ 2) *
          (BoxSemialgebraicGenerator i *
            embedUnivariate i (Polynomial.Chebyshev.U ℝ (k - 1 : ℤ)) ^ 2) =
        MvPolynomial.C (1 / (k : ℝ) ^ 2) * BoxSemialgebraicGenerator i *
          (MvPolynomial.C ((k : ℝ) ^ 2) -
            embedUnivariate i (Polynomial.Chebyshev.U ℝ ((k - 1 : ℕ) : ℤ)) ^ 2) := by
      rw [show (k - 1 : ℤ) = ((k - 1 : ℕ) : ℤ) by omega]
      linear_combination (norm := ring_nf) -BoxSemialgebraicGenerator i * hCscalar
    _ = MvPolynomial.C (1 / (k : ℝ) ^ 2) * BoxSemialgebraicGenerator i *
          ((4 : MvPolynomial (Fin n) ℝ) * BoxSemialgebraicGenerator i *
            embedUnivariate i (chebyshevSplitTriangularSum k)) := by rw [hlift]
    _ = MvPolynomial.C (4 * (1 / (k : ℝ) ^ 2)) *
          (BoxSemialgebraicGenerator i ^ 2 *
            embedUnivariate i (chebyshevSplitTriangularSum k)) := by
      linear_combination (norm := ring_nf)
        (BoxSemialgebraicGenerator i ^ 2 *
          embedUnivariate i (chebyshevSplitTriangularSum k)) * hCfour


/-- Every root occurring in the triangular decomposition has degree at most `k`. -/
theorem putinarSplitRoot_totalDegree_le
    (k : ℕ) (i : Fin n) (t q : ℕ)
    (ht : t ∈ Finset.range (k - 1)) (hq : q ∈ Finset.range (t + 1)) :
    (putinarSplitRoot i q).totalDegree ≤ k := by
  have hqk : q + 2 ≤ k := by
    simp only [Finset.mem_range] at ht hq
    omega
  unfold putinarSplitRoot
  calc
    (BoxSemialgebraicGenerator i *
        embedUnivariate i (Polynomial.Chebyshev.U ℝ (q : ℤ))).totalDegree ≤
        (BoxSemialgebraicGenerator i).totalDegree +
          (embedUnivariate i (Polynomial.Chebyshev.U ℝ (q : ℤ))).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 2 + q := by
      gcongr
      · exact boxSemialgebraicGenerator_totalDegree_le_two i
      · exact (totalDegree_embedUnivariate i _).trans_eq
          (Polynomial.Chebyshev.natDegree_U_natCast ℝ q)
    _ ≤ k := by omega

/-- The normalized first-kind factor has degree at most `k`. -/
theorem putinarSplitC_totalDegree_le (k : ℕ) (i : Fin n) :
    (putinarSplitC k i).totalDegree ≤ k := by
  unfold putinarSplitC
  calc
    (MvPolynomial.C ((k : ℝ)⁻¹) * embedUnivariate i (chebyshevT k)).totalDegree ≤
        (MvPolynomial.C ((k : ℝ)⁻¹)).totalDegree +
          (embedUnivariate i (chebyshevT k)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + k := by
      gcongr
      · simp
      · exact (totalDegree_embedUnivariate i _).trans_eq (natDegree_chebyshevT k)
    _ = k := by omega

/-- The localized factor `a_i` has degree at most `2k`. -/
theorem putinarPairFactor_totalDegree_le
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    (putinarPairFactor k i).totalDegree ≤ 2 * k := by
  unfold putinarPairFactor putinarPairU
  have hU :
      (embedUnivariate i (Polynomial.Chebyshev.U ℝ (k - 1 : ℤ))).totalDegree ≤ k - 1 := by
    apply totalDegree_embedUnivariate i _ |>.trans
    rw [Polynomial.Chebyshev.natDegree_U]
    have hcast : ((k - 1 : ℤ) + 1).natAbs = k := by
      rw [show (k - 1 : ℤ) + 1 = (k : ℤ) by omega]
      exact Int.natAbs_natCast k
    rw [hcast]
  calc
    (MvPolynomial.C (putinarPairMu k) *
        (BoxSemialgebraicGenerator i *
          embedUnivariate i (Polynomial.Chebyshev.U ℝ (k - 1 : ℤ)) ^ 2)).totalDegree ≤
        (MvPolynomial.C (putinarPairMu k)).totalDegree +
          (BoxSemialgebraicGenerator i *
            embedUnivariate i (Polynomial.Chebyshev.U ℝ (k - 1 : ℤ)) ^ 2).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + (2 + 2 * (k - 1)) := by
      apply Nat.add_le_add
      · simp
      · exact (MvPolynomial.totalDegree_mul _ _).trans
          (Nat.add_le_add (boxSemialgebraicGenerator_totalDegree_le_two i)
            ((MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hU)))
    _ = 2 * k := by omega

/-- The residual factor `s_i` has degree at most `2k`. -/
theorem putinarSplitS_totalDegree_le
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    (putinarSplitS k i).totalDegree ≤ 2 * k := by
  unfold putinarSplitS
  exact (MvPolynomial.totalDegree_sub _ _).trans
    (max_le (boxSemialgebraicGenerator_totalDegree_le_two i |>.trans (by omega))
      (putinarPairFactor_totalDegree_le k hk i))

/-- The explicit triangular square sum is an SOS. -/
theorem putinarSplitSquareSum_isSOS (k : ℕ) (i : Fin n) :
    IsSOS (putinarSplitSquareSum k i) := by
  unfold putinarSplitSquareSum
  apply IsSOS_sum_finset
  intro t ht
  apply IsSOS_sum_finset
  intro q hq
  exact IsSOS_sq _

/-- The residual factor is SOS by the explicit finite Chebyshev decomposition;
no univariate nonnegativity-to-SOS theorem is used. -/
theorem putinarSplitS_isSOS
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) : IsSOS (putinarSplitS k i) := by
  rw [putinarSplitS_eq_scaled_squareSum k hk i]
  apply IsSOS_nonneg_scale (putinarSplitSquareSum_isSOS k i)
  unfold putinarPairMu delta
  positivity

/-- The complete explicit SOS polynomial has degree at most `2k`. -/
theorem putinarSplitSquareSum_totalDegree_le
    (k : ℕ) (i : Fin n) : (putinarSplitSquareSum k i).totalDegree ≤ 2 * k := by
  unfold putinarSplitSquareSum
  apply MvPolynomial.totalDegree_finsetSum_le
  intro t ht
  apply MvPolynomial.totalDegree_finsetSum_le
  intro q hq
  exact (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left 2 (putinarSplitRoot_totalDegree_le k i t q ht hq))


/-- The manuscript weighted square sum, with zero-based Chebyshev index `q`. -/
def putinarSplitWeightedSquareSum (k : ℕ) (i : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ q ∈ Finset.range (k - 1),
    MvPolynomial.C ((k - 1 - q : ℕ) : ℝ) * putinarSplitRoot i q ^ 2

private def putinarSplitWeightedAux (m : ℕ) (i : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ q ∈ Finset.range m,
    MvPolynomial.C ((m - q : ℕ) : ℝ) * putinarSplitRoot i q ^ 2

private theorem putinarSplitWeightedAux_succ (m : ℕ) (i : Fin n) :
    putinarSplitWeightedAux (m + 1) i =
      putinarSplitWeightedAux m i +
        ∑ q ∈ Finset.range (m + 1), putinarSplitRoot i q ^ 2 := by
  unfold putinarSplitWeightedAux
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show m + 1 - m = 1 by omega]
  simp only [Nat.cast_one, MvPolynomial.C_1, one_mul]
  rw [← add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hqm : q < m := Finset.mem_range.mp hq
  have hsub : m + 1 - q = (m - q) + 1 := by omega
  rw [hsub, Nat.cast_add, Nat.cast_one, map_add, MvPolynomial.C_1]
  ring

private theorem putinarSplitTriangularSum_eq_weightedAux
    (m : ℕ) (i : Fin n) :
    (∑ t ∈ Finset.range m,
      ∑ q ∈ Finset.range (t + 1), putinarSplitRoot i q ^ 2) =
        putinarSplitWeightedAux m i := by
  induction m with
  | zero => simp [putinarSplitWeightedAux]
  | succ m ih =>
      rw [Finset.sum_range_succ, putinarSplitWeightedAux_succ, ih]

/-- The triangular implementation is exactly the manuscript weighted sum:
the root with index `q` has multiplicity `k - 1 - q`. -/
theorem putinarSplitSquareSum_eq_weightedSquareSum (k : ℕ) (i : Fin n) :
    putinarSplitSquareSum k i = putinarSplitWeightedSquareSum k i := by
  unfold putinarSplitSquareSum putinarSplitWeightedSquareSum
  exact putinarSplitTriangularSum_eq_weightedAux (k - 1) i

/-- Literal weighted form of the explicit Chebyshev split:
`(4/k²) ∑_{q<k-1} (k-1-q) (g_i U_q(X_i))²`. -/
theorem putinarSplitS_eq_weighted_squareSum
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    putinarSplitS k i =
      MvPolynomial.C (4 * putinarPairMu k) * putinarSplitWeightedSquareSum k i := by
  rw [putinarSplitS_eq_scaled_squareSum k hk i,
    putinarSplitSquareSum_eq_weightedSquareSum]


/-- The normalized second-kind factor has degree at most `k - 1`. -/
theorem putinarPairQ_totalDegree_le
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    (putinarPairQ k i).totalDegree ≤ k - 1 := by
  unfold putinarPairQ putinarPairU
  have hind : (k - 1 : ℤ) = ((k - 1 : ℕ) : ℤ) := by omega
  calc
    (MvPolynomial.C (k : ℝ)⁻¹ *
        embedUnivariate i (Polynomial.Chebyshev.U ℝ (k - 1 : ℤ))).totalDegree ≤
      (MvPolynomial.C (k : ℝ)⁻¹).totalDegree +
        (embedUnivariate i (Polynomial.Chebyshev.U ℝ (k - 1 : ℤ))).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + (k - 1) := by
      apply Nat.add_le_add
      · simp
      · rw [hind]
        exact (totalDegree_embedUnivariate i _).trans_eq
          (Polynomial.Chebyshev.natDegree_U_natCast ℝ (k - 1))
    _ = k - 1 := by omega

/-- On the cube, the localized and residual factors satisfy the manuscript
bounds `0 ≤ a_i ≤ μ` and `0 ≤ s_i ≤ g_i`. -/
theorem putinarSplit_bounds_on_hypercube
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    0 ≤ MvPolynomial.eval x (putinarPairFactor k i) ∧
      MvPolynomial.eval x (putinarPairFactor k i) ≤ putinarPairMu k ∧
      0 ≤ MvPolynomial.eval x (putinarSplitS k i) ∧
      MvPolynomial.eval x (putinarSplitS k i) ≤
        MvPolynomial.eval x (BoxSemialgebraicGenerator i) := by
  have hg : 0 ≤ MvPolynomial.eval x (BoxSemialgebraicGenerator i) :=
    BoxSemialgebraicGenerator_nonneg_on_hypercube i x hx
  have ha : 0 ≤ MvPolynomial.eval x (putinarPairFactor k i) := by
    rw [putinarPairFactor_eq_generator_mul_q_sq k hk i]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow]
    positivity
  have hs : 0 ≤ MvPolynomial.eval x (putinarSplitS k i) :=
    IsSOS_nonneg _ (putinarSplitS_isSOS k hk i) x (Set.mem_univ x)
  have ha_le : MvPolynomial.eval x (putinarPairFactor k i) ≤ putinarPairMu k := by
    have hcomp := congrArg (MvPolynomial.eval x)
      (putinarPairMu_sub_factor_eq_putinarSplitC_sq k hk i)
    simp only [map_sub, MvPolynomial.eval_C, map_pow] at hcomp
    nlinarith [sq_nonneg (MvPolynomial.eval x (putinarSplitC k i))]
  have hs_le : MvPolynomial.eval x (putinarSplitS k i) ≤
      MvPolynomial.eval x (BoxSemialgebraicGenerator i) := by
    have hsplit := congrArg (MvPolynomial.eval x)
      (boxGenerator_eq_putinarSplitS_add_factor k i)
    simp only [map_add] at hsplit
    linarith
  exact ⟨ha, ha_le, hs, hs_le⟩


/-- The manuscript formula in literal zero-based notation:
`(4/k²) g_i² ∑_{q < k-1} (k-1-q) U_q(X_i)²`. -/
theorem putinarSplitS_eq_explicit_chebyshev_sum
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    putinarSplitS k i =
      MvPolynomial.C (4 * putinarPairMu k) * BoxSemialgebraicGenerator i ^ 2 *
        ∑ q ∈ Finset.range (k - 1),
          MvPolynomial.C ((k - 1 - q : ℕ) : ℝ) *
            embedUnivariate i (Polynomial.Chebyshev.U ℝ (q : ℤ)) ^ 2 := by
  rw [putinarSplitS_eq_weighted_squareSum k hk i]
  have hweighted :
      putinarSplitWeightedSquareSum k i = BoxSemialgebraicGenerator i ^ 2 *
        ∑ q ∈ Finset.range (k - 1),
          MvPolynomial.C ((k - 1 - q : ℕ) : ℝ) *
            embedUnivariate i (Polynomial.Chebyshev.U ℝ (q : ℤ)) ^ 2 := by
    unfold putinarSplitWeightedSquareSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    unfold putinarSplitRoot
    ring
  rw [hweighted]
  ring

end QuarticConvergence
end OptimalConvergenceRates

end
