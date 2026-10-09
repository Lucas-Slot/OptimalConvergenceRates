/-
  Root-count-free angular estimates for finite families of circle polynomials.

  The family is always packaged as one Euclidean vector.  Consequently the
  constants below do not contain the number of roots.  The sine-removal
  lemmas use exact factorizations and multiplication/cancellation only; no
  totalized quotient by a sine is introduced.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.CircleRoots
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ParityComponents
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SignOrthogonality
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SignedCircle
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PositiveKernelContraction
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.LiftRegularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Common.VectorPolynomialEstimates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open MvPolynomial Finset Set
open OptimalConvergenceRates.SphereBallTransfers
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-! ## Compatibility between the two finite-vector packages -/

/-- `finiteEuclideanVector` has exactly the square-root-of-sum-of-squares norm
used by the pre-existing SOS vector estimates. -/
theorem norm_finiteEuclideanVector_eq_interiorVecNorm {N : ℕ} {X : Type*}
    (b : Fin N → X → ℝ) (x : X) :
    ‖finiteEuclideanVector b x‖ = interiorVecNorm (fun i ↦ b i x) := by
  have hleft := finiteEuclideanVector_norm_sq b x
  have hright : interiorVecNorm (fun i : Fin N ↦ b i x) ^ 2 =
      ∑ i, (b i x) ^ 2 := by
    unfold interiorVecNorm interiorVecSqNorm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg (b i x))
  have hleft_nonneg : 0 ≤ ‖finiteEuclideanVector b x‖ := norm_nonneg _
  have hright_nonneg : 0 ≤ interiorVecNorm (fun i : Fin N ↦ b i x) :=
    interiorVecNorm_nonneg _
  nlinarith

/-- The repository's vector Bernstein estimate, stated directly in the norm
used for finite root families.  Its constant is independent of `N`. -/
theorem norm_finiteEuclideanVector_derivative_le_bernstein
    {N d : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ d)
    (hbound : ∀ t : ℝ, |t| ≤ 1 →
      ‖finiteEuclideanVector (fun i u ↦ (P i).eval u) t‖ ≤ M) :
    ‖finiteEuclideanVector
        (fun i (_u : Unit) ↦ (Polynomial.derivative (P i)).eval 0) ()‖ ≤
      2 * (d : ℝ) * M := by
  rw [norm_finiteEuclideanVector_eq_interiorVecNorm]
  apply interior_bernstein_vector_first_derivative_unit P hM hdeg
  intro t ht
  calc
    interiorVecNorm (fun i : Fin N ↦ (P i).eval t) =
        ‖finiteEuclideanVector (fun i u ↦ (P i).eval u) t‖ :=
      (norm_finiteEuclideanVector_eq_interiorVecNorm
        (fun i u ↦ (P i).eval u) t).symm
    _ ≤ M := hbound t ht

/-- Sum-of-squares form of the same vector Bernstein estimate. -/
theorem sum_sq_derivative_le_bernstein
    {N d : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ d)
    (hbound : ∀ t : ℝ, |t| ≤ 1 →
      ‖finiteEuclideanVector (fun i u ↦ (P i).eval u) t‖ ≤ M) :
    ∑ i, ((Polynomial.derivative (P i)).eval 0) ^ 2 ≤
      (2 * (d : ℝ) * M) ^ 2 := by
  let b : Fin N → Unit → ℝ :=
    fun i _ ↦ (Polynomial.derivative (P i)).eval 0
  have hnorm : ‖finiteEuclideanVector b ()‖ ≤ 2 * (d : ℝ) * M := by
    exact norm_finiteEuclideanVector_derivative_le_bernstein P hM hdeg hbound
  have hright : 0 ≤ 2 * (d : ℝ) * M := by positivity
  have hsq := (sq_le_sq₀ (norm_nonneg (finiteEuclideanVector b ())) hright).2 hnorm
  rw [finiteEuclideanVector_norm_sq] at hsq
  simpa [b] using hsq

/-! ## Algebraic angular derivatives -/

/-- A partial derivative in a paired circle variable lowers total degree by one. -/
private theorem totalDegree_pderiv_cubeCircle_le_pred {n : ℕ}
    (i : CubeCircleVar n) (p : MvPolynomial (CubeCircleVar n) ℝ) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, pderiv_monomial]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  by_cases hsi : s i = 0
  · simp [hsi]
  · calc
      (monomial (s - Finsupp.single i 1) (coeff s p * ↑(s i))).totalDegree
          ≤ (s - Finsupp.single i 1).sum fun _ e ↦ e :=
        MvPolynomial.totalDegree_monomial_le _ _
      _ ≤ p.totalDegree - 1 := by
        have hsumlt :
            (s - Finsupp.single i 1).sum (fun _ e ↦ e) <
              s.sum (fun _ e ↦ e) := by
          rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl),
            Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
          apply Finset.sum_lt_sum
          · intro j _
            exact Nat.sub_le _ _
          · refine ⟨i, Finset.mem_univ _, ?_⟩
            have hpos : 0 < s i := by omega
            have hsub : s i - 1 < s i := Nat.sub_lt hpos (by omega)
            simpa using hsub
        have hsdeg : s.sum (fun _ e ↦ e) ≤ p.totalDegree :=
          MvPolynomial.le_totalDegree hs
        omega

/-- A circle rotation does not increase total degree. -/
theorem circleRotationDeriv_totalDegree_le {n : ℕ} (i : Fin n)
    (p : MvPolynomial (CubeCircleVar n) ℝ) :
    (circleRotationDeriv i p).totalDegree ≤ p.totalDegree := by
  by_cases hp : p.totalDegree = 0
  · have hpC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp
    rw [hpC]
    simp [circleRotationDeriv]
  · have hdegree : 1 ≤ p.totalDegree := by omega
    have hleft :
        (X (i, false) * pderiv (i, true) p).totalDegree ≤
          p.totalDegree := by
      calc
        (X (i, false) * pderiv (i, true) p).totalDegree ≤
            (X (i, false) : MvPolynomial (CubeCircleVar n) ℝ).totalDegree +
              (pderiv (i, true) p).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ 1 + (p.totalDegree - 1) := by
          rw [MvPolynomial.totalDegree_X]
          exact Nat.add_le_add_left
            (totalDegree_pderiv_cubeCircle_le_pred (i, true) p) 1
        _ = p.totalDegree := by omega
    have hright :
        (X (i, true) * pderiv (i, false) p).totalDegree ≤
          p.totalDegree := by
      calc
        (X (i, true) * pderiv (i, false) p).totalDegree ≤
            (X (i, true) : MvPolynomial (CubeCircleVar n) ℝ).totalDegree +
              (pderiv (i, false) p).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ 1 + (p.totalDegree - 1) := by
          rw [MvPolynomial.totalDegree_X]
          exact Nat.add_le_add_left
            (totalDegree_pderiv_cubeCircle_le_pred (i, false) p) 1
        _ = p.totalDegree := by omega
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le hleft hright)

@[simp] theorem circleRotationDeriv_C_mul {n : ℕ} (i : Fin n) (c : ℝ)
    (p : MvPolynomial (CubeCircleVar n) ℝ) :
    circleRotationDeriv i (MvPolynomial.C c * p) =
      MvPolynomial.C c * circleRotationDeriv i p := by
  rw [circleRotationDeriv_mul]
  simp [circleRotationDeriv]

theorem circleRotationDeriv_finset_sum {n : ℕ} {ι : Type*}
    (i : Fin n) (s : Finset ι)
    (p : ι → MvPolynomial (CubeCircleVar n) ℝ) :
    circleRotationDeriv i (∑ j ∈ s, p j) =
      ∑ j ∈ s, circleRotationDeriv i (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih => simp [hjs, ih, circleRotationDeriv_add]

/-- Ordered iteration of angular rotation derivations. -/
def iteratedCircleRotationDeriv {n : ℕ} :
    List (Fin n) → MvPolynomial (CubeCircleVar n) ℝ →
      MvPolynomial (CubeCircleVar n) ℝ
  | [], p => p
  | i :: is, p => circleRotationDeriv i (iteratedCircleRotationDeriv is p)

@[simp] theorem iteratedCircleRotationDeriv_nil {n : ℕ}
    (p : MvPolynomial (CubeCircleVar n) ℝ) :
    iteratedCircleRotationDeriv [] p = p := rfl

@[simp] theorem iteratedCircleRotationDeriv_cons {n : ℕ} (i : Fin n)
    (is : List (Fin n)) (p : MvPolynomial (CubeCircleVar n) ℝ) :
    iteratedCircleRotationDeriv (i :: is) p =
      circleRotationDeriv i (iteratedCircleRotationDeriv is p) := rfl

/-- Every ordered mixed angular derivative preserves the original total-degree
bound. -/
theorem iteratedCircleRotationDeriv_totalDegree_le {n : ℕ}
    (is : List (Fin n)) (p : MvPolynomial (CubeCircleVar n) ℝ) :
    (iteratedCircleRotationDeriv is p).totalDegree ≤ p.totalDegree := by
  induction is with
  | nil => simp
  | cons i is ih =>
      exact (circleRotationDeriv_totalDegree_le i _).trans ih

/-! ## Jordan's inequality and one-coordinate sine removal -/

/-- A rearranged form of Jordan's inequality which is convenient for
cancelling an explicit sine factor. -/
theorem abs_le_pi_div_two_mul_abs_sin {t : ℝ} (ht : |t| ≤ Real.pi / 2) :
    |t| ≤ (Real.pi / 2) * |Real.sin t| := by
  have hJordan := Real.mul_abs_le_abs_sin ht
  calc
    |t| = (Real.pi / 2) * ((2 / Real.pi) * |t|) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ (Real.pi / 2) * |Real.sin t| :=
      mul_le_mul_of_nonneg_left hJordan (by positivity)

/-- One-coordinate odd-sine removal away from the sine zero.  The hypothesis
is an exact product identity, not a definition by division. -/
theorem oddSineRemoval_one_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P V D : ℝ → E} {L t : ℝ}
    (hL : 0 ≤ L) (ht : |t| ≤ Real.pi / 2) (ht0 : t ≠ 0)
    (hfactor : ∀ u, P u = Real.sin u • V u)
    (hderiv : ∀ u, HasDerivAt P (D u) u)
    (hDbound : ∀ u, ‖D u‖ ≤ L) :
    ‖V t‖ ≤ (Real.pi / 2) * L := by
  have hmv : ‖P t - P 0‖ ≤ L * ‖t - 0‖ := by
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (s := (Set.univ : Set ℝ)) (f := P) (x := 0) (y := t)
      (fun u _ ↦ (hderiv u).differentiableAt)
      (fun u _ ↦ by simpa [(hderiv u).deriv] using hDbound u)
      convex_univ (Set.mem_univ _) (Set.mem_univ _)
  have hP0 : P 0 = 0 := by simp [hfactor]
  have hsin_pos : 0 < |Real.sin t| := by
    have habs_pos : 0 < |t| := abs_pos.mpr ht0
    have hcoef : 0 < 2 / Real.pi := div_pos (by norm_num) Real.pi_pos
    exact lt_of_lt_of_le (mul_pos hcoef habs_pos) (Real.mul_abs_le_abs_sin ht)
  have hscaled : |Real.sin t| * ‖V t‖ ≤ |t| * L := by
    simpa [hfactor, hP0, norm_smul, Real.norm_eq_abs, mul_comm] using hmv
  have hangle := abs_le_pi_div_two_mul_abs_sin ht
  have hcancel : |Real.sin t| * ‖V t‖ ≤
      |Real.sin t| * ((Real.pi / 2) * L) := by
    calc
      |Real.sin t| * ‖V t‖ ≤ |t| * L := hscaled
      _ ≤ ((Real.pi / 2) * |Real.sin t|) * L :=
        mul_le_mul_of_nonneg_right hangle hL
      _ = |Real.sin t| * ((Real.pi / 2) * L) := by ring
  nlinarith

/-- One-coordinate odd-sine removal including the sine zero.  At zero the
ordinary product rule identifies the derivative of `sin t • V t` with `V 0`;
thus no quotient is used even there. -/
theorem oddSineRemoval_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P V D W : ℝ → E} {L t : ℝ}
    (hL : 0 ≤ L) (ht : |t| ≤ Real.pi / 2)
    (hfactor : ∀ u, P u = Real.sin u • V u)
    (hPderiv : ∀ u, HasDerivAt P (D u) u)
    (hVderiv : ∀ u, HasDerivAt V (W u) u)
    (hDbound : ∀ u, ‖D u‖ ≤ L) :
    ‖V t‖ ≤ (Real.pi / 2) * L := by
  by_cases ht0 : t = 0
  · subst t
    have hprod : HasDerivAt (fun u ↦ Real.sin u • V u) (V 0) 0 := by
      simpa using (Real.hasDerivAt_sin 0).smul (hVderiv 0)
    have hPasV : HasDerivAt P (V 0) 0 :=
      hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u ↦ hfactor u))
    have hDV : D 0 = V 0 := (hPderiv 0).unique hPasV
    calc
      ‖V 0‖ = ‖D 0‖ := by rw [hDV]
      _ ≤ L := hDbound 0
      _ ≤ (Real.pi / 2) * L := by
        have hhalf : 1 ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
        simpa using mul_le_mul_of_nonneg_right hhalf hL
  · exact oddSineRemoval_one_ne_zero hL ht ht0 hfactor hPderiv hDbound

/-! ## Iterated fundamental-theorem-of-calculus estimate -/

@[simp] theorem replaceAngle_apply_same {n : ℕ} (theta : Fin n → ℝ)
    (i : Fin n) (t : ℝ) :
    replaceAngle theta i t i = t := by
  simp [replaceAngle]

theorem replaceAngle_apply_of_ne {n : ℕ} (theta : Fin n → ℝ)
    {i j : Fin n} (hji : j ≠ i) (t : ℝ) :
    replaceAngle theta i t j = theta j := by
  simp [replaceAngle, hji]

@[simp] theorem replaceAngle_replaceAngle_same {n : ℕ}
    (theta : Fin n → ℝ) (i : Fin n) (s t : ℝ) :
    replaceAngle (replaceAngle theta i s) i t = replaceAngle theta i t := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [replaceAngle_apply_of_ne _ hji]

/-- An abstract mixed angular derivative tower.  `F pref` is the derivative
obtained after the coordinates in `pref` have been processed, in reverse
chronological order. -/
def IsAngularDerivativeTower
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : List (Fin n) → (Fin n → ℝ) → E) : Prop :=
  ∀ (pref : List (Fin n)) (i : Fin n) (theta : Fin n → ℝ),
    HasDerivAt
      (fun t ↦ F pref (replaceAngle theta i t))
      (F (i :: pref) theta) (theta i)

/-- Oddness in every not-yet-differentiated coordinate, phrased as the exact
vanishing property needed by repeated FTC.  This formulation is stable under
differentiation in distinct coordinates. -/
def IsOddAngularDerivativeTower
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (indices : List (Fin n)) (F : List (Fin n) → (Fin n → ℝ) → E) : Prop :=
  ∀ (pref : List (Fin n)) (i : Fin n) (theta : Fin n → ℝ),
    i ∈ indices → i ∉ pref → F pref (replaceAngle theta i 0) = 0

private theorem iteratedOddFtcBound_aux
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (hderiv : IsAngularDerivativeTower F)
    {support : List (Fin n)} (hodd : IsOddAngularDerivativeTower support F)
    {L : ℝ} (pref remaining : List (Fin n))
    (hnodup : remaining.Nodup)
    (hdisjoint : ∀ i ∈ remaining, i ∉ pref)
    (hsupport : ∀ i ∈ remaining, i ∈ support)
    (hterminal : ∀ theta,
      ‖F (remaining.reverse ++ pref) theta‖ ≤ L)
    (theta : Fin n → ℝ) :
    ‖F pref theta‖ ≤
      (remaining.map (fun i ↦ |theta i|)).prod * L := by
  induction remaining generalizing pref theta with
  | nil =>
      simpa using hterminal theta
  | cons i remaining ih =>
      have hi_remaining : i ∉ remaining := (List.nodup_cons.mp hnodup).1
      have hremaining_nodup : remaining.Nodup := (List.nodup_cons.mp hnodup).2
      have hi_prefix : i ∉ pref := hdisjoint i (by simp)
      have htail_disjoint : ∀ j ∈ remaining, j ∉ i :: pref := by
        intro j hj
        simp only [List.mem_cons, not_or]
        constructor
        · intro hji
          subst j
          exact hi_remaining hj
        · exact hdisjoint j (by simp [hj])
      have htail_terminal : ∀ phi,
          ‖F (remaining.reverse ++ i :: pref) phi‖ ≤ L := by
        intro phi
        simpa [List.reverse_cons, List.append_assoc] using hterminal phi
      have htail (phi : Fin n → ℝ) :
          ‖F (i :: pref) phi‖ ≤
            (remaining.map (fun j ↦ |phi j|)).prod * L :=
        ih (i :: pref) hremaining_nodup htail_disjoint
          (fun j hj ↦ hsupport j (by simp [hj])) htail_terminal phi
      let g : ℝ → E := fun t ↦ F pref (replaceAngle theta i t)
      let gPrime : ℝ → E := fun t ↦ F (i :: pref) (replaceAngle theta i t)
      have hgderiv (t : ℝ) : HasDerivAt g (gPrime t) t := by
        simpa [g, gPrime] using hderiv pref i (replaceAngle theta i t)
      have hprod_replace (t : ℝ) :
          (remaining.map (fun j ↦ |replaceAngle theta i t j|)).prod =
            (remaining.map (fun j ↦ |theta j|)).prod := by
        congr 1
        apply List.map_congr_left
        intro j hj
        rw [replaceAngle_apply_of_ne]
        intro hji
        subst j
        exact hi_remaining hj
      have hgPrimebound (t : ℝ) :
          ‖gPrime t‖ ≤ (remaining.map (fun j ↦ |theta j|)).prod * L := by
        simpa [gPrime, hprod_replace] using htail (replaceAngle theta i t)
      have hmv : ‖g (theta i) - g 0‖ ≤
          ((remaining.map (fun j ↦ |theta j|)).prod * L) *
            ‖theta i - 0‖ := by
        exact Convex.norm_image_sub_le_of_norm_deriv_le
          (s := (Set.univ : Set ℝ)) (f := g) (x := 0) (y := theta i)
          (fun t _ ↦ (hgderiv t).differentiableAt)
          (fun t _ ↦ by simpa [(hgderiv t).deriv] using hgPrimebound t)
          convex_univ (Set.mem_univ _) (Set.mem_univ _)
      have hg0 : g 0 = 0 :=
        hodd pref i theta (hsupport i (by simp)) hi_prefix
      calc
        ‖F pref theta‖ = ‖g (theta i) - g 0‖ := by
          simp [g, hg0]
        _ ≤ ((remaining.map (fun j ↦ |theta j|)).prod * L) *
              ‖theta i - 0‖ := hmv
        _ = (((i :: remaining).map (fun j ↦ |theta j|)).prod) * L := by
          simp
          ring

/-- Repeated one-dimensional FTC for a finite Euclidean (indeed, arbitrary
normed) vector.  The estimate has no factor depending on the vector dimension:
only the mixed derivative and the coordinate increments occur. -/
theorem iteratedOddFtcBound
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (indices : List (Fin n))
    (hderiv : IsAngularDerivativeTower F)
    (hodd : IsOddAngularDerivativeTower indices F)
    {L : ℝ} (hnodup : indices.Nodup)
    (hterminal : ∀ theta, ‖F indices.reverse theta‖ ≤ L)
    (theta : Fin n → ℝ) :
    ‖F [] theta‖ ≤ (indices.map (fun i ↦ |theta i|)).prod * L := by
  apply iteratedOddFtcBound_aux F hderiv hodd [] indices hnodup
  · simp
  · simp
  · simpa using hterminal

/-- The preceding FTC estimate for a finite family written using the public
`finiteEuclideanVector` constructor. -/
theorem iteratedOddFtcBound_finiteEuclideanVector
    {n N : ℕ}
    (f : List (Fin n) → Fin N → (Fin n → ℝ) → ℝ)
    (indices : List (Fin n))
    (hderiv : ∀ (pref : List (Fin n)) (i : Fin n) (theta : Fin n → ℝ),
      HasDerivAt
        (fun t ↦ finiteEuclideanVector (f pref) (replaceAngle theta i t))
        (finiteEuclideanVector (f (i :: pref)) theta) (theta i))
    (hodd : ∀ (pref : List (Fin n)) (i : Fin n) (theta : Fin n → ℝ),
      i ∈ indices → i ∉ pref →
        finiteEuclideanVector (f pref) (replaceAngle theta i 0) = 0)
    {L : ℝ} (hnodup : indices.Nodup)
    (hterminal : ∀ theta,
      ‖finiteEuclideanVector (f indices.reverse) theta‖ ≤ L)
    (theta : Fin n → ℝ) :
    ‖finiteEuclideanVector (f []) theta‖ ≤
      (indices.map (fun i ↦ |theta i|)).prod * L := by
  let F : List (Fin n) → (Fin n → ℝ) → EuclideanSpace ℝ (Fin N) :=
    fun pref ↦ finiteEuclideanVector (f pref)
  exact iteratedOddFtcBound F indices hderiv hodd hnodup hterminal theta

/-- Strict positivity of the sine on the punctured central half-period, in the
absolute-value form used for cancellation below. -/
theorem abs_sin_pos_of_ne_zero_of_abs_le_pi_div_two {t : ℝ}
    (ht0 : t ≠ 0) (ht : |t| ≤ Real.pi / 2) :
    0 < |Real.sin t| := by
  have habs_pos : 0 < |t| := abs_pos.mpr ht0
  have hcoef : 0 < 2 / Real.pi := div_pos (by norm_num) Real.pi_pos
  exact lt_of_lt_of_le (mul_pos hcoef habs_pos) (Real.mul_abs_le_abs_sin ht)

private theorem list_prod_nonneg_of_forall (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.prod_cons]
      exact mul_nonneg (hxs x (by simp))
        (ih (fun y hy ↦ hxs y (by simp [hy])))

/-- Product form of Jordan inequality for an ordered collection of angles. -/
theorem prod_abs_le_pi_div_two_pow_mul_prod_abs_sin
    {n : ℕ} (indices : List (Fin n)) (theta : Fin n → ℝ)
    (hrange : ∀ i ∈ indices, |theta i| ≤ Real.pi / 2) :
    (indices.map (fun i ↦ |theta i|)).prod ≤
      (Real.pi / 2) ^ indices.length *
        (indices.map (fun i ↦ |Real.sin (theta i)|)).prod := by
  induction indices with
  | nil => simp
  | cons i indices ih =>
      have hi := abs_le_pi_div_two_mul_abs_sin (hrange i (by simp))
      have htail : ∀ j ∈ indices, |theta j| ≤ Real.pi / 2 := by
        intro j hj
        exact hrange j (by simp [hj])
      have hih := ih htail
      have hprod_nonneg :
          0 ≤ (indices.map (fun j ↦ |theta j|)).prod := by
        apply list_prod_nonneg_of_forall
        intro x hx
        rcases List.mem_map.mp hx with ⟨j, _hj, rfl⟩
        exact abs_nonneg _
      calc
        ((i :: indices).map (fun j ↦ |theta j|)).prod =
            |theta i| * (indices.map (fun j ↦ |theta j|)).prod := by simp
        _ ≤ ((Real.pi / 2) * |Real.sin (theta i)|) *
              (indices.map (fun j ↦ |theta j|)).prod :=
          mul_le_mul_of_nonneg_right hi hprod_nonneg
        _ ≤ ((Real.pi / 2) * |Real.sin (theta i)|) *
              ((Real.pi / 2) ^ indices.length *
                (indices.map (fun j ↦ |Real.sin (theta j)|)).prod) :=
          mul_le_mul_of_nonneg_left hih (by positivity)
        _ = (Real.pi / 2) ^ (i :: indices).length *
              ((i :: indices).map (fun j ↦ |Real.sin (theta j)|)).prod := by
          simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
          ring

private theorem abs_prod_sin_eq_prod_abs_sin
    {n : ℕ} (indices : List (Fin n)) (theta : Fin n → ℝ) :
    |(indices.map (fun i ↦ Real.sin (theta i))).prod| =
      (indices.map (fun i ↦ |Real.sin (theta i)|)).prod := by
  induction indices with
  | nil => simp
  | cons i indices ih => simp [ih, abs_mul]

private theorem prod_abs_sin_pos
    {n : ℕ} (indices : List (Fin n)) (theta : Fin n → ℝ)
    (hrange : ∀ i ∈ indices, |theta i| ≤ Real.pi / 2)
    (hnonzero : ∀ i ∈ indices, theta i ≠ 0) :
    0 < (indices.map (fun i ↦ |Real.sin (theta i)|)).prod := by
  induction indices with
  | nil => simp
  | cons i indices ih =>
      have hi : 0 < |Real.sin (theta i)| :=
        abs_sin_pos_of_ne_zero_of_abs_le_pi_div_two
          (hnonzero i (by simp)) (hrange i (by simp))
      have htail_range : ∀ j ∈ indices, |theta j| ≤ Real.pi / 2 := by
        intro j hj
        exact hrange j (by simp [hj])
      have htail_nonzero : ∀ j ∈ indices, theta j ≠ 0 := by
        intro j hj
        exact hnonzero j (by simp [hj])
      simpa using mul_pos hi (ih htail_range htail_nonzero)

/-- Iterated odd-sine removal at points where the displayed sine factors are
nonzero.  `hfactor` is an explicit multiplication identity, and the proof uses
repeated FTC followed by positive cancellation; it never defines a quotient.
The constant `(π/2)^indices.length` is independent of the dimension of `E`. -/
theorem oddSineRemoval_iterated_ne_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (V : (Fin n → ℝ) → E)
    (indices : List (Fin n))
    (hderiv : IsAngularDerivativeTower F)
    (hodd : IsOddAngularDerivativeTower indices F)
    {L : ℝ} (hL : 0 ≤ L) (hnodup : indices.Nodup)
    (hterminal : ∀ phi, ‖F indices.reverse phi‖ ≤ L)
    (theta : Fin n → ℝ)
    (hrange : ∀ i ∈ indices, |theta i| ≤ Real.pi / 2)
    (hnonzero : ∀ i ∈ indices, theta i ≠ 0)
    (hfactor : F [] theta =
      (indices.map (fun i ↦ Real.sin (theta i))).prod • V theta) :
    ‖V theta‖ ≤ (Real.pi / 2) ^ indices.length * L := by
  let A : ℝ := (indices.map (fun i ↦ |theta i|)).prod
  let S : ℝ := (indices.map (fun i ↦ |Real.sin (theta i)|)).prod
  have hftc : ‖F [] theta‖ ≤ A * L := by
    exact iteratedOddFtcBound F indices hderiv hodd hnodup hterminal theta
  have hangle : A ≤ (Real.pi / 2) ^ indices.length * S := by
    exact prod_abs_le_pi_div_two_pow_mul_prod_abs_sin indices theta hrange
  have hSpos : 0 < S := prod_abs_sin_pos indices theta hrange hnonzero
  have hnorm_factor : ‖F [] theta‖ = S * ‖V theta‖ := by
    rw [hfactor, norm_smul, Real.norm_eq_abs]
    exact congrArg (fun x : ℝ ↦ x * ‖V theta‖)
      (abs_prod_sin_eq_prod_abs_sin indices theta)
  have hcancel : S * ‖V theta‖ ≤
      S * ((Real.pi / 2) ^ indices.length * L) := by
    calc
      S * ‖V theta‖ = ‖F [] theta‖ := hnorm_factor.symm
      _ ≤ A * L := hftc
      _ ≤ ((Real.pi / 2) ^ indices.length * S) * L :=
        mul_le_mul_of_nonneg_right hangle hL
      _ = S * ((Real.pi / 2) ^ indices.length * L) := by ring
  nlinarith

/-- Finite-Euclidean-vector specialization of iterated odd-sine removal. -/
theorem oddSineRemoval_iterated_finiteEuclideanVector_ne_zero
    {n N : ℕ}
    (f : List (Fin n) → Fin N → (Fin n → ℝ) → ℝ)
    (v : Fin N → (Fin n → ℝ) → ℝ)
    (indices : List (Fin n))
    (hderiv : ∀ (pref : List (Fin n)) (i : Fin n) (theta : Fin n → ℝ),
      HasDerivAt
        (fun t ↦ finiteEuclideanVector (f pref) (replaceAngle theta i t))
        (finiteEuclideanVector (f (i :: pref)) theta) (theta i))
    (hodd : ∀ (pref : List (Fin n)) (i : Fin n) (theta : Fin n → ℝ),
      i ∈ indices → i ∉ pref →
        finiteEuclideanVector (f pref) (replaceAngle theta i 0) = 0)
    {L : ℝ} (hL : 0 ≤ L) (hnodup : indices.Nodup)
    (hterminal : ∀ phi, ‖finiteEuclideanVector (f indices.reverse) phi‖ ≤ L)
    (theta : Fin n → ℝ)
    (hrange : ∀ i ∈ indices, |theta i| ≤ Real.pi / 2)
    (hnonzero : ∀ i ∈ indices, theta i ≠ 0)
    (hfactor : finiteEuclideanVector (f []) theta =
      (indices.map (fun i ↦ Real.sin (theta i))).prod •
        finiteEuclideanVector v theta) :
    ‖finiteEuclideanVector v theta‖ ≤
      (Real.pi / 2) ^ indices.length * L := by
  let F : List (Fin n) → (Fin n → ℝ) → EuclideanSpace ℝ (Fin N) :=
    fun pref ↦ finiteEuclideanVector (f pref)
  exact oddSineRemoval_iterated_ne_zero F (finiteEuclideanVector v) indices
    hderiv hodd hL hnodup hterminal theta hrange hnonzero hfactor

/-- Perturb exactly the selected zero coordinates by a positive sequence
converging to zero. -/
private def perturbSelectedZeroAngles {n : ℕ}
    (indices : List (Fin n)) (theta : Fin n → ℝ) (m : ℕ) : Fin n → ℝ :=
  fun i ↦ if theta i = 0 ∧ i ∈ indices then 1 / ((m : ℝ) + 1) else theta i

private theorem tendsto_perturbSelectedZeroAngles {n : ℕ}
    (indices : List (Fin n)) (theta : Fin n → ℝ) :
    Filter.Tendsto (fun m ↦ perturbSelectedZeroAngles indices theta m)
      Filter.atTop (nhds theta) := by
  rw [tendsto_pi_nhds]
  intro i
  by_cases hi : theta i = 0 ∧ i ∈ indices
  · simpa [perturbSelectedZeroAngles, hi, hi.1] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · simp [perturbSelectedZeroAngles, hi]

private theorem perturbSelectedZeroAngles_range {n : ℕ}
    (indices : List (Fin n)) (theta : Fin n → ℝ)
    (hrange : ∀ i ∈ indices, |theta i| ≤ Real.pi / 2)
    (m : ℕ) {i : Fin n} (hi : i ∈ indices) :
    |perturbSelectedZeroAngles indices theta m i| ≤ Real.pi / 2 := by
  by_cases hzero : theta i = 0
  · have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hdenom : 1 ≤ (m : ℝ) + 1 := by linarith
    have hdenom_pos : 0 < (m : ℝ) + 1 := by linarith
    have hfrac_nonneg : 0 ≤ 1 / ((m : ℝ) + 1) :=
      div_nonneg (by norm_num) hdenom_pos.le
    have hfrac_le : 1 / ((m : ℝ) + 1) ≤ 1 := by
      exact (div_le_one hdenom_pos).2 hdenom
    have hpi : 1 ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
    rw [perturbSelectedZeroAngles, if_pos ⟨hzero, hi⟩,
      abs_of_nonneg hfrac_nonneg]
    exact hfrac_le.trans hpi
  · simpa [perturbSelectedZeroAngles, hzero] using hrange i hi

private theorem perturbSelectedZeroAngles_ne_zero {n : ℕ}
    (indices : List (Fin n)) (theta : Fin n → ℝ)
    (m : ℕ) {i : Fin n} (hi : i ∈ indices) :
    perturbSelectedZeroAngles indices theta m i ≠ 0 := by
  by_cases hzero : theta i = 0
  · rw [perturbSelectedZeroAngles, if_pos ⟨hzero, hi⟩]
    exact one_div_ne_zero (by positivity)
  · simp [perturbSelectedZeroAngles, hzero]

/-- Iterated odd-sine removal on the whole closed central half-period,
including all sine-zero boundary strata.  Continuity of the residual extends
the punctured estimate; no value is ever defined by division. -/
theorem oddSineRemoval_iterated
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (V : (Fin n → ℝ) → E)
    (indices : List (Fin n))
    (hderiv : IsAngularDerivativeTower F)
    (hodd : IsOddAngularDerivativeTower indices F)
    {L : ℝ} (hL : 0 ≤ L) (hnodup : indices.Nodup)
    (hterminal : ∀ phi, ‖F indices.reverse phi‖ ≤ L)
    (hVcont : Continuous V)
    (hfactor : ∀ phi, F [] phi =
      (indices.map (fun i ↦ Real.sin (phi i))).prod • V phi)
    (theta : Fin n → ℝ)
    (hrange : ∀ i ∈ indices, |theta i| ≤ Real.pi / 2) :
    ‖V theta‖ ≤ (Real.pi / 2) ^ indices.length * L := by
  let thetaSeq : ℕ → (Fin n → ℝ) :=
    fun m ↦ perturbSelectedZeroAngles indices theta m
  have hseq : Filter.Tendsto thetaSeq Filter.atTop (nhds theta) :=
    tendsto_perturbSelectedZeroAngles indices theta
  have hnorm : Filter.Tendsto (fun m ↦ ‖V (thetaSeq m)‖)
      Filter.atTop (nhds ‖V theta‖) :=
    (hVcont.continuousAt.tendsto.comp hseq).norm
  apply le_of_tendsto hnorm
  exact Filter.Eventually.of_forall (fun m ↦
    oddSineRemoval_iterated_ne_zero F V indices hderiv hodd hL hnodup
      hterminal (thetaSeq m)
      (fun i hi ↦ perturbSelectedZeroAngles_range indices theta hrange m hi)
      (fun i hi ↦ perturbSelectedZeroAngles_ne_zero indices theta m hi)
      (hfactor (thetaSeq m)))

/-- Squared form of closed-half-period sine removal. -/
theorem oddSineRemoval_iterated_sq
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (V : (Fin n → ℝ) → E)
    (indices : List (Fin n))
    (hderiv : IsAngularDerivativeTower F)
    (hodd : IsOddAngularDerivativeTower indices F)
    {Q : ℝ} (hQ : 0 ≤ Q) (hnodup : indices.Nodup)
    (hterminal : ∀ phi, ‖F indices.reverse phi‖ ^ 2 ≤ Q)
    (hVcont : Continuous V)
    (hfactor : ∀ phi, F [] phi =
      (indices.map (fun i ↦ Real.sin (phi i))).prod • V phi)
    (theta : Fin n → ℝ)
    (hrange : ∀ i ∈ indices, |theta i| ≤ Real.pi / 2) :
    ‖V theta‖ ^ 2 ≤
      (Real.pi / 2) ^ (2 * indices.length) * Q := by
  have hterminalNorm (phi : Fin n → ℝ) :
      ‖F indices.reverse phi‖ ≤ Real.sqrt Q := by
    have hsqrt_sq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
    have hnorm_nonneg := norm_nonneg (F indices.reverse phi)
    have hsqrt_nonneg := Real.sqrt_nonneg Q
    nlinarith [hterminal phi]
  have hnorm := oddSineRemoval_iterated F V indices hderiv hodd
    (Real.sqrt_nonneg Q) hnodup hterminalNorm hVcont hfactor theta hrange
  have hright_nonneg :
      0 ≤ (Real.pi / 2) ^ indices.length * Real.sqrt Q := by positivity
  have hsquare := (sq_le_sq₀ (norm_nonneg (V theta)) hright_nonneg).2 hnorm
  calc
    ‖V theta‖ ^ 2 ≤
        ((Real.pi / 2) ^ indices.length * Real.sqrt Q) ^ 2 := hsquare
    _ = (Real.pi / 2) ^ (2 * indices.length) * Q := by
      rw [mul_pow, Real.sq_sqrt hQ, ← pow_mul]
      congr 2
      omega

/-- A uniform squared-norm bound for one level of an angular derivative tower. -/
def UniformAngularSqBound
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (pref : List (Fin n)) (Q : ℝ) : Prop :=
  ∀ theta, ‖F pref theta‖ ^ 2 ≤ Q

/-- A scalar Bernstein estimate intrinsic to one block of the product of
circles.  The estimate is uniform in all frozen circle coordinates. -/
def ProductCircleFirstRotationBound (D : ℕ) (K : ℝ) : Prop :=
  ∀ {n : ℕ} (p : MvPolynomial (CubeCircleVar n) ℝ),
    p.totalDegree ≤ D →
    ∀ {M : ℝ}, 0 ≤ M →
      (∀ theta, |MvPolynomial.eval (cosineSineCirclePoint theta) p| ≤ M) →
      ∀ (i : Fin n) (theta : Fin n → ℝ),
        |MvPolynomial.eval (cosineSineCirclePoint theta)
          (circleRotationDeriv i p)| ≤ K * M


/-- The two coordinates used for one circle block. -/
def circleBoolCoordinate : Bool → Fin 2
  | false => 0
  | true => 1

@[simp] theorem circleBoolCoordinate_false : circleBoolCoordinate false = 0 := rfl
@[simp] theorem circleBoolCoordinate_true : circleBoolCoordinate true = 1 := rfl

/-- Freeze every circle block except `i`, leaving a polynomial in the two
coordinates of the `i`-th circle. -/
def circleSliceSubstitution {n : ℕ} (theta : Fin n → ℝ) (i : Fin n)
    (ib : CubeCircleVar n) : MvPolynomial (Fin 2) ℝ :=
  if ib.1 = i then X (circleBoolCoordinate ib.2)
  else C (cosineSineCirclePoint theta ib)

def circleSlicePolynomial {n : ℕ} (theta : Fin n → ℝ) (i : Fin n)
    (p : MvPolynomial (CubeCircleVar n) ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.aeval (circleSliceSubstitution theta i) p

def circleSlicePoint {n : ℕ} (theta : Fin n → ℝ) (i : Fin n)
    (x : Fin 2 → ℝ) (ib : CubeCircleVar n) : ℝ :=
  if ib.1 = i then x (circleBoolCoordinate ib.2)
  else cosineSineCirclePoint theta ib

/-- Evaluation commutes with freezing all but one circle block. -/
theorem eval_circleSlicePolynomial {n : ℕ} (theta : Fin n → ℝ) (i : Fin n)
    (x : Fin 2 → ℝ) (p : MvPolynomial (CubeCircleVar n) ℝ) :
    MvPolynomial.eval x (circleSlicePolynomial theta i p) =
      MvPolynomial.eval (circleSlicePoint theta i x) p := by
  unfold circleSlicePolynomial
  rw [← MvPolynomial.aeval_eq_eval]
  rw [show MvPolynomial.aeval x
      (MvPolynomial.aeval (circleSliceSubstitution theta i) p) =
    ((MvPolynomial.aeval x).comp
      (MvPolynomial.aeval (circleSliceSubstitution theta i))) p from rfl]
  rw [MvPolynomial.comp_aeval]
  change MvPolynomial.eval
    (fun ib ↦ MvPolynomial.eval x (circleSliceSubstitution theta i ib)) p = _
  apply congrArg (fun z : CubeCircleVar n → ℝ ↦ MvPolynomial.eval z p)
  funext ib
  rcases ib with ⟨j, b⟩
  by_cases hji : j = i
  · subst j
    simp [circleSliceSubstitution, circleSlicePoint]
  · simp [circleSliceSubstitution, circleSlicePoint, hji]

/-- Freezing the other blocks cannot increase total degree. -/
theorem circleSlicePolynomial_totalDegree_le {n : ℕ}
    (theta : Fin n → ℝ) (i : Fin n)
    (p : MvPolynomial (CubeCircleVar n) ℝ) :
    (circleSlicePolynomial theta i p).totalDegree ≤ p.totalDegree := by
  unfold circleSlicePolynomial
  have hsub : ∀ ib,
      (circleSliceSubstitution theta i ib).totalDegree ≤ 1 := by
    intro ib
    rcases ib with ⟨j, b⟩
    by_cases hji : j = i
    · subst j
      simp [circleSliceSubstitution]
    · simp [circleSliceSubstitution, hji]
  have hdegree := totalDegree_aeval_le_mul_general
    (circleSliceSubstitution theta i) hsub p
  simpa using hdegree


@[simp] theorem circleSlicePolynomial_add {n : ℕ}
    (theta : Fin n → ℝ) (i : Fin n)
    (p q : MvPolynomial (CubeCircleVar n) ℝ) :
    circleSlicePolynomial theta i (p + q) =
      circleSlicePolynomial theta i p + circleSlicePolynomial theta i q := by
  exact map_add (MvPolynomial.aeval (circleSliceSubstitution theta i)) p q

@[simp] theorem circleSlicePolynomial_mul {n : ℕ}
    (theta : Fin n → ℝ) (i : Fin n)
    (p q : MvPolynomial (CubeCircleVar n) ℝ) :
    circleSlicePolynomial theta i (p * q) =
      circleSlicePolynomial theta i p * circleSlicePolynomial theta i q := by
  exact map_mul (MvPolynomial.aeval (circleSliceSubstitution theta i)) p q

/-- The generator calculation behind commutation with the circle rotation. -/
theorem circleSlicePolynomial_circleRotationDeriv_X {n : ℕ}
    (theta : Fin n → ℝ) (i j : Fin n) (b : Bool) :
    circleSlicePolynomial theta i (circleRotationDeriv i (X (j, b))) =
      rotationDeriv (0 : Fin 2) (1 : Fin 2)
        (circleSlicePolynomial theta i (X (j, b))) := by
  by_cases hji : j = i
  · subst j
    cases b <;>
      simp [circleSlicePolynomial, circleSliceSubstitution,
        circleRotationDeriv, rotationDeriv]
  · cases b <;>
      simp [circleSlicePolynomial, circleSliceSubstitution,
        circleRotationDeriv, rotationDeriv, hji]

/-- Freezing the other blocks intertwines the block rotation with the ordinary
rotation of the two remaining variables. -/
theorem circleSlicePolynomial_circleRotationDeriv {n : ℕ}
    (theta : Fin n → ℝ) (i : Fin n)
    (p : MvPolynomial (CubeCircleVar n) ℝ) :
    circleSlicePolynomial theta i (circleRotationDeriv i p) =
      rotationDeriv (0 : Fin 2) (1 : Fin 2)
        (circleSlicePolynomial theta i p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp [circleSlicePolynomial, circleRotationDeriv, rotationDeriv]
  | add p q hp hq =>
      simp only [circleRotationDeriv_add, circleSlicePolynomial_add,
        rotationDeriv_add, hp, hq]
  | mul_X p ib hp =>
      obtain ⟨j, b⟩ := ib
      have hcircle :
          circleRotationDeriv i (p * X (j, b)) =
            circleRotationDeriv i p * X (j, b) +
              p * circleRotationDeriv i (X (j, b)) :=
        circleRotationDeriv_mul i p (X (j, b))
      have hrot :
          rotationDeriv (0 : Fin 2) (1 : Fin 2)
              (circleSlicePolynomial theta i p *
                circleSlicePolynomial theta i (X (j, b))) =
            rotationDeriv (0 : Fin 2) (1 : Fin 2)
                (circleSlicePolynomial theta i p) *
                circleSlicePolynomial theta i (X (j, b)) +
              circleSlicePolynomial theta i p *
                rotationDeriv (0 : Fin 2) (1 : Fin 2)
                  (circleSlicePolynomial theta i (X (j, b))) := by
        simp only [rotationDeriv, pderiv_mul]
        ring
      rw [hcircle, circleSlicePolynomial_add, circleSlicePolynomial_mul,
        circleSlicePolynomial_mul, hp,
        circleSlicePolynomial_circleRotationDeriv_X theta i j b,
        circleSlicePolynomial_mul]
      exact hrot.symm

/-- Every point of the real unit circle has a simultaneous cosine/sine
parameter. -/
theorem exists_cos_eq_and_sin_eq_of_sq_add_sq_eq_one {x y : ℝ}
    (hxy : x ^ 2 + y ^ 2 = 1) :
    ∃ t : ℝ, Real.cos t = x ∧ Real.sin t = y := by
  have hxlower : -1 ≤ x := by nlinarith [sq_nonneg (x + 1), sq_nonneg y]
  have hxupper : x ≤ 1 := by nlinarith [sq_nonneg (x - 1), sq_nonneg y]
  have hone : 1 - x ^ 2 = y ^ 2 := by nlinarith
  by_cases hy : 0 ≤ y
  · refine ⟨Real.arccos x, Real.cos_arccos hxlower hxupper, ?_⟩
    rw [Real.sin_arccos, hone, Real.sqrt_sq hy]
  · have hyneg : y ≤ 0 := le_of_not_ge hy
    refine ⟨-Real.arccos x, ?_, ?_⟩
    · rw [Real.cos_neg, Real.cos_arccos hxlower hxupper]
    · rw [Real.sin_neg, Real.sin_arccos, hone, Real.sqrt_sq_eq_abs,
        abs_of_nonpos hyneg]
      ring

/-- The product-circle first-rotation Bernstein estimate follows from the
repositorys proved spherical estimate after freezing all other blocks. -/
theorem productCircleFirstRotationBound (D : ℕ) :
    ProductCircleFirstRotationBound D (10 * (D : ℝ)) := by
  intro n p hpdeg M hM hbound i theta
  let q := circleSlicePolynomial theta i p
  have hqdeg : q.totalDegree ≤ D :=
    (circleSlicePolynomial_totalDegree_le theta i p).trans hpdeg
  have hqSup : sphereSupNorm q ≤ M := by
    apply sphereSupNorm_le_of_bound (by omega : 0 < 2)
    intro x hx
    have hxy : x (0 : Fin 2) ^ 2 + x (1 : Fin 2) ^ 2 = 1 := by
      simpa [sphereSet, sphereQuadratic, Fin.sum_univ_two] using hx
    obtain ⟨t, hcost, hsint⟩ :=
      exists_cos_eq_and_sin_eq_of_sq_add_sq_eq_one hxy
    let phi := replaceAngle theta i t
    have hpoint : circleSlicePoint theta i x = cosineSineCirclePoint phi := by
      funext ib
      rcases ib with ⟨j, b⟩
      by_cases hji : j = i
      · subst j
        cases b <;> simp [circleSlicePoint, phi, replaceAngle, hcost, hsint]
      · cases b <;> simp [circleSlicePoint, phi, replaceAngle, hji]
    rw [eval_circleSlicePolynomial, hpoint]
    exact hbound phi
  have hrot := sphereSupNorm_rotationDeriv_le_bernstein
    (by omega : 0 < 2) q hqdeg (0 : Fin 2) (1 : Fin 2)
  have hxmem : (fun j : Fin 2 ↦ if j = 0 then Real.cos (theta i)
      else Real.sin (theta i)) ∈ sphereSet 2 := by
    simp [sphereSet, sphereQuadratic, Fin.sum_univ_two,
      Real.cos_sq_add_sin_sq]
  let x : Fin 2 → ℝ := fun j ↦
    if j = 0 then Real.cos (theta i) else Real.sin (theta i)
  have hx0 : x 0 = Real.cos (theta i) := by simp [x]
  have hx1 : x 1 = Real.sin (theta i) := by simp [x]
  have hslicePoint : circleSlicePoint theta i x = cosineSineCirclePoint theta := by
    funext ib
    rcases ib with ⟨j, b⟩
    by_cases hji : j = i
    · subst j
      cases b <;> simp [circleSlicePoint, hx0, hx1]
    · cases b <;> simp [circleSlicePoint, hji]
  have hpoint := sphereSupNorm_eval_le
    (rotationDeriv (0 : Fin 2) (1 : Fin 2) q) x (by simpa [x] using hxmem)
  calc
    |MvPolynomial.eval (cosineSineCirclePoint theta)
        (circleRotationDeriv i p)| =
        |MvPolynomial.eval x
          (rotationDeriv (0 : Fin 2) (1 : Fin 2) q)| := by
      rw [← circleSlicePolynomial_circleRotationDeriv theta i p,
        eval_circleSlicePolynomial, hslicePoint]
    _ ≤ sphereSupNorm (rotationDeriv (0 : Fin 2) (1 : Fin 2) q) := hpoint
    _ ≤ 10 * (D : ℝ) * sphereSupNorm q := hrot
    _ ≤ 10 * (D : ℝ) * M := by
      exact mul_le_mul_of_nonneg_left hqSup (by positivity)

/-- Scalarization turns any scalar product-circle Bernstein estimate into a
finite-vector estimate with exactly the same constant.  In particular there
is no factor depending on the number of roots. -/
theorem finiteEuclideanVector_circleRotation_sq_le
    {n N D : ℕ} {K Q : ℝ}
    (p : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (hdegree : ∀ nu, (p nu).totalDegree ≤ D)
    (hrotation : ProductCircleFirstRotationBound D K)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hbound : ∀ theta,
      ‖finiteEuclideanVector
        (fun nu phi ↦ MvPolynomial.eval (cosineSineCirclePoint phi) (p nu))
        theta‖ ^ 2 ≤ Q)
    (i : Fin n) (theta : Fin n → ℝ) :
    ‖finiteEuclideanVector
        (fun nu phi ↦ MvPolynomial.eval (cosineSineCirclePoint phi)
          (circleRotationDeriv i (p nu))) theta‖ ^ 2 ≤ K ^ 2 * Q := by
  let d : Fin N → ℝ := fun nu ↦
    MvPolynomial.eval (cosineSineCirclePoint theta)
      (circleRotationDeriv i (p nu))
  have hM : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg Q
  have hvalueNorm (phi : Fin n → ℝ) :
      interiorVecNorm (fun nu ↦
        MvPolynomial.eval (cosineSineCirclePoint phi) (p nu)) ≤
        Real.sqrt Q := by
    have hsquare := hbound phi
    have hsqrt_sq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
    have hnorm_nonneg := norm_nonneg
      (finiteEuclideanVector
        (fun nu psi ↦ MvPolynomial.eval (cosineSineCirclePoint psi) (p nu)) phi)
    have hsqrt_nonneg := Real.sqrt_nonneg Q
    have hnorm :
        ‖finiteEuclideanVector
          (fun nu psi ↦ MvPolynomial.eval (cosineSineCirclePoint psi) (p nu))
          phi‖ ≤ Real.sqrt Q := by
      nlinarith
    calc
      interiorVecNorm (fun nu ↦
          MvPolynomial.eval (cosineSineCirclePoint phi) (p nu)) =
          ‖finiteEuclideanVector
            (fun nu psi ↦ MvPolynomial.eval
              (cosineSineCirclePoint psi) (p nu)) phi‖ :=
        (norm_finiteEuclideanVector_eq_interiorVecNorm
          (fun nu psi ↦ MvPolynomial.eval
            (cosineSineCirclePoint psi) (p nu)) phi).symm
      _ ≤ Real.sqrt Q := hnorm
  have hdNorm : interiorVecNorm d ≤ K * Real.sqrt Q := by
    by_cases hd0 : interiorVecNorm d = 0
    · rw [hd0]
      exact mul_nonneg hK hM
    · let u : Fin N → ℝ := fun nu ↦ d nu / interiorVecNorm d
      let R : MvPolynomial (CubeCircleVar n) ℝ :=
        ∑ nu, MvPolynomial.C (u nu) * p nu
      have hRdegree : R.totalDegree ≤ D := by
        dsimp [R]
        apply MvPolynomial.totalDegree_finsetSum_le
        intro nu _hnu
        calc
          (MvPolynomial.C (u nu) * p nu).totalDegree ≤
              (MvPolynomial.C (u nu) :
                MvPolynomial (CubeCircleVar n) ℝ).totalDegree +
                (p nu).totalDegree := MvPolynomial.totalDegree_mul _ _
          _ ≤ 0 + D := Nat.add_le_add (by simp) (hdegree nu)
          _ = D := by simp
      have hRbound (phi : Fin n → ℝ) :
          |MvPolynomial.eval (cosineSineCirclePoint phi) R| ≤
            Real.sqrt Q := by
        dsimp [R]
        rw [map_sum]
        simp only [map_mul, eval_C]
        change |vecDot u (fun nu ↦
          MvPolynomial.eval (cosineSineCirclePoint phi) (p nu))| ≤
            Real.sqrt Q
        have hdot := abs_vecDot_unit_le (v := d)
          (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm]
            using hd0)
          (fun nu ↦ MvPolynomial.eval (cosineSineCirclePoint phi) (p nu))
        have hnorm : vecNorm (fun nu ↦
            MvPolynomial.eval (cosineSineCirclePoint phi) (p nu)) ≤
            Real.sqrt Q := by
          simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using
            hvalueNorm phi
        exact hdot.trans hnorm
      have hscalar := hrotation R hRdegree hM hRbound i theta
      have hrotationR :
          MvPolynomial.eval (cosineSineCirclePoint theta)
              (circleRotationDeriv i R) = interiorVecNorm d := by
        dsimp [R]
        rw [circleRotationDeriv_finset_sum, map_sum]
        simp only [circleRotationDeriv_C_mul, map_mul, eval_C]
        change vecDot (fun nu ↦ d nu / interiorVecNorm d) d =
          interiorVecNorm d
        exact vecDot_unit_self (v := d)
          (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm]
            using hd0)
      rw [hrotationR, abs_of_nonneg (interiorVecNorm_nonneg d)] at hscalar
      exact hscalar
  have hvectorNorm :
      ‖finiteEuclideanVector
        (fun nu phi ↦ MvPolynomial.eval (cosineSineCirclePoint phi)
          (circleRotationDeriv i (p nu))) theta‖ = interiorVecNorm d := by
    exact norm_finiteEuclideanVector_eq_interiorVecNorm _ _
  have hright_nonneg : 0 ≤ K * Real.sqrt Q := mul_nonneg hK hM
  have hsquare := (sq_le_sq₀ (interiorVecNorm_nonneg d) hright_nonneg).2 hdNorm
  rw [hvectorNorm]
  calc
    interiorVecNorm d ^ 2 ≤ (K * Real.sqrt Q) ^ 2 := hsquare
    _ = K ^ 2 * Q := by rw [mul_pow, Real.sq_sqrt hQ]

/-- The scalar product-circle Bernstein estimate supplies the `hstep` used by
`oddSineRemoval_sq_le_of_twoRotationSeed` for every polynomial angular tower. -/
theorem circlePolynomialAngularDerivativeVector_step
    {n N D : ℕ} {K : ℝ}
    (p : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (hdegree : ∀ nu, (p nu).totalDegree ≤ D)
    (hrotation : ProductCircleFirstRotationBound D K) (hK : 0 ≤ K) :
    ∀ (pref : List (Fin n)) (i : Fin n) {Q : ℝ},
      0 ≤ Q →
        UniformAngularSqBound
          (fun is theta ↦ finiteEuclideanVector
            (fun nu phi ↦ MvPolynomial.eval (cosineSineCirclePoint phi)
              (iteratedCircleRotationDeriv is (p nu))) theta) pref Q →
        UniformAngularSqBound
          (fun is theta ↦ finiteEuclideanVector
            (fun nu phi ↦ MvPolynomial.eval (cosineSineCirclePoint phi)
              (iteratedCircleRotationDeriv is (p nu))) theta)
          (i :: pref) (K ^ 2 * Q) := by
  intro pref i Q hQ hbound theta
  let q : Fin N → MvPolynomial (CubeCircleVar n) ℝ :=
    fun nu ↦ iteratedCircleRotationDeriv pref (p nu)
  have hqdegree (nu : Fin N) : (q nu).totalDegree ≤ D :=
    (iteratedCircleRotationDeriv_totalDegree_le pref (p nu)).trans (hdegree nu)
  have hqbound (phi : Fin n → ℝ) :
      ‖finiteEuclideanVector
        (fun nu psi ↦ MvPolynomial.eval (cosineSineCirclePoint psi) (q nu))
        phi‖ ^ 2 ≤ Q := by
    exact hbound phi
  simpa [q] using
    finiteEuclideanVector_circleRotation_sq_le q hqdegree hrotation hK hQ
      hqbound i theta

/-- Iterating a root-count-free one-rotation estimate after an arbitrary seed
costs exactly `D^(2*m)` in squared norm. -/
theorem uniformAngularSqBound_iterate
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (remaining seed : List (Fin n)) {D H : ℝ}
    (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hseed : UniformAngularSqBound F seed H)
    (hstep : ∀ (pref : List (Fin n)) (i : Fin n) {Q : ℝ},
      0 ≤ Q → UniformAngularSqBound F pref Q →
        UniformAngularSqBound F (i :: pref) (D ^ 2 * Q)) :
    UniformAngularSqBound F (remaining.reverse ++ seed)
      (D ^ (2 * remaining.length) * H) := by
  induction remaining generalizing seed H with
  | nil => simpa [UniformAngularSqBound] using hseed
  | cons i remaining ih =>
      have hnext : UniformAngularSqBound F (i :: seed) (D ^ 2 * H) :=
        hstep seed i hH hseed
      have hnext_nonneg : 0 ≤ D ^ 2 * H :=
        mul_nonneg (pow_nonneg hD 2) hH
      have hout := ih (i :: seed) hnext_nonneg hnext
      rw [List.reverse_cons, List.append_assoc]
      simp only [List.singleton_append]
      rw [show D ^ (2 * (i :: remaining).length) * H =
          D ^ (2 * remaining.length) * (D ^ 2 * H) by
        rw [show 2 * (i :: remaining).length =
          2 * remaining.length + 2 by simp; omega, pow_add]
        ring]
      exact hout

/-- The manuscript exponent bookkeeping: a two-rotation seed followed by
`m` one-rotation steps costs `D^(2*m)`, and removal of all `m+2` odd sine
factors costs only the dimension-dependent Jordan factor. -/
theorem oddSineRemoval_sq_le_of_twoRotationSeed
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (V : (Fin n → ℝ) → E)
    (a b : Fin n) (remaining : List (Fin n))
    {D H : ℝ} (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hderiv : IsAngularDerivativeTower F)
    (hodd : IsOddAngularDerivativeTower (a :: b :: remaining) F)
    (hnodup : (a :: b :: remaining).Nodup)
    (hseed : UniformAngularSqBound F [b, a] H)
    (hstep : ∀ (pref : List (Fin n)) (i : Fin n) {Q : ℝ},
      0 ≤ Q → UniformAngularSqBound F pref Q →
        UniformAngularSqBound F (i :: pref) (D ^ 2 * Q))
    (hVcont : Continuous V)
    (hfactor : ∀ phi, F [] phi =
      ((a :: b :: remaining).map (fun i ↦ Real.sin (phi i))).prod • V phi)
    (theta : Fin n → ℝ)
    (hrange : ∀ i ∈ a :: b :: remaining,
      |theta i| ≤ Real.pi / 2) :
    ‖V theta‖ ^ 2 ≤
      (Real.pi / 2) ^ (2 * (remaining.length + 2)) *
        (D ^ (2 * remaining.length) * H) := by
  have hterminal : UniformAngularSqBound F
      ((a :: b :: remaining).reverse)
      (D ^ (2 * remaining.length) * H) := by
    simpa [List.reverse_cons, List.append_assoc] using
      uniformAngularSqBound_iterate F remaining [b, a] hD hH hseed hstep
  simpa [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    oddSineRemoval_iterated_sq F V (a :: b :: remaining) hderiv hodd
      (mul_nonneg (pow_nonneg hD _) hH) hnodup hterminal hVcont hfactor
      theta hrange

/-! ## Polynomial and parity-component realizations -/

/-- The scalar angular derivative tower generated by one finite family of
paired-variable polynomials. -/
def circlePolynomialAngularDerivativeFamily {n N : ℕ}
    (p : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (pref : List (Fin n)) (nu : Fin N) (theta : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval (cosineSineCirclePoint theta)
    (iteratedCircleRotationDeriv pref (p nu))

@[simp] theorem circlePolynomialAngularDerivativeFamily_nil
    {n N : ℕ} (p : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (nu : Fin N) (theta : Fin n → ℝ) :
    circlePolynomialAngularDerivativeFamily p [] nu theta =
      MvPolynomial.eval (cosineSineCirclePoint theta) (p nu) := rfl

/-- Every polynomial-generated tower has the required exact angular chain
rule, with no analytic regularity assumption added. -/
theorem circlePolynomialAngularDerivativeFamily_hasDerivAt
    {n N : ℕ} (p : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (pref : List (Fin n)) (nu : Fin N) (theta : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t ↦ circlePolynomialAngularDerivativeFamily p pref nu
        (replaceAngle theta i t))
      (circlePolynomialAngularDerivativeFamily p (i :: pref) nu theta)
      (theta i) := by
  simpa [circlePolynomialAngularDerivativeFamily] using
    hasDerivAt_eval_cosineSineCirclePoint_replaceAngle
      (iteratedCircleRotationDeriv pref (p nu)) theta i

/-- The polynomial at every level of the angular tower has degree bounded by
that of the original member of the family. -/
theorem circlePolynomialAngularDerivativeFamily_totalDegree_le
    {n N : ℕ} (p : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (pref : List (Fin n)) (nu : Fin N) :
    (iteratedCircleRotationDeriv pref (p nu)).totalDegree ≤
      (p nu).totalDegree :=
  iteratedCircleRotationDeriv_totalDegree_le pref (p nu)

/-- Packaging all polynomial roots into one Euclidean vector preserves the
exact derivative tower.  This is the root-count-free bridge from
`CircleRoots` to the abstract FTC lemmas above. -/
theorem circlePolynomialAngularDerivativeVector_isAngularDerivativeTower
    {n N : ℕ} (p : Fin N → MvPolynomial (CubeCircleVar n) ℝ) :
    IsAngularDerivativeTower
      (fun pref theta ↦
        finiteEuclideanVector
          (circlePolynomialAngularDerivativeFamily p pref) theta) := by
  intro pref i theta
  have hpi : HasDerivAt
      (fun t ↦ fun nu : Fin N ↦
        circlePolynomialAngularDerivativeFamily p pref nu
          (replaceAngle theta i t))
      (fun nu : Fin N ↦
        circlePolynomialAngularDerivativeFamily p (i :: pref) nu theta)
      (theta i) := by
    rw [hasDerivAt_pi]
    intro nu
    exact circlePolynomialAngularDerivativeFamily_hasDerivAt
      p pref nu theta i
  let e := (EuclideanSpace.equiv (Fin N) ℝ).symm
  have hcomp := e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (theta i) hpi
  simpa [Function.comp_def, finiteEuclideanVector, e] using hcomp

/-- Oddness of the base function along selected coordinate hyperplanes is
preserved by differentiating in distinct coordinates. -/
theorem isOddAngularDerivativeTower_of_base_vanish
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : List (Fin n) → (Fin n → ℝ) → E)
    (indices : List (Fin n))
    (hderiv : IsAngularDerivativeTower F)
    (hbase : ∀ i ∈ indices, ∀ theta,
      F [] (replaceAngle theta i 0) = 0) :
    IsOddAngularDerivativeTower indices F := by
  intro pref
  induction pref with
  | nil =>
      intro i theta hi _hi
      exact hbase i hi theta
  | cons j pref ih =>
      intro i theta hi hi_prefix
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hi_prefix (by simp)
      have hi_tail : i ∉ pref := by
        intro hip
        exact hi_prefix (by simp [hip])
      let thetaZero := replaceAngle theta i 0
      have hsection_zero (t : ℝ) :
          F pref (replaceAngle thetaZero j t) = 0 := by
        have hzero := ih i (replaceAngle thetaZero j t) hi hi_tail
        have hcoord : replaceAngle thetaZero j t i = 0 := by
          rw [replaceAngle_apply_of_ne]
          · exact replaceAngle_apply_same theta i 0
          · exact hij
        have hreplace :
            replaceAngle (replaceAngle thetaZero j t) i 0 =
              replaceAngle thetaZero j t := by
          funext l
          by_cases hli : l = i
          · subst l
            simp [hcoord]
          · simp [replaceAngle_apply_of_ne _ hli]
        rw [hreplace] at hzero
        exact hzero
      have hzero_deriv : HasDerivAt
          (fun t ↦ F pref (replaceAngle thetaZero j t)) 0 (thetaZero j) := by
        exact (hasDerivAt_const (x := thetaZero j) (0 : E)).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun t ↦ hsection_zero t))
      have htower := hderiv pref j thetaZero
      have hvalue : F (j :: pref) thetaZero = 0 := htower.unique hzero_deriv
      exact hvalue

/-- Reconstruct the explicit paired-variable polynomial represented by a cube
coefficient and an odd-coordinate set. -/
def circleParityReconstruction {n : ℕ}
    (q : MvPolynomial (Fin n) ℝ) (J : Finset (Fin n)) :
    MvPolynomial (CubeCircleVar n) ℝ :=
  MvPolynomial.rename (fun i ↦ (i, false)) q *
    ∏ i ∈ J, MvPolynomial.X (i, true)

/-- Exact angular factorization of a reconstructed parity term. -/
@[simp] theorem eval_circleParityReconstruction_angle
    {n : ℕ} (q : MvPolynomial (Fin n) ℝ) (J : Finset (Fin n))
    (theta : Fin n → ℝ) :
    MvPolynomial.eval (cosineSineCirclePoint theta)
        (circleParityReconstruction q J) =
      MvPolynomial.eval (fun i ↦ Real.cos (theta i)) q *
        ∏ i ∈ J, Real.sin (theta i) := by
  rw [circleParityReconstruction, map_mul, MvPolynomial.eval_rename, map_prod]
  simp [Function.comp_def]

/-- The reconstructed parity term has precisely the expected coarse degree
bound: coefficient degree plus the number of odd coordinates. -/
theorem circleParityReconstruction_totalDegree_le
    {n : ℕ} (q : MvPolynomial (Fin n) ℝ) (J : Finset (Fin n)) :
    (circleParityReconstruction q J).totalDegree ≤ q.totalDegree + J.card := by
  calc
    (circleParityReconstruction q J).totalDegree ≤
        (MvPolynomial.rename (fun i ↦ (i, false)) q).totalDegree +
          (∏ i ∈ J, MvPolynomial.X (i, true) :
            MvPolynomial (CubeCircleVar n) ℝ).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ q.totalDegree + J.card := by
      apply Nat.add_le_add (MvPolynomial.totalDegree_rename_le _ q)
      calc
        (∏ i ∈ J, MvPolynomial.X (i, true) :
            MvPolynomial (CubeCircleVar n) ℝ).totalDegree ≤
            ∑ i ∈ J, (MvPolynomial.X (i, true) :
              MvPolynomial (CubeCircleVar n) ℝ).totalDegree :=
          MvPolynomial.totalDegree_finset_prod J _
        _ = J.card := by simp

/-- The actual parity term attached to the repositorys canonical
`circleParityComponent`. -/
def pairedPolynomialParityTerm {n : ℕ}
    (P : MvPolynomial (CubeCircleVar n) ℝ) (J : Finset (Fin n)) :
    MvPolynomial (CubeCircleVar n) ℝ :=
  circleParityReconstruction (circleParityComponent P J) J

/-- Canonical parity terms inherit the total-degree bound of their source
paired polynomial. -/
theorem pairedPolynomialParityTerm_totalDegree_le
    {n : ℕ} (P : MvPolynomial (CubeCircleVar n) ℝ) (J : Finset (Fin n)) :
    (pairedPolynomialParityTerm P J).totalDegree ≤ P.totalDegree := by
  rcases circleParityComponent_eq_zero_or_totalDegree_add_card_le P J with hzero | hdeg
  · simp [pairedPolynomialParityTerm, circleParityReconstruction, hzero]
  · exact (circleParityReconstruction_totalDegree_le
      (circleParityComponent P J) J).trans hdeg

/-- The repositorys parity expansion is literally a sum of the reconstructed
odd-sine terms. -/
theorem eval_eq_sum_pairedPolynomialParityTerm_angle
    {n : ℕ} (P : MvPolynomial (CubeCircleVar n) ℝ)
    (theta : Fin n → ℝ) :
    MvPolynomial.eval (cosineSineCirclePoint theta) P =
      ∑ J : Finset (Fin n),
        MvPolynomial.eval (cosineSineCirclePoint theta)
          (pairedPolynomialParityTerm P J) := by
  rw [eval_eq_sum_circleParityComponents (cosineSineCirclePoint_mem theta) P]
  apply Finset.sum_congr rfl
  intro J _hJ
  simp [pairedPolynomialParityTerm, mul_comm]

/-- For a finite family, a fixed canonical parity term factors as the same
sine product times the Euclidean vector of cube coefficients. -/
theorem finiteEuclideanVector_pairedPolynomialParityTerm_factor
    {n N : ℕ} (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (J : Finset (Fin n)) (theta : Fin n → ℝ) :
    finiteEuclideanVector
        (fun nu theta ↦ MvPolynomial.eval (cosineSineCirclePoint theta)
          (pairedPolynomialParityTerm (P nu) J)) theta =
      (∏ i ∈ J, Real.sin (theta i)) •
        finiteEuclideanVector
          (fun nu theta ↦ MvPolynomial.eval
            (fun i ↦ Real.cos (theta i))
            (circleParityComponent (P nu) J)) theta := by
  ext nu
  simp [pairedPolynomialParityTerm, mul_comm]

/-! ## Walsh realization of canonical parity terms -/

/-- Flip angular coordinates by independent Walsh signs. -/
def walshSignedAngle {n : ℕ} (eps : Fin n → Bool)
    (theta : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ boolSign (eps i) * theta i

@[simp] theorem cos_walshSignedAngle {n : ℕ} (eps : Fin n → Bool)
    (theta : Fin n → ℝ) (i : Fin n) :
    Real.cos (walshSignedAngle eps theta i) = Real.cos (theta i) := by
  cases h : eps i <;> simp [walshSignedAngle, boolSign, h]

@[simp] theorem sin_walshSignedAngle {n : ℕ} (eps : Fin n → Bool)
    (theta : Fin n → ℝ) (i : Fin n) :
    Real.sin (walshSignedAngle eps theta i) =
      boolSign (eps i) * Real.sin (theta i) := by
  cases h : eps i <;> simp [walshSignedAngle, boolSign, h]

theorem prod_sin_walshSignedAngle {n : ℕ} (eps : Fin n → Bool)
    (theta : Fin n → ℝ) (J : Finset (Fin n)) :
    ∏ i ∈ J, Real.sin (walshSignedAngle eps theta i) =
      cubeSignCharacter eps J * ∏ i ∈ J, Real.sin (theta i) := by
  classical
  rw [cubeSignCharacter_eq_prod]
  simp_rw [sin_walshSignedAngle]
  exact Finset.prod_mul_distrib

/-- The canonical parity term is the normalized Walsh projection of the
source polynomial on every angular product-circle point. -/
theorem eval_pairedPolynomialParityTerm_eq_walshProjection
    {n : ℕ} (P : MvPolynomial (CubeCircleVar n) ℝ)
    (I : Finset (Fin n)) (theta : Fin n → ℝ) :
    MvPolynomial.eval (cosineSineCirclePoint theta)
        (pairedPolynomialParityTerm P I) =
      (∑ eps : Fin n → Bool, cubeSignCharacter eps I *
        MvPolynomial.eval (cosineSineCirclePoint (walshSignedAngle eps theta)) P) /
        (2 : ℝ) ^ n := by
  classical
  let a : Finset (Fin n) → ℝ := fun J ↦
    MvPolynomial.eval (cosineSineCirclePoint theta)
      (pairedPolynomialParityTerm P J)
  have hsigned (eps : Fin n → Bool) :
      MvPolynomial.eval (cosineSineCirclePoint (walshSignedAngle eps theta)) P =
        ∑ J : Finset (Fin n), cubeSignCharacter eps J * a J := by
    rw [eval_eq_sum_pairedPolynomialParityTerm_angle]
    apply Finset.sum_congr rfl
    intro J _hJ
    dsimp [a]
    rw [pairedPolynomialParityTerm, eval_circleParityReconstruction_angle,
      eval_circleParityReconstruction_angle]
    rw [prod_sin_walshSignedAngle]
    simp only [cos_walshSignedAngle]
    ring
  have hnum :
      (∑ eps : Fin n → Bool, cubeSignCharacter eps I *
        MvPolynomial.eval (cosineSineCirclePoint (walshSignedAngle eps theta)) P) =
        (2 : ℝ) ^ n * a I := by
    simp_rw [hsigned]
    calc
      (∑ eps : Fin n → Bool, cubeSignCharacter eps I *
          ∑ J : Finset (Fin n), cubeSignCharacter eps J * a J) =
          ∑ J : Finset (Fin n),
            (∑ eps : Fin n → Bool,
              cubeSignCharacter eps I * cubeSignCharacter eps J) * a J := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro J _hJ
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro eps _heps
        ring
      _ = ∑ J : Finset (Fin n),
          (if I = J then (2 : ℝ) ^ n else 0) * a J := by
        apply Finset.sum_congr rfl
        intro J _hJ
        rw [sum_cubeSignCharacter_mul]
      _ = (2 : ℝ) ^ n * a I := by simp
  rw [hnum]
  dsimp [a]
  field_simp

/-- Walsh coefficient after differentiating in the listed angular coordinates. -/
def walshDerivativeWeight {n : ℕ} (eps : Fin n → Bool)
    (I : Finset (Fin n)) (pref : List (Fin n)) : ℝ :=
  cubeSignCharacter eps I *
    (pref.map (fun i ↦ boolSign (eps i))).prod

@[simp] theorem walshDerivativeWeight_nil {n : ℕ}
    (eps : Fin n → Bool) (I : Finset (Fin n)) :
    walshDerivativeWeight eps I [] = cubeSignCharacter eps I := by
  simp [walshDerivativeWeight]

@[simp] theorem walshDerivativeWeight_cons {n : ℕ}
    (eps : Fin n → Bool) (I : Finset (Fin n))
    (i : Fin n) (pref : List (Fin n)) :
    walshDerivativeWeight eps I (i :: pref) =
      boolSign (eps i) * walshDerivativeWeight eps I pref := by
  simp [walshDerivativeWeight]
  ring

@[simp] theorem walshDerivativeWeight_sq {n : ℕ}
    (eps : Fin n → Bool) (I : Finset (Fin n))
    (pref : List (Fin n)) :
    walshDerivativeWeight eps I pref ^ 2 = 1 := by
  induction pref with
  | nil =>
      rw [walshDerivativeWeight_nil]
      unfold cubeSignCharacter
      rw [← Finset.prod_pow]
      apply Finset.prod_eq_one
      intro i _hi
      by_cases hi : i ∈ I <;> simp [hi, boolSign_sq]
  | cons i pref ih =>
      rw [walshDerivativeWeight_cons, mul_pow, boolSign_sq, ih, one_mul]

theorem walshSignedAngle_replaceAngle {n : ℕ}
    (eps : Fin n → Bool) (theta : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    walshSignedAngle eps (replaceAngle theta i t) =
      replaceAngle (walshSignedAngle eps theta) i (boolSign (eps i) * t) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [walshSignedAngle]
  · simp [walshSignedAngle, replaceAngle_apply_of_ne _ hji]

/-- Chain rule for a signed angular section. -/
theorem hasDerivAt_eval_walshSignedAngle_replaceAngle
    {n : ℕ} (p : MvPolynomial (CubeCircleVar n) ℝ)
    (eps : Fin n → Bool) (theta : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t ↦ MvPolynomial.eval
        (cosineSineCirclePoint
          (walshSignedAngle eps (replaceAngle theta i t))) p)
      (boolSign (eps i) *
        MvPolynomial.eval (cosineSineCirclePoint (walshSignedAngle eps theta))
          (circleRotationDeriv i p))
      (theta i) := by
  have houter := hasDerivAt_eval_cosineSineCirclePoint_replaceAngle
    p (walshSignedAngle eps theta) i
  have hinner : HasDerivAt (fun t : ℝ ↦ boolSign (eps i) * t)
      (boolSign (eps i)) (theta i) :=
    hasDerivAt_const_mul (x := theta i) (boolSign (eps i))
  have hcomp := houter.comp (theta i) hinner
  convert hcomp using 1
  · funext t
    rw [walshSignedAngle_replaceAngle]
    simp only [Function.comp_apply]
  · ring

/-! ## Root-count-free Walsh projection -/

@[simp] theorem cubeSignCharacter_sq_value {n : ℕ}
    (eps : Fin n → Bool) (J : Finset (Fin n)) :
    cubeSignCharacter eps J ^ 2 = 1 := by
  classical
  unfold cubeSignCharacter
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _hi
  by_cases hiJ : i ∈ J <;> simp [hiJ, boolSign_sq]

/-- Cauchy--Schwarz for a Walsh projection, summed over an arbitrary finite
root family.  There is no factor depending on the root count. -/
theorem sum_sq_walshProjection_unnormalized_le
    {n N : ℕ} (b : Fin N → (Fin n → Bool) → ℝ)
    (J : Finset (Fin n)) :
    ∑ nu, (∑ eps, cubeSignCharacter eps J * b nu eps) ^ 2 ≤
      (2 : ℝ) ^ n * ∑ eps, ∑ nu, (b nu eps) ^ 2 := by
  classical
  let c : ℝ := (2 : ℝ) ^ n
  have hchar (nu : Fin N) :
      (∑ eps : Fin n → Bool, cubeSignCharacter eps J ^ 2) = c := by
    simp [c, cubeSignCharacter_sq_value]
  have hone (nu : Fin N) :
      (∑ eps : Fin n → Bool, (1 : ℝ) ^ 2) = c := by simp [c]
  have heach (nu : Fin N) :
      (∑ eps, cubeSignCharacter eps J * b nu eps) ^ 2 ≤
        c * ∑ eps, (b nu eps) ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n → Bool))
      (fun eps ↦ cubeSignCharacter eps J) (fun eps ↦ b nu eps)
    simpa [hchar nu, hone nu] using hcs
  calc
    ∑ nu, (∑ eps, cubeSignCharacter eps J * b nu eps) ^ 2 ≤
        ∑ nu, c * ∑ eps, (b nu eps) ^ 2 :=
      Finset.sum_le_sum (fun nu _hnu ↦ heach nu)
    _ = c * ∑ nu, ∑ eps, (b nu eps) ^ 2 := by
      rw [Finset.mul_sum]
    _ = c * ∑ eps, ∑ nu, (b nu eps) ^ 2 := by
      rw [Finset.sum_comm]
    _ = (2 : ℝ) ^ n * ∑ eps, ∑ nu, (b nu eps) ^ 2 := rfl

/-- Normalized form: multiplying the squared norm of a Walsh coefficient by
`2^n` is bounded by the sum of the raw squared norms over all signs. -/
theorem two_pow_mul_sum_sq_walshProjection_le
    {n N : ℕ} (b : Fin N → (Fin n → Bool) → ℝ)
    (J : Finset (Fin n)) :
    (2 : ℝ) ^ n *
        ∑ nu, ((∑ eps, cubeSignCharacter eps J * b nu eps) /
          (2 : ℝ) ^ n) ^ 2 ≤
      ∑ eps, ∑ nu, (b nu eps) ^ 2 := by
  let c : ℝ := (2 : ℝ) ^ n
  have hc : 0 < c := by dsimp [c]; positivity
  have hraw := sum_sq_walshProjection_unnormalized_le b J
  have hdiv :
      (∑ nu, (∑ eps, cubeSignCharacter eps J * b nu eps) ^ 2) / c ≤
        ∑ eps, ∑ nu, (b nu eps) ^ 2 := by
    apply (div_le_iff₀ hc).2
    simpa [c, mul_comm] using hraw
  calc
    (2 : ℝ) ^ n *
        ∑ nu, ((∑ eps, cubeSignCharacter eps J * b nu eps) /
          (2 : ℝ) ^ n) ^ 2 =
        (∑ nu, (∑ eps, cubeSignCharacter eps J * b nu eps) ^ 2) / c := by
      dsimp [c]
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro nu _hnu
      field_simp
    _ ≤ _ := hdiv

/-! ## The weighted residual seen by the Putinar correction -/

/-- After removing the sine factors indexed by `J`, the remaining vector is
exactly the cube parity coefficient weighted by the complementary factors in
`I \ J`.  This is the vector whose squared norm occurs in the weighted
Putinar correction estimate. -/
def parityResidualVector {n N : ℕ}
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (I J : Finset (Fin n)) (theta : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin N) :=
  finiteEuclideanVector
    (fun nu phi ↦
      MvPolynomial.eval (fun i ↦ Real.cos (phi i))
          (circleParityComponent (P nu) I) *
        ∏ i ∈ I \ J, Real.sin (phi i)) theta

/-- Exact split of a canonical parity term into the selected `J` sine
factors and the weighted residual vector. -/
theorem finiteEuclideanVector_pairedPolynomialParityTerm_split_factor
    {n N : ℕ} (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    {I J : Finset (Fin n)} (hJI : J ⊆ I) (theta : Fin n → ℝ) :
    finiteEuclideanVector
        (fun nu phi ↦ MvPolynomial.eval (cosineSineCirclePoint phi)
          (pairedPolynomialParityTerm (P nu) I)) theta =
      (∏ i ∈ J, Real.sin (theta i)) •
        parityResidualVector P I J theta := by
  classical
  rw [finiteEuclideanVector_pairedPolynomialParityTerm_factor]
  ext nu
  simp only [finiteEuclideanVector_apply, parityResidualVector,
    PiLp.smul_apply, smul_eq_mul]
  rw [← Finset.prod_sdiff hJI]
  ring

/-- Evaluation of a box-generator product at cosine coordinates is the
square of the corresponding sine product. -/
theorem eval_BoxSemialgebraicGeneratorProd_cosine
    {n : ℕ} (K : Finset (Fin n)) (theta : Fin n → ℝ) :
    MvPolynomial.eval (fun i ↦ Real.cos (theta i))
        (BoxSemialgebraicGeneratorProd K) =
      (∏ i ∈ K, Real.sin (theta i)) ^ 2 := by
  classical
  unfold BoxSemialgebraicGeneratorProd
  rw [map_prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [BoxSemialgebraicGenerator_eval]
  nlinarith [Real.cos_sq_add_sin_sq (theta i)]

/-- The residual vector has *exactly* the weighted square function required
by `PutinarCorrectionRate`.  In particular, passing to the finite Euclidean
vector introduces no factor depending on the number of roots. -/
theorem parityResidualVector_norm_sq_eq_weightedParity
    {n N : ℕ} (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (I J : Finset (Fin n)) (theta : Fin n → ℝ) :
    ‖parityResidualVector P I J theta‖ ^ 2 =
      MvPolynomial.eval (fun i ↦ Real.cos (theta i))
        (BoxSemialgebraicGeneratorProd (I \ J) *
          ∑ nu, (circleParityComponent (P nu) I) ^ 2) := by
  classical
  unfold parityResidualVector
  rw [finiteEuclideanVector_norm_sq, map_mul,
    eval_BoxSemialgebraicGeneratorProd_cosine]
  rw [map_sum]
  simp only [map_pow]
  simp_rw [mul_pow]
  rw [← Finset.sum_mul]
  ring

/-- Angular derivative tower of one fixed canonical parity component across a
finite polynomial family. -/
def parityTermAngularDerivativeVector {n N : ℕ}
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    (I : Finset (Fin n)) (pref : List (Fin n)) (theta : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin N) :=
  finiteEuclideanVector
    (circlePolynomialAngularDerivativeFamily
      (fun nu ↦ pairedPolynomialParityTerm (P nu) I) pref) theta

/-- A two-rotation square bound and root-count-free one-rotation propagation
imply the exact weighted parity estimate.  The statement includes points on
all cube boundary strata; those are handled by `oddSineRemoval_iterated`, not
by totalized division. -/
theorem eval_weightedParitySum_le_of_twoRotationSeed
    {n N : ℕ} (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ)
    {I J : Finset (Fin n)} (hJI : J ⊆ I)
    (a b : Fin n) (remaining : List (Fin n))
    (hselected : (a :: b :: remaining).toFinset = J)
    (hnodup : (a :: b :: remaining).Nodup)
    {D H : ℝ} (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hseed : UniformAngularSqBound
      (parityTermAngularDerivativeVector P I) [b, a] H)
    (hstep : ∀ (pref : List (Fin n)) (i : Fin n) {Q : ℝ},
      0 ≤ Q →
        UniformAngularSqBound (parityTermAngularDerivativeVector P I) pref Q →
        UniformAngularSqBound (parityTermAngularDerivativeVector P I)
          (i :: pref) (D ^ 2 * Q))
    (theta : Fin n → ℝ)
    (hrange : ∀ i ∈ a :: b :: remaining,
      |theta i| ≤ Real.pi / 2) :
    MvPolynomial.eval (fun i ↦ Real.cos (theta i))
        (BoxSemialgebraicGeneratorProd (I \ J) *
          ∑ nu, (circleParityComponent (P nu) I) ^ 2) ≤
      (Real.pi / 2) ^ (2 * (remaining.length + 2)) *
        (D ^ (2 * remaining.length) * H) := by
  let selected : List (Fin n) := a :: b :: remaining
  let Q : Fin N → MvPolynomial (CubeCircleVar n) ℝ :=
    fun nu ↦ pairedPolynomialParityTerm (P nu) I
  let F : List (Fin n) → (Fin n → ℝ) → EuclideanSpace ℝ (Fin N) :=
    parityTermAngularDerivativeVector P I
  have hderiv : IsAngularDerivativeTower F := by
    exact circlePolynomialAngularDerivativeVector_isAngularDerivativeTower Q
  have hbase : ∀ i ∈ selected, ∀ phi,
      F [] (replaceAngle phi i 0) = 0 := by
    intro i hi phi
    have hiJ : i ∈ J := by
      rw [← hselected]
      simpa [selected] using hi
    have hiI : i ∈ I := hJI hiJ
    ext nu
    change MvPolynomial.eval
      (cosineSineCirclePoint (replaceAngle phi i 0))
        (pairedPolynomialParityTerm (P nu) I) = 0
    rw [pairedPolynomialParityTerm, eval_circleParityReconstruction_angle]
    apply mul_eq_zero.mpr
    right
    exact Finset.prod_eq_zero hiI (by simp)
  have hodd : IsOddAngularDerivativeTower selected F :=
    isOddAngularDerivativeTower_of_base_vanish F selected hderiv hbase
  have hcont : Continuous (parityResidualVector P I J) := by
    apply continuous_finiteEuclideanVector
    intro nu
    apply Continuous.mul
    · exact (MvPolynomial.continuous_eval _).comp
        (continuous_pi (fun i ↦ Real.continuous_cos.comp (continuous_apply i)))
    · apply continuous_finset_prod
      intro i _hi
      exact Real.continuous_sin.comp (continuous_apply i)
  have hfactor (phi : Fin n → ℝ) :
      F [] phi =
        (selected.map (fun i ↦ Real.sin (phi i))).prod •
          parityResidualVector P I J phi := by
    have hsplit :=
      finiteEuclideanVector_pairedPolynomialParityTerm_split_factor
        P hJI phi
    have hprod :
        (∏ i ∈ J, Real.sin (phi i)) =
          (selected.map (fun i ↦ Real.sin (phi i))).prod := by
      rw [← hselected]
      exact List.prod_toFinset _ hnodup
    simpa [F, Q, selected, parityTermAngularDerivativeVector, hprod] using hsplit
  have hsquare :
      ‖parityResidualVector P I J theta‖ ^ 2 ≤
        (Real.pi / 2) ^ (2 * (remaining.length + 2)) *
          (D ^ (2 * remaining.length) * H) := by
    exact oddSineRemoval_sq_le_of_twoRotationSeed F
      (parityResidualVector P I J) a b remaining hD hH hderiv
      (by simpa [selected] using hodd) hnodup hseed hstep hcont
      (by simpa [selected] using hfactor) theta hrange
  rw [← parityResidualVector_norm_sq_eq_weightedParity P I J theta]
  exact hsquare


/-! ## Walsh projection after mixed angular derivatives -/

/-- Mixed circle rotations commute with the Walsh realization of a canonical
parity term.  Every coefficient remains a sign, so this identity loses no
factor depending on the polynomial family. -/
theorem eval_iteratedCircleRotationDeriv_pairedPolynomialParityTerm_eq_walsh
    {n : Nat} (P : MvPolynomial (CubeCircleVar n) Real)
    (I : Finset (Fin n)) (pref : List (Fin n)) (theta : Fin n -> Real) :
    MvPolynomial.eval (cosineSineCirclePoint theta)
        (iteratedCircleRotationDeriv pref (pairedPolynomialParityTerm P I)) =
      (Finset.sum Finset.univ (fun eps : Fin n -> Bool =>
          walshDerivativeWeight eps I pref *
            MvPolynomial.eval
              (cosineSineCirclePoint (walshSignedAngle eps theta))
              (iteratedCircleRotationDeriv pref P))) /
        (2 : Real) ^ n := by
  classical
  induction pref generalizing theta with
  | nil =>
      simpa using eval_pairedPolynomialParityTerm_eq_walshProjection P I theta
  | cons i pref ih =>
      let qI := iteratedCircleRotationDeriv pref
        (pairedPolynomialParityTerm P I)
      let q := iteratedCircleRotationDeriv pref P
      have hleft :=
        hasDerivAt_eval_cosineSineCirclePoint_replaceAngle qI theta i
      have hsum : HasDerivAt
          (fun t : Real => Finset.sum Finset.univ
            (fun eps : Fin n -> Bool =>
              walshDerivativeWeight eps I pref *
                MvPolynomial.eval
                  (cosineSineCirclePoint
                    (walshSignedAngle eps (replaceAngle theta i t))) q))
          (Finset.sum Finset.univ (fun eps : Fin n -> Bool =>
            walshDerivativeWeight eps I pref *
              (boolSign (eps i) *
                MvPolynomial.eval
                  (cosineSineCirclePoint (walshSignedAngle eps theta))
                  (circleRotationDeriv i q))))
          (theta i) := by
        apply HasDerivAt.fun_sum
        intro eps _heps
        exact (hasDerivAt_eval_walshSignedAngle_replaceAngle
          q eps theta i).const_mul (walshDerivativeWeight eps I pref)
      have hright := hsum.div_const ((2 : Real) ^ n)
      have hrightOnLeft := hright.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun t => by
          simpa [qI, q] using ih (replaceAngle theta i t)))
      have hder := hleft.unique hrightOnLeft
      simp only [iteratedCircleRotationDeriv_cons]
      change MvPolynomial.eval (cosineSineCirclePoint theta)
          (circleRotationDeriv i qI) = _
      rw [hder]
      congr 1
      apply Finset.sum_congr rfl
      intro eps _heps
      rw [walshDerivativeWeight_cons]
      ring


/-- Cauchy--Schwarz for any sign-valued projection.  This is the form used
after angular derivatives toggle the original Walsh character. -/
theorem sum_sq_signProjection_unnormalized_le
    {n N : Nat} (c : (Fin n -> Bool) -> Real)
    (hc : forall eps, c eps ^ 2 = 1)
    (b : Fin N -> (Fin n -> Bool) -> Real) :
    Finset.sum Finset.univ (fun nu =>
        (Finset.sum Finset.univ (fun eps => c eps * b nu eps)) ^ 2) <=
      (2 : Real) ^ n *
        Finset.sum Finset.univ (fun eps =>
          Finset.sum Finset.univ (fun nu => (b nu eps) ^ 2)) := by
  classical
  let card : Real := (2 : Real) ^ n
  have hchar (nu : Fin N) :
      Finset.sum Finset.univ (fun eps : Fin n -> Bool => c eps ^ 2) = card := by
    simp [hc, card]
  have heach (nu : Fin N) :
      (Finset.sum Finset.univ (fun eps => c eps * b nu eps)) ^ 2 <=
        card * Finset.sum Finset.univ (fun eps => (b nu eps) ^ 2) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n -> Bool)) c (fun eps => b nu eps)
    simpa [hchar nu] using hcs
  calc
    Finset.sum Finset.univ (fun nu =>
        (Finset.sum Finset.univ (fun eps => c eps * b nu eps)) ^ 2) <=
        Finset.sum Finset.univ (fun nu =>
          card * Finset.sum Finset.univ (fun eps => (b nu eps) ^ 2)) :=
      Finset.sum_le_sum (fun nu _hnu => heach nu)
    _ = card * Finset.sum Finset.univ (fun nu =>
          Finset.sum Finset.univ (fun eps => (b nu eps) ^ 2)) := by
      rw [Finset.mul_sum]
    _ = card * Finset.sum Finset.univ (fun eps =>
          Finset.sum Finset.univ (fun nu => (b nu eps) ^ 2)) := by
      rw [Finset.sum_comm]
    _ = (2 : Real) ^ n * Finset.sum Finset.univ (fun eps =>
          Finset.sum Finset.univ (fun nu => (b nu eps) ^ 2)) := rfl

/-- A normalized sign projection contracts a uniform finite-vector square
bound.  In particular the constant is independent of the vector dimension. -/
theorem sum_sq_normalized_signProjection_le
    {n N : Nat} (c : (Fin n -> Bool) -> Real)
    (hc : forall eps, c eps ^ 2 = 1)
    (b : Fin N -> (Fin n -> Bool) -> Real) {H : Real}
    (hraw : forall eps,
      Finset.sum Finset.univ (fun nu => (b nu eps) ^ 2) <= H) :
    Finset.sum Finset.univ (fun nu =>
        ((Finset.sum Finset.univ (fun eps => c eps * b nu eps)) /
          (2 : Real) ^ n) ^ 2) <= H := by
  let card : Real := (2 : Real) ^ n
  have hcard : 0 < card := by
    dsimp [card]
    positivity
  have hcs := sum_sq_signProjection_unnormalized_le c hc b
  have hdiv :
      card * Finset.sum Finset.univ (fun nu =>
          ((Finset.sum Finset.univ (fun eps => c eps * b nu eps)) /
            card) ^ 2) <=
        Finset.sum Finset.univ (fun eps =>
          Finset.sum Finset.univ (fun nu => (b nu eps) ^ 2)) := by
    have hquot :
        (Finset.sum Finset.univ (fun nu =>
          (Finset.sum Finset.univ (fun eps => c eps * b nu eps)) ^ 2)) /
            card <=
          Finset.sum Finset.univ (fun eps =>
            Finset.sum Finset.univ (fun nu => (b nu eps) ^ 2)) := by
      apply (div_le_iff₀ hcard).2
      simpa [card, mul_comm] using hcs
    calc
      card * Finset.sum Finset.univ (fun nu =>
          ((Finset.sum Finset.univ (fun eps => c eps * b nu eps)) /
            card) ^ 2) =
          (Finset.sum Finset.univ (fun nu =>
            (Finset.sum Finset.univ (fun eps => c eps * b nu eps)) ^ 2)) /
              card := by
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro nu _hnu
        field_simp
      _ <= _ := hquot
  have hrawSum :
      Finset.sum Finset.univ (fun eps =>
          Finset.sum Finset.univ (fun nu => (b nu eps) ^ 2)) <=
        card * H := by
    calc
      Finset.sum Finset.univ (fun eps =>
          Finset.sum Finset.univ (fun nu => (b nu eps) ^ 2)) <=
          Finset.sum Finset.univ (fun _eps : Fin n -> Bool => H) :=
        Finset.sum_le_sum (fun eps _heps => hraw eps)
      _ = card * H := by simp [card]
  exact le_of_mul_le_mul_left (hdiv.trans hrawSum) hcard

/-- Walsh parity projection contracts every mixed-rotation finite-vector
square bound, without a root-count factor. -/
theorem uniformAngularSqBound_parityTerm_of_raw
    {n N : Nat} (P : Fin N -> MvPolynomial (CubeCircleVar n) Real)
    (I : Finset (Fin n)) (pref : List (Fin n)) {H : Real}
    (hraw : forall theta,
      Finset.sum Finset.univ (fun nu =>
        (MvPolynomial.eval (cosineSineCirclePoint theta)
          (iteratedCircleRotationDeriv pref (P nu))) ^ 2) <= H) :
    UniformAngularSqBound (parityTermAngularDerivativeVector P I) pref H := by
  intro theta
  unfold parityTermAngularDerivativeVector
  rw [finiteEuclideanVector_norm_sq]
  simp only [
    circlePolynomialAngularDerivativeFamily]
  simp_rw [eval_iteratedCircleRotationDeriv_pairedPolynomialParityTerm_eq_walsh]
  apply sum_sq_normalized_signProjection_le
    (fun eps => walshDerivativeWeight eps I pref)
    (fun eps => walshDerivativeWeight_sq eps I pref)
  intro eps
  exact hraw (walshSignedAngle eps theta)

/-- Two-rotation specialization matching the controlled-root Hessian seed.
The order `[b, a]` is the canonical order: rotate first in `a`, then in `b`. -/
theorem uniformAngularSqBound_parityTerm_twoRotation_of_raw
    {n N : Nat} (P : Fin N -> MvPolynomial (CubeCircleVar n) Real)
    (I : Finset (Fin n)) (a b : Fin n) {H : Real}
    (hraw : forall theta,
      Finset.sum Finset.univ (fun nu =>
        (MvPolynomial.eval (cosineSineCirclePoint theta)
          (circleRotationDeriv b (circleRotationDeriv a (P nu)))) ^ 2) <= H) :
    UniformAngularSqBound (parityTermAngularDerivativeVector P I) [b, a] H := by
  apply uniformAngularSqBound_parityTerm_of_raw P I [b, a]
  simpa using hraw

end QuarticConvergence
end OptimalConvergenceRates

end
