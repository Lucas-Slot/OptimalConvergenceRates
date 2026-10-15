/-
  Coefficient-bounded Archimedean coefficient envelopes.
-/
import OptimalConvergenceRates.GeneralArchimedean.BoundedModuleOrder

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- Coefficient-tracked version of multiplication of two square bounds. -/
def bounded_mul_square_bound_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {A B : ℝ} {a b : MvPolynomial (Fin n) ℝ}
    {r s : ℕ} {Ha Hb Ka : ℝ}
    (hB : 0 ≤ B)
    (ca : BoundedQuadraticModuleCertificate g (C A - a ^ 2) r Ha)
    (cb : BoundedQuadraticModuleCertificate g (C B - b ^ 2) s Hb)
    (haNorm : coeffL1Norm (a ^ 2) ≤ Ka) :
    BoundedQuadraticModuleCertificate g
      (C (A * B) - (a * b) ^ 2)
      (max r (s + (a ^ 2).totalDegree))
      (B * Ha + Ka * Hb) := by
  have hCNorm : coeffL1Norm (C B : MvPolynomial (Fin n) ℝ) ≤ B := by
    simpa [abs_of_nonneg hB] using coeffL1Norm_C_le (n := n) B
  let cleft := ca.sosMulOfNormLe (IsSOS_C_nonneg B hB) hCNorm
  let cright := cb.sosMulOfNormLe (IsSOS_sq a) haNorm
  have csum := cleft.add cright
  have horder :
      max ((C B : MvPolynomial (Fin n) ℝ).totalDegree + r)
          ((a ^ 2).totalDegree + s) ≤
        max r (s + (a ^ 2).totalDegree) := by
    simp [add_comm]
  exact ((csum.mono horder).congr (by
    simp only [map_mul]
    ring))

/-- A coarse budget stable under repeatedly propagating one coordinate
square bound. -/
def boundedCoordinatePowerBudget (B Hcoord : ℝ) (k : ℕ) : ℝ :=
  (B + 1) ^ k * (Hcoord + 1)

theorem boundedCoordinatePowerBudget_nonneg
    {B Hcoord : ℝ} (hB : 0 ≤ B) (hHcoord : 0 ≤ Hcoord) (k : ℕ) :
    0 ≤ boundedCoordinatePowerBudget B Hcoord k := by
  unfold boundedCoordinatePowerBudget
  positivity

/-- A bounded coordinate-square certificate propagates to all powers with
an explicit geometric coefficient budget. -/
def bounded_coordinate_power_square_bound_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B Hcoord : ℝ} {t : ℕ}
    (hB : 1 ≤ B) (hHcoord : 0 ≤ Hcoord)
    (hcoord : ∀ i : Fin n,
      BoundedQuadraticModuleCertificate g (C B - X i ^ 2) t Hcoord)
    (i : Fin n) : ∀ k : ℕ,
      BoundedQuadraticModuleCertificate g
        (C (B ^ k) - (X i ^ k) ^ 2)
        (t + 2 * k)
        (boundedCoordinatePowerBudget B Hcoord k) := by
  intro k
  induction k with
  | zero =>
      let czero := BoundedQuadraticModuleCertificate.ofSOS g
        (0 : MvPolynomial (Fin n) ℝ) IsSOS_zero
        (Nat.zero_le (t + 2 * 0))
      exact (czero.congr (by simp)).weakenBound (by
        unfold boundedCoordinatePowerBudget
        simpa using add_nonneg hHcoord zero_le_one)
  | succ k ih =>
      have hX : coeffL1Norm
          ((X i ^ k : MvPolynomial (Fin n) ℝ) ^ 2) ≤ 1 := by
        have hvar :
            coeffL1Norm (X i : MvPolynomial (Fin n) ℝ) ≤ 1 := by
          simpa [MvPolynomial.X] using coeffL1Norm_monomial_le
            (n := n) (Finsupp.single i 1) (1 : ℝ)
        calc
          coeffL1Norm ((X i ^ k : MvPolynomial (Fin n) ℝ) ^ 2) ≤
              coeffL1Norm (X i : MvPolynomial (Fin n) ℝ) ^ (k * 2) := by
            rw [← pow_mul]
            exact coeffL1Norm_pow_le _ _
          _ ≤ 1 ^ (k * 2) :=
            pow_le_pow_left₀ (coeffL1Norm_nonneg _) hvar _
          _ = 1 := by simp
      have craw := bounded_mul_square_bound_at
        (show 0 ≤ B by linarith) ih (hcoord i) hX
      have hdegree :
          ((X i ^ k : MvPolynomial (Fin n) ℝ) ^ 2).totalDegree ≤
            2 * k := by
        calc
          ((X i ^ k : MvPolynomial (Fin n) ℝ) ^ 2).totalDegree ≤
              2 * (X i ^ k : MvPolynomial (Fin n) ℝ).totalDegree :=
            MvPolynomial.totalDegree_pow _ _
          _ = 2 * k := by simp
      have horder :
          max (t + 2 * k)
              (t + ((X i ^ k : MvPolynomial (Fin n) ℝ) ^ 2).totalDegree) ≤
            t + 2 * (k + 1) := by
        apply max_le <;> omega
      have hbudget :
          B * boundedCoordinatePowerBudget B Hcoord k + 1 * Hcoord ≤
            boundedCoordinatePowerBudget B Hcoord (k + 1) := by
        have hbase : 1 ≤ B + 1 := by linarith
        have hpow : 1 ≤ (B + 1) ^ k := one_le_pow₀ hbase
        have hQ : Hcoord ≤ boundedCoordinatePowerBudget B Hcoord k := by
          unfold boundedCoordinatePowerBudget
          nlinarith [mul_le_mul_of_nonneg_right hpow (by linarith : 0 ≤ Hcoord + 1)]
        unfold boundedCoordinatePowerBudget at *
        rw [pow_succ]
        nlinarith
      exact ((craw.mono horder).weakenBound hbudget).congr (by
        simp [pow_succ])

/-- Common order for the bounded product construction of a monomial square
bound. -/
def boundedMonomialSquareOrder (n t d : ℕ) : ℕ :=
  n * ((t + 2 * d) + 2 * d)

/-- Common coefficient budget for a monomial square bound of degree at most
`d`. -/
def boundedMonomialSquareBudget
    (n d : ℕ) (B Hcoord : ℝ) : ℝ :=
  (((B + 1) ^ d) + 1) ^ n *
    boundedCoordinatePowerBudget B Hcoord d

theorem boundedMonomialSquareBudget_nonneg
    (n d : ℕ) {B Hcoord : ℝ}
    (hB : 0 ≤ B) (hHcoord : 0 ≤ Hcoord) :
    0 ≤ boundedMonomialSquareBudget n d B Hcoord := by
  unfold boundedMonomialSquareBudget
  exact mul_nonneg (by positivity)
    (boundedCoordinatePowerBudget_nonneg hB hHcoord d)

/-- A bounded coordinate-square family gives an explicit bounded certificate
for every monomial square of bounded degree. -/
theorem bounded_monomial_square_bound_of_degree_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B Hcoord : ℝ} {t d : ℕ}
    (hB : 1 ≤ B) (hHcoord : 0 ≤ Hcoord)
    (hcoord : ∀ i : Fin n,
      BoundedQuadraticModuleCertificate g (C B - X i ^ 2) t Hcoord)
    (α : Fin n →₀ ℕ) (hα : α.degree ≤ d) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (C (B ^ α.degree) - (monomial α (1 : ℝ)) ^ 2)
      (boundedMonomialSquareOrder n t d)
      (boundedMonomialSquareBudget n d B Hcoord)) := by
  classical
  let K : ℝ := (B + 1) ^ d
  let Q : ℝ := boundedCoordinatePowerBudget B Hcoord d
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hbase : 1 ≤ B + 1 := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact boundedCoordinatePowerBudget_nonneg hB0 hHcoord d
  have hexp (i : Fin n) : α i ≤ d :=
    (Finsupp.le_degree i α).trans hα
  have hrel : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      BoundedModuleLEAt g (t + 2 * d) Q
        ((X i ^ α i : MvPolynomial (Fin n) ℝ) ^ 2)
        (C (B ^ α i)) := by
    intro i hi
    have cpower :=
      bounded_coordinate_power_square_bound_at hB hHcoord hcoord i (α i)
    have hbudget :
        boundedCoordinatePowerBudget B Hcoord (α i) ≤ Q := by
      unfold boundedCoordinatePowerBudget
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hbase (hexp i)) (by linarith)
    exact (cpower.mono
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (hexp i)) t)).weakenBound
        hbudget
  obtain ⟨cprod⟩ := BoundedModuleLEAt.prod
    (Finset.univ : Finset (Fin n))
    (fun i => ((X i ^ α i : MvPolynomial (Fin n) ℝ) ^ 2))
    (fun i => C (B ^ α i))
    (t + 2 * d) (2 * d) hQ hK
    (fun i _ => IsSOS_sq (X i ^ α i))
    (fun i _ => IsSOS_C_nonneg (B ^ α i) (pow_nonneg hB0 _))
    (fun i _ => by
      calc
        ((X i ^ α i : MvPolynomial (Fin n) ℝ) ^ 2).totalDegree ≤
            2 * (X i ^ α i : MvPolynomial (Fin n) ℝ).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ = 2 * α i := by simp
        _ ≤ 2 * d := Nat.mul_le_mul_left 2 (hexp i))
    (fun i _ => by
      calc
        (C (B ^ α i) : MvPolynomial (Fin n) ℝ).totalDegree ≤ 0 :=
          (MvPolynomial.totalDegree_C _).le
        _ ≤ 2 * d := Nat.zero_le _)
    (fun i _ => by
      have hvar :
          coeffL1Norm (X i : MvPolynomial (Fin n) ℝ) ≤ 1 := by
        simpa [MvPolynomial.X] using coeffL1Norm_monomial_le
          (n := n) (Finsupp.single i 1) (1 : ℝ)
      calc
        coeffL1Norm ((X i ^ α i : MvPolynomial (Fin n) ℝ) ^ 2) ≤
            coeffL1Norm (X i : MvPolynomial (Fin n) ℝ) ^ (α i * 2) := by
          rw [← pow_mul]
          exact coeffL1Norm_pow_le _ _
        _ ≤ 1 := by
          simpa using pow_le_pow_left₀ (coeffL1Norm_nonneg _) hvar (α i * 2)
        _ ≤ K := by
          dsimp [K]
          exact one_le_pow₀ hbase)
    (fun i _ => by
      calc
        coeffL1Norm (C (B ^ α i) : MvPolynomial (Fin n) ℝ) ≤
            B ^ α i := by
          simpa [abs_of_nonneg (pow_nonneg hB0 _)] using
            coeffL1Norm_C_le (n := n) (B ^ α i)
        _ ≤ K := by
          dsimp [K]
          exact (pow_le_pow_left₀ hB0 (by linarith) _).trans
            (pow_le_pow_right₀ hbase (hexp i)))
    hrel
  have hmon :
      (∏ i : Fin n, (X i : MvPolynomial (Fin n) ℝ) ^ α i) =
        monomial α 1 := by
    rw [← Finsupp.prod_pow]
    exact (MvPolynomial.monic_monomial_eq α).symm
  have hsum : α.degree = ∑ i : Fin n, α i := by
    change α.sum (fun _ e => e) = _
    exact Finsupp.sum_fintype α (fun _ e => e) (fun _ => rfl)
  have hscalar : (∏ i : Fin n, B ^ α i) = B ^ α.degree := by
    calc
      (∏ i : Fin n, B ^ α i) = B ^ ∑ i : Fin n, α i := by
        simpa using
          (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin n))
            (fun i => α i) B)
      _ = B ^ α.degree := by rw [← hsum]
  exact ⟨by
    simpa [boundedMonomialSquareOrder, boundedMonomialSquareBudget, K, Q]
      using cprod.congr (by
        rw [← map_prod, hscalar, Finset.prod_pow, hmon, map_pow])⟩

/-- Common order for bounded coefficient-envelope certificates. -/
def boundedCoeffEnvelopeOrder (n t d : ℕ) : ℕ :=
  boundedMonomialSquareOrder n t d + 2 * d

/-- Coefficient budget for one weighted monomial envelope certificate. -/
def boundedWeightedMonomialBudget
    (n d : ℕ) (B Hcoord : ℝ)
    (α : Fin n →₀ ℕ) (c : ℝ) : ℝ :=
  (c / 2) ^ 2 * boundedMonomialSquareBudget n d B Hcoord +
    coeffL1Norm
      ((C (c / 2) * monomial α (1 : ℝ) + 1) ^ 2)

theorem boundedWeightedMonomialBudget_nonneg
    (n d : ℕ) {B Hcoord : ℝ}
    (hB : 0 ≤ B) (hHcoord : 0 ≤ Hcoord)
    (α : Fin n →₀ ℕ) (c : ℝ) :
    0 ≤ boundedWeightedMonomialBudget n d B Hcoord α c := by
  unfold boundedWeightedMonomialBudget
  exact add_nonneg
    (mul_nonneg (sq_nonneg _)
      (boundedMonomialSquareBudget_nonneg n d hB hHcoord))
    (coeffL1Norm_nonneg _)

/-- One coefficient-weighted monomial admits a bounded one-sided
Archimedean certificate. -/
theorem bounded_weighted_monomial_plus_mem_of_degree_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B Hcoord : ℝ} {t d : ℕ}
    (hB : 1 ≤ B) (hHcoord : 0 ≤ Hcoord)
    (hcoord : ∀ i : Fin n,
      BoundedQuadraticModuleCertificate g (C B - X i ^ 2) t Hcoord)
    (α : Fin n →₀ ℕ) (hα : α.degree ≤ d) (c : ℝ) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (C (weightedMonomialBound B α c) + monomial α c)
      (boundedCoeffEnvelopeOrder n t d)
      (boundedWeightedMonomialBudget n d B Hcoord α c)) := by
  let M : MvPolynomial (Fin n) ℝ := monomial α 1
  obtain ⟨cmon⟩ :=
    bounded_monomial_square_bound_of_degree_at
      hB hHcoord hcoord α hα
  have hscaleNorm :
      coeffL1Norm ((C (c / 2) : MvPolynomial (Fin n) ℝ) ^ 2) ≤
        (c / 2) ^ 2 := by
    calc
      coeffL1Norm ((C (c / 2) : MvPolynomial (Fin n) ℝ) ^ 2) ≤
          coeffL1Norm (C (c / 2) : MvPolynomial (Fin n) ℝ) ^ 2 :=
        coeffL1Norm_pow_le _ _
      _ ≤ |c / 2| ^ 2 :=
        pow_le_pow_left₀ (coeffL1Norm_nonneg _)
          (coeffL1Norm_C_le (n := n) (c / 2)) 2
      _ = (c / 2) ^ 2 := sq_abs (c / 2)
  have cscaledRaw := cmon.sosMulOfNormLe
    (IsSOS_sq (C (c / 2))) hscaleNorm
  have cscaled : BoundedQuadraticModuleCertificate g
      ((C (c / 2)) ^ 2 *
        (C (B ^ α.degree) - M ^ 2))
      (boundedCoeffEnvelopeOrder n t d)
      ((c / 2) ^ 2 * boundedMonomialSquareBudget n d B Hcoord) := by
    have horder :
        ((C (c / 2) : MvPolynomial (Fin n) ℝ) ^ 2).totalDegree +
            boundedMonomialSquareOrder n t d ≤
          boundedCoeffEnvelopeOrder n t d := by
      have hcdeg :
          ((C (c / 2) : MvPolynomial (Fin n) ℝ) ^ 2).totalDegree = 0 := by
        rw [← MvPolynomial.C_pow]
        exact MvPolynomial.totalDegree_C _
      rw [hcdeg, Nat.zero_add]
      exact Nat.le_add_right
        (boundedMonomialSquareOrder n t d) (2 * d)
    simpa [M] using cscaledRaw.mono horder
  have hM : M.totalDegree = α.degree := by
    simpa [M] using totalDegree_monomial_one_eq_degree α
  have hbase :
      (C (c / 2) * M + 1).totalDegree ≤ d := by
    calc
      (C (c / 2) * M + 1).totalDegree ≤
          max (C (c / 2) * M).totalDegree
            (1 : MvPolynomial (Fin n) ℝ).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ d := by
        apply max_le
        · exact (MvPolynomial.totalDegree_mul _ _).trans (by
            simpa [hM] using hα)
        · simp
  let freeTerm : MvPolynomial (Fin n) ℝ :=
    (C (c / 2) * M + 1) ^ 2
  have hfreeDegree :
      freeTerm.totalDegree ≤ boundedCoeffEnvelopeOrder n t d := by
    calc
      freeTerm.totalDegree ≤ 2 * (C (c / 2) * M + 1).totalDegree := by
        dsimp [freeTerm]
        exact MvPolynomial.totalDegree_pow _ _
      _ ≤ 2 * d := Nat.mul_le_mul_left 2 hbase
      _ ≤ boundedCoeffEnvelopeOrder n t d := by
        simp [boundedCoeffEnvelopeOrder]
  let cfree := BoundedQuadraticModuleCertificate.ofSOS g freeTerm
    (IsSOS_sq (C (c / 2) * M + 1)) hfreeDegree
  have csum := cscaled.add cfree
  have hmon : monomial α c = C c * M := by
    dsimp [M]
    rw [MvPolynomial.C_mul_monomial]
    simp
  have hc_two :
      (C (c / 2) : MvPolynomial (Fin n) ℝ) * 2 = C c := by
    change C (c / 2) * C 2 = C c
    rw [← map_mul]
    congr 1
    ring
  have hlinear :
      C (c / 2) * M * 2 = C c * M := by
    calc
      C (c / 2) * M * 2 = (C (c / 2) * 2) * M := by ring
      _ = C c * M := by rw [hc_two]
  have hlinear' :
      C (c / 2) * monomial α (1 : ℝ) * 2 =
        C c * monomial α (1 : ℝ) := by
    simpa [M] using hlinear
  exact ⟨by
    simpa [boundedWeightedMonomialBudget, freeTerm, max_self] using
      csum.congr (by
        rw [hmon]
        dsimp [weightedMonomialBound, M, freeTerm]
        simp only [map_add, map_mul, map_pow, map_one]
        rw [← hlinear']
        ring)⟩

/-- Explicit coefficient budget for the positive weighted envelope of a
polynomial. -/
def boundedWeightedCoeffPlusBudget
    (n d : ℕ) (B Hcoord : ℝ)
    (q : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∑ α ∈ q.support,
    boundedWeightedMonomialBudget n d B Hcoord α (q.coeff α)

theorem bounded_weightedCoeffEnvelope_plus_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B Hcoord : ℝ} {t d : ℕ}
    (hB : 1 ≤ B) (hHcoord : 0 ≤ Hcoord)
    (hcoord : ∀ i : Fin n,
      BoundedQuadraticModuleCertificate g (C B - X i ^ 2) t Hcoord)
    (q : MvPolynomial (Fin n) ℝ)
    (hqDegree : q.totalDegree ≤ d) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (C (weightedCoeffEnvelope B q) + q)
      (boundedCoeffEnvelopeOrder n t d)
      (boundedWeightedCoeffPlusBudget n d B Hcoord q)) := by
  classical
  obtain ⟨csum⟩ := BoundedQuadraticModuleCertificate.sum_nonempty_of_bounds
    q.support
    (fun α => C (weightedMonomialBound B α (q.coeff α)) +
      monomial α (q.coeff α))
    (fun α => boundedWeightedMonomialBudget n d B Hcoord α (q.coeff α))
    (fun α hα => bounded_weighted_monomial_plus_mem_of_degree_at
      hB hHcoord hcoord α
        ((MvPolynomial.le_totalDegree hα).trans hqDegree) (q.coeff α))
  exact ⟨by
    simpa [boundedWeightedCoeffPlusBudget] using csum.congr (by
      simp only [weightedCoeffEnvelope, map_sum, Finset.sum_add_distrib,
        MvPolynomial.support_sum_monomial_coeff])⟩

/-- Explicit coefficient budget for the negative weighted envelope of a
polynomial. -/
def boundedWeightedCoeffMinusBudget
    (n d : ℕ) (B Hcoord : ℝ)
    (q : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∑ α ∈ q.support,
    boundedWeightedMonomialBudget n d B Hcoord α (-(q.coeff α))

theorem bounded_weightedCoeffEnvelope_minus_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B Hcoord : ℝ} {t d : ℕ}
    (hB : 1 ≤ B) (hHcoord : 0 ≤ Hcoord)
    (hcoord : ∀ i : Fin n,
      BoundedQuadraticModuleCertificate g (C B - X i ^ 2) t Hcoord)
    (q : MvPolynomial (Fin n) ℝ)
    (hqDegree : q.totalDegree ≤ d) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (C (weightedCoeffEnvelope B q) - q)
      (boundedCoeffEnvelopeOrder n t d)
      (boundedWeightedCoeffMinusBudget n d B Hcoord q)) := by
  classical
  have hterm : ∀ α ∈ q.support,
      Nonempty (BoundedQuadraticModuleCertificate g
        (C (weightedMonomialBound B α (q.coeff α)) -
          monomial α (q.coeff α))
        (boundedCoeffEnvelopeOrder n t d)
        (boundedWeightedMonomialBudget n d B Hcoord α (-(q.coeff α)))) := by
    intro α hα
    obtain ⟨cneg⟩ := bounded_weighted_monomial_plus_mem_of_degree_at
      hB hHcoord hcoord α
        ((MvPolynomial.le_totalDegree hα).trans hqDegree) (-(q.coeff α))
    exact ⟨cneg.congr (by
      have hsquare :
          (-(q.coeff α) / 2) ^ 2 = (q.coeff α / 2) ^ 2 := by ring
      simp [weightedMonomialBound, sub_eq_add_neg, hsquare])⟩
  obtain ⟨csum⟩ := BoundedQuadraticModuleCertificate.sum_nonempty_of_bounds
    q.support
    (fun α => C (weightedMonomialBound B α (q.coeff α)) -
      monomial α (q.coeff α))
    (fun α => boundedWeightedMonomialBudget n d B Hcoord α (-(q.coeff α)))
    hterm
  exact ⟨by
    simpa [boundedWeightedCoeffMinusBudget] using csum.congr (by
      simp only [weightedCoeffEnvelope, map_sum, Finset.sum_sub_distrib,
        MvPolynomial.support_sum_monomial_coeff])⟩

/-- Uniform upper budget for a coefficient envelope with a prescribed
support-cardinality and coefficient-norm bound. -/
def boundedCoeffEnvelopeBudgetUpper
    (supportCard n d : ℕ) (B Hcoord H : ℝ) : ℝ :=
  (supportCard : ℝ) * (H + 1) ^ 2 *
    (boundedMonomialSquareBudget n d B Hcoord + 1)

theorem boundedWeightedMonomialBudget_le
    (n d : ℕ) {B Hcoord H c : ℝ}
    (hB : 0 ≤ B) (hHcoord : 0 ≤ Hcoord)
    (hH : 0 ≤ H) (hc : |c| ≤ H)
    (α : Fin n →₀ ℕ) :
    boundedWeightedMonomialBudget n d B Hcoord α c ≤
      (H + 1) ^ 2 *
        (boundedMonomialSquareBudget n d B Hcoord + 1) := by
  let M : MvPolynomial (Fin n) ℝ := monomial α 1
  let Q := boundedMonomialSquareBudget n d B Hcoord
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact boundedMonomialSquareBudget_nonneg n d hB hHcoord
  have hH1 : 0 ≤ H + 1 := by linarith
  have hcdiv : |c / 2| ≤ H := by
    rw [abs_div]
    norm_num
    nlinarith
  have hcSq : (c / 2) ^ 2 ≤ (H + 1) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hcdiv.trans (by linarith)) 2
  have hMnorm : coeffL1Norm M ≤ 1 := by
    dsimp [M]
    simpa [MvPolynomial.X] using coeffL1Norm_monomial_le α (1 : ℝ)
  have hscaledNorm :
      coeffL1Norm (C (c / 2) * M) ≤ |c / 2| := by
    calc
      coeffL1Norm (C (c / 2) * M) ≤
          coeffL1Norm (C (c / 2) : MvPolynomial (Fin n) ℝ) *
            coeffL1Norm M :=
        coeffL1Norm_mul_le _ _
      _ ≤ |c / 2| * 1 := by
        exact mul_le_mul (coeffL1Norm_C_le (n := n) (c / 2))
          hMnorm (coeffL1Norm_nonneg _) (abs_nonneg _)
      _ = |c / 2| := by ring
  have hbaseNorm :
      coeffL1Norm (C (c / 2) * M + 1) ≤ H + 1 := by
    calc
      coeffL1Norm (C (c / 2) * M + 1) ≤
          coeffL1Norm (C (c / 2) * M) +
            coeffL1Norm (1 : MvPolynomial (Fin n) ℝ) :=
        coeffL1Norm_add_le _ _
      _ ≤ |c / 2| + 1 := by
        exact add_le_add hscaledNorm
          (by simpa using coeffL1Norm_C_le (n := n) (1 : ℝ))
      _ ≤ H + 1 := by
        simpa [add_comm] using add_le_add_right hcdiv 1
  have hfree :
      coeffL1Norm ((C (c / 2) * M + 1) ^ 2) ≤
        (H + 1) ^ 2 := by
    exact (coeffL1Norm_pow_le _ 2).trans
      (pow_le_pow_left₀ (coeffL1Norm_nonneg _) hbaseNorm 2)
  unfold boundedWeightedMonomialBudget
  dsimp [M, Q] at hfree ⊢
  calc
    (c / 2) ^ 2 * boundedMonomialSquareBudget n d B Hcoord +
        coeffL1Norm ((C (c / 2) * monomial α 1 + 1) ^ 2) ≤
      (H + 1) ^ 2 * boundedMonomialSquareBudget n d B Hcoord +
        (H + 1) ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcSq hQ) hfree
    _ = (H + 1) ^ 2 *
        (boundedMonomialSquareBudget n d B Hcoord + 1) := by ring

theorem boundedWeightedCoeffPlusBudget_le
    (n d : ℕ) {B Hcoord H : ℝ}
    (hB : 0 ≤ B) (hHcoord : 0 ≤ Hcoord) (hH : 0 ≤ H)
    (q : MvPolynomial (Fin n) ℝ) (hqNorm : coeffL1Norm q ≤ H) :
    boundedWeightedCoeffPlusBudget n d B Hcoord q ≤
      boundedCoeffEnvelopeBudgetUpper q.support.card n d B Hcoord H := by
  unfold boundedWeightedCoeffPlusBudget boundedCoeffEnvelopeBudgetUpper
  calc
    ∑ α ∈ q.support,
        boundedWeightedMonomialBudget n d B Hcoord α (q.coeff α) ≤
      ∑ _α ∈ q.support,
        (H + 1) ^ 2 *
          (boundedMonomialSquareBudget n d B Hcoord + 1) := by
      exact Finset.sum_le_sum fun α hα =>
        boundedWeightedMonomialBudget_le n d hB hHcoord hH
          ((abs_coeff_le_coeffL1Norm q α).trans hqNorm) α
    _ = (q.support.card : ℝ) * (H + 1) ^ 2 *
        (boundedMonomialSquareBudget n d B Hcoord + 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

theorem boundedWeightedCoeffMinusBudget_le
    (n d : ℕ) {B Hcoord H : ℝ}
    (hB : 0 ≤ B) (hHcoord : 0 ≤ Hcoord) (hH : 0 ≤ H)
    (q : MvPolynomial (Fin n) ℝ) (hqNorm : coeffL1Norm q ≤ H) :
    boundedWeightedCoeffMinusBudget n d B Hcoord q ≤
      boundedCoeffEnvelopeBudgetUpper q.support.card n d B Hcoord H := by
  unfold boundedWeightedCoeffMinusBudget boundedCoeffEnvelopeBudgetUpper
  calc
    ∑ α ∈ q.support,
        boundedWeightedMonomialBudget n d B Hcoord α (-(q.coeff α)) ≤
      ∑ _α ∈ q.support,
        (H + 1) ^ 2 *
          (boundedMonomialSquareBudget n d B Hcoord + 1) := by
      exact Finset.sum_le_sum fun α hα =>
        boundedWeightedMonomialBudget_le n d hB hHcoord hH
          (by simpa using (abs_coeff_le_coeffL1Norm q α).trans hqNorm) α
    _ = (q.support.card : ℝ) * (H + 1) ^ 2 *
        (boundedMonomialSquareBudget n d B Hcoord + 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

end OptimalConvergenceRates.GeneralArchimedean

end
