import OptimalConvergenceRates.CQC.EqualityCertificate
import OptimalConvergenceRates.CQC.EqualityLiftDegree
import OptimalConvergenceRates.CQC.MultiplierRemovalTheorem
import OptimalConvergenceRates.CQC.ZeroMinimum

/-!
# Fixed-instance transfer with encoded equalities
-/

noncomputable section

open MvPolynomial Set

namespace OptimalConvergenceRates
namespace CQCInternal

open GeneralArchimedean

variable {n m : ℕ}

theorem exists_fixedInstanceTransferWithEqualities_raw
    (hn : 0 < n)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hcqc : CQCWithEqualities g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ P : MvPolynomial (Fin (n + m)) ℝ,
      ∃ a : MvPolynomial (Fin n) ℝ,
      ∃ c Clog : ℝ, ∃ s : ℕ,
        1 ≤ c ∧ 0 < Clog ∧
        IsNonnegOn P (Hypercube (n + m)) ∧
        (0 < m → ∀ {e d : ℕ}, 2 ≤ e →
          (∀ i, (g i).totalDegree ≤ e) → p.totalDegree ≤ d →
          P.totalDegree ≤ d + 4 * m * (e - 1)) ∧
        (∀ x ∈ KrivineStengle.basicClosedSet g,
          0 < MvPolynomial.eval x a) ∧
        ((∃ x ∈ KrivineStengle.basicClosedSet g,
            MvPolynomial.eval x p = 0) →
          ∃ z ∈ Hypercube (n + m), MvPolynomial.eval z P = 0) ∧
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 → ∀ {r : ℕ},
          P + C (ε / c) ∈ BoxQuadraticModule (n + m) r →
          p + C ε ∈ GenQuadraticModule g
            ((s + generatorDegree g * r) +
              Nat.ceil (Clog * (1 + Real.log (c / ε)))) := by
  obtain ⟨R, M, hR, hM, _hVsub, hstrict, hpenalty⟩ :=
    exists_penalizedEqualitySlackObjective_nonneg_on_scaledHypercube
      hn hne harch hcqc hp
  let Psmall := descendedEqualitySlackObjective g p M
  let Pdesc := embedSelectedPolynomial g Psmall
  let P := unitBoxLiftPolynomial R Pdesc
  let a := determinantMultiplier (selectedGenerator g)
  have hsmallNonneg :
      ∀ z ∈ slackValueBox R, 0 ≤ MvPolynomial.eval z Psmall := by
    simpa only [Psmall] using
      descendedEqualitySlackObjective_nonneg_on_slackValueBox
        hR g p hpenalty
  have hdescNonneg :
      ∀ z ∈ slackValueBox R, 0 ≤ MvPolynomial.eval z Pdesc := by
    simpa only [Pdesc] using
      embedSelectedPolynomial_nonneg_on_slackValueBox g Psmall hsmallNonneg
  have hPnonneg : IsNonnegOn P (Hypercube (n + m)) :=
    unitBoxLiftPolynomial_nonneg_on_hypercube hR hdescNonneg
  have hbase :
      ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ j, |x j| < R := by
    intro x hx j
    have hz := hstrict (equalitySlackLift g x)
      (equalitySlackLift_mem_equalitySlackZeroSet hx)
      (Fin.castAdd (selectedConstraintCount g) j)
    change |basePoint (equalitySlackLift g x) j| < R at hz
    simpa only [basePoint_equalitySlackLift] using hz
  have hslack :
      ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ i,
        MvPolynomial.eval x (g i) < R ^ 2 := by
    intro x hx i
    by_cases hi : HasOppositeConstraint g i
    · rw [eval_eq_zero_of_hasOppositeConstraint hx hi]
      positivity
    · let is : SelectedConstraintIndex g := ⟨i, Or.inl hi⟩
      let k := selectedIndexOf g is
      have hkraw : selectedRawIndex g k = i := by
        simp [k, is]
      have hkordinary : ¬SelectedEncodesEquality g k := by
        simpa [SelectedEncodesEquality, hkraw] using hi
      have hz := hstrict (equalitySlackLift g x)
        (equalitySlackLift_mem_equalitySlackZeroSet hx)
        (Fin.natAdd n k)
      change |slackPoint (equalitySlackLift g x) k| < R at hz
      rw [slackPoint_equalitySlackLift] at hz
      simp only [hkordinary, ↓reduceIte] at hz
      have hnonneg : 0 ≤ MvPolynomial.eval x (g i) := hx i
      have hsqrt :
          (Real.sqrt (MvPolynomial.eval x (g i))) ^ 2 =
            MvPolynomial.eval x (g i) :=
        Real.sq_sqrt hnonneg
      have hz' :
          Real.sqrt (MvPolynomial.eval x (g i)) < R := by
        simpa [selectedGenerator, hkraw, abs_of_nonneg (Real.sqrt_nonneg _)]
          using hz
      have hy0 : 0 ≤ Real.sqrt (MvPolynomial.eval x (g i)) :=
        Real.sqrt_nonneg _
      have hproduct :
          0 < (R - Real.sqrt (MvPolynomial.eval x (g i))) *
            (R + Real.sqrt (MvPolynomial.eval x (g i))) :=
        mul_pos (sub_pos.mpr hz') (add_pos_of_pos_of_nonneg hR hy0)
      nlinarith
  have hPdegree :
      0 < m → ∀ {e d : ℕ}, 2 ≤ e →
        (∀ i, (g i).totalDegree ≤ e) → p.totalDegree ≤ d →
        P.totalDegree ≤ d + 4 * m * (e - 1) := by
    intro hm e d he hg hpdegree
    exact totalDegree_unitBoxLiftPolynomial_equality_le
      hm he g p M R hg hpdegree
  have ha :
      ∀ x ∈ KrivineStengle.basicClosedSet g,
        0 < MvPolynomial.eval x a := by
    simpa only [a] using selectedDeterminantMultiplier_posOn hcqc
  have hpull :
      generatorSlackSubstitution g Pdesc =
        a ^ 2 * p + C M * equalityRepresentativeSum g := by
    simpa only [Pdesc, Psmall, a] using
      generatorSlackSubstitution_embedded_descendedEqualitySlackObjective g p M
  have hPzero :
      (∃ x ∈ KrivineStengle.basicClosedSet g,
          MvPolynomial.eval x p = 0) →
        ∃ z ∈ Hypercube (n + m), MvPolynomial.eval z P = 0 := by
    rintro ⟨x, hx, hpx⟩
    refine ⟨feasibleToUnitPoint R g x,
      feasibleToUnitPoint_mem_hypercube hR hx (hbase x hx) (hslack x hx), ?_⟩
    rw [show P = unitBoxLiftPolynomial R Pdesc by rfl,
      eval_unitBoxLiftPolynomial_feasibleToUnitPoint hR.ne', hpull,
      MvPolynomial.eval_add, MvPolynomial.eval_mul,
      MvPolynomial.eval_pow, hpx,
      MvPolynomial.eval_mul,
      eval_equalityRepresentativeSum_eq_zero hx]
    ring
  obtain ⟨sbox, hmodule⟩ := unitCube_certificate_pullback
    hR g hne harch hbase hslack
  obtain ⟨seq, hequality⟩ :=
    exists_order_neg_equalityRepresentativeSum (g := g) hM
  obtain ⟨c₀, Clog, hc₀, hClog, hremove⟩ :=
    removePositiveMultiplier_log g p a hne harch ha
  let c : ℝ := max c₀ 1
  let s : ℕ := max sbox seq
  have hc : 1 ≤ c := le_max_right _ _
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hc₀c : c₀ ≤ c := le_max_left _ _
  refine ⟨P, a, c, Clog, s, hc, hClog, hPnonneg, hPdegree, ha, hPzero, ?_⟩
  intro ε hε hεhalf r hbox
  let δ : ℝ := ε / c
  have hδ : 0 < δ := div_pos hε hcpos
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    calc
      ε / c ≤ ε := (div_le_iff₀ hcpos).2 (by nlinarith)
      _ ≤ 1 / 2 := hεhalf
  have hpulled := hmodule hbox
  have hremainder :
      a ^ 2 * p + C M * equalityRepresentativeSum g + C δ ∈
        GenQuadraticModule g (sbox + generatorDegree g * r) := by
    convert hpulled using 1
    simp only [P, map_add, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
    rw [unitCubePullback_unitBoxLiftPolynomial hR.ne' g, hpull]
  have hsum := genQuadraticModule_add hremainder hequality
  have hweighted0 :
      a ^ 2 * p + C δ ∈
        GenQuadraticModule g
          (max (sbox + generatorDegree g * r) seq) := by
    convert hsum using 1; ring
  have hfixed :
      max (sbox + generatorDegree g * r) seq ≤
        s + generatorDegree g * r := by
    dsimp [s]
    omega
  have hweighted :
      a ^ 2 * p + C δ ∈
        GenQuadraticModule g (s + generatorDegree g * r) :=
    GenQuadraticModule_mono hfixed hweighted0
  have hremoved := hremove hδ hδhalf hweighted
  have hgap : 0 ≤ ε - c₀ * δ := by
    dsimp [δ]
    have hratio : c₀ / c ≤ 1 := (div_le_one hcpos).2 hc₀c
    have hfactor : 0 ≤ 1 - c₀ / c := sub_nonneg.mpr hratio
    calc
      0 ≤ ε * (1 - c₀ / c) := mul_nonneg hε.le hfactor
      _ = ε - c₀ * (ε / c) := by field_simp
  have hconst := genQuadraticModule_C_nonneg g hgap
  have hsum' := genQuadraticModule_add hremoved hconst
  have htarget : p + C ε ∈ GenQuadraticModule g
      (max ((s + generatorDegree g * r) + Nat.ceil
        (Clog * (1 + Real.log (1 / δ)))) 0) := by
    have hC : (C ε : MvPolynomial (Fin n) ℝ) =
        C (c₀ * δ) + C (ε - c₀ * δ) := by
      rw [← map_add]
      congr 1
      ring
    rw [hC]
    simpa only [add_assoc] using hsum'
  have hlog : 1 / δ = c / ε := by
    dsimp [δ]
    field_simp
  simpa [hlog] using htarget

end CQCInternal
end OptimalConvergenceRates

end
