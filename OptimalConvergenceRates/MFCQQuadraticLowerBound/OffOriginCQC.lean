/-
  Linear independence of the active gradients away from the origin.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.Qualifications

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

private theorem linearIndependent_of_card_le_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → (Fin 3 → ℝ))
    (hcard : Fintype.card ι ≤ 2)
    (hne : ∀ i, v i ≠ 0)
    (hpair : ∀ i j, i ≠ j → ∀ a b : ℝ,
      a • v i + b • v j = 0 → a = 0 ∧ b = 0) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro a hsum i
  by_cases hother : ∃ j, j ≠ i ∧ a j ≠ 0
  · obtain ⟨j, hji, _⟩ := hother
    have hall (k : ι) : k = i ∨ k = j := by
      by_contra hk
      push Not at hk
      have hthree : ({i, j, k} : Finset ι).card = 3 := by
        simp [hji, Ne.symm hji, hk.1, hk.2, Ne.symm hk.1, Ne.symm hk.2]
      have hle := Finset.card_le_card
        (show ({i, j, k} : Finset ι) ⊆ Finset.univ by simp)
      rw [hthree, Finset.card_univ] at hle
      omega
    have huniv : (Finset.univ : Finset ι) = {i, j} := by
      ext k
      simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
        Finset.mem_singleton]
      exact hall k
    have hpairSum : a i • v i + a j • v j = 0 := by
      change (∑ k ∈ Finset.univ, a k • v k) = 0 at hsum
      rw [huniv] at hsum
      simpa [hji, Ne.symm hji] using hsum
    exact (hpair i j (Ne.symm hji) (a i) (a j) hpairSum).1
  · have hzero (j : ι) (hji : j ≠ i) : a j = 0 := by
      by_contra haj
      exact hother ⟨j, hji, haj⟩
    have hsingle : a i • v i = 0 := by
      calc
        a i • v i = ∑ k ∈ Finset.univ, a k • v k := by
          symm
          apply Finset.sum_eq_single i
          · intro j _ hji
            rw [hzero j hji, zero_smul]
          · simp
        _ = 0 := hsum
    exact (smul_eq_zero.mp hsingle).resolve_right (hne i)

private theorem first_gradient_last (z : Fin 3 → ℝ) (i : Fin 4) :
    gradientAt (generators i.castSucc) z 2 = 1 := by
  fin_cases i <;> simp

private theorem first_gradient_ne {z : Fin 3 → ℝ}
    (huv : z 0 ≠ 0 ∨ z 1 ≠ 0) {i j : Fin 4} (hij : i ≠ j) :
    gradientAt (generators i.castSucc) z ≠
      gradientAt (generators j.castSucc) z := by
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals
    intro h
    have hx := congrFun h 0
    have hy := congrFun h 1
    simp at hx hy
    rcases huv with hu | hv
    · apply hu
      nlinarith
    · apply hv
      nlinarith

private theorem first_gradient_pair_relation {z : Fin 3 → ℝ}
    (huv : z 0 ≠ 0 ∨ z 1 ≠ 0) (i j : Fin 4) (hij : i ≠ j)
    (a b : ℝ)
    (hrelation :
      a • gradientAt (generators i.castSucc) z +
        b • gradientAt (generators j.castSucc) z = 0) :
    a = 0 ∧ b = 0 := by
  have ht := congrFun hrelation 2
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
    first_gradient_last, smul_eq_mul, mul_one] at ht
  have hab : b = -a := by linarith
  by_cases ha : a = 0
  · exact ⟨ha, by linarith⟩
  · exfalso
    apply first_gradient_ne huv hij
    funext k
    have hk := congrFun hrelation k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hk
    rw [hab] at hk
    have hproduct : a *
        (gradientAt (generators i.castSucc) z k -
          gradientAt (generators j.castSucc) z k) = 0 := by
      linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left ha)

private theorem uv_zero_of_XY {u v : ℝ}
    (hX : u ^ 2 - v ^ 2 = 0) (hY : u * v = 0) :
    u = 0 ∧ v = 0 := by
  rcases mul_eq_zero.mp hY with hu | hv
  · refine ⟨hu, ?_⟩
    nlinarith [sq_nonneg v]
  · refine ⟨?_, hv⟩
    nlinarith [sq_nonneg u]

private theorem first_active_card_le_two (z : Fin 3 → ℝ)
    (huv : z 0 ≠ 0 ∨ z 1 ≠ 0) :
    Fintype.card
      {i : Fin 4 // eval z (generators i.castSucc) = 0} ≤ 2 := by
  classical
  let p : Fin 4 → Prop := fun i ↦ eval z (generators i.castSucc) = 0
  have contradict_uv (hX : z 0 ^ 2 - z 1 ^ 2 = 0)
      (hY : z 0 * z 1 = 0) : False := by
    have hzero := uv_zero_of_XY hX hY
    exact huv.elim (fun h ↦ h hzero.1) (fun h ↦ h hzero.2)
  have h012 : ¬(p 0 ∧ p 1 ∧ p 2) := by
    rintro ⟨h0, h1, h2⟩
    simp [p] at h0 h1 h2
    apply contradict_uv
    · nlinarith
    · nlinarith
  have h013 : ¬(p 0 ∧ p 1 ∧ p 3) := by
    rintro ⟨h0, h1, h3⟩
    simp [p] at h0 h1 h3
    apply contradict_uv
    · nlinarith
    · nlinarith
  have h023 : ¬(p 0 ∧ p 2 ∧ p 3) := by
    rintro ⟨h0, h2, h3⟩
    simp [p] at h0 h2 h3
    apply contradict_uv
    · nlinarith
    · nlinarith
  have h123 : ¬(p 1 ∧ p 2 ∧ p 3) := by
    rintro ⟨h1, h2, h3⟩
    simp [p] at h1 h2 h3
    apply contradict_uv
    · nlinarith
    · nlinarith
  rw [Fintype.card_subtype]
  by_cases h0 : p 0 <;> by_cases h1 : p 1 <;>
    by_cases h2 : p 2 <;> by_cases h3 : p 3
  all_goals first
    | exact (h012 ⟨h0, h1, h2⟩).elim
    | exact (h013 ⟨h0, h1, h3⟩).elim
    | exact (h023 ⟨h0, h2, h3⟩).elim
    | exact (h123 ⟨h1, h2, h3⟩).elim
    | (rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_four];
       change (((if p 0 then 1 else 0) + (if p 1 then 1 else 0)) +
         (if p 2 then 1 else 0)) + (if p 3 then 1 else 0) ≤ 2;
       simp [h0, h1, h2, h3])

private theorem first_active_linearIndependent {z : Fin 3 → ℝ}
    (huv : z 0 ≠ 0 ∨ z 1 ≠ 0) :
    LinearIndependent ℝ
      (fun i : {i : Fin 4 // eval z (generators i.castSucc) = 0} ↦
        gradientAt (generators i.1.castSucc) z) := by
  apply linearIndependent_of_card_le_two _ (first_active_card_le_two z huv)
  · intro i hzero
    have hlast := congrFun hzero 2
    simpa [first_gradient_last] using hlast
  · intro i j hij
    apply first_gradient_pair_relation huv i.1 j.1
    intro hval
    apply hij
    exact Subtype.ext hval

/-- CQC/LICQ holds at every feasible point other than the origin. -/
theorem cqc_off_origin {z : Fin 3 → ℝ} (hz : z ∈ feasibleSet)
    (hzOrigin : z ≠ origin) : CQCAt generators z := by
  classical
  refine ⟨hz, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro a hsum target
  let active : Fin 5 → Prop := fun i ↦ eval z (generators i) = 0
  let c : Fin 5 → ℝ := fun i ↦ if hi : active i then a ⟨i, hi⟩ else 0
  have hc_active (i : Fin 5) (hi : active i) : c i = a ⟨i, hi⟩ := by
    simp [c, hi]
  have hc_inactive (i : Fin 5) (hi : ¬active i) : c i = 0 := by
    simp [c, hi]
  have hsum5 :
      ∑ i : Fin 5, c i • gradientAt (generators i) z = 0 := by
    calc
      ∑ i : Fin 5, c i • gradientAt (generators i) z =
          ∑ i ∈ Finset.univ.filter active,
            c i • gradientAt (generators i) z := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : active i
        · rw [ite_eq_left hi]
        · rw [ite_eq_right hi, hc_inactive i hi, zero_smul]
      _ = ∑ i : {i : Fin 5 // active i},
          c i.1 • gradientAt (generators i.1) z :=
        Finset.sum_subtype _ (by simp) _
      _ = ∑ i : {i : Fin 5 // active i},
          a i • gradientAt (generators i.1) z := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hc_active i.1 i.2]
      _ = 0 := hsum
  by_cases huv : z 0 ≠ 0 ∨ z 1 ≠ 0
  · have hterm0 : c 0 *
        (-2 * z 0 * z 0 + 6 * z 1 * z 1 + 2 * z 2) = 0 := by
      by_cases h0 : active 0
      · have heval := h0
        simp [active, eval_generator_zero] at heval
        have hinner : -2 * z 0 * z 0 + 6 * z 1 * z 1 + 2 * z 2 = 0 := by nlinarith
        rw [hinner, mul_zero]
      · rw [hc_inactive 0 h0, zero_mul]
    have hterm1 : c 1 *
        (6 * z 0 * z 0 - 2 * z 1 * z 1 + 2 * z 2) = 0 := by
      by_cases h1 : active 1
      · have heval := h1
        simp [active, eval_generator_one] at heval
        have hinner : 6 * z 0 * z 0 - 2 * z 1 * z 1 + 2 * z 2 = 0 := by nlinarith
        rw [hinner, mul_zero]
      · rw [hc_inactive 1 h1, zero_mul]
    have hterm2 : c 2 *
        ((2 * z 0 - 4 * z 1) * z 0 +
          (2 * z 1 - 4 * z 0) * z 1 + 2 * z 2) = 0 := by
      by_cases h2 : active 2
      · have heval := h2
        simp [active, eval_generator_two] at heval
        have hinner : (2 * z 0 - 4 * z 1) * z 0 +
            (2 * z 1 - 4 * z 0) * z 1 + 2 * z 2 = 0 := by nlinarith
        rw [hinner, mul_zero]
      · rw [hc_inactive 2 h2, zero_mul]
    have hterm3 : c 3 *
        ((2 * z 0 + 4 * z 1) * z 0 +
          (2 * z 1 + 4 * z 0) * z 1 + 2 * z 2) = 0 := by
      by_cases h3 : active 3
      · have heval := h3
        simp [active, eval_generator_three] at heval
        have hinner : (2 * z 0 + 4 * z 1) * z 0 +
            (2 * z 1 + 4 * z 0) * z 1 + 2 * z 2 = 0 := by nlinarith
        rw [hinner, mul_zero]
      · rw [hc_inactive 3 h3, zero_mul]
    have hdotsum := congrArg
      (fun w : Fin 3 → ℝ ↦
        ∑ j : Fin 3, w j * (![z 0, z 1, 2 * z 2] : Fin 3 → ℝ) j)
      hsum5
    simp [Fin.sum_univ_five, Fin.sum_univ_three] at hdotsum
    have hc4Product : c 4 *
        (-2 * z 0 ^ 2 - 2 * z 1 ^ 2 - 4 * z 2 ^ 2) = 0 := by
      nlinarith
    have hfactor : -2 * z 0 ^ 2 - 2 * z 1 ^ 2 - 4 * z 2 ^ 2 ≠ 0 := by
      rcases huv with hu | hv
      · nlinarith [sq_pos_of_ne_zero hu, sq_nonneg (z 1), sq_nonneg (z 2)]
      · nlinarith [sq_nonneg (z 0), sq_pos_of_ne_zero hv, sq_nonneg (z 2)]
    have hc4 : c 4 = 0 :=
      (mul_eq_zero.mp hc4Product).resolve_right hfactor
    have hsum4 :
        ∑ i : Fin 4, c i.castSucc • gradientAt (generators i.castSucc) z = 0 := by
      simpa [Fin.sum_univ_five, Fin.sum_univ_four, hc4] using hsum5
    let firstActive : Fin 4 → Prop :=
      fun i ↦ eval z (generators i.castSucc) = 0
    have hfirstSum :
        ∑ i : {i : Fin 4 // firstActive i},
          c i.1.castSucc • gradientAt (generators i.1.castSucc) z = 0 := by
      calc
        ∑ i : {i : Fin 4 // firstActive i},
            c i.1.castSucc • gradientAt (generators i.1.castSucc) z =
            ∑ i ∈ Finset.univ.filter firstActive,
              c i.castSucc • gradientAt (generators i.castSucc) z :=
          (Finset.sum_subtype (Finset.univ.filter firstActive) (fun i ↦ by simp) (fun i ↦ c i.castSucc • gradientAt (generators i.castSucc) z)).symm
        _ = ∑ i : Fin 4,
              c i.castSucc • gradientAt (generators i.castSucc) z := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : firstActive i
          · rw [ite_eq_left hi]
          · have hinactive : ¬active i.castSucc := by simpa [firstActive, active]
            rw [ite_eq_right hi, hc_inactive i.castSucc hinactive, zero_smul]
        _ = 0 := hsum4
    have hfirstZero := (Fintype.linearIndependent_iff.mp
      (first_active_linearIndependent huv))
      (fun i ↦ c i.1.castSucc) hfirstSum
    have hcFirst (i : Fin 4) : c i.castSucc = 0 := by
      by_cases hi : eval z (generators i.castSucc) = 0
      · exact hfirstZero ⟨i, hi⟩
      · exact hc_inactive i.castSucc (by simpa [active])
    have hcAll (i : Fin 5) : c i = 0 := by
      fin_cases i
      · exact hcFirst 0
      · exact hcFirst 1
      · exact hcFirst 2
      · exact hcFirst 3
      · exact hc4
    calc
      a target = c target.1 := (hc_active target.1 target.2).symm
      _ = 0 := hcAll target.1
  · push Not at huv
    have ht : z 2 ≠ 0 := by
      intro ht
      apply hzOrigin
      funext i
      fin_cases i <;> simp [origin, huv.1, huv.2, ht]
    have hfirstInactive (i : Fin 4) : ¬active i.castSucc := by
      intro hi
      fin_cases i <;> simp [active, huv.1, huv.2] at hi <;> exact ht hi
    have hcFirst (i : Fin 4) : c i.castSucc = 0 :=
      hc_inactive i.castSucc (hfirstInactive i)
    have hc0 : c 0 = 0 := hcFirst 0
    have hc1 : c 1 = 0 := hcFirst 1
    have hc2 : c 2 = 0 := hcFirst 2
    have hc3 : c 3 = 0 := hcFirst 3
    have htcoord := congrFun hsum5 2
    simp [Fin.sum_univ_five, hc0, hc1, hc2, hc3, huv.1, huv.2] at htcoord
    have hc4 : c 4 = 0 := by
      rcases htcoord with hc4 | ht0
      · exact hc4
      · exact (ht ht0).elim
    have hcAll (i : Fin 5) : c i = 0 := by
      fin_cases i
      · exact hcFirst 0
      · exact hcFirst 1
      · exact hcFirst 2
      · exact hcFirst 3
      · exact hc4
    calc
      a target = c target.1 := (hc_active target.1 target.2).symm
      _ = 0 := hcAll target.1

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
