/-
  OptimalConvergenceRates/KrivineStengle/ConditionalNonnegative.lean

  The certificate theorem reduced to finite ordered-field sign realization.
-/
import OptimalConvergenceRates.KrivineStengle.LocalizedCone
import OptimalConvergenceRates.KrivineStengle.OrderedFractionField

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- The finite real sign-realization principle used by the certificate argument.
It packages finitely many weak inequalities and one strict inequality. -/
def FiniteSignRealizationStatement : Prop :=
  ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (F : Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (phi : MvPolynomial (Fin n) ℝ →+* F),
    (∀ i, 0 ≤ phi (g i)) → phi p < 0 →
      ∃ x : Fin n → ℝ, x ∈ basicClosedSet g ∧ MvPolynomial.eval x p < 0

/-- The short localization/separation proof of Krivine--Stengle, conditional only on finite
ordered-field sign realization. -/
theorem nonnegative_krivine_stengle_of_signRealization
    (hsign : FiniteSignRealizationStatement)
    {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsNonnegOn p (basicClosedSet g)) :
    Nonempty (KSWitness g p) := by
  by_cases hp0 : p = 0
  · subst p
    exact ⟨⟨1, by simp, 0, 0, preorderingMem_zero g, preorderingMem_zero g, by simp⟩⟩
  · apply localizedCertificateCone_extract hp0
    by_contra hneg
    have hproper : IsProperSquareCone (localizedCertificateCone g p) :=
      ⟨localizedCertificateCone_isSquareCone g p, hneg⟩
    obtain ⟨sep⟩ := exists_orderedFieldSeparator hproper
    let F := sep.FieldType
    letI : Field F := sep.field
    letI : LinearOrder F := sep.order
    letI : IsStrictOrderedRing F := sep.strictOrderedRing
    let phi : MvPolynomial (Fin n) ℝ →+* F :=
      sep.map.comp (algebraMap _ (Localization.Away p))
    have hg : ∀ i, 0 ≤ phi (g i) := by
      intro i
      exact sep.nonneg (localizedCertificateCone_generator g p i)
    have hp_nonpos : phi p ≤ 0 := by
      have h := sep.nonneg (localizedCertificateCone_neg_self g p)
      simpa [phi] using h
    have hp_ne : phi p ≠ 0 := by
      have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℝ) (Localization.Away p) p) :=
        IsLocalization.Away.algebraMap_isUnit p
      exact (hu.map sep.map).ne_zero
    have hp_neg : phi p < 0 := lt_of_le_of_ne hp_nonpos hp_ne
    obtain ⟨x, hx, hpx⟩ := hsign g p F phi hg hp_neg
    exact (not_lt_of_ge (hp x hx)) hpx

/-- A Krivine--Stengle witness always implies nonnegativity on the basic closed set. -/
theorem KSWitness.nonnegOn {n m : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} (w : KSWitness g p) :
    IsNonnegOn p (basicClosedSet g) := by
  intro x hx
  have hS : 0 ≤ MvPolynomial.eval x w.S := w.hS.nonnegOn x hx
  have hT : 0 ≤ MvPolynomial.eval x w.T := w.hT.nonnegOn x hx
  by_contra hpneg
  have hpneg' : MvPolynomial.eval x p < 0 := lt_of_not_ge hpneg
  have hleft : MvPolynomial.eval x p * MvPolynomial.eval x w.S ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hpneg'.le hS
  have hpow_ne : (MvPolynomial.eval x p) ^ w.k ≠ 0 :=
    pow_ne_zero _ (ne_of_lt hpneg')
  have hpow : 0 < (MvPolynomial.eval x p) ^ (2 * w.k) := by
    rw [show 2 * w.k = w.k + w.k by omega, pow_add]
    exact mul_self_pos.mpr hpow_ne
  have hright : 0 < (MvPolynomial.eval x p) ^ (2 * w.k) + MvPolynomial.eval x w.T :=
    add_pos_of_pos_of_nonneg hpow hT
  have heval := congrArg (MvPolynomial.eval x) w.identity
  simp only [map_mul, map_add, map_pow] at heval
  exact (not_lt_of_ge hleft) (heval.symm ▸ hright)

end OptimalConvergenceRates.KrivineStengle

end
