/-
  OptimalConvergenceRates/KrivineStengle/SignTransfer.lean

  Interfaces separating ordered real-closure existence from real-closed sign transfer.
-/
import OptimalConvergenceRates.KrivineStengle.ConditionalNonnegative
import OptimalConvergenceRates.KrivineStengle.PolynomialSigns
import OptimalConvergenceRates.KrivineStengle.SignFormula

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

/-- An ordered real-closed algebraic target is not required at this interface: only an ordered
embedding into some real-closed field is used by finite sign transfer. -/
structure OrderedRealClosureData (F : Type) [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] where
  Carrier : Type
  field : Field Carrier
  order : LinearOrder Carrier
  strictOrderedRing : @IsStrictOrderedRing Carrier field.toSemiring order.toPartialOrder
  realClosed : @IsRealClosed Carrier field
  embedding : F →+*o Carrier

/-- Existence of an ordered real-closed extension for every ordered field. -/
def OrderedRealClosureExistenceStatement : Prop :=
  ∀ (F : Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F],
    Nonempty (OrderedRealClosureData F)

/-- The real-closed transfer theorem needed after constructing ordered real closures. -/
def RealClosedFiniteSignTransferStatement : Prop :=
  ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (F : Type) [Field F] [LinearOrder F] [IsStrictOrderedRing F] [IsRealClosed F]
    (phi : MvPolynomial (Fin n) ℝ →+* F),
    (∀ i, 0 ≤ phi (g i)) → phi p < 0 →
      ∃ x : Fin n → ℝ, x ∈ basicClosedSet g ∧ MvPolynomial.eval x p < 0

/-- Ordered real-closure existence plus transfer between real-closed fields gives the exact
finite sign-realization statement consumed by the certificate theorem. -/
theorem finiteSignRealization_of_realClosure_and_transfer
    (hclosure : OrderedRealClosureExistenceStatement)
    (htransfer : RealClosedFiniteSignTransferStatement) :
    FiniteSignRealizationStatement := by
  intro n m g p F _ _ _ phi hg hp
  obtain ⟨E⟩ := hclosure F
  letI : Field E.Carrier := E.field
  letI : LinearOrder E.Carrier := E.order
  letI : IsStrictOrderedRing E.Carrier := E.strictOrderedRing
  letI : IsRealClosed E.Carrier := E.realClosed
  let psi : MvPolynomial (Fin n) ℝ →+* E.Carrier := E.embedding.toRingHom.comp phi
  have hinj : Function.Injective E.embedding := E.embedding.toRingHom.injective
  have hstrict : StrictMono E.embedding := E.embedding.monotone'.strictMono_of_injective hinj
  have hg' : ∀ i, 0 ≤ psi (g i) := by
    intro i
    change 0 ≤ E.embedding (phi (g i))
    simpa using E.embedding.monotone' (hg i)
  have hp' : psi p < 0 := by
    change E.embedding (phi p) < 0
    simpa using hstrict hp
  exact htransfer g p E.Carrier psi hg' hp'

/-- Assembly of the conditional algebraic certificate half with the two real-algebraic
milestones. -/
theorem nonnegative_krivine_stengle_of_realClosure_and_transfer
    (hclosure : OrderedRealClosureExistenceStatement)
    (htransfer : RealClosedFiniteSignTransferStatement)
    {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsNonnegOn p (basicClosedSet g)) :
    Nonempty (KSWitness g p) :=
  nonnegative_krivine_stengle_of_signRealization
    (finiteSignRealization_of_realClosure_and_transfer hclosure htransfer) g p hp

end OptimalConvergenceRates.KrivineStengle

end
