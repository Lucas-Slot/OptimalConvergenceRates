/- Regression tests for the Krivine--Stengle sublibrary. -/
import OptimalConvergenceRates.KrivineStengle.Refutation
import OptimalConvergenceRates.KrivineStengle.MainResults

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

example : KSWitness sharpSeedGenerators sharpSeedZ := sharpSeedWitness

example {ε : ℝ} (hε : 0 < ε) :
    PreorderingMem
      (appendGenerator sharpSeedGenerators (perturbationGenerator sharpSeedZ ε)) (-1) :=
  sharpSeedWitness.perturbation_refutation hε

example : ∃ r, ∀ {ε : ℝ}, 0 < ε →
    (-1 : MvPolynomial (Fin 3) ℝ) ∈
      GenPreordering
        (appendGenerator sharpSeedGenerators (perturbationGenerator sharpSeedZ ε)) r :=
  sharpSeedWitness.exists_perturbation_refutation_order

example {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ) :
    KSWitness g 0 where
  k := 1
  k_pos := by simp
  S := 0
  T := 0
  hS := preorderingMem_zero g
  hT := preorderingMem_zero g
  identity := by simp

example :
    matrixSignature (!![(0 : ℝ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  simpa using matrixSignature_traceZero_two (0 : ℝ) 1

example :
    hermiteSignature ((Polynomial.X - Polynomial.C 1) ^ 2 : Polynomial ℝ) 1
        ((Polynomial.monic_X_sub_C (1 : ℝ)).pow 2) =
      rootSignSum ((Polynomial.X - Polynomial.C 1) ^ 2 : Polynomial ℝ) 1 := by
  exact hermiteSignature_eq_rootSignSum_monic _ _ _

example :
    hermiteSignature (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial ℝ) 1
        (Polynomial.monic_X_pow_add_C (1 : ℝ) (by norm_num)) =
      rootSignSum (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial ℝ) 1 := by
  exact hermiteSignature_eq_rootSignSum_monic _ _ _

example :
    let f : Polynomial (MvPolynomial (Fin 1) ℝ) :=
      Polynomial.C (MvPolynomial.X 0) * Polynomial.X + 1
    specializePolynomial (RingHom.id ℝ) (fun _ : Fin 1 ↦ 0) f = 1 := by
  simp [specializePolynomial]

example :
    let fs : List (Polynomial (MvPolynomial (Fin 0) ℝ)) :=
      [Polynomial.X, 1 - Polynomial.X]
    (strictSamplerFormula fs).Realizes (RingHom.id ℝ)
      (fun i : Fin 0 ↦ Fin.elim0 i) := by
  dsimp only
  apply (realizes_strictSamplerFormula_iff_exists
    (RingHom.id ℝ) (fun i : Fin 0 ↦ Fin.elim0 i) [Polynomial.X, 1 - Polynomial.X]).2
  refine ⟨(1 / 2 : ℝ), ?_⟩
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> norm_num [specializePolynomial]

example : IsRealClosed ℝ := inferInstance

example : OrderedRealClosureExistenceStatement := orderedRealClosureExistence

example : RealClosedSignFormulaTransferStatement := realClosedSignFormulaTransfer

example : FiniteSignRealizationStatement := finiteSignRealization

example : MainTheoremStatement := mainTheorem

example : MainTheoremIffStatement := mainTheoremIff

example {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Nonempty (KSWitness g 0) := by
  apply nonnegative_krivine_stengle g 0
  intro x hx
  simp

end OptimalConvergenceRates.KrivineStengle

end
