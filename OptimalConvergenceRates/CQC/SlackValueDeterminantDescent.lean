import OptimalConvergenceRates.CQC.SlackGramFormula

/-! Descent identities for the Gram determinant. -/

noncomputable section

open MvPolynomial Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

@[simp]
theorem squareSlackSubstitution_slackValueDeterminant
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    squareSlackSubstitution (slackValueDeterminant g) =
      slackDeterminant g := by
  let φ := (squareSlackSubstitution (n := n) (m := m)).toRingHom
  have hm : φ.mapMatrix (slackValueGramPolynomial g) =
      slackGramPolynomial g := by
    apply Matrix.ext
    intro i k
    exact squareSlackSubstitution_slackValueGramPolynomial g i k
  calc
    squareSlackSubstitution (slackValueDeterminant g) =
        φ (Matrix.det (slackValueGramPolynomial g)) := rfl
    _ = Matrix.det (φ.mapMatrix (slackValueGramPolynomial g)) :=
      RingHom.map_det φ (slackValueGramPolynomial g)
    _ = Matrix.det (slackGramPolynomial g) := by rw [hm]
    _ = slackDeterminant g := rfl

theorem squareSlackSubstitution_adjugate_slackValueGramPolynomial
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i k : Fin m) :
    squareSlackSubstitution ((slackValueGramPolynomial g).adjugate i k) =
      (slackGramPolynomial g).adjugate i k := by
  let φ := (squareSlackSubstitution (n := n) (m := m)).toRingHom
  have hm : (slackValueGramPolynomial g).map φ =
      slackGramPolynomial g := by
    apply Matrix.ext
    intro a b
    exact squareSlackSubstitution_slackValueGramPolynomial g a b
  have hmap := congrFun (congrFun
    (RingHom.map_adjugate φ (slackValueGramPolynomial g)) i) k
  calc
    squareSlackSubstitution ((slackValueGramPolynomial g).adjugate i k) =
        φ ((slackValueGramPolynomial g).adjugate i k) := rfl
    _ = ((slackValueGramPolynomial g).map φ).adjugate i k := hmap
    _ = (slackGramPolynomial g).adjugate i k := by rw [hm]

@[simp]
theorem squareSlackSubstitution_slackValueBaseW
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (j : Fin n) :
    squareSlackSubstitution (slackValueBaseW g p j) =
      slackW g p (Fin.castAdd m j) := by
  have hpderiv :
      MvPolynomial.pderiv (Fin.castAdd m j) (liftBasePolynomial p) =
        liftBasePolynomial (MvPolynomial.pderiv j p) := by
    simp [liftBasePolynomial,
      MvPolynomial.pderiv_rename (Fin.castAdd_injective n m)]
  have hd : squareSlackSubstitution
      (MvPolynomial.pderiv (Fin.castAdd m j) (slackValueDeterminant g)) =
        MvPolynomial.pderiv (Fin.castAdd m j) (slackDeterminant g) := by
    calc
      squareSlackSubstitution
          (MvPolynomial.pderiv (Fin.castAdd m j) (slackValueDeterminant g)) =
          MvPolynomial.pderiv (Fin.castAdd m j)
            (squareSlackSubstitution (slackValueDeterminant g)) :=
              (pderiv_base_squareSlackSubstitution
                (slackValueDeterminant g) j).symm
      _ = MvPolynomial.pderiv (Fin.castAdd m j) (slackDeterminant g) := by
        rw [squareSlackSubstitution_slackValueDeterminant]
  simp [slackValueBaseW, slackW, hpderiv, hd]

end CQCInternal
end OptimalConvergenceRates

end
