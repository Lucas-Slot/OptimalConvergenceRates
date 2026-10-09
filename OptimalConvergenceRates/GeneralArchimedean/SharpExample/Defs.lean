/-
  Definitions for the fixed three-variable sharp Archimedean example.
-/
import OptimalConvergenceRates.GeneralArchimedean.Defs
import OptimalConvergenceRates.KrivineStengle.RateSeed

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

abbrev sharpArchimedeanA : MvPolynomial (Fin 3) ℝ :=
  KrivineStengle.sharpSeedA

abbrev sharpArchimedeanB : MvPolynomial (Fin 3) ℝ :=
  KrivineStengle.sharpSeedB

abbrev sharpArchimedeanZ : MvPolynomial (Fin 3) ℝ :=
  KrivineStengle.sharpSeedZ

abbrev sharpArchimedeanW : MvPolynomial (Fin 3) ℝ :=
  KrivineStengle.sharpSeedW

/-- The fixed generators in the matching three-variable example. -/
abbrev sharpArchimedeanGenerators : Fin 4 → MvPolynomial (Fin 3) ℝ :=
  KrivineStengle.sharpSeedGenerators

/-- The objective z in the matching three-variable example. -/
abbrev sharpArchimedeanObjective : MvPolynomial (Fin 3) ℝ :=
  sharpArchimedeanZ

end OptimalConvergenceRates.GeneralArchimedean

end
