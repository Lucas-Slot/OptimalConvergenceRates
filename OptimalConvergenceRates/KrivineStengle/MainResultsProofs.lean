import OptimalConvergenceRates.KrivineStengle.MainResultStatements
import OptimalConvergenceRates.KrivineStengle.RateSeed
import OptimalConvergenceRates.KrivineStengle.UniformRefutation

namespace OptimalConvergenceRates.KrivineStengle

theorem mainTheorem_proof : MainTheoremStatement := by
  intro n m g p hp
  obtain ⟨w⟩ := nonnegative_krivine_stengle g p hp
  exact ⟨w.k, w.k_pos, w.S, w.T, w.hS, w.hT, w.identity⟩

theorem mainTheoremIff_proof : MainTheoremIffStatement := by
  intro n m g p
  constructor
  · exact mainTheorem_proof g p
  · rintro ⟨k, hk, S, T, hS, hT, hidentity⟩
    exact (KSWitness.mk k hk S T hS hT hidentity).nonnegOn

end OptimalConvergenceRates.KrivineStengle
