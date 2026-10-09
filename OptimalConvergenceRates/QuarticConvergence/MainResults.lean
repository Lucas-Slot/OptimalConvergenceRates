import OptimalConvergenceRates.QuarticConvergence.MainResultsProofs

/-!
# Main quartic-convergence results

This is the readable public statement layer for the sphere, Schmüdgen cube,
and Putinar cube developments.
-/

open MvPolynomial Finset Set

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence

open SphereBallTransfers

/-- Quartic certificate membership for polynomial optimization on the sphere. -/
theorem sphereQuarticRate_membership {n : ℕ} (hn : 3 ≤ n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        f.totalDegree ≤ d → c * max d 1 ≤ r →
          SphereSOSMod
            (f - MvPolynomial.C (spherePolyMin f) +
              MvPolynomial.C
                (A * sphereC6Norm
                  (f - MvPolynomial.C (spherePolyMin f)) / (r : ℝ) ^ 4))
            r :=
  MainResultsProofs.sphereQuarticRate_membership hn

/-- Quartic error bound for the real-valued sphere SOS/Lasserre bound. -/
theorem sphereQuarticRate_lasserreError {n : ℕ} (hn : 3 ≤ n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        f.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ b : ℝ,
            sphereSOSBound f r = (b : WithBot ℝ) ∧
            0 ≤ spherePolyMin f - b ∧
            spherePolyMin f - b ≤
              A * sphereC6Norm
                (f - MvPolynomial.C (spherePolyMin f)) / (r : ℝ) ^ 4 :=
  MainResultsProofs.sphereQuarticRate_lasserreError hn

/-- Fixed-degree quartic certificate membership on the sphere, stated using
only the maximum and minimum of the objective on the sphere. -/
theorem sphereFixedDegreeQuarticRate_membership {n d : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (r : ℕ),
        f.totalDegree ≤ d → r₀ ≤ r →
          SphereSOSMod
            (f - MvPolynomial.C (spherePolyMin f) +
              MvPolynomial.C
                (C * (spherePolyMax f - spherePolyMin f) /
                  (r : ℝ) ^ 4))
            r :=
  MainResultsProofs.sphereFixedDegreeQuarticRate_membership hn

/-- Fixed-degree quartic error bound for the real-valued sphere SOS/Lasserre
bound, stated using only the maximum and minimum on the sphere. -/
theorem sphereFixedDegreeQuarticRate_lasserreError {n d : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (r₀ : ℕ),
      0 < C ∧ 0 < r₀ ∧
      ∀ (f : MvPolynomial (Fin n) ℝ) (r : ℕ),
        f.totalDegree ≤ d → r₀ ≤ r →
          ∃ b : ℝ,
            sphereSOSBound f r = (b : WithBot ℝ) ∧
            0 ≤ spherePolyMin f - b ∧
            spherePolyMin f - b ≤
              C * (spherePolyMax f - spherePolyMin f) /
                (r : ℝ) ^ 4 :=
  MainResultsProofs.sphereFixedDegreeQuarticRate_lasserreError hn

/-- Quartic certificate membership for the canonical Schmüdgen preordering on the cube. -/
theorem schmudgenCubeQuarticRate_membership {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          p - MvPolynomial.C
              (polyMin p -
                A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                  (polyMax p - polyMin p) / (r : ℝ) ^ 4) ∈
            BoxPreordering n r :=
  MainResultsProofs.schmudgenCubeQuarticRate_membership hn

/-- Quartic error bound for the real-valued Schmüdgen cube Lasserre bound. -/
theorem schmudgenCubeQuarticRate_lasserreError {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ b : ℝ,
            lasserre_bound_box_preo p r = (b : WithBot ℝ) ∧
            0 ≤ polyMin p - b ∧
            polyMin p - b ≤
              A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                (polyMax p - polyMin p) / (r : ℝ) ^ 4 :=
  MainResultsProofs.schmudgenCubeQuarticRate_lasserreError hn

/-- Quartic certificate membership for the canonical Putinar quadratic module on the cube. -/
theorem putinarCubeQuarticRate_membership {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (h : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        h.totalDegree ≤ d → IsNonnegOn h (Hypercube n) →
          c * max d 1 ≤ r →
          h + MvPolynomial.C
              (A * ((max d 1 : ℕ) : ℝ) ^ 6 * polySupNorm h /
                (r : ℝ) ^ 4) ∈
            BoxQuadraticModule n r :=
  MainResultsProofs.putinarCubeQuarticRate_membership hn

/-- Inverse form of the quartic Putinar cube rate, with the homogeneous
fourth root of `polySupNorm h / epsilon`. -/
theorem putinarCubeQuarticDegreeBound {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (h : MvPolynomial (Fin n) ℝ) (d : ℕ) (epsilon : ℝ),
        h.totalDegree ≤ d → IsNonnegOn h (Hypercube n) → 0 < epsilon →
          ∃ r : ℕ,
            (r : ℝ) < ((c * max d 1 : ℕ) : ℝ) +
                (A * ((max d 1 : ℕ) : ℝ) ^ 6 * polySupNorm h / epsilon) ^
                  ((1 : ℝ) / 4) + 1 ∧
              h + C epsilon ∈ BoxQuadraticModule n r :=
  MainResultsProofs.putinarCubeQuarticDegreeBound hn

/-- The same inverse quartic degree bound for the larger canonical box
preordering. -/
theorem schmudgenCubeQuarticDegreeBound {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (h : MvPolynomial (Fin n) ℝ) (d : ℕ) (epsilon : ℝ),
        h.totalDegree ≤ d → IsNonnegOn h (Hypercube n) → 0 < epsilon →
          ∃ r : ℕ,
            (r : ℝ) < ((c * max d 1 : ℕ) : ℝ) +
                (A * ((max d 1 : ℕ) : ℝ) ^ 6 * polySupNorm h / epsilon) ^
                  ((1 : ℝ) / 4) + 1 ∧
              h + C epsilon ∈ BoxPreordering n r :=
  MainResultsProofs.schmudgenCubeQuarticDegreeBound hn

/-- Quartic error bound for the real-valued Putinar cube Lasserre bound. -/
theorem putinarCubeQuarticRate_lasserreError {n : ℕ} (hn : 0 < n) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ (p : MvPolynomial (Fin n) ℝ) (d r : ℕ),
        p.totalDegree ≤ d → c * max d 1 ≤ r →
          ∃ b : ℝ,
            lasserre_bound_box_qm p r = (b : WithBot ℝ) ∧
            0 ≤ polyMin p - b ∧
            polyMin p - b ≤
              A * ((max d 1 : ℕ) : ℝ) ^ 6 *
                (polyMax p - polyMin p) / (r : ℝ) ^ 4 :=
  MainResultsProofs.putinarCubeQuarticRate_lasserreError hn

end OptimalConvergenceRates.QuarticConvergence

end
