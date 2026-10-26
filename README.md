# Optimal degree bounds for sum-of-squares representations

This repository contains a Lean formalization of the claims made in the following research announcement by Taveira Blomenhofer, Gribling, Henrion, Korda, Kumar, Magron, Slot, Vargas, and Vera:

- **arXiv/DOI:** https://arxiv.org/abs/2610.24638.
- **Announcement PDF:** [Optimal degree bounds for sum-of-squares representations](Announcement.pdf)

Below is a list of every formalized theorem in the order used in that announcement.
Each entry gives the mathematical statement, its Lean formalization, and the location of its formalization within this repo.
The final section gives additional sphere bounds with explicit dependence on dimension and degree.

## Building and navigating the project

The repository pins its Lean toolchain in `lean-toolchain`. With
[Elan](https://github.com/leanprover/elan) installed, run the following from the
repository root:

```sh
lake exe cache get
lake build OptimalConvergenceRates
```

The first command downloads available Mathlib build artifacts; the second checks the complete
production library. `lake build` is equivalent here because `OptimalConvergenceRates` is the
default target. Use `lake build Comparator` to also compile the production-backed Comparator
solution.

[`OptimalConvergenceRates.lean`](OptimalConvergenceRates.lean) is the aggregate production
module. For the announced results, start from the seven `MainResults.lean` files linked below;
the supporting definitions, estimates, and proofs are organized in the surrounding result
folders. The Comparator surface is under [`Comparator/AllResults`](Comparator/AllResults):
`Challenge.lean` is the Mathlib-only statement interface, while `Solution.lean` imports the
production `MainResults` modules that implement it.

### What the Comparator checks

A normal Lake build checks that the production development type-checks. The pinned Comparator
additionally checks the 22 advertised theorems and two intentional definition targets against
the standalone challenge interface. Its configuration is
[`Comparator/AllResults/comparator.json`](Comparator/AllResults/comparator.json). The check
permits only `propext`, `Quot.sound`, and `Classical.choice`, and replays exported proofs with
NanoDa's independent kernel.

Run the full local Comparator verification with:

```sh
./scripts/verify-comparator.sh
```

This downloads and builds pinned verification tools, so it is substantially slower than
`lake build`.

The three dimension-dependent sphere statements have a separate Mathlib-only challenge in
[`Comparator/SphereDimensionBounds`](Comparator/SphereDimensionBounds). The verification
script checks both configurations. With Lean 4.35's bundled Comparator, each configuration
can also be checked directly, including its configured NanoDa replay:

```sh
lake comparator --config Comparator/AllResults/comparator.json
lake comparator --config Comparator/SphereDimensionBounds/comparator.json
```

## Contents

1. [Archimedean, upper degree bound](#1-archimedean-upper-degree-bound)
2. [Archimedean, lower degree bound](#2-archimedean-lower-degree-bound)
3. [Compact, upper degree bound](#3-compact-upper-degree-bound)
4. [Compact, lower degree bound](#4-compact-lower-degree-bound)
5. [Hypercube, upper degree bound](#5-hypercube-upper-degree-bound)
6. [Hypercube, lower degree bound I](#6-hypercube-lower-degree-bound-i)
7. [Hypercube, lower degree bound II](#7-hypercube-lower-degree-bound-ii)
8. [Hypercube, lower degree bound III](#8-hypercube-lower-degree-bound-iii)
9. [LICQ upper bound](#9-licq-upper-bound)
10. [MFCQ quadratic lower bound](#10-mfcq-quadratic-lower-bound)
11. [Dimension-dependent sphere bounds](#11-dimension-dependent-sphere-bounds)

## Notes
The announcement writes `k` for a relaxation order whose certificates have degree at most
`2k`. Most of the Lean development instead uses `r` for the complete certificate degree.
This changes fixed constants, but not any of the asymptotic rates below. In the displayed
formulas, `QM` denotes the quadratic module and `PO` the preordering.
Section 11 uses `r` for the square-root degree, as in the existing `SphereSOSMod` definition;
its SOS part therefore has degree at most `2r`.

## 1. Archimedean, upper degree bound

**Result.** Let `g` define a nonempty basic closed set and an Archimedean quadratic module,
and let `p` be nonnegative on that set. There are constants `C`, `k₀`, and `ε₀` such that

$$
\varepsilon_{p,k,\mathrm{QM}(g)}
  \le C\frac{(\log k)^4}{k^2}
\quad (k\ge k_0),
\qquad
k_{p,\varepsilon,\mathrm{QM}(g)}
  \le C\frac{\log(1/\varepsilon)^2}{\sqrt{\varepsilon}}
\quad (\varepsilon\le\varepsilon_0).
$$

- **TeX name:** `Archimedean, upper degree bound`
- **Folder:** [`OptimalConvergenceRates/GeneralArchimedean`](OptimalConvergenceRates/GeneralArchimedean)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/GeneralArchimedean/MainResults.lean)
- **Lean declarations:** `generalArchimedeanUpperRate`,
  `generalArchimedeanEpsilonCertificate`

```lean
theorem generalArchimedeanUpperRate :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
        (p : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsArchimedean g →
      IsNonnegOn p (KrivineStengle.basicClosedSet g) →
      ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
        ∀ r, r₀ ≤ r →
          p + C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2)) ∈
            GenQuadraticModule g r :=
  generalArchimedeanUpperRate_proof

theorem generalArchimedeanEpsilonCertificate :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
        (p : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsArchimedean g →
      IsNonnegOn p (KrivineStengle.basicClosedSet g) →
      ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧
        ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
          p + C epsilon ∈ GenQuadraticModule g
            (Nat.ceil (D + K / Real.sqrt epsilon *
              (1 + Real.log epsilon⁻¹) ^ 2)) :=
  generalArchimedeanEpsilonCertificate_proof
```

## 2. Archimedean, lower degree bound

**Result.** For the three-variable Archimedean example, the objective has matching lower
bounds

$$
\varepsilon_{p,k,\mathrm{QM}(g)}
  \ge c\frac{(\log k)^4}{k^2},
\qquad
k_{p,\varepsilon,\mathrm{QM}(g)}
  \ge c\frac{\log(1/\varepsilon)^2}{\sqrt{\varepsilon}}
$$

for all sufficiently large `k` and sufficiently small positive `ε`.

- **TeX name:** `Archimedean, lower degree bound`
- **Folder:** [`OptimalConvergenceRates/GeneralArchimedean`](OptimalConvergenceRates/GeneralArchimedean)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/GeneralArchimedean/MainResults.lean)
- **Lean declarations:** `sharpArchimedeanRate`, `sharpArchimedeanDegreeLowerBound`

```lean
theorem sharpArchimedeanRate :
    ∃ c C₀ r₀, 0 < c ∧ 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        sharpArchimedeanObjective +
            C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2)) ∈
            GenQuadraticModule sharpArchimedeanGenerators r ∧
          ∀ ε, 0 ≤ ε →
            sharpArchimedeanObjective + C ε ∈
                GenQuadraticModule sharpArchimedeanGenerators r →
              c * (Real.log ((max r 2 : ℕ) : ℝ) ^ 4 / (r : ℝ) ^ 2) ≤ ε :=
  sharpArchimedeanRate_proof

theorem sharpArchimedeanDegreeLowerBound :
    ∃ c epsilon₀ : ℝ, 0 < c ∧ 0 < epsilon₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ r : ℕ,
          sharpArchimedeanObjective + C epsilon ∈
              GenQuadraticModule sharpArchimedeanGenerators r →
            c * Real.log epsilon⁻¹ ^ 2 / Real.sqrt epsilon ≤ (r : ℝ) :=
  sharpArchimedeanDegreeLowerBound_proof
```

## 3. Compact, upper degree bound

**Result.** Let `g` define a nonempty compact basic closed set, and let `p` be nonnegative
on it. There are constants `C`, `k₀`, and `ε₀` such that

$$
\varepsilon_{p,k,\mathrm{PO}(g)}
  \le C\frac{(\log k)^2}{k^2}
\quad (k\ge k_0),
\qquad
k_{p,\varepsilon,\mathrm{PO}(g)}
  \le C\frac{\log(1/\varepsilon)}{\sqrt{\varepsilon}}
\quad (\varepsilon\le\varepsilon_0).
$$

- **TeX name:** `Compact, upper degree bound`
- **Folder:** [`OptimalConvergenceRates/GeneralCompact`](OptimalConvergenceRates/GeneralCompact)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/GeneralCompact/MainResults.lean)
- **Lean declarations:** `generalCompactUpperRate`, `generalCompactEpsilonCertificate`

```lean
theorem generalCompactUpperRate :
  ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
      (p : MvPolynomial (Fin n) ℝ),
    (KrivineStengle.basicClosedSet g).Nonempty →
    IsCompact (KrivineStengle.basicClosedSet g) →
    IsNonnegOn p (KrivineStengle.basicClosedSet g) →
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (C₀ * (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2)) ∈
          GenPreordering g r :=
  MainResultsProofs.upperRate

theorem generalCompactEpsilonCertificate :
    ∀ {n m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ)
        (p : MvPolynomial (Fin n) ℝ),
      (KrivineStengle.basicClosedSet g).Nonempty →
      IsCompact (KrivineStengle.basicClosedSet g) →
      IsNonnegOn p (KrivineStengle.basicClosedSet g) →
      ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧
        ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 2 →
          p + C epsilon ∈ GenPreordering g
            (Nat.ceil (D + K / Real.sqrt (epsilon / 2) *
              (1 + Real.log (epsilon / 2)⁻¹))) :=
  MainResultsProofs.epsilonCertificate
```

## 4. Compact, lower degree bound

**Result.** For the bivariate upper-half-ball example with objective `p = x₂`, there are
matching lower bounds

$$
\varepsilon_{p,k,\mathrm{PO}(g)}
  \ge c\frac{(\log k)^2}{k^2},
\qquad
k_{p,\varepsilon,\mathrm{PO}(g)}
  \ge c\frac{\log(1/\varepsilon)}{\sqrt{\varepsilon}}
$$

for all sufficiently large `k` and sufficiently small positive `ε`.

- **TeX name:** `Compact, lower degree bound`
- **Folder:** [`OptimalConvergenceRates/GeneralCompact`](OptimalConvergenceRates/GeneralCompact)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/GeneralCompact/MainResults.lean)
- **Lean declarations:** `sharpCompactRate`, `sharpCompactDegreeLowerBound`

```lean
theorem sharpCompactRate :
  ∃ c C₀ r₀, 0 < c ∧ 0 < C₀ ∧ 0 < r₀ ∧
    ∀ r, r₀ ≤ r →
      sharpObjective + C (C₀ *
          (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2)) ∈
          GenPreordering sharpGenerators r ∧
        ∀ ε, 0 ≤ ε →
          sharpObjective + C ε ∈ GenPreordering sharpGenerators r →
            c * (Real.log ((max r 2 : ℕ) : ℝ) ^ 2 / (r : ℝ) ^ 2) ≤ ε :=
  MainResultsProofs.sharpRate

theorem sharpCompactDegreeLowerBound :
    ∃ c epsilon₀ : ℝ, 0 < c ∧ 0 < epsilon₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ r : ℕ,
          sharpObjective + C epsilon ∈ GenPreordering sharpGenerators r →
            c * Real.log epsilon⁻¹ / Real.sqrt epsilon ≤ (r : ℝ) :=
  MainResultsProofs.sharpDegreeLowerBound
```

## 5. Hypercube, upper degree bound

**Result.** For every dimension `n ≥ 1` and degree bound `d`, every polynomial `p` of
degree at most `d` that is nonnegative on `[-1,1]ⁿ` has a Putinar certificate with error
`O(‖p‖∞/k⁴)`, and hence a certificate of order `O(ε⁻¹/⁴)` for `p + ε`. The same conclusion
holds for the larger Schmüdgen preordering.

- **TeX name:** `Hypercube, upper degree bound`
- **Folder:** [`OptimalConvergenceRates/QuarticConvergence`](OptimalConvergenceRates/QuarticConvergence)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/QuarticConvergence/MainResults.lean)
- **Lean declarations:** `putinarCubeQuarticRate_membership`,
  `putinarCubeQuarticDegreeBound`, `schmudgenCubeQuarticDegreeBound`

```lean
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
```

## 6. Hypercube, lower degree bound I

**Result.** For `p(x₁,x₂) = (1 - x₁²)(1 - x₂²)`, Putinar certificates for `p + ε` on the
two-dimensional box require degree `Ω(ε⁻¹/⁴)`. Equivalently, the relaxation error is
`Ω(k⁻⁴)`.

- **TeX name:** `Hypercube, lower degree bound I`
- **Folder:** [`OptimalConvergenceRates/LowerDegreeBoundsPutinar`](OptimalConvergenceRates/LowerDegreeBoundsPutinar)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/LowerDegreeBoundsPutinar/MainResults.lean)
- **Lean declarations:** `improvedLowerBoundMembershipBoxQM`,
  `improved_lasserre_box_qm_gap`

```lean
theorem improvedLowerBoundMembershipBoxQM
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ improvedEpsilon0) (r : ℕ)
    (hmem : f_eps ε ∈ BoxQuadraticModule 2 r) :
    improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) :=
  LowerDegreeBoundsPutinar.MainResultsProofs.improvedLowerBoundMembershipBoxQM
    ε hε hε0 r hmem

theorem improved_lasserre_box_qm_gap
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ improvedEpsilon0) (r : ℕ)
    (hr : (r : ℝ) < improvedLowerBoundConst * ε ^ (-(1 : ℝ) / 4)) :
    lasserre_bound_box_qm (f_eps ε) r < ↑ε :=
  LowerDegreeBoundsPutinar.MainResultsProofs.improved_lasserre_box_qm_gap
    ε hε hε0 r hr
```

## 7. Hypercube, lower degree bound II

**Result.** For the Motzkin form in three variables, the optimal Schmüdgen preordering
degree is `Θ(ε⁻¹/⁶)`, equivalently the optimal error rate is `Θ(k⁻⁶)`.

- **TeX name:** `Hypercube, lower degree bound II`
- **Folder:** [`OptimalConvergenceRates/LowerDegreeBoundsSchmudgen`](OptimalConvergenceRates/LowerDegreeBoundsSchmudgen)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/MainResults.lean)
- **Lean declarations:** `lowerBoundMembershipBoxPreoMotzkin_sixth`,
  `upperBoundMembershipBoxPreoMotzkin_sixth`

```lean
theorem lowerBoundMembershipBoxPreoMotzkin_sixth
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ Motzkin.motzkinEpsilon0) (r : ℕ)
    (hmem : Motzkin.motzkinPerturbed epsilon ∈ BoxPreordering 3 r) :
    Motzkin.motzkinLowerBoundConst * epsilon ^ (-(1 : ℝ) / 6) ≤ (r : ℝ) :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.lowerBoundMembershipBoxPreoMotzkin_sixth
    epsilon heps heps0 r hmem

theorem upperBoundMembershipBoxPreoMotzkin_sixth
    (epsilon : ℝ) (heps : 0 < epsilon) (heps8 : epsilon ≤ 8) :
    ∃ r : ℕ,
      (r : ℝ) ≤ 28 * epsilon ^ (-(1 : ℝ) / 6) ∧
        Motzkin.motzkinPerturbed epsilon ∈ BoxPreordering 3 r :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.upperBoundMembershipBoxPreoMotzkin_sixth
    epsilon heps heps8
```

## 8. Hypercube, lower degree bound III

**Result.** For the Choi--Lam form in four variables, Schmüdgen preordering certificates
for `p + ε` require degree `Ω(ε⁻¹/⁴)`, equivalently the relaxation error is `Ω(k⁻⁴)`.
The same lower bound follows for the smaller Putinar quadratic module.

- **TeX name:** `Hypercube, lower degree bound III`
- **Folder:** [`OptimalConvergenceRates/LowerDegreeBoundsSchmudgen`](OptimalConvergenceRates/LowerDegreeBoundsSchmudgen)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/MainResults.lean)
- **Lean declarations:** `lowerBoundMembershipBoxPreoChoiLam_quarter`,
  `lowerBoundMembershipBoxPreoChoiLam_quarter_contra`

```lean
theorem lowerBoundMembershipBoxPreoChoiLam_quarter
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hmem : choiLamPerturbed epsilon ∈ BoxPreordering 4 r) :
    schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4) ≤ (r : ℝ) :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.lowerBoundMembershipBoxPreoChoiLam_quarter
    epsilon heps heps0 r hmem

theorem lowerBoundMembershipBoxPreoChoiLam_quarter_contra
    (epsilon : ℝ) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0) (r : ℕ)
    (hr : (r : ℝ) < schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4)) :
    choiLamPerturbed epsilon ∉ BoxPreordering 4 r :=
  LowerDegreeBoundsSchmudgen.MainResultsProofs.lowerBoundMembershipBoxPreoChoiLam_quarter_contra
    epsilon heps heps0 r hr
```

## 9. LICQ upper bound

**Result.** Let `g` define a nonempty Archimedean basic closed set and satisfy
equality-aware CQC, allowing equalities encoded by opposite generator pairs.
For every polynomial `p` nonnegative on the set, there are constants `C`, `k₀`, and `ε₀`
such that

$$
\varepsilon_{p,k,\mathrm{QM}(g)}\le \frac{C}{k^4},
\qquad
k_{p,\varepsilon,\mathrm{QM}(g)}\le \frac{C}{\varepsilon^{1/4}}
$$

in the respective asymptotic ranges.

- **Folder:** [`OptimalConvergenceRates/CQC`](OptimalConvergenceRates/CQC)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/CQC/MainResults.lean)
- **Lean declarations:** `putinarQuarticRateWithEqualities`, `putinarQuarticDegreeBoundWithEqualities`

> **Hypothesis note.** Lean states nonemptiness and positive dimension/cardinality
> assumptions explicitly. Its predicate `CQCWithEqualities g` treats each exact signed class
> containing `q` and `-q` as one equality constraint while retaining ordinary active inequalities.

```lean
theorem putinarQuarticRateWithEqualities
    {n m : ℕ} (hn : 0 < n) (_hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : CQCWithEqualities g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r :=
  CQCMainResultsProofs.putinarQuarticRateWithEqualities hn hne harch hcqc hp

theorem putinarQuarticDegreeBoundWithEqualities
    {n m : ℕ} (hn : 0 < n) (_hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : CQCWithEqualities g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ r : ℕ,
          (r : ℝ) < (r₀ : ℝ) +
              (A / epsilon) ^ ((1 : ℝ) / 4) + 1 ∧
            p + C epsilon ∈ GenQuadraticModule g r :=
  CQCMainResultsProofs.putinarQuarticDegreeBoundWithEqualities hn hne harch hcqc hp
```

## 10. MFCQ quadratic lower bound

**Result.** For the three-variable MFCQ example and objective `p = x₃`, certificates for
`p + ε` require order `Ω(ε⁻¹/²)`, equivalently the hierarchy error is `Ω(k⁻²)`.

- **Folder:** [`OptimalConvergenceRates/MFCQQuadraticLowerBound`](OptimalConvergenceRates/MFCQQuadraticLowerBound)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/MFCQQuadraticLowerBound/MainResults.lean)
- **Lean declarations:** `certificate_lower_bound`, `certificate_order_lower_bound`,
  `hierarchy_error_lower_bound`

```lean
theorem certificate_lower_bound
    (r : ℕ) (hr : 1 ≤ r) (ε : ℝ)
    (hcertificate : objective + C ε ∈
      GenQuadraticModule generators (2 * r)) :
    (1 : ℝ) / (2 ^ 14 * (r : ℝ) ^ 2) < ε :=
  certificate_lower_bound_proof r hr ε hcertificate

theorem certificate_order_lower_bound
    (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε)
    (hcertificate : objective + C ε ∈
      GenQuadraticModule generators (2 * r)) :
    (1 : ℝ) / (128 * Real.sqrt ε) < (r : ℝ) :=
  certificate_order_lower_bound_proof r hr ε hε hcertificate

theorem hierarchy_error_lower_bound (r : ℕ) (hr : 1 ≤ r) :
    (1 : ℝ) / (2 ^ 14 * (r : ℝ) ^ 2) ≤ hierarchyError r :=
  hierarchy_error_lower_bound_proof r hr
```

## 11. Dimension-dependent sphere bounds

These results concern homogeneous forms of every even degree `d ≥ 4` on the full unit
sphere in `ℝⁿ`. They expose dimension and degree dependence using the existing
`SphereSOSMod`, `spherePolyMin`, `spherePolyMax`, and `sphereSOSBound` definitions.
Write `p_min` and `p_max` for the sphere extrema and `p_r` for the SOS lower bound at
square-root degree `r`.

**Upper bound.** For `n ≥ 3` and `r ≥ 8nd`, every homogeneous degree-`d` form satisfies

$$
0\le p_{\min}-p_r
\le C\frac{d^4 n^4(1+\lceil\log_2 n\rceil)^3}{r^4}
  (p_{\max}-p_{\min}),
\qquad C=192\pi^4\cdot5476140000.
$$

The membership theorem supplies the SOS certificate for `p - p_min` plus the displayed
error. The gap theorem also asserts that `sphereSOSBound p r` is a real value, so its
feasible set is nonempty. The kernel construction reuses the repository's normalized
Euclidean sphere measure.

**Lower bound.** There are absolute `c > 0` and `n₀` such that, for every `n ≥ n₀` and
every even `d ≥ 4`, there is a globally nonnegative homogeneous degree-`d` form `p` with
`p_min = 0` and `p_max = 1` satisfying

$$
p_{\min}-p_r\ge c\min\left\{\frac1n,\frac{d^4 n^3}{r^4}\right\}
\qquad(r\ge d/2).
$$

One form works simultaneously for all these orders, and each hierarchy value is real.
The upper and lower bounds have matching powers of `d` and `r` in the decay regime;
their dimension dependence still differs by a factor of `n(1+⌈log₂ n⌉)³`.

- **Main file:** [`SphereDimensionBounds/MainResults.lean`](OptimalConvergenceRates/SphereDimensionBounds/MainResults.lean)
- **Namespace:** `OptimalConvergenceRates.SphereDimensionBounds`
- **Lean declarations:** `sphereDimensionUpperRate_membership`,
  `sphereDimensionUpperRate_gap`, `sphereDimensionLowerRate`
- **Hierarchy compatibility:** [`SphereDimensionBounds/Compatibility.lean`](OptimalConvergenceRates/SphereDimensionBounds/Compatibility.lean)
- **Independent statements:** [`Comparator/SphereDimensionBounds/Challenge.lean`](Comparator/SphereDimensionBounds/Challenge.lean)

The compatibility lemmas identify the internal bounded free-multiplier convention with
the existing sphere certificates at the same order. They also identify the sphere
extrema and SOS bounds; the public statements use the existing repository definitions
throughout.
