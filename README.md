# Lean companion to the announced results

> **TODO:** Insert a PDF or arXiv link to a document containing a summary of all results.

This document lists every formalized theorem in the order used by that result summary.
Each entry gives the mathematical statement, its TeX name, the public Lean location, and
the corresponding declaration(s) from `MainResults.lean`.

The announcement writes `k` for a relaxation order whose certificates have degree at most
`2k`. Most of the Lean development instead uses `r` for the complete certificate degree.
This changes fixed constants, but not any of the asymptotic rates below. In the displayed
formulas, `QM` denotes the quadratic module and `PO` the preordering.

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
- **TeX label:** `THM:generalputinarupper`
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
- **TeX label:** `THM:generalputinarlower`
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
- **TeX label:** `THM:generalschmudgenupper`
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
- **TeX label:** none
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
- **TeX label:** `THM:cubeupper`
- **Folder:** [`OptimalConvergenceRates/QuarticConvergence`](OptimalConvergenceRates/QuarticConvergence)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/QuarticConvergence/MainResults.lean)
- **Lean declarations:** `putinarCubeQuarticRate_membership`,
  `putinarCubeQuarticDegreeBound`, `schmudgenCubeQuarticDegreeBound`

> **Normalization note.** Lean keeps the norm dependence homogeneous: the inverse bound
> contains `(‖p‖∞ / ε)^(1/4)`. For fixed `n` and `d`, the degree factors in the Lean
> statement are absorbed into the constants used in the announcement.

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
- **TeX label:** `THM:cubelowerI`
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
- **TeX label:** none (the label is commented out in the TeX source)
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
- **TeX label:** none (the label is commented out in the TeX source)
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

**Result.** Let `g` define a nonempty Archimedean basic closed set and satisfy LICQ/CQC.
For every polynomial `p` nonnegative on the set, there are constants `C`, `k₀`, and `ε₀`
such that

$$
\varepsilon_{p,k,\mathrm{QM}(g)}\le \frac{C}{k^4},
\qquad
k_{p,\varepsilon,\mathrm{QM}(g)}\le \frac{C}{\varepsilon^{1/4}}
$$

in the respective asymptotic ranges.

- **TeX name:** none; the theorem option contains only `\lean`
- **TeX label:** `thm:LICQupper`
- **Folder:** [`OptimalConvergenceRates/CQC`](OptimalConvergenceRates/CQC)
- **File:** [`MainResults.lean`](OptimalConvergenceRates/CQC/MainResults.lean)
- **Lean declarations:** `putinarQuarticRate`, `putinarQuarticDegreeBound`

> **Hypothesis note.** Lean states nonemptiness and positive dimension/cardinality
> assumptions explicitly. Its predicate `CQC g` is the formalized constraint qualification
> used for this result.

```lean
theorem putinarQuarticRate
    {n m : ℕ} (hn : 0 < n) (_hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : CQC g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (A / (r : ℝ) ^ 4) ∈ GenQuadraticModule g r :=
  CQCMainResultsProofs.putinarQuarticRate hn hne harch hcqc hp

theorem putinarQuarticDegreeBound
    {n m : ℕ} (hn : 0 < n) (_hm : 0 < m)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : GeneralArchimedean.IsArchimedean g)
    (hcqc : CQC g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    ∃ A : ℝ, ∃ r₀ : ℕ, 0 < A ∧ 0 < r₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ r : ℕ,
          (r : ℝ) < (r₀ : ℝ) +
              (A / epsilon) ^ ((1 : ℝ) / 4) + 1 ∧
            p + C epsilon ∈ GenQuadraticModule g r :=
  CQCMainResultsProofs.putinarQuarticDegreeBound hn hne harch hcqc hp
```

## 10. MFCQ quadratic lower bound

**Result.** For the three-variable MFCQ example and objective `p = x₃`, certificates for
`p + ε` require order `Ω(ε⁻¹/²)`, equivalently the hierarchy error is `Ω(k⁻²)`.

- **TeX name:** none; the theorem option contains only `\lean`
- **TeX label:** none
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
