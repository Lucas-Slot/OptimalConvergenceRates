# All results

This single Comparator entry covers 25 theorem statements presented in the repository
README, including the explicit homogeneous sphere upper certificate, upper hierarchy
gap, and uniform dimension/degree lower bound. It also checks positivity theorems for
the two constants in the Motzkin and Choi--Lam lower bounds.

The standalone `Challenge.lean` imports only Mathlib and includes the repository-local
definitions needed to state those results. The sphere targets use the existing
`SphereSOSMod`, sphere extrema, and `WithBot` hierarchy, with `r` bounding square-root
degrees. Each shared definition appears once. The CQC targets use `CQCWithEqualities`,
which treats exact opposite-generator pairs as equality constraints while retaining
ordinary active inequalities.

The theorem bodies are challenge holes. The only definition holes are
`OptimalConvergenceRates.schmInteriorLowerBoundConst4` and
`OptimalConvergenceRates.Motzkin.motzkinLowerBoundConst`, the two
separation-derived constants intentionally left abstract for Comparator review.
Their positivity theorems prevent the lower-bound statements from becoming
vacuous. The Comparator surface contains 29 declarations: 27 theorems and two
definitions.

`Solution.lean` imports the eight production `MainResults` modules containing
the implementations. The configuration permits only `propext`, `Quot.sound`,
and `Classical.choice`, and enables NanoDa replay.

From the repository root, run the pinned local verifier with:

```sh
./scripts/verify-comparator.sh
```
