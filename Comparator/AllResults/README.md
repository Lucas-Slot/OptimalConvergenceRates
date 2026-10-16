# README-wide optimal convergence-rate results

This Comparator entry covers all 22 theorems presented in the repository
README, plus positivity theorems for the two constants in the Motzkin and
Choi--Lam lower bounds. Its standalone `Challenge.lean` imports only Mathlib
and includes the repository-local definitions needed to state those results.

The theorem bodies are challenge holes. The only definition holes are
`OptimalConvergenceRates.schmInteriorLowerBoundConst4` and
`OptimalConvergenceRates.Motzkin.motzkinLowerBoundConst`, the two
separation-derived constants intentionally left abstract for Comparator review.
Their positivity theorems prevent the lower-bound statements from becoming
vacuous. Thus the Comparator surface contains 26 declarations in total: 24
theorems and two definitions.

`Solution.lean` imports the seven production `MainResults` modules containing
the implementations. The checked configuration permits only `propext`,
`Quot.sound`, and `Classical.choice`, and enables NanoDa replay.

From the repository root, run the pinned local verifier with:

```sh
./scripts/verify-comparator.sh
```
