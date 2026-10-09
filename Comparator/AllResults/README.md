# README-wide optimal convergence-rate results

This Comparator entry covers all 22 theorems presented in the repository
README. Its standalone `Challenge.lean` imports only Mathlib and includes the
repository-local definitions needed to state those results.

The theorem bodies are challenge holes. The only definition holes are
`OptimalConvergenceRates.schmInteriorLowerBoundConst4` and
`OptimalConvergenceRates.Motzkin.motzkinLowerBoundConst`, the two
separation-derived constants intentionally left abstract for Comparator review.
Thus the Comparator surface contains 24 declarations in total.

`Solution.lean` imports the seven production `MainResults` modules containing
the implementations. The checked configuration permits only `propext`,
`Quot.sound`, and `Classical.choice`, and enables NanoDa replay.

From the repository root, run the pinned local verifier with:

```sh
./scripts/verify-comparator.sh
```
