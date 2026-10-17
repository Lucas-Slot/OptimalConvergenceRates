# Comparator entry

`AllResults` is the single README-wide entry. It contains a Mathlib-only
`Challenge.lean`, a production-backed `Solution.lean`, a Comparator
configuration, and project metadata.

The entry compares the 22 README theorem holes, positivity theorem holes for the
Choi--Lam and Motzkin separation constants, and the two corresponding intentional
definition holes. Comparator permits only `propext`, `Quot.sound`, and
`Classical.choice`, with NanoDa replay enabled.

Run the pinned checks locally with:

```sh
./scripts/verify-comparator.sh
```

The GitHub Actions workflow is intentionally manual-only and can be started
from the Actions tab with **Run workflow**.
