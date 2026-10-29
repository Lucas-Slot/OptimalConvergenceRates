# Comparator entry

The single statement suite is [`AllResults`](AllResults). It contains a Mathlib-only
`Challenge.lean`, a production-backed `Solution.lean`, and one Comparator configuration.

The challenge covers 25 advertised theorem statements, including the three explicit
homogeneous sphere bounds, plus positivity theorems for the Choi--Lam and Motzkin
separation constants. Those two constants are the only intentional definition holes.
There are 29 checked declarations: 27 theorems and two definitions.

The sphere targets use the same certificate, extrema, and hierarchy definitions as
the existing general-polynomial sphere results. These definitions appear once in
the challenge. Comparator permits only `propext`, `Quot.sound`, and
`Classical.choice`, with NanoDa replay enabled.

Run the suite with the pinned tools:

```sh
./scripts/verify-comparator.sh
```

The GitHub Actions workflow is intentionally manual-only and can be started
from the Actions tab with **Run workflow**.
