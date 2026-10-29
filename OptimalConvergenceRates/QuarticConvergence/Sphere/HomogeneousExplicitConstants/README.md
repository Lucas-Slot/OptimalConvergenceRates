# Homogeneous sphere bounds with explicit constants

This development complements the general-polynomial sphere theorems in
`QuarticConvergence/MainResults.lean`. Their statements and proofs remain available.
The public entry here is `MainResults.lean`, in namespace
`OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants`.

## Results and conventions

The relaxation order `r` bounds the degree of each square root in an SOS certificate;
the sum of squares consequently has degree at most `2*r`. All public statements use
the existing `SphereSOSMod`, `spherePolyMin`, `spherePolyMax`, and `sphereSOSBound`.

For `n ≥ 3`, even `d ≥ 4`, a homogeneous polynomial of degree `d`, and `r ≥ 8*n*d`,
`sphereDimensionUpperRate_membership` supplies the certificate with additive error

```
(192 * π⁴ * 5476140000) * d⁴ * n⁴ * (1 + ceil(log₂ n))³ / r⁴
  * (sphere maximum - sphere minimum).
```

`sphereDimensionUpperRate_gap` bounds the hierarchy gap by the same quantity and
exhibits a real hierarchy value. The absolute upper constant is approximately `1.02e14`.

`sphereDimensionLowerRate` proves the existence of absolute `c > 0` and `n₀` such
that for every `n ≥ n₀` and even `d ≥ 4`, one globally nonnegative homogeneous
polynomial, normalized to sphere minimum zero and maximum one, has gap at least

```
c * min (1/n) (d⁴ * n³ / r⁴)
```

at every `r ≥ d/2`. The polynomial is chosen before quantifying over `r`.
Feasibility is proved at every such order, so the gap never relies on an empty-set
supremum convention. The construction uses a dimension threshold at least `2^53 + 2`.
The powers of `d` and `r` agree in the decay regime; the dimension dependence still
differs by a factor `n * (1 + ceil(log₂ n))³`, apart from absolute constants.

## Proof organization

- `Upper/`: the local cubic/quartic SOS certificate, matrix and selector estimates,
  Gegenbauer/Jacobi localization, homogeneous Taylor bounds, and upper assembly.
  The kernel fourth moment is at most `(12*n/r)^4`. Near-identity repair uses a
  controlled constant correction to the operator image. Homogeneous centering
  subtracts `p_min * (sum_i X_i^2)^(d/2)`, preserving homogeneity.
- `Lower/`: sparse-XOR/hypergraph existence, pseudoexpectations, hard nonnegative
  quartics, angular certificate obstructions, degree amplification, normalization,
  and the uniform all-order lower bound. Arbitrary finite variable types are used
  internally for the combinatorial construction and then reindexed to `Fin n`.
- `Shared/`: algebra and analytic estimates used by both routes, together with
  local notation and adapters to the existing hierarchy. The upper and lower
  folders have no imports of each other.

The specialized arguments originate in [PR #4 by a44l](https://github.com/Lucas-Slot/OptimalConvergenceRates/pull/4),
at commit `0b1429cba361a97ac7a9733f75bf0f5f02bda928`. This integration retains its
mathematical proofs and public theorem contracts while changing the supporting APIs
and dependency organization. It does not claim a new proof of the quantitative estimates.

## Shared repository infrastructure

- `BasicNotions/BoundedSOS.lean` presents bounded SOS as `Nonempty (DegreeBoundedSOS p r)`;
  all scalar SOS constructions use the canonical witness and shared closure operations.
- `Shared/Hierarchy.lean` aliases the existing certificate predicate, feasible set,
  and extrema. Its real supremum is taken over the canonical feasible set and is
  related to the existing `WithBot` value only with a nonemptiness proof.
- `Sphere/CertificateBounds.lean` derives the equality-multiplier degree bound from
  a canonical certificate when the objective degree is at most `2*r`.
- Sphere measure and coordinate transport use `Sphere/Kernel/Measure.lean`.
  The bounded polynomial function space is transported from `Sphere/FiniteDegree.lean`;
  the homogeneous subspace supplies homogeneous representatives for Taylor estimates.
- Linear-form polarization and coefficient-degree estimates reuse
  `Sphere/Kernel/PolynomialMoments.lean`.
- `Sphere/Kernel/NearIdentity.lean` shares the inverse estimates and positive-image
  repair machinery. The existing general-polynomial repair module imports it.
- `BasicNotions/FiniteAveraging.lean` supplies the general compact-convex-hull and
  finite-integral arguments; the existing sphere quadrature theorem uses it too.
- `BasicNotions/ClosedConeImage.lean` supplies closed-cone image estimates to both
  the selector construction and the existing SOS-cone closedness proof.

## Verification

From the repository root:

```sh
lake build OptimalConvergenceRates Comparator
./scripts/verify-comparator.sh
```

`Comparator/AllResults/Challenge.lean` independently states all three public
theorems alongside the other repository targets, using only Mathlib. The shared
sphere definitions appear once in this single challenge. Its solution imports this
development, and the verification script checks the combined suite with the pinned
tools, standard permitted axioms, and NanoDa replay.
