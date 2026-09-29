# Harmonic Coordinates: Integration Review

Owner: `blueprint-v4-integration`, session
`session_fd894b3e2eb047718aa35f162d35c568`.
Source revision: `751329327f4f582797bda8e6cffe7cdf7531cc1d`.
Status: bounded construction and annular interface reviewed. Neither
the Ricci-flow nor annular chapter is accepted by this record.

## Discovery and Placement

The scalar annular uniformization calls
`PoincareMT.RiemannianMetric.exists_uniform_harmonic_radius` through
`Uniformization/Scalar/LocalHarmonic.lean`. None of the eighteen drafts
previously developed harmonic coordinates. An M07 endpoint row does not
cover this dependency. The new `sec:rf-harmonic-coordinates` gives the
radial-metric theorem, its construction and the local surface specialization;
`sec:annular-uniformization` points to that exposition. Integration owns
both finished author drafts. All edits are publication-only.

## Actual Construction

Under `PoincareLib/Geometry/Riemannian/Coordinates/Harmonic/`, the following
source paths were inspected for the indicated steps:

- `Radius.lean`, `Basic.lean`, `Regularity/Coefficients/WeakMap.lean`:
  constants before the metric; global Gauss identity, local ellipticity
  1/4 and 9/4, local curvature bound; inverse pullback close to the identity;
  radii S=rho/8 and r=S/256; extended metric with ellipticity 1/9 and 9.
- `RadialFrame.lean`, `Regularity/WeakCoordinateCloseness.lean`:
  actual radial parallel transport, curvature integral for its connection,
  quadratic coframe error, small weak coordinate corrections and the
  gradient-error tolerance. The weak-closeness file was read through the
  local mean-value and final energy cancellation, including its
  tolerance/radius choices.
- `WeakCoordinates.lean`, `SmoothReplacement.lean` and the downstream
  `Geometry/Riemannian/Elliptic/Dirichlet/InteriorRegularity.lean`,
  `Analysis/Elliptic/Regularity/Eigenfunction.lean` and
  `Analysis/Elliptic/Regularity/Iteration/Bootstrap.lean`:
  compact cutoff boundary data, energy completion, weak derivatives,
  local elliptic Sobolev bootstrap, smooth representative and retained
  Laplacian. Qualitative constants may depend on this metric.
- `Regularity/GradientDifference.lean`, `Regularity/EnergyMeanValue.lean`
  and the exponent statements in `Regularity/SobolevScale.lean`:
  covariant vector test, positive regularization, cutoff power inequality,
  exponent chi=n/(n-1) for n>=2, shrinking-ball recurrence and the exact
  final radius power -n/2. The correction error is bounded by a small
  energy term plus a term of order r^4 before taking its square root.
- `Inverse.lean`: segment estimate, uniform injectivity, inverse
  differential bounds and image ball of one quarter the original radius.
- `Regularity/Hessian/Divergence.lean` (tensor definitions and commutator),
  `Regularity/Hessian/Flux.lean`, `Regularity/Hessian/MeanValue.lean`,
  `Regularity/Hessian/Bounds.lean`, `Regularity/MetricDerivative.lean`:
  explicit curvature flux and algebraic curvature action, weak Hessian
  equation, power estimate and mass seed from Bochner, then coordinate
  Hessian = negative Christoffel coefficient and metric compatibility.
  Curvature derivatives are never required quantitatively.
- `Regularity/Coefficients/Derivative.lean`,
  `Regularity/Coefficients/Interior.lean` (scalar argument and metric
  assembly through the coefficient forcing),
  `Regularity/Coefficients/Absorption.lean`,
  `Regularity/Potential/DivergenceEstimate.lean` and
  `Regularity/Potential/HessianHolder.lean`:
  density-weighted inverse metric, actual Ricci equation forcing,
  spatial and temporal cutoffs, second/third Gaussian derivative
  cancellation, split at distance squared, and strict half-seminorm
  absorption. Compact smoothness supplies finite initial seminorm,
  not a uniform estimate.

The annular consumer's `LocalHarmonic.lean` was read in full: normalized
exponential chart, local coefficient shrinkage, Gauss-preserving cutoff,
compact curvature bound and composition with the harmonic lift. Its
`LocalIsothermal.lean` converts the noncritical first harmonic coordinate
and its local conjugate into an isothermal chart. The proof does not need
completeness or a global curvature bound for the initial surface metric.

## Primary Source Comparison

Directly inspected the archived Part III PDF, stored as
`references/ricci-flow/techniques-and-applications/part-iii.html`
(the file contains PDF bytes), PDF pp. 404-405, printed pp. 383-384,
and the corresponding page transcriptions. The locator is Chow et al.,
Proposition 26.49, Step 3, equations (26.146)-(26.150).
The text invokes Jost--Karcher and DeTurck--Kazdan to obtain harmonic
coordinates after an exponential lift. The implemented radial theorem
instead constructs weak replacements and proves the quantitative bounds
outlined above. This is a source specialization and expanded construction,
not a claim of a new harmonic-coordinate theorem.

The existing `ChowEtAl2010` bibliography entry was copied into the
publication bibliography without changing the reference archive. The
source's later heat-equation Schauder application is not asserted to be
proved by the local surface specialization.

## Sequential Reading

The entire new section was reread as mathematics after drafting, separately
from the source traversal. Checked the curvature-flux signs against the
displayed weak tensor equation; distinguished qualitative representative
regularity from uniform coordinate estimates; retained the Moser radius
factor -n/2, the gradient-error squared remainder r^4 and the different
Hessian regularization of order r. The inverse image radius, pullback
ellipticity, coefficient tolerance before metric choice and final
S/128=2r shrink agree with the producer. Corrected a matrix-product
typesetting error and made standard-coordinate harmonicity explicit.
The annular input is supplied at this bounded interface. Acceptance of
either entire chapter remains pending.

## Review Still Required

- Other harmonic-coordinate consumers and placement of the expanded
  analytic material. This section does not stand in for the separate
  pointed-compactness construction or all distance-smoothing analysis.
- Complete Ricci-flow and annular chapter reviews, integrated citation
  and source metadata, and final PDF/site inspection after mathematics
  passes. No Lean build, make check, endpoint audit or comparator was
  run; operator direction 2418 requires reuse of pinned evidence.
