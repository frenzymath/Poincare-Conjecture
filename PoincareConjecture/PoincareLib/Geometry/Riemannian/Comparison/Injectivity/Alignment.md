# Local Injectivity Statement Alignment

Mission node: `injectivity-from-local-volume-bounds`, revision 2.

## Informal proof

Let s be the smaller of R and the Jacobi comparison radius. Relative volume
comparison bounds the volume of the ball of radius s/4 below by a positive
number depending only on n, K, R, and v. Choose a natural number N whose
multiple of this lower bound exceeds the upper bound for the pullback mass
of the tangent ball of radius s.

The precompact exponential has a nonsingular differential and Gauss identity
on this scale. A first failure of injectivity at a sufficiently small radius
produces a returning radial geodesic. Lift this loop N times. The lifts give
actual inverse images of the center and a smooth local deck motion. A
collision among the lifted endpoints yields a positive finite period of
that motion on a small connected ball by uniqueness of lifts.

Extend the pullback metric outside the comparison ball while preserving
uniform norm bounds and Gauss identity. Curvature is unchanged on the
retained region. The finite orbit energy attains a minimum near the origin;
the periodic deck motion sends it to a distinct minimum. A minimizing
geodesic between these points remains in the controlled region. Radial
Jacobi comparison makes the sum of squared radii strictly convex along
this geodesic, a contradiction. Thus the lifted endpoints are distinct.
Their volume packing contradicts the choice of N. The resulting injective
exponential maps onto the intrinsic ball by the minimizing-geodesic
coverage theorem, and its local inverse is smooth.

## Proposed formal statements

```lean
import PoincareLib.Geometry.Riemannian.Comparison.Injectivity.PackingScale
import PoincareLib.Geometry.Riemannian.Comparison.Injectivity.Noncollapse
import PoincareLib.Geometry.Riemannian.Comparison.Injectivity.BallDiffeomorphism

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace PoincareMT.RiemannianMetric

def localInjectivityRadius (n : ℕ) (K R v : ℝ) : ℝ :=
  let s := min R (Poincare.ODE.Jacobi.comparisonRadius K)
  packingInjectivityRadius n s (smallerBallVolumeBound n K R v (s / 4))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_uniform_precompact_exponential_diffeomorph
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    {K R v : ℝ} (hn : 1 ≤ n) (hK : 0 ≤ K) (hR : 0 < R) (hv : 0 < v)
    (hcompact : IsCompact (closure (g.ball p (2 * R))))
    (hcurv : ∀ x ∈ g.ball p (2 * R), D.curvatureTensorNorm x ≤ K)
    (hvol : letI : LocallyCompactSpace M :=
        ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
      ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p R)) :
    let ρ := localInjectivityRadius n K R v
    0 < ρ ∧ ρ < R ∧
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
    ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      Φ.source = Metric.ball 0 ρ ∧ Φ.target = g.ball p ρ ∧ Φ 0 = p ∧
      (∀ a b, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (extChartAt (𝓡 n) p p) (L a) (L b) = inner ℝ a b) ∧
      HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w)) L.toContinuousLinearMap 0 ∧
      (∀ w ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun t : ℝ => Φ (t • w))
          {t : ℝ | t • w ∈ Metric.ball 0 R}) ∧
      ∀ w ∈ Metric.ball 0 ρ, g.edist p (Φ w) = ENNReal.ofReal ‖w‖ := by
  sorry

end PoincareMT.RiemannianMetric
```

## Informal translation

**Proposition.** Fix an integer n >= 1 and real numbers K >= 0, R > 0,
and v > 0. The specified number rho = localInjectivityRadius(n,K,R,v)
depends only on these parameters and satisfies 0 < rho < R. Let M be a
Hausdorff, second-countable smooth n-manifold with its Borel structure,
Riemannian metric g, Levi-Civita connection D, and point p. Suppose the
closure of B_g(p,2R) is compact, the metric Hilbert-Schmidt norm of the
covariant curvature tensor is at most K throughout this open ball, and
the Euclidean-normalized n-dimensional Hausdorff measure for the intrinsic
Riemannian distance gives B_g(p,R) volume at least v.

For the specified chart chi at p, there are a linear isomorphism L of
Euclidean n-space and a map Phi from Euclidean n-space to M such that Phi
restricts to a smooth diffeomorphism from B(0,rho) onto B_g(p,rho), with
Phi(0)=p. The pullback metric through chi^{-1} at chi(p), evaluated on La,Lb,
equals the Euclidean inner product of a,b, and the derivative of chi composed
with Phi at zero is L. For every w of norm less than R, t maps to Phi(tw)
as an affine geodesic on the interval where the norm of tw is less than R.
For w of norm less than rho, the intrinsic distance from p to Phi(w) is
the norm of w. The numerical radius uses
s=min(R,comparisonRadius(K)) and
packingInjectivityRadius(n,s,smallerBallVolumeBound(n,K,R,v,s/4)).

## Alignment review

Accepted by the independent semantic reviewer after the translator supplied
the explicit volume and curvature conventions. The derivative I of Phi at
zero is an isometric isomorphism onto T_p M. The radial geodesic equation
and uniqueness give Phi(w)=exp_p(Iw), so the conclusion is the required
actual exponential diffeomorphism. The radius is chosen before the manifold
and metric. The Borel structure, chart, and Levi-Civita data add no geometric
hypotheses; completeness is not assumed. The dimension-one case is included.

The translator received only the complete formal declarations and the two
referenced measure/norm definitions. The reviewer received only the original
informal description and the translation. This is a statement review, not
an axiom audit or a claim that relative-volume comparison is complete.

## References

Morgan and Tian, *Ricci Flow and the Poincare Conjecture*, Theorem 1.36,
p. 20. Compact confinement in place of completeness is proved here using
the precompact minimizing-geodesic and exponential constructions.
