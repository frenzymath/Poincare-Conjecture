# Distance Laplacian upper supports

The target is graph PR #122, `distance-laplacian-upper-supports`.

## Informal proof

Write the dimension as m + 1, with m positive. Completeness makes intrinsic
closed balls compact and yields a minimizing geodesic from p to x. Move the
initial point a distance epsilon between zero and half the segment length.
Reversal and the absence of conjugate points inside a minimizing segment make
the shortened exponential differential nonsingular at x. Its inverse branch
gives a smooth radius s, and epsilon + s touches the original distance from
above by the triangle inequality. Gauss's lemma makes its gradient unit.
The coordinate divergence identity identifies its retained Laplacian with
the logarithmic radial polar-density derivative. Ricci comparison bounds
this by m k coth(k s), or m/s when k is zero. Finally,
k coth(k s) is at most 1/s + k and s is at least half the original distance.

The radial coordinate identities are intermediate calculations on explicit
smooth charts. They are compared directly with their displayed hypotheses;
they do not introduce a replacement definition of the distance or Laplacian.

## Proposed formal statements

```lean
open Set
open scoped Manifold ContDiff
namespace PoincareMT.RiemannianMetric
theorem exists_distance_laplacian_upper_support
    {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M]
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      -(m : ℝ) * k ^ 2 * g.inner y v v ≤ D.ricci y v v)
    (p x : M) (hpx : p ≠ x) :
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho x = (g.edist p x).toReal ∧
      (∀ y ∈ U, (g.edist p y).toReal ≤ rho y) ∧
      g.inner x (D.gradient rho x) (D.gradient rho x) = 1 ∧
      D.laplacian rho x ≤
        2 * (m : ℝ) / (g.edist p x).toReal + (m : ℝ) * k := by
  sorry
end PoincareMT.RiemannianMetric
```

## Informal translation

Let m be a positive integer and M a connected smooth real manifold of
dimension m + 1 with regular Hausdorff topology. Let g be a complete Riemannian
metric and D its Levi-Civita connection. If k is nonnegative and
Ric_D(v,v) >= -m k^2 g(v,v) at every point and tangent vector, then for every
distinct p and x there are an open neighborhood U of x and a function
rho : M -> R, smooth on U, with rho(x) = d_g(p,x), rho(y) >= d_g(p,y) on U,
unit squared gradient norm at x, and
Delta_D rho(x) <= 2m/d_g(p,x) + mk.

## Alignment review

An independent translator received only the complete formal statement above.
A separate reviewer compared its proposition with the pinned informal claim
and accepted the alignment. Dimension n = m + 1 gives the same bounds;
Hausdorff manifolds are regular, and a function on U extends arbitrarily to M
when no regularity is required outside U. The model space specifies no boundary.

This review fixes the intended full target. It does not certify the existence
of the shortened branch or completion of the support theorem.

## References

Petersen, *Riemannian Geometry*, third edition, Lemma 7.1.2, printed p. 278,
and Lemma 7.1.9, Section 7.1.4, printed pp. 284--285. See the verified source
notes in `references/riemannian-geometry/petersen/laplacian-comparison.md` and
the pinned source comparison in
`references/ricci-flow/chow-liao-qin-2026/distance-laplacian-reuse.md`.
