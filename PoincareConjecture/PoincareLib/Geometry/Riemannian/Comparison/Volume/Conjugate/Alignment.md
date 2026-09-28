# Nonsingularity before cut points

## Informal proof

Choose the normalized radial exponential supplied by compact closure of the
intrinsic ball. Its initial differential is the chosen tangent-space isometry.
If its differential has a nonzero kernel at an interior minimizing vector,
vary the initial velocity along that kernel and rescale the extended minimizing
segment to the unit interval. The resulting smooth Jacobi field vanishes at
zero and at an interior time, but has nonzero initial covariant derivative.
In a parallel orthonormal frame the index-form construction gives two smooth
fields, matching at that time, with zero outer endpoints and negative total
index. A finite chart variation realizes these fields using shared local
geodesics at the junctions. Its fixed endpoints and the minimizing distance
make its total energy locally minimal, while the second variation equals its
negative index, a contradiction. Thus the differential is injective, hence
invertible in equal finite dimensions. A nonterminal minimizing vector either
is zero or has a strictly larger minimizing multiple, giving the set version.

## Proposed formal statements

```lean
namespace PoincareMT.RiemannianMetric

theorem exists_nonsingular_exponential_of_precompact_ball
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareMT.RiemannianMetric n M) (D : PoincareMT.LeviCivitaData g)
    (p : M) (hn : 1 ≤ n) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ e : EuclideanSpace ℝ (Fin n) → M,
        (∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
          (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) ∧
        ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧
        e 0 = p ∧
        HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0 ∧
        (∀ v ∈ Metric.ball 0 R,
          g.IsGeodesicOn (fun t : ℝ => e (t • v))
            {t : ℝ | t • v ∈ Metric.ball 0 R} ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            g.tangentNorm (e (t • v))
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖ ∧
            g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t) ∧
        (∀ v ∈ Metric.ball 0 R,
          (v = 0 ∨ (v ≠ 0 ∧ ∃ q : ℝ, 1 < q ∧ q * ‖v‖ < R ∧
            g.edist p (e (q • v)) = ENNReal.ofReal (q * ‖v‖))) →
          (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible) ∧
        ∀ v ∈ Poincare.VolumeComparison.localMinimizingSet (fun w => g.edist p (e w)) R \
          Poincare.VolumeComparison.terminalRadialPoints
            (Poincare.VolumeComparison.localMinimizingSet (fun w => g.edist p (e w)) R) R,
          (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
  sorry

end PoincareMT.RiemannianMetric
```

## Informal translation

**Proposition.** Let n be a positive integer and let M be a smooth Hausdorff
n-dimensional manifold without boundary, with a smooth Riemannian metric g
and its smooth torsion-free, metric-compatible connection. Suppose R is positive
and the closure of the intrinsic ball centered at p of radius R is compact.
Write phi for the distinguished chart at p. There exist a linear isomorphism L
of Euclidean n-space and a map e from Euclidean n-space into M such that L
identifies the Euclidean inner product with the coordinate metric at p, e is
smooth on the radius-R ball, e(0)=p, and the derivative of phi composed with e
at zero is L. Each radial curve t maps to e(tv) is an affinely parametrized
geodesic wherever tv belongs to this ball; on the unit interval its speed is
the norm of v and its distance from p is at most t times that norm.

For every v in the parameter ball, de at v is invertible if v is zero or if
v is nonzero and there is a real q greater than one for which q times the norm
of v is less than R and the distance from p to e(qv) is q times that norm.
Moreover, let S consist of vectors in this ball whose endpoint distance equals
their norm, and let T consist of nonzero vectors in S having no rational q
greater than one with q times their norm less than R and qv in S. Then de is
invertible at every vector of S minus T.

## Alignment review

Accepted by the independent `statement_alignment_review` agent, using only the
mission's informal description and the independent `statement_translation`
agent's proposition. The connection is the Levi-Civita connection; the radial
geodesic and normalization properties identify the exponential. The extra
nonterminal-set conclusion follows from a rational minimizing extension.
No no-conjugacy, completeness, or index-positivity hypothesis was added.

The accepted declaration header, from `theorem` through `:= by` with its final
newline, has SHA-256
`0b8b0b030e9919a2c3af138ebd778644ab0e5f507550d440f1f97675b35ea549`.
The original mission claim is revision 1. The generic theorem
`isInvertible_mfderiv_on_nonterminal` applies the same checked criterion to an
already selected exponential; its intermediate interface was compared directly
with the conclusion above.
