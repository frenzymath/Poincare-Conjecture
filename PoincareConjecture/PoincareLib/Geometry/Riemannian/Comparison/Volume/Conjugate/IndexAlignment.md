# Index nonnegativity on a minimizing segment

## Informal description

Let a smooth Hausdorff Riemannian manifold carry its Levi-Civita connection.
Let a geodesic be defined on an open interval containing [a,b], with positive
constant speed C and endpoint distance (b-a)C. If a<c<b and two smooth vector
fields along the geodesic match at c and vanish at the respective outer
endpoints, their summed index integral over [a,c] and [c,b] is nonnegative.
The index density is the squared norm of the covariant derivative minus the
metric pairing of R(V,gamma')gamma' with V.

## Informal proof

Subdivide the compact parameter interval into finitely many coordinate pieces,
including c as a junction. Realize the fields in these coordinates using shared
local geodesics for the junction curves and fixed outer endpoints. Young's
inequality and the intrinsic distance triangle inequality give a lower bound
for the sum of energies of all competitor pieces. The base geodesic attains
this bound, hence its second variation is nonnegative. Metric compatibility
and the curvature commutator identify the second variation with the index
integral; geodesic junction curves have zero covariant acceleration and
therefore contribute no boundary term. Sum the interval integrals.

## Proposed formal statements

```lean
namespace PoincareMT.Conjugate.Realization

theorem index_nonneg_of_minimizing
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareMT.RiemannianMetric n M) (D : PoincareMT.LeviCivitaData g)
    {γ : ℝ → M} {V₀ V₁ : ℝ → EuclideanSpace ℝ (Fin n)} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) {I : Set ℝ} (hI : IsOpen I) (hsub : Set.Icc a b ⊆ I)
    (hgeo : g.IsGeodesicOn γ I)
    (hV₀ : ∀ t ∈ I, ContDiffAt ℝ ∞ (PoincareMT.ConnectionAlongCurve.chartField γ (γ t) V₀) t)
    (hV₁ : ∀ t ∈ I, ContDiffAt ℝ ∞ (PoincareMT.ConnectionAlongCurve.chartField γ (γ t) V₁) t)
    (hmatch : V₀ c = V₁ c) (hleft : V₀ a = 0) (hright : V₁ b = 0)
    {C : ℝ} (hC : 0 < C)
    (hspeed : ∀ t ∈ Set.Icc a b, g.tangentNorm (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = C)
    (hmin : g.edist (γ a) (γ b) = ENNReal.ofReal ((b - a) * C)) :
    0 ≤ (∫ t in a..c, PoincareMT.ConjugateVariation.intrinsicIndexIntegrand g D γ V₀ t) +
      ∫ t in c..b, PoincareMT.ConjugateVariation.intrinsicIndexIntegrand g D γ V₁ t := by
  sorry

end PoincareMT.Conjugate.Realization
```

## Informal translation

**Proposition.** Let M be a smooth Hausdorff Riemannian n-manifold without
boundary with smooth metric g and a smooth torsion-free, metric-compatible
connection D. Let a<c<b and let I be an open subset of the real line containing
[a,b]. Let gamma be a geodesic on I with positive constant speed C on [a,b] and
intrinsic endpoint distance (b-a)C. Let V0,V1 be vector fields along gamma,
defined for all real parameters and smooth on I in local charts. Suppose
V0(a)=0, V0(c)=V1(c), and V1(b)=0. Then the sum of their index integrals on
[a,c] and [c,b] is nonnegative, with density
|covariant derivative of V| squared minus <R(V,gamma')gamma',V>.
The curvature convention is R(X,Y)Z = D_X D_Y Z - D_Y D_X Z - D_[X,Y] Z.

## Alignment review

Accepted by the independent `index_alignment_review` agent using only the
informal description and the independent `index_statement_translation`
agent's proposition. An open set containing [a,b] may be restricted to its
component containing that interval. The connection, curvature convention,
matching and endpoint conditions, and minimizing-distance hypothesis agree.

The implementation declaration header, from `theorem` through `:= by` with
its final newline, has SHA-256
`cc5b7023c97c2349c1b21e53023d4d61d8e44b261c906bdb2be9c8cd15dcb213`.
Its ambient manifold binders are the section variables displayed in full above.
