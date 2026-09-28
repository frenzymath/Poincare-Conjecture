import KleinerLott.RicciFlow.PointSelection

/-!
# Complete metric-flow geometry

This file packages the compactness and continuity properties of a smooth
complete time-dependent metric that are used by the point-selection argument.
-/

namespace KleinerLott

namespace RicciFlowData

/-- The geometric consequences of smooth completeness needed on a time set:
proper time-slice distances, radial distance paths, and joint continuity of
distance and curvature. -/
structure HasSmoothCompleteGeometryOn {M : Type*} [TopologicalSpace M]
    (flow : RicciFlowData M) (I : Set ℝ) : Prop where
  curvature_continuous :
    ContinuousOn (Function.uncurry flow.curvatureNorm) (Set.univ ×ˢ I)
  proper : ∀ x₀ t, t ∈ I → flow.IsProperAt x₀ t
  dist_self_eq_zero : ∀ x₀ t, t ∈ I → flow.dist t x₀ x₀ = 0
  dist_continuous : ∀ x₀,
    ContinuousOn (Function.uncurry fun t x ↦ flow.dist t x₀ x)
      (I ×ˢ Set.univ)
  radial_paths : ∀ x₀, flow.HasRadialDistancePathsOn x₀ I

/-- Smooth-complete geometry makes bounded balls for nearby times uniformly
bounded in any fixed reference-time distance. -/
theorem HasSmoothCompleteGeometryOn.isLocallyDistanceComparableOn
    {M : Type*} [TopologicalSpace M] {flow : RicciFlowData M} {I : Set ℝ}
    (hgeometry : flow.HasSmoothCompleteGeometryOn I) (x₀ : M) :
    flow.IsLocallyDistanceComparableOn x₀ I :=
  (hgeometry.radial_paths x₀).hasAlmostRadialDistancePathsOn
    |>.isLocallyDistanceComparableOn
    (hgeometry.proper x₀) (hgeometry.dist_self_eq_zero x₀)
    (hgeometry.dist_continuous x₀)

/-- Over compact time, smooth-complete geometry places every bounded moving
ball in a compact spacetime set. -/
theorem HasSmoothCompleteGeometryOn.isSpacetimePrecompactOn
    {M : Type*} [TopologicalSpace M] {flow : RicciFlowData M} {I : Set ℝ}
    (hgeometry : flow.HasSmoothCompleteGeometryOn I) (x₀ : M)
    (hI : IsCompact I) : flow.IsSpacetimePrecompactOn x₀ I :=
  (hgeometry.isLocallyDistanceComparableOn x₀).isSpacetimePrecompactOn
    (hgeometry.proper x₀) hI

/-- Curvature is bounded on bounded moving balls over a compact time set with
smooth-complete geometry. -/
theorem HasSmoothCompleteGeometryOn.isCurvatureBoundedOnMovingBalls
    {M : Type*} [TopologicalSpace M] {flow : RicciFlowData M} {I : Set ℝ}
    (hgeometry : flow.HasSmoothCompleteGeometryOn I) (x₀ : M)
    (hI : IsCompact I) : flow.IsCurvatureBoundedOnMovingBalls x₀ I :=
  (hgeometry.isSpacetimePrecompactOn x₀ hI)
    |>.isCurvatureBoundedOnMovingBalls_of_continuousOn hI
      hgeometry.curvature_continuous

end RicciFlowData

/-- Point selection for scalar flow data carrying the compactness and
continuity consequences of a smooth complete metric flow on the relevant time
slab. -/
theorem exists_point_selection_of_smooth_complete_geometry
    {M : Type*} [TopologicalSpace M]
    (flow : RicciFlowData M) (n : ℕ) {alpha A epsilon t : ℝ} {x₀ x : M}
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (hAepsilon : A * epsilon < (100 * (n : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : flow.dist t x₀ x ≤ epsilon)
    (hcurvature :
      alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤ flow.curvatureNorm x t)
    (hgeometry :
      flow.HasSmoothCompleteGeometryOn (Set.Icc 0 (epsilon ^ 2))) :
    ∃ xbar tbar,
      (xbar, tbar) ∈ flow.highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        flow.dist tbar x₀ xbar < (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈ flow.highCurvatureRegion alpha →
            t' ∈ Set.Ioc 0 tbar →
              flow.dist t' x₀ x' ≤
                  flow.dist tbar x₀ xbar +
                    A * (Real.sqrt (flow.curvatureNorm xbar tbar))⁻¹ →
                flow.curvatureNorm x' t' ≤ 4 * flow.curvatureNorm xbar tbar := by
  exact exists_point_selection_of_continuous_proper_distance_family flow n
    halpha hA hepsilon hAepsilon ht hdist hcurvature
    hgeometry.curvature_continuous (hgeometry.proper x₀)
    (hgeometry.dist_self_eq_zero x₀) (hgeometry.dist_continuous x₀)
    (hgeometry.radial_paths x₀)

end KleinerLott
