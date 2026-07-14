import MorganTianLib.Ch02.GeodesicLimits
import OpenGALib.Riemannian.Geodesic.HopfRinow

/-!
# Morgan–Tian Ch. 2 — existence of minimizing geodesic segments

Blueprint `lem:minimizing-segment-exists`: on a connected, complete Riemannian
manifold `(M, g)` (with the ambient distance the Riemannian distance of `g`),
any two points `x, y` are joined by a **unit-speed minimizing geodesic segment**
`σ : [0, d(x,y)] → M`, i.e. `dist (σ s) (σ t) = |s - t|` for
`s, t ∈ [0, d(x,y)]`, with `σ 0 = x` and `σ (d(x,y)) = y`.

This discharges the metric-space predicate `HasMinSegments M`
(`GeodesicLimits.lean`), the standing hypothesis of the ray/line existence
backbones `exists_isGeodesicRay_of_noncompact` (`lem:ray-exists-metric`) and
`exists_isMinGeodesicOn_univ_of_ends_ne` (`lem:line-exists-metric`) that feed
the asymptotic-ray, Busemann and ends machinery of this chapter.

The mathematical content is do Carmo's Hopf–Rinow minimizing-geodesic theorem
(`Riemannian.Geodesic.exists_minimizing_geodesic`, do Carmo Ch. 7, Thm 2.8 f),
which produces a proportional-to-arclength minimizing geodesic `γ : [0,1] → M`
with `dist (γ s) (γ t) = |s - t| · d(x,y)`; reparametrizing by `s ↦ s / d(x,y)`
turns it into the unit-speed segment on `[0, d(x,y)]`.  This is an equivalent
route to the cut-locus argument sketched in the blueprint proof.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4;
do Carmo, *Riemannian Geometry*, Ch. 7, Theorem 2.8.
-/

open Set Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** Blueprint `lem:minimizing-segment-exists`: on a connected,
complete Riemannian manifold `(M, g)` — with the ambient distance the
Riemannian distance of `g` (`g.IsRiemannianDist`) — any two points are joined by
a unit-speed minimizing geodesic segment.  Formally, `M` satisfies the
metric-space predicate `HasMinSegments M`: for all `x, y`, there is `σ : ℝ → M`
with `σ 0 = x`, `σ (d(x,y)) = y`, and `dist (σ s) (σ t) = |s - t|` for
`s, t ∈ [0, d(x,y)]`.

The witness is do Carmo's proportional-to-arclength minimizing geodesic
`γ : [0,1] → M` (`Riemannian.Geodesic.exists_minimizing_geodesic`) reparametrized
to unit speed by `s ↦ γ (s / d(x,y))`; the degenerate case `x = y` uses the
constant curve. -/
theorem hasMinSegments_of_complete (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [ConnectedSpace M] [CompleteSpace M] :
    HasMinSegments M := by
  intro x y
  by_cases hxy : x = y
  · -- Degenerate case `x = y`: the window `[0, d(x,x)] = [0,0] = {0}` collapses,
    -- and the constant curve is a (trivial) minimizing segment.
    subst hxy
    refine ⟨fun _ => x, rfl, rfl, ?_⟩
    intro s hs t ht
    rw [dist_self] at hs ht
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst hs0; subst ht0
    simp
  · -- Non-degenerate case `x ≠ y`, so `d := d(x,y) > 0`.
    have hd : 0 < dist x y := dist_pos.mpr hxy
    obtain ⟨γ, h0, h1, _hgeo, hdist⟩ :=
      Riemannian.Geodesic.exists_minimizing_geodesic (I := I) g hg x y
    refine ⟨fun s => γ (s / dist x y), ?_, ?_, ?_⟩
    · show γ (0 / dist x y) = x
      rw [zero_div, h0]
    · show γ (dist x y / dist x y) = y
      rw [div_self hd.ne', h1]
    · intro s hs t ht
      show dist (γ (s / dist x y)) (γ (t / dist x y)) = |s - t|
      have hmem : ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) (dist x y) →
          u / dist x y ∈ Set.Icc (0 : ℝ) 1 := fun {u} hu =>
        ⟨div_nonneg hu.1 hd.le, (div_le_one hd).mpr hu.2⟩
      rw [hdist _ (hmem hs) _ (hmem ht), div_sub_div_same, abs_div, abs_of_pos hd,
        div_mul_eq_mul_div, mul_div_assoc, div_self hd.ne', mul_one]

end MorganTianLib

end
