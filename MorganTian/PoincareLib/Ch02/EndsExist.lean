import PoincareLib.Ch02.MinimizingSegment
import PoincareLib.Ch02.EndsLine
import OpenGALib.Riemannian.Exponential.ProperAssembly

/-!
# Morgan–Tian Ch. 2 — non-compact complete manifolds have ends

Blueprint `lem:ends-exist`: a complete, connected, non-compact Riemannian
manifold `(M, g)` (with the ambient distance the Riemannian distance of `g`)
has a minimizing geodesic ray emanating from any point `p`, and, if it has
more than one end, a minimizing line.

Following the blueprint proof, this reduces to three metric-space facts about
`M`:

* `M` **has minimizing segments** (`HasMinSegments M`): any two points are
  joined by a unit-speed minimizing geodesic segment — this is
  `hasMinSegments_of_complete` (do Carmo Hopf–Rinow f), landed in
  `MinimizingSegment.lean`.
* `M` is **proper** (`ProperSpace M`): closed metric balls are compact.  This
  is the geometric heart: on a complete manifold every tangent vector at `p`
  generates a *global* geodesic (Hopf–Rinow c ⟹ d,
  `isGeodesicallyComplete_of_complete`), and, together with the endpoint
  continuity of those geodesics in their initial data, the closed ball
  `B̄_R(p) = exp_p(B̄_R(0))` is the continuous image of a compact set
  (`Riemannian.Exponential.properSpace_of_forall_geodesic`).
* the ray and line then come from the metric backbones
  `exists_isGeodesicRay_of_noncompact` (`lem:ray-exists-metric`) and
  `exists_isMinGeodesicOn_univ_of_ends_ne` (`lem:line-exists-metric`).

The one analytic input that is not yet available as a standalone theorem is the
**endpoint continuity** of geodesics emanating from `p`,
`GeodesicEndpointContinuity g p` below (do Carmo Ch. 7, Theorem 2.8, the
`hend` hypothesis of `properSpace_of_forall_geodesic`; the flow-box chaining is
sketched in `OpenGALib`'s `Geodesic/EndpointContinuity.lean`, whose step lemma
`exists_conv_step` is still open).  The results here take it as an explicit
hypothesis; discharging it unconditionally upgrades them to the blueprint's
unconditional statement.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4;
do Carmo, *Riemannian Geometry*, Ch. 7, Theorem 2.8.
-/

open Set Filter Riemannian Riemannian.Geodesic Riemannian.Exponential
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- **Math.** **Endpoint continuity of geodesics emanating from `p`.** If global geodesics
`γₙ` all start at `p` with chart-`p` velocities `vₙ → v`, and `γ` is a global
geodesic through `(p, v)`, then `γₙ(tₙ) → γ(t₀)` whenever `tₙ → t₀`.

This is the analytic hypothesis `hend` of
`Riemannian.Exponential.properSpace_of_forall_geodesic`; it packages the
continuous dependence of the geodesic flow on its initial velocity, uniformly
along the limit geodesic (the flow-box chaining of do Carmo Ch. 7, Thm 2.8,
f ⟹ b). -/
def GeodesicEndpointContinuity (g : RiemannianMetric I M) (p : M) : Prop :=
  ∀ (γ : ℝ → M) (γs : ℕ → ℝ → M) (v : E) (vs : ℕ → E) (ts : ℕ → ℝ) (t₀ : ℝ),
    IsGeodesic (I := I) g γ → Continuous γ → γ 0 = p →
    (∀ n, IsGeodesic (I := I) g (γs n)) → (∀ n, Continuous (γs n)) →
    (∀ n, γs n 0 = p) →
    HasDerivAt (fun τ => extChartAt I p (γ τ)) v 0 →
    (∀ n, HasDerivAt (fun τ => extChartAt I p (γs n τ)) (vs n) 0) →
    Tendsto vs atTop (𝓝 v) →
    Tendsto ts atTop (𝓝 t₀) →
    Tendsto (fun n => γs n (ts n)) atTop (𝓝 (γ t₀))

/-- **Math.** A complete Riemannian manifold, metrized by the Riemannian
distance of `g`, is a **proper** metric space (closed balls are compact),
provided its geodesics emanating from some point `p` depend continuously on
their initial data (`GeodesicEndpointContinuity g p`).

Every tangent vector at `p` generates a global geodesic by Hopf–Rinow c ⟹ d
(`isGeodesicallyComplete_of_complete`); properness is then
`Riemannian.Exponential.properSpace_of_forall_geodesic`. -/
theorem properSpace_of_complete (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (hend : GeodesicEndpointContinuity g p) :
    ProperSpace M :=
  properSpace_of_forall_geodesic (I := I) g hg p
    (fun v => isGeodesicallyComplete_of_complete (I := I) g hg p v) hend

/-- **Math.** Blueprint `lem:ends-exist` (ray half): a complete, connected,
non-compact Riemannian manifold has a unit-speed minimizing geodesic ray
emanating from any point `p` — conditionally on the endpoint continuity of
geodesics from `p`. -/
theorem exists_isGeodesicRay_of_complete_noncompact
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] [ConnectedSpace M] [NoncompactSpace M]
    (p : M) (hend : GeodesicEndpointContinuity g p) :
    ∃ γ : ℝ → M, IsGeodesicRay γ ∧ γ 0 = p := by
  haveI : ProperSpace M := properSpace_of_complete g hg p hend
  exact exists_isGeodesicRay_of_noncompact (hasMinSegments_of_complete g hg) p

/-- **Math.** Blueprint `lem:ends-exist` (line half): a complete, connected
Riemannian manifold with two distinct ends contains a unit-speed minimizing
geodesic line — conditionally on the endpoint continuity of geodesics from some
point `p`. -/
theorem exists_isMinGeodesicOn_univ_of_complete_ends_ne
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] [ConnectedSpace M]
    (p : M) (hend : GeodesicEndpointContinuity g p)
    {e₁ e₂ : SpaceOfEnds M} (hne : e₁ ≠ e₂) :
    ∃ γ : ℝ → M, IsMinGeodesicOn γ Set.univ := by
  haveI : ProperSpace M := properSpace_of_complete g hg p hend
  exact exists_isMinGeodesicOn_univ_of_ends_ne (hasMinSegments_of_complete g hg) hne

end PoincareLib

end
