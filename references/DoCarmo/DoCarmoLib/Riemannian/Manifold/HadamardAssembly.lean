import DoCarmoLib.Riemannian.Manifold.CoveringDiffeomorph
import DoCarmoLib.Riemannian.Geodesic.HopfRinow

/-!
# The Hadamard assembly from geodesic completeness at a point (do Carmo Ch. 7, §3.4)

`CoveringDiffeomorph.lean` proved `DCExpandsMetric.diffeomorphOfSimplyConnected`: a
metric-expanding smooth local diffeomorphism `f : M → M'` out of a **proper**
(`[ProperSpace M]`) manifold `M`, onto a simply connected `M'`, is a diffeomorphism. That
statement takes properness as a *typeclass instance*. In do Carmo's proof of the Hadamard
theorem, however, properness of the source `T_pM` (with the pulled-back metric) is **not**
assumed — it is *derived* from the sentence

> Such a metric is complete, because the geodesics of `T_pM` passing through the origin are
> straight lines (cf. Theorem 2.8, (a) ⟹ (d)).

i.e. from **geodesic completeness at the single point `o = 0`**: every ray direction generates
a geodesic defined for all time. This file provides the assembly in exactly that form.

* `DCExpandsMetric.diffeomorphOfSimplyConnectedOfGeodesicCompleteAt` — the do Carmo Ch. 7
  §3.4 assembly with the completeness hypothesis stated as do Carmo states it: given some
  `o : M` at which `M` is geodesically complete (every `v ∈ T_oM` generates a continuous
  global geodesic), the map `f` (metric-expanding smooth local diffeomorphism onto a simply
  connected `M'`) is a diffeomorphism. Internally it derives `[ProperSpace M]` from
  `Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at` (Hopf–Rinow, a) ⟹ b)) and
  then applies `DCExpandsMetric.diffeomorphOfSimplyConnected`.

This is the correct interface for the eventual instantiation at `f = exp_p : T_pM → M`: one
cannot supply a `[ProperSpace (T_pM)]` *instance* for the pulled-back metric, only *derive*
properness from "the rays are geodesics" (`ho`). The two remaining analytic obligations of
the Hadamard theorem — that `exp_p` is a smooth local diffeomorphism (`lem:dc-ch7-3-2`, via
Ch. 5 Jacobi fields) and that the rays of `T_pM` are geodesics of the pulled-back metric
(the local-isometry input `ho`) — are precisely the inputs this assembly still consumes;
everything topological/smooth downstream of them is now checked.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3.4, proof of Theorem 3.1 (Hadamard) and
Remark 3.4 (poles).
-/

open Bundle Manifold Set Function
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** do Carmo Ch. 7, §3.4, proof of the Hadamard theorem (`thm:dc-ch7-3-1`),
completeness-from-geodesics form. Let `f : M → M'` be a smooth local diffeomorphism between
Riemannian manifolds which **expands the metric** (`|df_p(v)| ≥ |v|`), let `M'` be **simply
connected**, and suppose `M` is **geodesically complete at some point `o`**: every
`v ∈ T_oM` generates a continuous geodesic `γ : ℝ → M` defined for all time with `γ 0 = o`
and chart-`o` velocity `v`. Then `f` is a **diffeomorphism**.

This is `DCExpandsMetric.diffeomorphOfSimplyConnected` with the `[ProperSpace M]` instance
requirement replaced by do Carmo's own completeness hypothesis: properness of `M` is derived
internally from `Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at` (Hopf–Rinow,
a) ⟹ b)). Applied to `f = exp_p : T_pM → M`, the hypothesis `ho` is "the geodesics of `T_pM`
through the origin are straight lines" and the conclusion is the Hadamard diffeomorphism. -/
def DCExpandsMetric.diffeomorphOfSimplyConnectedOfGeodesicCompleteAt
    [T2Space M'] [I'.Boundaryless] [ConnectedSpace M]
    [SimplyConnectedSpace M'] [LocallyPathConnectedSpace M']
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (o : M) (ho : ∀ v : TangentSpace I o, ∃ γ : ℝ → M, γ 0 = o ∧
      HasDerivAt (fun s => extChartAt I o (γ s)) v 0 ∧ Continuous γ ∧
        Geodesic.IsGeodesic (I := I) gM γ)
    (hf : IsLocalDiffeomorph I I' ∞ f) : Diffeomorph I I' M M' ∞ :=
  haveI : ProperSpace M :=
    Geodesic.properSpace_of_geodesicallyComplete_at (I := I) gM hgM o ho
  hexp.diffeomorphOfSimplyConnected hgM hf

/-- **Math.** The underlying map of `diffeomorphOfSimplyConnectedOfGeodesicCompleteAt` is `f`
itself: the constructed diffeomorphism is `f`, upgraded, not a new map. -/
theorem DCExpandsMetric.diffeomorphOfSimplyConnectedOfGeodesicCompleteAt_coe
    [T2Space M'] [I'.Boundaryless] [ConnectedSpace M]
    [SimplyConnectedSpace M'] [LocallyPathConnectedSpace M']
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (o : M) (ho : ∀ v : TangentSpace I o, ∃ γ : ℝ → M, γ 0 = o ∧
      HasDerivAt (fun s => extChartAt I o (γ s)) v 0 ∧ Continuous γ ∧
        Geodesic.IsGeodesic (I := I) gM γ)
    (hf : IsLocalDiffeomorph I I' ∞ f) :
    ⇑(hexp.diffeomorphOfSimplyConnectedOfGeodesicCompleteAt hgM o ho hf) = f := rfl

end Riemannian

end
