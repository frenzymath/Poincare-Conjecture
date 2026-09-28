import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Hausdorffness of fiber bundle total spaces

For a topological fiber bundle `E : B → Type*` with model fiber `F` over a base `B`, the total
space `Bundle.TotalSpace F E` is Hausdorff as soon as both `B` and `F` are. The argument is the
usual "separate along the base, or trivialize and separate in the product" dichotomy:

* if two points of the total space project to distinct points of the base, their preimages
  under the (continuous) projection separate them;
* if they share the same base point, they both lie in the source of the preferred
  trivialization at that point, which is a homeomorphism onto an open subset of `B × F`; pulling
  back disjoint neighbourhoods of their (distinct) images in the Hausdorff space `B × F`
  separates them.

As a corollary, the tangent bundle `TangentBundle I M` of a `C^1` manifold `M` modelled on a
normed space over a Hausdorff base `M` is Hausdorff, since the model fiber (a normed space) is
always Hausdorff.

## Main results

* `FiberBundle.t2Space_totalSpace` — the total space of a fiber bundle over a Hausdorff base
  with Hausdorff model fiber is Hausdorff.
* `TangentBundle.t2Space` — the tangent bundle of a `C^1` manifold over a Hausdorff base is
  Hausdorff.
-/

open Bundle

/-- **Math.** The total space of a (topological) fiber bundle with model fiber `F` over a base
`B` is Hausdorff as soon as `B` and `F` both are. Two points with distinct base projections are
separated by pulling back disjoint open sets around their projections through the continuous
projection map; two points sharing the same base point are separated by pulling back disjoint
open sets around their (distinct) images under the preferred trivialization at that point, which
identifies a neighbourhood of both points with an open subset of the Hausdorff space `B × F`. -/
theorem FiberBundle.t2Space_totalSpace {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    {E : B → Type*} [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [T2Space B] [T2Space F] : T2Space (Bundle.TotalSpace F E) := by
  constructor
  intro x y hxy
  rcases eq_or_ne x.proj y.proj with hp | hp
  · -- Same base point: separate inside the preferred trivialization at `x.proj`.
    set e := trivializationAt F E x.proj with he_def
    have hxs : x ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have hys : y ∈ e.source :=
      e.mem_source.mpr (hp ▸ FiberBundle.mem_baseSet_trivializationAt F E x.proj)
    have hne : e x ≠ e y := fun h => hxy (e.injOn hxs hys h)
    obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hne
    exact ⟨e.source ∩ e ⁻¹' u, e.source ∩ e ⁻¹' v,
      e.isOpen_inter_preimage hu, e.isOpen_inter_preimage hv,
      ⟨hxs, hxu⟩, ⟨hys, hyv⟩,
      Set.disjoint_left.mpr fun _ hz hz' => Set.disjoint_left.mp huv hz.2 hz'.2⟩
  · -- Distinct base points: separate along the (continuous) projection.
    obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hp
    exact ⟨Bundle.TotalSpace.proj ⁻¹' u, Bundle.TotalSpace.proj ⁻¹' v,
      hu.preimage (FiberBundle.continuous_proj F E), hv.preimage (FiberBundle.continuous_proj F E),
      hxu, hyv, huv.preimage _⟩

/-- **Math.** The tangent bundle `TangentBundle I M` of a `C^1` manifold `M`, modelled on a
normed space `E` and charted on `H`, is Hausdorff as soon as the base manifold `M` is. This
specializes `FiberBundle.t2Space_totalSpace` to the tangent bundle, using that the model fiber
`E` (a normed space) is automatically Hausdorff. -/
instance TangentBundle.t2Space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M] :
    T2Space (TangentBundle I M) :=
  FiberBundle.t2Space_totalSpace

open scoped Manifold ContDiff in
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold J ∞ M] :
    T2Space (TangentBundle J M) := inferInstance
