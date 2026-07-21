import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import LeeSmoothLib.Ch08.Sec08_57.Definition_8_57_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Domain sampling:
-- * primary domain: smooth vector fields on manifolds and their relatedness along smooth maps;
-- * core/canonical owners sampled before refinement:
--   `C^∞⟮I, M; J, N⟯` for bundled smooth maps,
--   `Cₛ^∞⟮I; E, TangentSpace I⟯` for smooth vector fields,
--   `VectorField.f_related` for the source-facing relatedness predicate;
-- * bridge data: the graph-related rough vector field, whose smoothness is a derived fact.
-- The graph construction uses only `mfderiv`, product manifolds, bundled smooth maps/sections,
-- and the chapter owner `VectorField.f_related`, so no finite-dimensional ambient hypothesis
-- belongs in this file.
-- Semantic recall note: `lean_leansearch` confirmed that the tangent-coordinate API is centered
-- on `inTangentCoordinates_eq_mfderiv_comp`; the local source-facing owner remains
-- `VectorField.f_related`.

universe u𝕜 uE uE' uH uH' uM uN

noncomputable section

section

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E' H'}
  [IsManifold I ∞ M]
  [IsManifold J ∞ N]

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun x : M ↦ TangentSpace I x⟯
local notation "SmoothProductVectorField" =>
  Cₛ^∞⟮I.prod J; E × E', fun p : M × N ↦ TangentSpace (I.prod J) p⟯
local notation "SmoothMap" => C^∞⟮I, M; J, N⟯

namespace VectorField

/-- Helper for Problem 8-14: the first projection as a bundled smooth map on the pair base
`N × N`. -/
abbrev graphTransportPairBaseFstSmoothMap : C^∞⟮J.prod J, N × N; J, N⟯ :=
  ⟨Prod.fst, contMDiff_fst⟩

/-- Helper for Problem 8-14: the second projection as a bundled smooth map on the pair base
`N × N`. -/
abbrev graphTransportPairBaseSndSmoothMap : C^∞⟮J.prod J, N × N; J, N⟯ :=
  ⟨Prod.snd, contMDiff_snd⟩

/-- Helper for Problem 8-14: the source tangent bundle pulled back to the pair base through
`Prod.fst`. -/
abbrev graphTransportSourceBundle : (N × N) → Type _ :=
  graphTransportPairBaseFstSmoothMap (J := J) *ᵖ (fun x : N ↦ TangentSpace J x)

/-- Helper for Problem 8-14: the target tangent bundle pulled back to the pair base through
`Prod.snd`. -/
abbrev graphTransportTargetBundle : (N × N) → Type _ :=
  graphTransportPairBaseSndSmoothMap (J := J) *ᵖ (fun x : N ↦ TangentSpace J x)

/-- Helper for Problem 8-14: the bundle of fiberwise continuous linear maps from the source
pullback tangent bundle to the target pullback tangent bundle over the pair base. -/
abbrev graphTransportPairBaseHomBundle : (N × N) → Type _ :=
  fun q ↦
    graphTransportSourceBundle (J := J) q →L[𝕜]
      graphTransportTargetBundle (J := J) q

/-- Helper for Problem 8-14: the graph transport only depends on the pair base
`(f p.1, p.2) ∈ N × N`. -/
abbrev graphTransportPairBase (f : SmoothMap) : M × N → N × N :=
  fun p ↦ (f p.1, p.2)

/-- The vector field on `M × N` whose first component is `X` and whose second component is
`mfderiv I J f x (X x)`, pulled back constantly along the `N`-factor. -/
@[simp]
def graphRelated (f : M → N) (X : ∀ x : M, TangentSpace I x) :
    ∀ p : M × N, TangentSpace (I.prod J) p :=
  fun p ↦ (X p.1, mfderiv I J f p.1 (X p.1))

/-- Helper for Problem 8-14: pushing the section `T% X` forward by `tangentMap I J f` and then
pulling it back along `Prod.fst` gives a smooth section of `TN` over `f ∘ Prod.fst`. -/
lemma graphDerivativeSectionAlongFst_contMDiff
    (f : SmoothMap) {X : ∀ x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X)) :
    ContMDiff (I.prod J) J.tangent ∞
      (fun p : M × N ↦ tangentMap I J f (T% X p.1)) := by
  -- Smoothness comes from the bundled tangent map of `f` composed with the smooth first-factor
  -- section `p ↦ T% X p.1`.
  have htangent :
      ContMDiff I.tangent J.tangent ∞ (tangentMap I J f) := by
    simpa using f.contMDiff.contMDiff_tangentMap (by simp)
  simpa [Function.comp] using htangent.comp (hX.comp contMDiff_fst)

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Problem 8-14: the graph-source chart neighborhood around `f p₀.1` is a genuine
neighborhood of `p₀` in `M × N`. -/
lemma graphTransportSourceChart_mem_nhds
    (f : SmoothMap) (p0 : M × N) :
    {p : M × N | f p.1 ∈ (chartAt H' (f p0.1)).source} ∈ nhds p0 := by
  -- Continuity of `f ∘ Prod.fst` keeps the source point inside the fixed chart near `p₀`.
  have hcont :
      ContinuousAt (fun p : M × N ↦ f p.1) p0 :=
    ((f.contMDiff.comp
        (contMDiff_fst : ContMDiff (I.prod J) I ∞ (Prod.fst : M × N → M))) p0).continuousAt
  have hsource : (extChartAt J (f p0.1)).source ∈ nhds (f p0.1) := by
    simpa using
      (extChartAt_source_mem_nhds (f p0.1) :
        (extChartAt J (f p0.1)).source ∈ nhds (f p0.1))
  simpa [Function.comp] using
    hcont.preimage_mem_nhds hsource

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Problem 8-14: the source chart map `p ↦ extChartAt J (f p₀.1) (f p.1)` is smooth at
`p₀`. -/
lemma graphTransportSourceChart_contMDiffAt
    (f : SmoothMap) (p0 : M × N) :
    ContMDiffAt (I.prod J) 𝓘(𝕜, E') ∞
      (fun p : M × N ↦ extChartAt J (f p0.1) (f p.1)) p0 := by
  -- Compose the smooth graph-base map `f ∘ Prod.fst` with the fixed target chart.
  have hbase : ContMDiffAt (I.prod J) J ∞ (fun p : M × N ↦ f p.1) p0 := by
    simpa [Function.comp] using
      ((f.contMDiff.comp
          (contMDiff_fst : ContMDiff (I.prod J) I ∞ (Prod.fst : M × N → M))) p0)
  have hchart :
      ContMDiffAt J 𝓘(𝕜, E') ∞ (extChartAt J (f p0.1)) (f p0.1) := by
    simpa using
      (contMDiffAt_extChartAt :
        ContMDiffAt J 𝓘(𝕜, E') ∞ (extChartAt J (f p0.1)) (f p0.1))
  simpa [Function.comp] using hchart.comp p0 hbase

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Problem 8-14: on the source-chart neighborhood, the chart map lands in
`Set.range J`, so within-derivative statements over `range J` can be evaluated there. -/
lemma graphTransportSourceChart_mapsTo_range
    (f : SmoothMap) (p0 : M × N) :
    Set.MapsTo
      (fun p : M × N ↦ extChartAt J (f p0.1) (f p.1))
      {p : M × N | f p.1 ∈ (chartAt H' (f p0.1)).source}
      (Set.range J) := by
  -- Chart images of points in the source lie in the preferred target set `range J`.
  intro p hp
  have hp' : f p.1 ∈ (extChartAt J (f p0.1)).source := by
    simpa [extChartAt_source] using (show f p.1 ∈ (chartAt H' (f p0.1)).source from hp)
  exact extChartAt_target_subset_range (f p0.1)
    ((extChartAt J (f p0.1)).map_source hp')

/-- Helper for Problem 8-14: the fixed target chart derivative is smooth in the tangent-coordinate
form produced by `ContMDiffAt.mfderiv_const`. -/
lemma graphTransportTargetDerivativeInCoordinates_contMDiffAt
    (y0 : N) :
    ContMDiffAt J 𝓘(𝕜, E' →L[𝕜] E') ∞
      (inTangentCoordinates J 𝓘(𝕜, E') id (extChartAt J y0)
        (fun y : N ↦ mfderiv% (extChartAt J y0) y) y0) y0 := by
  -- `ContMDiffAt.mfderiv_const` is already stated in exactly these fixed-base tangent coordinates.
  simpa using
    ((contMDiffAt_extChartAt :
      ContMDiffAt J 𝓘(𝕜, E') ∞ (extChartAt J y0) y0)).mfderiv_const (by simp)

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: composing the fixed target derivative-in-coordinates family with
`Prod.snd` gives a smooth `E' →L[𝕜] E'` family on `M × N`. -/
lemma graphTransportTargetDerivativeInCoordinatesAlongSnd_contMDiffAt
    (p0 : M × N) :
    ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun p : M × N ↦
        inTangentCoordinates J 𝓘(𝕜, E') id (extChartAt J p0.2)
          (fun y : N ↦ mfderiv% (extChartAt J p0.2) y) p0.2 p.2) p0 := by
  -- Pull the one-variable target derivative-in-coordinates family back along the smooth second
  -- projection.
  simpa [Function.comp] using
    (graphTransportTargetDerivativeInCoordinates_contMDiffAt p0.2).comp p0
      (contMDiffAt_snd : ContMDiffAt (I.prod J) J ∞ (Prod.snd : M × N → N) p0)

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: composing the fixed inverse chart derivative-in-coordinates family
with the graph-source chart gives a smooth `E' →L[𝕜] E'` family on `M × N`. -/
lemma graphTransportSourceInverseDerivativeInCoordinatesAlongGraph_contMDiffAt
    (f : SmoothMap) (p0 : M × N) :
    ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun p : M × N ↦
        inTangentCoordinates 𝓘(𝕜, E') J id (extChartAt J (f p0.1)).symm
          (fun z : E' ↦ mfderiv[Set.range J] (extChartAt J (f p0.1)).symm z)
          (extChartAt J (f p0.1) (f p0.1))
          (extChartAt J (f p0.1) (f p.1))) p0 := by
  -- First prove smoothness of the fixed inverse chart derivative-in-coordinates on the model
  -- chart range.
  have hmodel :
      ContMDiffWithinAt 𝓘(𝕜, E') 𝓘(𝕜, E' →L[𝕜] E') ∞
        (inTangentCoordinates 𝓘(𝕜, E') J id (extChartAt J (f p0.1)).symm
          (fun z : E' ↦ mfderiv[Set.range J] (extChartAt J (f p0.1)).symm z)
          (extChartAt J (f p0.1) (f p0.1)))
        (Set.range J) (extChartAt J (f p0.1) (f p0.1)) := by
    have hsymm :
        ContMDiffWithinAt 𝓘(𝕜, E') J ∞
          (extChartAt J (f p0.1)).symm (Set.range J)
          (extChartAt J (f p0.1) (f p0.1)) :=
      contMDiffWithinAt_extChartAt_symm_range_self (f p0.1)
    exact hsymm.mfderivWithin_const (by simp)
      (by simp) J.uniqueMDiffOn
  -- Next compose this model-space family with the already-smooth source chart map.
  have hsourceWithin :
      ContMDiffWithinAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun p : M × N ↦
          inTangentCoordinates 𝓘(𝕜, E') J id (extChartAt J (f p0.1)).symm
            (fun z : E' ↦ mfderiv[Set.range J] (extChartAt J (f p0.1)).symm z)
            (extChartAt J (f p0.1) (f p0.1))
            (extChartAt J (f p0.1) (f p.1)))
        {p : M × N | f p.1 ∈ (chartAt H' (f p0.1)).source} p0 := by
    -- The chart map lands in `range J` on the source-chart neighborhood, so within-composition
    -- applies without any pullback-bundle API.
    exact
      hmodel.comp p0
        (graphTransportSourceChart_contMDiffAt f p0).contMDiffWithinAt
        (graphTransportSourceChart_mapsTo_range f p0)
  -- Finally upgrade the within-smooth statement to a pointwise one using that neighborhood fact.
  exact hsourceWithin.contMDiffAt
    (graphTransportSourceChart_mem_nhds f p0)

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the chart-derivative sandwich written entirely in fixed model-space
coordinates is smooth at the chosen base point. -/
lemma graphTransportDerivativeSandwichInCoordinates_contMDiffAt
    (f : SmoothMap) (p0 : M × N) :
    ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun p : M × N ↦
        (inTangentCoordinates J 𝓘(𝕜, E') id (extChartAt J p0.2)
          (fun y : N ↦ mfderiv% (extChartAt J p0.2) y) p0.2 p.2).comp
        (inTangentCoordinates 𝓘(𝕜, E') J id (extChartAt J (f p0.1)).symm
          (fun z : E' ↦ mfderiv[Set.range J] (extChartAt J (f p0.1)).symm z)
          (extChartAt J (f p0.1) (f p0.1))
          (extChartAt J (f p0.1) (f p.1)))) p0 := by
  -- Both coordinate factors already vary smoothly in the fixed model fiber `E' →L[𝕜] E'`.
  have htarget :
      ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun p : M × N ↦
          inTangentCoordinates J 𝓘(𝕜, E') id (extChartAt J p0.2)
            (fun y : N ↦ mfderiv% (extChartAt J p0.2) y) p0.2 p.2) p0 :=
    graphTransportTargetDerivativeInCoordinatesAlongSnd_contMDiffAt p0
  have hsource :
      ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun p : M × N ↦
          inTangentCoordinates 𝓘(𝕜, E') J id (extChartAt J (f p0.1)).symm
            (fun z : E' ↦ mfderiv[Set.range J] (extChartAt J (f p0.1)).symm z)
            (extChartAt J (f p0.1) (f p0.1))
            (extChartAt J (f p0.1) (f p.1))) p0 :=
    graphTransportSourceInverseDerivativeInCoordinatesAlongGraph_contMDiffAt f p0
  -- Compose the two smooth continuous-linear-map families pointwise.
  exact htarget.clm_comp hsource

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: on the common chart neighborhood, the raw graph-transport sandwich
is exactly the composition of the fixed target tangent trivialization with the inverse source
tangent trivialization. -/
lemma graphTransportRawDerivativeSandwich_eq_trivialization
    (f : SmoothMap) {p0 p : M × N}
    (hp1 : f p.1 ∈ (chartAt H' (f p0.1)).source)
    (hp2 : p.2 ∈ (chartAt H' p0.2).source) :
    (mfderiv% (extChartAt J p0.2) p.2).comp
        (mfderiv[Set.range J] (extChartAt J (f p0.1)).symm
          (extChartAt J (f p0.1) (f p.1))) =
      ((trivializationAt E' (TangentSpace J) p0.2).continuousLinearMapAt 𝕜 p.2).comp
        ((trivializationAt E' (TangentSpace J) (f p0.1)).symmL 𝕜 (f p.1)) := by
  -- Rewrite each raw derivative as the corresponding tangent-bundle trivialization linear map.
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hp2,
    TangentBundle.symmL_trivializationAt hp1]
  rfl

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: near `p₀`, the graph transport written by
`inTangentCoordinates` is the raw chart-derivative sandwich. -/
lemma graphTransportIdentityInCoordinates_eventuallyEq_rawDerivativeSandwich
    (f : SmoothMap) (p0 : M × N) :
    (fun p : M × N ↦
      inTangentCoordinates J J (fun q : M × N ↦ f q.1) Prod.snd
        (fun _ ↦ (1 : E' →L[𝕜] E')) p0 p) =ᶠ[nhds p0]
      (fun p : M × N ↦
        (mfderiv% (extChartAt J p0.2) p.2).comp
          (mfderiv[Set.range J] (extChartAt J (f p0.1)).symm
            (extChartAt J (f p0.1) (f p.1)))) := by
  -- Work on the neighborhood where both preferred charts stay valid.
  have hfst := graphTransportSourceChart_mem_nhds f p0
  have hsnd :
      {p : M × N | p.2 ∈ (chartAt H' p0.2).source} ∈ nhds p0 := by
    have hcont : ContinuousAt (Prod.snd : M × N → N) p0 :=
      (contMDiffAt_snd : ContMDiffAt (I.prod J) J ∞ (Prod.snd : M × N → N) p0).continuousAt
    simpa [extChartAt_source] using hcont.preimage_mem_nhds
      (extChartAt_source_mem_nhds p0.2 : (extChartAt J p0.2).source ∈ nhds p0.2)
  filter_upwards [hfst, hsnd] with p hp1 hp2
  -- On that neighborhood, `inTangentCoordinates` expands to the expected derivative sandwich.
  exact inTangentCoordinates_eq_mfderiv_comp hp1 hp2

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: near `p₀`, the raw graph-transport sandwich agrees with the fixed
trivialization transport family. -/
lemma graphTransportRawDerivativeSandwich_eventuallyEq_trivialization
    (f : SmoothMap) (p0 : M × N) :
    (fun p : M × N ↦
      (mfderiv% (extChartAt J p0.2) p.2).comp
        (mfderiv[Set.range J] (extChartAt J (f p0.1)).symm
          (extChartAt J (f p0.1) (f p.1)))) =ᶠ[nhds p0]
      (fun p : M × N ↦
        ((trivializationAt E' (TangentSpace J) p0.2).continuousLinearMapAt 𝕜 p.2).comp
          ((trivializationAt E' (TangentSpace J) (f p0.1)).symmL 𝕜 (f p.1))) := by
  -- Work on the common chart neighborhood where both derivative factors identify with the fixed
  -- tangent trivializations.
  have hfst := graphTransportSourceChart_mem_nhds f p0
  have hsnd :
      {p : M × N | p.2 ∈ (chartAt H' p0.2).source} ∈ nhds p0 := by
    have hcont : ContinuousAt (Prod.snd : M × N → N) p0 :=
      (contMDiffAt_snd : ContMDiffAt (I.prod J) J ∞ (Prod.snd : M × N → N) p0).continuousAt
    simpa [extChartAt_source] using hcont.preimage_mem_nhds
      (extChartAt_source_mem_nhds p0.2 : (extChartAt J p0.2).source ∈ nhds p0.2)
  filter_upwards [hfst, hsnd] with p hp1 hp2
  -- Rewrite the raw derivative sandwich in terms of the fixed trivializations at `f p₀.1` and
  -- `p₀.2`.
  exact graphTransportRawDerivativeSandwich_eq_trivialization f hp1 hp2

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: near `p₀`, the graph transport written by
`inTangentCoordinates` agrees with the fixed-trivialization transport family. -/
lemma graphTransportIdentityInCoordinates_eventuallyEq_trivialization
    (f : SmoothMap) (p0 : M × N) :
    (fun p : M × N ↦
      inTangentCoordinates J J (fun q : M × N ↦ f q.1) Prod.snd
        (fun _ ↦ (1 : E' →L[𝕜] E')) p0 p) =ᶠ[nhds p0]
      (fun p : M × N ↦
        ((trivializationAt E' (TangentSpace J) p0.2).continuousLinearMapAt 𝕜 p.2).comp
          ((trivializationAt E' (TangentSpace J) (f p0.1)).symmL 𝕜 (f p.1))) := by
  -- Pass through the already-proved raw derivative sandwich to keep the bridge lemma shallow.
  exact
    (graphTransportIdentityInCoordinates_eventuallyEq_rawDerivativeSandwich f p0).trans
      (graphTransportRawDerivativeSandwich_eventuallyEq_trivialization f p0)

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Problem 8-14: applying a fixed chart and then its inverse stays in the same chart
source. -/
lemma chartAt_symm_chartAt_mem_source
    {x0 x : N} (hx : x ∈ (chartAt H' x0).source) :
    (chartAt H' x0).symm ((chartAt H' x0) x) ∈ (chartAt H' x0).source := by
  rw [(chartAt H' x0).left_inv hx]
  exact hx

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Problem 8-14: the pair-base map `p ↦ (f p.1, p.2)` is smooth at every point. -/
lemma graphTransportPairBase_contMDiffAt
    (f : SmoothMap) (p0 : M × N) :
    ContMDiffAt (I.prod J) (J.prod J) ∞ (graphTransportPairBase f) p0 := by
  -- The pair base is the product of the smooth graph base `f ∘ Prod.fst` and the smooth second
  -- projection.
  have hfst :
      ContMDiffAt (I.prod J) J ∞ (fun p : M × N ↦ f p.1) p0 := by
    simpa [Function.comp] using
      ((f.contMDiff.comp
        (contMDiff_fst : ContMDiff (I.prod J) I ∞ (Prod.fst : M × N → M))) p0)
  simpa [graphTransportPairBase] using hfst.prodMk (contMDiffAt_snd :
    ContMDiffAt (I.prod J) J ∞ (Prod.snd : M × N → N) p0)

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the fixed source pullback trivialization has the same forward linear
map as the original tangent-bundle trivialization after evaluating on `Prod.fst`. -/
lemma graphTransportSourcePullbackContinuousLinearMapAt_eq
    (q0 q : N × N) :
    (trivializationAt E' (graphTransportSourceBundle (J := J)) q0).continuousLinearMapAt 𝕜 q =
      (trivializationAt E' (fun x : N ↦ TangentSpace J x) q0.1).continuousLinearMapAt 𝕜 q.1 := by
  -- Unfolding the pullback trivialization shows that the forward map only sees `Prod.fst`.
  ext v
  rfl

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the fixed target pullback trivialization has the same forward linear
map as the original tangent-bundle trivialization after evaluating on `Prod.snd`. -/
lemma graphTransportTargetPullbackContinuousLinearMapAt_eq
    (q0 q : N × N) :
    (trivializationAt E' (graphTransportTargetBundle (J := J)) q0).continuousLinearMapAt 𝕜 q =
      (trivializationAt E' (fun x : N ↦ TangentSpace J x) q0.2).continuousLinearMapAt 𝕜 q.2 := by
  -- Unfolding the pullback trivialization shows that the forward map only sees `Prod.snd`.
  ext v
  rfl

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: on the source base set, the inverse linear map of the source pullback
trivialization agrees with the original tangent-bundle inverse trivialization. -/
lemma graphTransportSourcePullbackSymmL_eq
    (q0 q : N × N)
    (hq : q ∈ (trivializationAt E' (graphTransportSourceBundle (J := J)) q0).baseSet) :
    (trivializationAt E' (graphTransportSourceBundle (J := J)) q0).symmL 𝕜 q =
      (trivializationAt E' (fun x : N ↦ TangentSpace J x) q0.1).symmL 𝕜 q.1 := by
  -- Compare both inverse maps through the common forward trivialization map.
  ext v
  have hMap :
      (trivializationAt E' (graphTransportSourceBundle (J := J)) q0).continuousLinearMapAt 𝕜 q =
        (trivializationAt E' (fun x : N ↦ TangentSpace J x) q0.1).continuousLinearMapAt 𝕜 q.1 :=
    graphTransportSourcePullbackContinuousLinearMapAt_eq (J := J) q0 q
  have hq' : q.1 ∈ (trivializationAt E' (fun x : N ↦ TangentSpace J x) q0.1).baseSet := by
    simpa [graphTransportSourceBundle, graphTransportPairBaseFstSmoothMap] using hq
  have hleft :
      (trivializationAt E' (graphTransportSourceBundle (J := J)) q0).continuousLinearMapAt 𝕜 q
        ((trivializationAt E' (fun x : N ↦ TangentSpace J x) q0.1).symmL 𝕜 q.1 v) = v := by
    rw [hMap]
    simpa using
      Bundle.Trivialization.continuousLinearMapAt_symmL
        (R := 𝕜) (e := trivializationAt (F := E') (E := fun x : N ↦ TangentSpace J x) q0.1)
        hq' v
  have hinj :
      Function.Injective
        ((trivializationAt E' (graphTransportSourceBundle (J := J)) q0).continuousLinearMapAt 𝕜 q) := by
    intro v w h
    rw [← Bundle.Trivialization.symmL_continuousLinearMapAt
        (R := 𝕜) (e := trivializationAt (F := E') (E := graphTransportSourceBundle (J := J)) q0)
        hq v,
      ← Bundle.Trivialization.symmL_continuousLinearMapAt
        (R := 𝕜) (e := trivializationAt (F := E') (E := graphTransportSourceBundle (J := J)) q0)
        hq w, h]
  apply hinj
  exact
    (Bundle.Trivialization.continuousLinearMapAt_symmL
      (R := 𝕜) (e := trivializationAt (F := E') (E := graphTransportSourceBundle (J := J)) q0)
      hq v).trans hleft.symm

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: on the common chart neighborhood, the explicit fixed-trivialization
transport family is exactly the pair-base `inCoordinates` family with constant model map `1`. -/
lemma graphTransportTrivializationSandwich_eq_pairBaseInCoordinates
    (f : SmoothMap) {p0 p : M × N}
    (hp1 : f p.1 ∈ (chartAt H' (f p0.1)).source) :
    ContinuousLinearMap.inCoordinates E' (graphTransportSourceBundle (J := J))
        E' (graphTransportTargetBundle (J := J))
        (graphTransportPairBase f p0) (graphTransportPairBase f p)
        (graphTransportPairBase f p0) (graphTransportPairBase f p)
        (1 : E' →L[𝕜] E') =
      ((trivializationAt E' (TangentSpace J) p0.2).continuousLinearMapAt 𝕜 p.2).comp
        ((trivializationAt E' (TangentSpace J) (f p0.1)).symmL 𝕜 (f p.1)) := by
  -- Rewrite the pair-base pullback trivializations back to the original tangent-bundle
  -- trivializations on the source and target factors.
  rw [ContinuousLinearMap.inCoordinates]
  rw [graphTransportTargetPullbackContinuousLinearMapAt_eq (J := J)
    (graphTransportPairBase f p0) (graphTransportPairBase f p)]
  have hq :
      graphTransportPairBase f p ∈
        (trivializationAt E' (graphTransportSourceBundle (J := J))
          (graphTransportPairBase f p0)).baseSet := by
    simpa [graphTransportPairBase, graphTransportSourceBundle,
      graphTransportPairBaseFstSmoothMap] using hp1
  rw [graphTransportSourcePullbackSymmL_eq (J := J)
    (graphTransportPairBase f p0) (graphTransportPairBase f p) hq]
  -- The remaining `1` composes away in model space.
  ext v
  change
    (Bundle.Trivialization.continuousLinearMapAt 𝕜
      (trivializationAt E' (fun x : N ↦ TangentSpace J x) p0.2) p.2)
      ((1 : E' →L[𝕜] E') ((Bundle.Trivialization.symmL 𝕜
        (trivializationAt E' (fun x : N ↦ TangentSpace J x) (f p0.1)) (f p.1)) v)) =
      (Bundle.Trivialization.linearMapAt 𝕜
        (trivializationAt E' (fun x : N ↦ TangentSpace J x) p0.2) p.2)
        ((Bundle.Trivialization.symmL 𝕜
          (trivializationAt E' (fun x : N ↦ TangentSpace J x) (f p0.1)) (f p.1)) v)
  simp

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: near `p₀`, the explicit fixed-trivialization transport family agrees
with the pair-base `inCoordinates` family for the constant model map `1`. -/
lemma graphTransportTrivializationSandwich_eventuallyEq_pairBaseInCoordinates
    (f : SmoothMap) (p0 : M × N) :
    (fun p : M × N ↦
      ((trivializationAt E' (TangentSpace J) p0.2).continuousLinearMapAt 𝕜 p.2).comp
        ((trivializationAt E' (TangentSpace J) (f p0.1)).symmL 𝕜 (f p.1))) =ᶠ[nhds p0]
      (fun p : M × N ↦
        ContinuousLinearMap.inCoordinates E' (graphTransportSourceBundle (J := J))
          E' (graphTransportTargetBundle (J := J))
          (graphTransportPairBase f p0) (graphTransportPairBase f p)
          (graphTransportPairBase f p0) (graphTransportPairBase f p)
          (1 : E' →L[𝕜] E')) := by
  -- The pair-base coordinates match the explicit formula as soon as the fixed source and target
  -- charts remain valid.
  have hfst := graphTransportSourceChart_mem_nhds f p0
  have hsnd :
      {p : M × N | p.2 ∈ (chartAt H' p0.2).source} ∈ nhds p0 := by
    have hcont : ContinuousAt (Prod.snd : M × N → N) p0 :=
      (contMDiffAt_snd : ContMDiffAt (I.prod J) J ∞ (Prod.snd : M × N → N) p0).continuousAt
    simpa [extChartAt_source] using hcont.preimage_mem_nhds
      (extChartAt_source_mem_nhds p0.2 : (extChartAt J p0.2).source ∈ nhds p0.2)
  filter_upwards [hfst, hsnd] with p hp1 hp2
  -- On this neighborhood, the pair-base coordinate family is exactly the desired explicit family.
  symm
  exact graphTransportTrivializationSandwich_eq_pairBaseInCoordinates (J := J) f hp1

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: specializing the raw derivative-to-trivialization comparison to
`id : N → N` rewrites the pair-base explicit transport family to the pair-base raw derivative
sandwich. -/
lemma graphTransportPairBaseTrivializationSandwich_eventuallyEq_rawDerivativeSandwich
    (q0 : N × N) :
    (fun q : N × N ↦
      ((trivializationAt E' (TangentSpace J) q0.2).continuousLinearMapAt 𝕜 q.2).comp
        ((trivializationAt E' (TangentSpace J) q0.1).symmL 𝕜 q.1)) =ᶠ[nhds q0]
      (fun q : N × N ↦
        (mfderiv% (extChartAt J q0.2) q.2).comp
          (mfderiv[Set.range J] (extChartAt J q0.1).symm
            (extChartAt J q0.1 q.1))) := by
  let fId : C^∞⟮J, N; J, N⟯ := ⟨id, contMDiff_id⟩
  -- The pair-base statement is the identity-graph raw-derivative bridge after simplifying `id`.
  simpa [fId] using
    (graphTransportRawDerivativeSandwich_eventuallyEq_trivialization
      (I := J) (M := N) (J := J) fId q0).symm

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: composing the fixed inverse chart derivative-in-coordinates family
with `Prod.fst` on the pair base `N × N` is smooth at `q₀`. -/
lemma graphTransportSourceInverseDerivativeInCoordinatesAlongFst_contMDiffAt
    (q0 : N × N) :
    ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun q : N × N ↦
        inTangentCoordinates 𝓘(𝕜, E') J id (extChartAt J q0.1).symm
          (fun z : E' ↦ mfderiv[Set.range J] (extChartAt J q0.1).symm z)
          (extChartAt J q0.1 q0.1)
          (extChartAt J q0.1 q.1)) q0 := by
  -- First prove smoothness of the fixed inverse chart derivative-in-coordinates on the model
  -- chart range, exactly as in the graph-based source factor.
  have hmodel :
      ContMDiffWithinAt 𝓘(𝕜, E') 𝓘(𝕜, E' →L[𝕜] E') ∞
        (inTangentCoordinates 𝓘(𝕜, E') J id (extChartAt J q0.1).symm
          (fun z : E' ↦ mfderiv[Set.range J] (extChartAt J q0.1).symm z)
          (extChartAt J q0.1 q0.1))
        (Set.range J) (extChartAt J q0.1 q0.1) := by
    have hsymm :
        ContMDiffWithinAt 𝓘(𝕜, E') J ∞
          (extChartAt J q0.1).symm (Set.range J)
          (extChartAt J q0.1 q0.1) :=
      contMDiffWithinAt_extChartAt_symm_range_self q0.1
    exact hsymm.mfderivWithin_const (by simp)
      (by simp) J.uniqueMDiffOn
  -- Next pull that model-space family back along the smooth first projection.
  have hsourceWithin :
      ContMDiffWithinAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun q : N × N ↦
          inTangentCoordinates 𝓘(𝕜, E') J id (extChartAt J q0.1).symm
            (fun z : E' ↦ mfderiv[Set.range J] (extChartAt J q0.1).symm z)
            (extChartAt J q0.1 q0.1)
            (extChartAt J q0.1 q.1))
        {q : N × N | q.1 ∈ (chartAt H' q0.1).source} q0 := by
    have hfstMapsTo :
        Set.MapsTo
          (fun q : N × N ↦ extChartAt J q0.1 q.1)
          {q : N × N | q.1 ∈ (chartAt H' q0.1).source}
          (Set.range J) := by
      intro q hq
      have hq' : q.1 ∈ (extChartAt J q0.1).source := by
        simpa [extChartAt_source] using hq
      exact extChartAt_target_subset_range q0.1
        ((extChartAt J q0.1).map_source hq')
    exact
      hmodel.comp q0
        (by
          -- The first projection followed by the fixed source chart is smooth at `q₀`.
          have hfst :
              ContMDiffAt (J.prod J) J ∞ (Prod.fst : N × N → N) q0 :=
            contMDiffAt_fst
          have hchart :
              ContMDiffAt J 𝓘(𝕜, E') ∞ (extChartAt J q0.1) q0.1 := by
            simpa using
              (contMDiffAt_extChartAt :
                ContMDiffAt J 𝓘(𝕜, E') ∞ (extChartAt J q0.1) q0.1)
          exact (show
              ContMDiffAt (J.prod J) 𝓘(𝕜, E') ∞
                (fun q : N × N ↦ extChartAt J q0.1 q.1) q0 from
              by
                simpa [Function.comp] using hchart.comp q0 hfst).contMDiffWithinAt)
        hfstMapsTo
  -- Finally upgrade the within-smooth statement to a pointwise one using the chart neighborhood.
  exact hsourceWithin.contMDiffAt
    (by
      -- Staying in the fixed source chart is a neighborhood condition at `q₀`.
      have hcont : ContinuousAt (Prod.fst : N × N → N) q0 :=
        (contMDiffAt_fst : ContMDiffAt (J.prod J) J ∞ (Prod.fst : N × N → N) q0).continuousAt
      simpa [extChartAt_source] using hcont.preimage_mem_nhds
        (extChartAt_source_mem_nhds q0.1 : (extChartAt J q0.1).source ∈ nhds q0.1))

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: on the pair base `N × N`, the fixed source and target
chart-derivative sandwich is smooth at `q₀`. -/
lemma graphTransportPairBaseDerivativeSandwichInCoordinates_contMDiffAt
    (q0 : N × N) :
    ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun q : N × N ↦
        (inTangentCoordinates J 𝓘(𝕜, E') id (extChartAt J q0.2)
          (fun y : N ↦ mfderiv% (extChartAt J q0.2) y) q0.2 q.2).comp
        (inTangentCoordinates 𝓘(𝕜, E') J id (extChartAt J q0.1).symm
          (fun z : E' ↦ mfderiv[Set.range J] (extChartAt J q0.1).symm z)
          (extChartAt J q0.1 q0.1)
          (extChartAt J q0.1 q.1))) q0 := by
  -- Smoothness on the pair base splits into the already-proved target `Prod.snd` factor and the
  -- new source `Prod.fst` factor.
  have htarget :
      ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun q : N × N ↦
          inTangentCoordinates J 𝓘(𝕜, E') id (extChartAt J q0.2)
            (fun y : N ↦ mfderiv% (extChartAt J q0.2) y) q0.2 q.2) q0 :=
    graphTransportTargetDerivativeInCoordinatesAlongSnd_contMDiffAt
      (I := J) (M := N) (p0 := q0)
  have hsource :
      ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun q : N × N ↦
          inTangentCoordinates 𝓘(𝕜, E') J id (extChartAt J q0.1).symm
            (fun z : E' ↦ mfderiv[Set.range J] (extChartAt J q0.1).symm z)
            (extChartAt J q0.1 q0.1)
            (extChartAt J q0.1 q.1)) q0 :=
    graphTransportSourceInverseDerivativeInCoordinatesAlongFst_contMDiffAt (J := J) q0
  -- Compose the two smooth continuous-linear-map families pointwise.
  exact htarget.clm_comp hsource

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: specializing the graph-transport trivialization comparison to
`id : N → N` rewrites the pair-base explicit transport family to the pair-base hom-bundle
coordinate family. -/
lemma graphTransportPairBaseTrivializationSandwich_eventuallyEq_pairBaseInCoordinates
    (q0 : N × N) :
    (fun q : N × N ↦
      ((trivializationAt E' (TangentSpace J) q0.2).continuousLinearMapAt 𝕜 q.2).comp
        ((trivializationAt E' (TangentSpace J) q0.1).symmL 𝕜 q.1)) =ᶠ[nhds q0]
      (fun q : N × N ↦
        ContinuousLinearMap.inCoordinates E' (graphTransportSourceBundle (J := J))
          E' (graphTransportTargetBundle (J := J))
          q0 q q0 q
          (1 : E' →L[𝕜] E')) := by
  -- Package the identity map on `N` as a bundled smooth map so the existing bridge applies.
  let fId : C^∞⟮J, N; J, N⟯ := ⟨id, contMDiff_id⟩
  -- The pair-base statement is exactly the identity-graph statement after simplifying `id`.
  simpa [fId] using
    (graphTransportTrivializationSandwich_eventuallyEq_pairBaseInCoordinates
      (I := J) (M := N) (J := J) fId q0)

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: specializing the graph-transport trivialization comparison to
`id : N → N` identifies the theorem-facing pair-base transport family with the corresponding
pair-base `inTangentCoordinates` family. -/
lemma graphTransportPairBaseIdentityInTangentCoordinates_eventuallyEq_trivialization
    (q0 : N × N) :
    (fun q : N × N ↦
      inTangentCoordinates J J Prod.fst Prod.snd
        (fun _ ↦ (1 : E' →L[𝕜] E')) q0 q) =ᶠ[nhds q0]
      (fun q : N × N ↦
        ((trivializationAt E' (TangentSpace J) q0.2).continuousLinearMapAt 𝕜 q.2).comp
          ((trivializationAt E' (TangentSpace J) q0.1).symmL 𝕜 q.1)) := by
  let fId : C^∞⟮J, N; J, N⟯ := ⟨id, contMDiff_id⟩
  -- The pair-base statement is the identity-graph statement after simplifying `id`.
  simpa [fId] using
    (graphTransportIdentityInCoordinates_eventuallyEq_trivialization
      (I := J) (M := N) (J := J) fId q0)

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the fixed source pullback trivialization base set is a neighborhood
of `q₀` on the pair base. -/
lemma graphTransportPairBaseSourceBaseSet_mem_nhds
    (q0 : N × N) :
    (trivializationAt E' (graphTransportSourceBundle (J := J)) q0).baseSet ∈ nhds q0 := by
  -- The fixed source pullback chart is valid at `q₀`, hence on a neighborhood of `q₀`.
  exact
    (trivializationAt E' (graphTransportSourceBundle (J := J)) q0).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' q0)

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the fixed target pullback trivialization base set is a neighborhood
of `q₀` on the pair base. -/
lemma graphTransportPairBaseTargetBaseSet_mem_nhds
    (q0 : N × N) :
    (trivializationAt E' (graphTransportTargetBundle (J := J)) q0).baseSet ∈ nhds q0 := by
  -- The fixed target pullback chart is valid at `q₀`, hence on a neighborhood of `q₀`.
  exact
    (trivializationAt E' (graphTransportTargetBundle (J := J)) q0).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' q0)

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the explicit fixed-trivialization transport family is smooth on the
pair base `N × N`. -/
lemma graphTransportPairBaseFixedTrivialization_contMDiffAt
    (q0 : N × N) :
    ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun q : N × N ↦
        ((trivializationAt E' (TangentSpace J) q0.2).continuousLinearMapAt 𝕜 q.2).comp
          ((trivializationAt E' (TangentSpace J) q0.1).symmL 𝕜 q.1)) q0 := by
  -- Route correction: the clean hom-bundle section route reduces the theorem to smoothness of the
  -- pair-base `inCoordinates` family, but the required total-space/charted-space instance bridge
  -- for `graphTransportPairBaseHomBundle` is not inferable in this file.
  -- TODO: either expose that canonical hom-bundle instance bridge for the pullback bundles, or
  -- prove the pair-base `inCoordinates` family directly without the total-space section API.
  sorry

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the pair-base hom-bundle coordinates of the constant model map `1`
are smooth at `q₀`. -/
lemma graphTransportPairBaseInCoordinates_contMDiffAt
    (q0 : N × N) :
    ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun q : N × N ↦
        ContinuousLinearMap.inCoordinates E' (graphTransportSourceBundle (J := J))
          E' (graphTransportTargetBundle (J := J))
          q0 q q0 q
          (1 : E' →L[𝕜] E')) q0 := by
  have htriv :
      ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun q : N × N ↦
          ((trivializationAt E' (TangentSpace J) q0.2).continuousLinearMapAt 𝕜 q.2).comp
            ((trivializationAt E' (TangentSpace J) q0.1).symmL 𝕜 q.1)) q0 :=
    graphTransportPairBaseFixedTrivialization_contMDiffAt (J := J) q0
  -- Transfer smoothness from the explicit trivialization family to the theorem-facing
  -- `inCoordinates` family.
  exact htriv.congr_of_eventuallyEq
    (graphTransportPairBaseTrivializationSandwich_eventuallyEq_pairBaseInCoordinates
      (J := J) q0).symm

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the pair-base `inTangentCoordinates` family with constant model map
`1` is smooth at `q₀`. -/
lemma graphTransportPairBaseIdentityInTangentCoordinates_contMDiffAt
    (q0 : N × N) :
    ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun q : N × N ↦
        inTangentCoordinates J J Prod.fst Prod.snd
          (fun _ ↦ (1 : E' →L[𝕜] E')) q0 q) q0 := by
  have htriv :
      ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun q : N × N ↦
          ((trivializationAt E' (TangentSpace J) q0.2).continuousLinearMapAt 𝕜 q.2).comp
            ((trivializationAt E' (TangentSpace J) q0.1).symmL 𝕜 q.1)) q0 :=
    graphTransportPairBaseFixedTrivialization_contMDiffAt (J := J) q0
  -- Transfer smoothness from the explicit trivialization family to the theorem-facing pair-base
  -- `inTangentCoordinates` expression.
  exact htriv.congr_of_eventuallyEq
    (graphTransportPairBaseIdentityInTangentCoordinates_eventuallyEq_trivialization
      (J := J) q0).symm

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the explicit fixed-trivialization transport family is smooth on the
pair base `N × N`. -/
lemma graphTransportPairBaseTrivializationSandwich_contMDiffAt
    (q0 : N × N) :
    ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun q : N × N ↦
        ((trivializationAt E' (TangentSpace J) q0.2).continuousLinearMapAt 𝕜 q.2).comp
          ((trivializationAt E' (TangentSpace J) q0.1).symmL 𝕜 q.1)) q0 := by
  -- Route correction: the naive section-first rewrite is circular here, because it rewrites the
  -- total-space smoothness question back to the same pair-base transport coordinates. Work instead
  -- with the pair-base `inTangentCoordinates` family and transfer smoothness through the existing
  -- chart comparison.
  have hcoords :
      ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun q : N × N ↦
          inTangentCoordinates J J Prod.fst Prod.snd
            (fun _ ↦ (1 : E' →L[𝕜] E')) q0 q) q0 :=
    graphTransportPairBaseIdentityInTangentCoordinates_contMDiffAt (J := J) q0
  have hEq :
      (fun q : N × N ↦
        inTangentCoordinates J J Prod.fst Prod.snd
          (fun _ ↦ (1 : E' →L[𝕜] E')) q0 q) =ᶠ[nhds q0]
        (fun q : N × N ↦
          ((trivializationAt E' (TangentSpace J) q0.2).continuousLinearMapAt 𝕜 q.2).comp
            ((trivializationAt E' (TangentSpace J) q0.1).symmL 𝕜 q.1)) := by
    -- Specializing the general graph-transport bridge to `id : N → N` gives the pair-base
    -- trivialization comparison.
    exact graphTransportPairBaseIdentityInTangentCoordinates_eventuallyEq_trivialization
      (J := J) q0
  -- Transfer smoothness from the pair-base coordinate family to the theorem-facing explicit
  -- trivialization sandwich.
  exact hcoords.congr_of_eventuallyEq hEq

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: once the explicit fixed-trivialization family is known to be smooth on
the pair base `N × N`, pulling it back along `graphTransportPairBase f` gives the theorem-facing
`M × N` family. -/
lemma graphTransportFixedTrivializationFamily_contMDiffAt_of_pairBase
    (f : SmoothMap) (p0 : M × N)
    (hpair :
      ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun q : N × N ↦
          (Bundle.Trivialization.continuousLinearMapAt 𝕜
              (trivializationAt E' (TangentSpace J) (graphTransportPairBase f p0).2) q.2).comp
            (Bundle.Trivialization.symmL 𝕜
              (trivializationAt E' (TangentSpace J) (graphTransportPairBase f p0).1) q.1))
        (graphTransportPairBase f p0)) :
    ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun p : M × N ↦
        ((trivializationAt E' (TangentSpace J) p0.2).continuousLinearMapAt 𝕜 p.2).comp
          ((trivializationAt E' (TangentSpace J) (f p0.1)).symmL 𝕜 (f p.1))) p0 := by
  -- Pull the pair-base smooth family back along the smooth graph base map `p ↦ (f p.1, p.2)`.
  simpa [graphTransportPairBase] using
    hpair.comp p0 (graphTransportPairBase_contMDiffAt (I := I) (J := J) f p0)

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the explicit fixed-trivialization graph-transport family is smooth
at `p₀`. -/
lemma graphTransportFixedTrivializationFamily_contMDiffAt
    (f : SmoothMap) (p0 : M × N) :
    ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun p : M × N ↦
        ((trivializationAt E' (TangentSpace J) p0.2).continuousLinearMapAt 𝕜 p.2).comp
          ((trivializationAt E' (TangentSpace J) (f p0.1)).symmL 𝕜 (f p.1))) p0 := by
  -- Route correction: first solve the theorem-facing transport family on the pair base `N × N`.
  have hpair :
      ContMDiffAt (J.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun q : N × N ↦
          (Bundle.Trivialization.continuousLinearMapAt 𝕜
              (trivializationAt E' (TangentSpace J) (graphTransportPairBase f p0).2) q.2).comp
            (Bundle.Trivialization.symmL 𝕜
              (trivializationAt E' (TangentSpace J) (graphTransportPairBase f p0).1) q.1))
        (graphTransportPairBase f p0) :=
    graphTransportPairBaseTrivializationSandwich_contMDiffAt
      (J := J) (graphTransportPairBase f p0)
  -- Pull that pair-base smoothness back along `p ↦ (f p.1, p.2)`.
  exact graphTransportFixedTrivializationFamily_contMDiffAt_of_pairBase (I := I) (J := J) f p0 hpair

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the pair-base `inCoordinates` family for the constant identity map
is smooth at `p₀`. -/
lemma graphTransportPairBaseIdentityInCoordinates_contMDiffAt
    (f : SmoothMap) (p0 : M × N) :
    ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun p : M × N ↦
        ContinuousLinearMap.inCoordinates E' (graphTransportSourceBundle (J := J))
          E' (graphTransportTargetBundle (J := J))
          (graphTransportPairBase f p0) (graphTransportPairBase f p)
          (graphTransportPairBase f p0) (graphTransportPairBase f p)
          (1 : E' →L[𝕜] E')) p0 := by
  -- Route correction: prove smoothness first for the explicit fixed-trivialization family, then
  -- transport it back to the pair-base `inCoordinates` expression by eventual equality.
  exact
    (graphTransportFixedTrivializationFamily_contMDiffAt f p0).congr_of_eventuallyEq
      (graphTransportTrivializationSandwich_eventuallyEq_pairBaseInCoordinates f p0).symm

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: the fixed-trivialization graph-transport family is the remaining
smoothness blocker for the coordinate transport proof. -/
lemma graphTransportTrivializationSandwich_contMDiffAt
    (f : SmoothMap) (p0 : M × N) :
    ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun p : M × N ↦
        ((trivializationAt E' (TangentSpace J) p0.2).continuousLinearMapAt 𝕜 p.2).comp
          ((trivializationAt E' (TangentSpace J) (f p0.1)).symmL 𝕜 (f p.1))) p0 := by
  -- This theorem is now just the public alias for the explicit fixed-trivialization family.
  simpa using graphTransportFixedTrivializationFamily_contMDiffAt f p0

omit [IsManifold I ∞ M] in
/-- Helper for Problem 8-14: in tangent coordinates around `(f p₀.1, p₀.2)`, the identity map
between the source and target tangent fibers varies smoothly along the graph base map. -/
lemma graphTransportIdentityInCoordinates_contMDiffAt
    (f : SmoothMap) (p0 : M × N) :
    ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun p : M × N ↦
        inTangentCoordinates J J (fun q : M × N ↦ f q.1) Prod.snd
          (fun _ ↦ (1 : E' →L[𝕜] E')) p0 p) p0 := by
  -- Route correction: the raw-derivative normalization route leaves an extra middle coordinate
  -- change, so the smallest stable bridge is the fixed-trivialization sandwich.
  exact
    (graphTransportTrivializationSandwich_contMDiffAt f p0).congr_of_eventuallyEq
      (graphTransportIdentityInCoordinates_eventuallyEq_trivialization f p0)

/-- Helper for Problem 8-14: the derivative section over `f ∘ Prod.fst` can be reused pointwise
at a fixed base point when applying the transport operator. -/
lemma graphDerivativeSectionAlongPairBase_contMDiffAt
    (f : SmoothMap) {X : ∀ x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X)) (p0 : M × N) :
    ContMDiffAt (I.prod J) J.tangent ∞
      (fun p : M × N ↦
        (⟨f p.1, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N)) p0 := by
  -- The already-smooth tangent map section can be reused unchanged at the chosen base point.
  simpa [tangentMap, Function.comp] using
    (graphDerivativeSectionAlongFst_contMDiff f hX).contMDiffAt

/-- Helper for Problem 8-14: the `N`-component of `graphRelated f X` is the derivative section
based at `Prod.snd`. -/
lemma graphRelatedSecondComponent_contMDiff
    (f : SmoothMap) {X : ∀ x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X)) :
    ContMDiff (I.prod J) J.tangent ∞
      (fun p : M × N ↦
        (⟨p.2, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N)) := by
  intro p0
  let b₁ : M × N → N := fun p ↦ f p.1
  let b₂ : M × N → N := Prod.snd
  let ϕ : ∀ p : M × N, TangentSpace J (b₁ p) →L[𝕜] TangentSpace J (b₂ p) :=
    fun _ ↦ (ContinuousLinearMap.id 𝕜 E' : E' →L[𝕜] E')
  let v : ∀ p : M × N, TangentSpace J (b₁ p) := fun p ↦ mfderiv I J f p.1 (X p.1)
  have hϕ :
      ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun p : M × N ↦ inTangentCoordinates J J b₁ b₂ ϕ p0 p) p0 := by
    -- This is the only genuine transport step: the coordinate form of the identity map between
    -- tangent fibers must vary smoothly with both base points.
    simpa [b₁, b₂, ϕ] using graphTransportIdentityInCoordinates_contMDiffAt f p0
  have hv :
      ContMDiffAt (I.prod J) J.tangent ∞ (fun p : M × N ↦ (v p : TangentBundle J N)) p0 := by
    -- Reuse the previously proved smooth derivative section without reopening the tangent-map
    -- regularity argument.
    simpa [b₁, v] using graphDerivativeSectionAlongPairBase_contMDiffAt f hX p0
  have hb₂ : ContMDiffAt (I.prod J) J ∞ b₂ p0 := by
    -- The target base map is just the second projection.
    simpa [b₂] using (contMDiffAt_snd : ContMDiffAt (I.prod J) J ∞ (Prod.snd : M × N → N) p0)
  -- Apply the smooth transport family to the smooth derivative section.
  simpa [b₁, b₂, ϕ, v] using (ContMDiffAt.clm_apply_of_inCoordinates hϕ hv hb₂)

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Problem 8-14: under the product tangent-bundle equivalence, `graphRelated f X`
splits into the original section `X` and the derivative section over `N`. -/
lemma equivTangentBundleProd_graphRelated_apply
    (f : SmoothMap) (X : ∀ x : M, TangentSpace I x) (p : M × N) :
    equivTangentBundleProd I M J N (T% (graphRelated f X) p) =
      (T% X p.1, (⟨p.2, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N)) := by
  -- Expanding `graphRelated` shows that the product tangent-bundle equivalence just separates the
  -- two components.
  rcases p with ⟨x, y⟩
  rfl

/-- The explicit vector field on `M × N` attached to `f` and `X` is smooth when `f` and `X`
are smooth. -/
theorem contMDiff_graphRelated
    (f : SmoothMap) {X : ∀ x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X)) :
    ContMDiff (I.prod J) (I.prod J).tangent ∞
      (T% ((graphRelated f X : ∀ p : M × N, TangentSpace (I.prod J) p))) :=
  by
    -- Route correction: separate the product tangent-bundle components first, so the remaining
    -- work is only the transport from base `f ∘ Prod.fst` to base `Prod.snd` in the `N`-part.
    let F : M × N → TangentBundle I M × TangentBundle J N := fun p ↦
      (T% X p.1, (⟨p.2, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N))
    have hF : ContMDiff (I.prod J) (I.tangent.prod J.tangent) ∞ F := by
      -- Each component is smooth after pulling back along the corresponding projection.
      have hfirst : ContMDiff (I.prod J) I.tangent ∞ (fun p : M × N ↦ T% X p.1) := by
        simpa using hX.comp contMDiff_fst
      have hsecond :
          ContMDiff (I.prod J) J.tangent ∞
            (fun p : M × N ↦
              (⟨p.2, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N)) :=
        graphRelatedSecondComponent_contMDiff f hX
      simpa [F, Function.comp] using hfirst.prodMk hsecond
    have htransport :
        ContMDiff (I.prod J) (I.prod J).tangent ∞
          ((equivTangentBundleProd I M J N).symm ∘ F) := by
      -- Transport the smooth pair of tangent-bundle sections back to the tangent bundle of
      -- the product manifold.
      exact
        contMDiff_equivTangentBundleProd_symm.comp hF
    have hEq : ((equivTangentBundleProd I M J N).symm ∘ F) =
        T% ((graphRelated f X : ∀ p : M × N, TangentSpace (I.prod J) p)) := by
      -- The forward bundle equivalence identifies the transported pair with `graphRelated f X`.
      funext p
      apply (equivTangentBundleProd I M J N).injective
      rw [Function.comp_apply, Equiv.apply_symm_apply]
      change
        (T% X p.1, (⟨p.2, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N)) =
          equivTangentBundleProd I M J N (T% (graphRelated f X) p)
      exact (equivTangentBundleProd_graphRelated_apply f X p).symm
    simpa [hEq] using htransport

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Problem 8-14: differentiating the graph map `x ↦ (x, f x)` applies `X x` to the
product derivative componentwise. -/
lemma graphMapMfderiv_apply
    (f : SmoothMap) (X : ∀ x : M, TangentSpace I x) (x : M) :
    mfderiv I (I.prod J) (fun y : M ↦ (y, f y)) x (X x) =
      graphRelated f X (x, f x) := by
  -- Differentiate the two graph-map coordinates separately and repackage the result.
  rw [mfderiv_prodMk]
  · rw [graphRelated]
    change
      ((((mfderiv I I (fun y : M ↦ y) x) (X x)), mfderiv I J f x (X x)) :
        TangentSpace (I.prod J) (x, f x)) =
        (X x, mfderiv I J f x (X x))
    change (((mfderiv I I (@id M) x) (X x)), mfderiv I J f x (X x)) =
        (X x, mfderiv I J f x (X x))
    rw [mfderiv_id]
    rfl
  · exact mdifferentiableAt_id
  · exact f.contMDiff.mdifferentiableAt (by simp)

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Along the graph map `x ↦ (x, f x)`, the explicit vector field on `M × N` is related to `X`. -/
theorem graphMap_f_related_graphRelated
    (f : SmoothMap) (X : ∀ x : M, TangentSpace I x) :
    f_related
      ((fun x : M ↦ (x, f x)) : M → M × N)
      X
      (graphRelated f X : ∀ p : M × N, TangentSpace (I.prod J) p) :=
  by
    constructor
    · -- The graph map is smooth because each coordinate is smooth.
      simpa using contMDiff_id.prodMk f.contMDiff
    · intro x
      -- The relatedness identity is exactly the graph-map derivative formula.
      simpa using graphMapMfderiv_apply f X x

/-- The canonical bundled smooth vector field on `M × N` attached to a smooth map `f` and a
smooth vector field `X` on `M`. -/
def graphRelatedSmooth
    (f : SmoothMap) (X : SmoothVectorField) :
    SmoothProductVectorField :=
  ⟨graphRelated f X, contMDiff_graphRelated f X.contMDiff⟩

/-- The bundled graph-related vector field is related to `X` along the graph map. -/
theorem graphMap_f_related_graphRelatedSmooth
    (f : SmoothMap) (X : SmoothVectorField) :
    f_related
      (fun x : M ↦ (x, f x))
      X
      (graphRelatedSmooth f X) :=
  graphMap_f_related_graphRelated f X

end VectorField

/-- Problem 8-14: if `f : M → N` is smooth and `X` is a smooth vector field on `M`, then there
exists a smooth vector field on `M × N` whose value along the graph map `F(x) = (x, f x)` is
`mfderiv I (I.prod J) F x (X x)`. -/
theorem exists_smooth_graph_related_vector_field
    (f : SmoothMap) (X : SmoothVectorField) :
    ∃ Y : SmoothProductVectorField,
      VectorField.f_related
        (fun x : M ↦ (x, f x))
        X
        Y :=
  ⟨VectorField.graphRelatedSmooth f X, VectorField.graphMap_f_related_graphRelatedSmooth f X⟩

end
