import DoCarmoLib.Riemannian.Manifold.PathLifting
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.CurveReadback

/-!
# From path lifting toward the covering-map conclusion (do Carmo Ch. 7, §3, Lemma 3.3)

`PathLifting.lean` established the **continuous path-lifting property** for a
metric-expanding local diffeomorphism `f : M → M'` out of a complete (hence
proper) Riemannian manifold: every `C¹` curve `c : [0,1] → M'` of finite length
lifts through any point of the fibre over `c(0)`.

This file records the next ingredient do Carmo's Lemma 3.3 proof uses on top of
existence of lifts: **uniqueness of continuous lifts**. Two continuous lifts of
the same base curve over a preconnected parameter set that agree at one parameter
agree everywhere. In do Carmo's proof this is the sentence *"by the uniqueness of
the lift"* that makes the sheet decomposition of `f⁻¹(V)` well defined.

The uniqueness is elementary once packaged through mathlib's covering-space
plumbing:

* a smooth local diffeomorphism is a **local homeomorphism**, hence
  **locally injective** (`IsLocalHomeomorph.isLocallyInjective`);
* the source `M` is a metric space, hence Hausdorff, so `f` is automatically a
  **separated map** (`T2Space.isSeparatedMap`);
* a separated, locally injective map has **unique lifts on preconnected sets**
  (`IsSeparatedMap.eqOn_of_comp_eqOn`).

Combined with `DCExpandsMetric.exists_pathLift` this upgrades path lifting to a
`∃!`-statement, which is what the covering-map argument consumes.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3, proof of Lemma 3.3.
-/

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** **Uniqueness of continuous lifts through a local homeomorphism.** If
`f : M → M'` is a local homeomorphism out of a Hausdorff space and `g₁, g₂` are two
continuous lifts of the same base curve `c` (`f ∘ gᵢ = c`) over a preconnected
parameter set `s`, then they agree on all of `s` as soon as they agree at one point
`t₀ ∈ s`. This is do Carmo's *"by the uniqueness of the lift"* step in Lemma 3.3.

Proof: `M` is a metric space, hence `T2`, so `f` is a separated map
(`T2Space.isSeparatedMap`); a local homeomorphism is locally injective
(`IsLocalHomeomorph.isLocallyInjective`); a separated locally injective map has
unique lifts on preconnected sets (`IsSeparatedMap.eqOn_of_comp_eqOn`). -/
theorem IsLocalHomeomorph.eqOn_lift {f : M → M'} (hf : IsLocalHomeomorph f)
    {c : ℝ → M'} {g₁ g₂ : ℝ → M} {s : Set ℝ} (hs : IsPreconnected s)
    (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (hlift₁ : ∀ t ∈ s, f (g₁ t) = c t) (hlift₂ : ∀ t ∈ s, f (g₂ t) = c t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (h0 : g₁ t₀ = g₂ t₀) :
    Set.EqOn g₁ g₂ s := by
  have sep : IsSeparatedMap f := T2Space.isSeparatedMap f
  have inj : IsLocallyInjective f := hf.isLocallyInjective
  have he : Set.EqOn (f ∘ g₁) (f ∘ g₂) s := fun t ht =>
    (hlift₁ t ht).trans (hlift₂ t ht).symm
  exact sep.eqOn_of_comp_eqOn inj hs h₁ h₂ he ht₀ h0

/-- **Math.** **Uniqueness of the continuous lift of a `C¹` curve** (do Carmo Ch. 7,
Lemma 3.3, specialised to the lift produced by `DCExpandsMetric.exists_pathLift`).
For a smooth local diffeomorphism `f`, any two continuous lifts of a curve
`c : [0,1] → M'` that start at the same point coincide on `[0,1]`. -/
theorem IsLocalDiffeomorph.eqOn_pathLift {f : M → M'}
    (hf : IsLocalDiffeomorph I I' ∞ f) {c : ℝ → M'} {g₁ g₂ : ℝ → M}
    (h₁ : ContinuousOn g₁ (Icc 0 1)) (h₂ : ContinuousOn g₂ (Icc 0 1))
    (hlift₁ : ∀ t ∈ Icc (0 : ℝ) 1, f (g₁ t) = c t)
    (hlift₂ : ∀ t ∈ Icc (0 : ℝ) 1, f (g₂ t) = c t)
    (h0 : g₁ 0 = g₂ 0) :
    Set.EqOn g₁ g₂ (Icc 0 1) :=
  IsLocalHomeomorph.eqOn_lift (IsLocalDiffeomorph.isLocalHomeomorph hf)
    isPreconnected_Icc h₁ h₂ hlift₁ hlift₂ ⟨le_rfl, by norm_num⟩ h0

/-- **Math.** **The continuous lift of a `C¹` curve is unique** (do Carmo Ch. 7,
Lemma 3.3). Packaged as a `∃!`: for a metric-expanding smooth local
diffeomorphism `f` out of a proper Riemannian manifold whose distance is the
Riemannian distance, every finite-length `C¹` curve `c : [0,1] → M'` has a *unique*
continuous lift through a chosen point `q` over `c(0)`.

Existence is `DCExpandsMetric.exists_pathLift`; uniqueness is
`IsLocalDiffeomorph.eqOn_pathLift`. The `∃!` is taken over the graph on `[0,1]`:
two lifts are identified when they agree on `Icc 0 1`. -/
theorem DCExpandsMetric.existsUnique_pathLift_eqOn [ProperSpace M] [T2Space M']
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : IsLocalDiffeomorph I I' ∞ f)
    {c : ℝ → M'} (hc : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 c (Icc 0 1))
    (hLc : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
             ⟨gN.toRiemannianMetric⟩
           Manifold.pathELength I' c 0 1 ≠ ⊤)
    {q : M} (hq : f q = c 0) :
    ∃ g : ℝ → M, (ContinuousOn g (Icc 0 1) ∧ g 0 = q ∧
        ∀ t ∈ Icc (0 : ℝ) 1, f (g t) = c t) ∧
      ∀ g' : ℝ → M, (ContinuousOn g' (Icc 0 1) ∧ g' 0 = q ∧
        ∀ t ∈ Icc (0 : ℝ) 1, f (g' t) = c t) → Set.EqOn g' g (Icc 0 1) := by
  obtain ⟨g, hgc, hg0, hgl⟩ := hexp.exists_pathLift hgM hf hc hLc hq
  refine ⟨g, ⟨hgc, hg0, hgl⟩, fun g' ⟨hg'c, hg'0, hg'l⟩ => ?_⟩
  exact IsLocalDiffeomorph.eqOn_pathLift hf hg'c hgc hg'l hgl (hg'0.trans hg0.symm)

/-! ### Finiteness of the length of a chart-contained `C¹` curve

The path-lifting property (`DCExpandsMetric.exists_pathLift`) has a finiteness
hypothesis on the base curve, `ℓ(c) ≠ ⊤`. For a `C¹` curve confined to a single
chart this is automatic: reading the length through the chart
(`Geodesic.pathELength_eq_ofReal_integral_chartMetricInner`) presents it as
`ENNReal.ofReal (∫ …)`, a real number, hence never `⊤`. This is precisely the
input needed to lift the straight chart-segments that build the evenly covered
neighbourhoods in do Carmo's covering-map argument. -/

/-- **Math.** **A `C¹` curve confined to one chart has finite length.** If
`γ : [a,b] → M'` is `C¹` and its image lies in the source of the chart at some
`α : M'`, then `ℓ(γ) ≠ ⊤`. Proof: the chart reading of the length is
`ENNReal.ofReal (∫ᵃᵇ √⟨γ',γ'⟩)`, which is finite. -/
theorem Geodesic.pathELength_ne_top_of_mapsTo_chartSource [I'.Boundaryless]
    {gN : RiemannianMetric I' M'}
    {γ : ℝ → M'} {a b : ℝ} {α : M'} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 γ (Icc a b))
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H' α).source) :
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    Manifold.pathELength I' γ a b ≠ ⊤ := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  rw [Riemannian.Geodesic.pathELength_eq_ofReal_integral_chartMetricInner gN hab hγ hsrc]
  exact ENNReal.ofReal_ne_top

/-! ### Closed image and surjectivity

For the empty fibres in do Carmo's covering-map conclusion (points of `N` not in
the image), an evenly covered neighbourhood is one with empty preimage — i.e. the
image must be closed. Here we prove the stronger, self-contained fact underlying
it: a metric-expanding local diffeomorphism out of a complete manifold has
**closed image**, and hence is **surjective** onto a connected target. The image is
open (local homeomorphism); it is closed because any limit point `y` of the image
is joined, inside a chart, to a nearby image point `f(x₁)` by a $C^1$ chart segment
of finite length (\ref no infinity: `Geodesic.pathELength_ne_top_of_mapsTo_chartSource`),
which lifts through `x₁` (`DCExpandsMetric.exists_pathLift`) to a point over `y`. -/

/-- **Math.** **The image of a metric-expanding local diffeomorphism out of a
complete manifold is closed** (do Carmo Ch. 7, Lemma 3.3, the empty-fibre case of
the covering-map conclusion). Let `f : M → M'` be a smooth local diffeomorphism out
of a proper Riemannian manifold `M` whose distance is the Riemannian distance, and
which expands the metric. Then `Set.range f` is closed. Proof: for `y` a cluster
point of the image, work in the chart at `y`; a neighbourhood of `y` meets the
image at some `f(x₁)`, and the straight chart-segment from `f(x₁)` to `y` is a `C¹`
curve of finite length inside one chart, so it lifts through `x₁`; the lift's
endpoint maps to `y`, hence `y ∈ range f`. -/
theorem DCExpandsMetric.isClosed_range [ProperSpace M] [T2Space M'] [I'.Boundaryless]
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : IsLocalDiffeomorph I I' ∞ f) :
    IsClosed (Set.range f) := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  rw [isClosed_iff_clusterPt]
  intro y hy
  set c₁ := extChartAt I' y with hc₁
  set b₀ := c₁ y with hb₀
  -- a ball around `b₀` inside the chart target
  obtain ⟨r, hr, hballsub⟩ := Metric.mem_nhds_iff.mp (extChartAt_target_mem_nhds (I := I') y)
  -- the open neighbourhood `W` of `y` whose points map into that ball
  set W : Set M' := c₁.source ∩ c₁ ⁻¹' (Metric.ball b₀ r) with hW
  have hWopen : IsOpen W :=
    (continuousOn_extChartAt (I := I') y).isOpen_inter_preimage
      (isOpen_extChartAt_source y) Metric.isOpen_ball
  have hyW : y ∈ W := by
    refine ⟨mem_extChartAt_source (I := I') y, ?_⟩
    rw [Set.mem_preimage, Metric.mem_ball, ← hb₀, dist_self]
    exact hr
  -- `W` meets the image
  obtain ⟨y₁, hy₁W, x₁, rfl⟩ := (clusterPt_principal_iff.mp hy) W (hWopen.mem_nhds hyW)
  set b₁ := c₁ (f x₁) with hb₁
  have hb₁ball : b₁ ∈ Metric.ball b₀ r := hy₁W.2
  have hfx₁src : f x₁ ∈ c₁.source := hy₁W.1
  -- the chart segment from `f x₁` (t=0) to `y` (t=1)
  set L : ℝ → E' := fun t => AffineMap.lineMap b₁ b₀ t with hL
  set σ : ℝ → M' := fun t => c₁.symm (L t) with hσ
  have hLball : ∀ t ∈ Icc (0 : ℝ) 1, L t ∈ Metric.ball b₀ r := fun t ht =>
    (convex_ball b₀ r).lineMap_mem hb₁ball (Metric.mem_ball_self hr) ht
  have hLtgt : ∀ t ∈ Icc (0 : ℝ) 1, L t ∈ c₁.target := fun t ht => hballsub (hLball t ht)
  -- `σ` stays in the chart source
  have hσsrc : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ (chartAt H' y).source := by
    intro t ht
    rw [← extChartAt_source (I := I') y]
    exact c₁.map_target (hLtgt t ht)
  -- `σ` is `C¹`
  have hLeq : L = fun t : ℝ => t • (b₀ - b₁) + b₁ := by
    funext t
    simp only [hL, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hLcmdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E') 1 L (Icc 0 1) := by
    rw [hLeq]
    exact ((contDiff_id.smul contDiff_const).add contDiff_const).contDiffOn.contMDiffOn
  have hσcmdiff : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 σ (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm (I := I') y).comp hLcmdiff hLtgt
  -- finite length
  have hσfin : Manifold.pathELength I' σ 0 1 ≠ ⊤ :=
    Geodesic.pathELength_ne_top_of_mapsTo_chartSource (α := y) zero_le_one hσcmdiff hσsrc
  -- endpoints
  have hσ0 : σ 0 = f x₁ := by
    simp only [hσ, hL, AffineMap.lineMap_apply_zero, hb₁]
    exact c₁.left_inv hfx₁src
  have hσ1 : σ 1 = y := by
    simp only [hσ, hL, AffineMap.lineMap_apply_one, hb₀]
    exact extChartAt_to_inv (I := I') y
  -- lift the segment through `x₁`
  obtain ⟨g, -, -, hgl⟩ := hexp.exists_pathLift hgM hf hσcmdiff hσfin hσ0.symm
  exact ⟨g 1, by rw [hgl 1 ⟨zero_le_one, le_rfl⟩, hσ1]⟩

/-- **Math.** **A metric-expanding local diffeomorphism out of a complete manifold
onto a connected manifold is surjective** (do Carmo Ch. 7, Lemma 3.3). The image is
open (local homeomorphism, `IsLocalHomeomorph.isOpenMap`) and closed
(`DCExpandsMetric.isClosed_range`), hence clopen; a nonempty clopen subset of a
connected space is everything. -/
theorem DCExpandsMetric.surjective [ProperSpace M] [T2Space M'] [I'.Boundaryless]
    [Nonempty M] [PreconnectedSpace M']
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : IsLocalDiffeomorph I I' ∞ f) :
    Function.Surjective f := by
  have hopen : IsOpen (Set.range f) :=
    (IsLocalDiffeomorph.isLocalHomeomorph hf).isOpenMap.isOpen_range
  have hclopen : IsClopen (Set.range f) := ⟨hexp.isClosed_range hgM hf, hopen⟩
  have hne : (Set.range f).Nonempty := Set.range_nonempty f
  rw [← Set.range_eq_univ]
  exact (isClopen_iff.mp hclopen).resolve_left (Set.nonempty_iff_ne_empty.mp hne)

end Riemannian
