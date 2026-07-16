import OpenGALib.Riemannian.Manifold.CoveringMapBridge
import Mathlib.Topology.Homotopy.Lifting

/-!
# The covering-map conclusion of do Carmo Ch. 7, §3, Lemma 3.3

`PathLifting.lean` and `CoveringMapBridge.lean` established, for a metric-expanding
smooth local diffeomorphism `f : M → M'` out of a complete (hence proper)
Riemannian manifold:

* the **continuous path-lifting property** (`DCExpandsMetric.exists_pathLift`),
* **uniqueness of continuous lifts** (`IsLocalHomeomorph.eqOn_lift`), and
* **closed image / surjectivity** (`DCExpandsMetric.isClosed_range`).

This file assembles them into do Carmo's conclusion: **`f` is a covering map**
(`lem:dc-ch7-3-3`). The construction realises do Carmo's evenly-covered
neighbourhoods concretely: over a chart ball `V` around a point `x₀ ∈ M'`, each
`y ∈ V` is joined to `x₀` by the straight `C¹` chart segment (of finite length),
so lifting this family of segments through each fibre point `e ∈ f⁻¹{x₀}` produces
a continuous section `φ_e : V → M`. Joint continuity of the family of lifts is
mathlib's `IsLocalHomeomorph.continuous_lift` for a **separated local
homeomorphism** (no covering-map circularity). Uniqueness of lifts makes the
sheets `φ_e(V)` pairwise disjoint; the reverse-segment lift shows they exhaust
`f⁻¹(V)`; and `IsOpen.trivializationDiscrete` packages the disjoint sheets into a
`Trivialization`. Feeding these into `IsCoveringMap.mk'` — whose closed-range
hypothesis is `DCExpandsMetric.isClosed_range` — yields `IsCoveringMap f`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3, Lemma 3.3.
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

/-- **Math.** The fibre `f ⁻¹' {x}` of a local homeomorphism is discrete: each fibre
point `e` has a chart neighbourhood on which `f` is injective, meeting the fibre only
at `e`. -/
theorem IsLocalHomeomorph.discreteTopology_fiber {f : M → M'} (hf : IsLocalHomeomorph f)
    (x : M') : DiscreteTopology ↥(f ⁻¹' {x}) :=
  (isDiscrete_iff_discreteTopology (s := f ⁻¹' {x})).mp <|
    IsDiscrete.of_openPartialHomeomorph f subset_rfl fun e _ => by
      obtain ⟨φ, he_src, hfφ⟩ := hf e
      exact ⟨φ, he_src, hfφ.symm⟩

/-- **Math.** **Continuous local section from a lifted segment family** (do Carmo Ch. 7,
Lemma 3.3). Let `f : M → M'` be a metric-expanding smooth local diffeomorphism out of a
proper Riemannian manifold whose distance is the Riemannian distance. Suppose `V ⊆ M'` is
equipped with a jointly-continuous family of `C¹`, finite-length "segments"
`seg y : [0,1] → M'` running from the fixed base `x₀` (`seg y 0 = x₀`) to `y`
(`seg y 1 = y`), the base segment `seg x₀` being constant at `x₀`. Then through any
`e` over `x₀` there is a continuous section `s : V → M` of `f` with `s x₀ = e`.

Proof: lift each `seg y` through `e` (`DCExpandsMetric.exists_pathLift`); joint continuity
of the family of lifts is mathlib's `IsLocalHomeomorph.continuous_lift` for the separated
local homeomorphism `f`. Set `s y := (lift of seg y)(1)`; then `f (s y) = seg y 1 = y`,
and uniqueness of lifts (`IsLocalHomeomorph.eqOn_lift`) against the constant lift `e` of the
constant base segment gives `s x₀ = e`. -/
theorem DCExpandsMetric.exists_section_of_segmentFamily [ProperSpace M] [T2Space M']
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : IsLocalDiffeomorph I I' ∞ f)
    {V : Set M'} {x₀ : M'} (hx₀V : x₀ ∈ V) (seg : M' → ℝ → M')
    (hseg_cont : Continuous (fun q : unitInterval × V => seg q.2.val q.1.val))
    (hseg_C1 : ∀ y ∈ V, ContMDiffOn 𝓘(ℝ, ℝ) I' 1 (seg y) (Icc 0 1))
    (hseg_fin : ∀ y ∈ V, letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
        ⟨gN.toRiemannianMetric⟩
      Manifold.pathELength I' (seg y) 0 1 ≠ ⊤)
    (hseg_0 : ∀ y ∈ V, seg y 0 = x₀) (hseg_1 : ∀ y ∈ V, seg y 1 = y)
    (hseg_const₀ : ∀ t ∈ Icc (0 : ℝ) 1, seg x₀ t = x₀)
    {e : M} (he : f e = x₀) :
    ∃ s : M' → M, ContinuousOn s V ∧ (∀ y ∈ V, f (s y) = y) ∧ s x₀ = e ∧
      ∀ y ∈ V, ∃ h : ℝ → M, ContinuousOn h (Icc 0 1) ∧ h 0 = e ∧ h 1 = s y ∧
        ∀ t ∈ Icc (0 : ℝ) 1, f (h t) = seg y t := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  have hlh : IsLocalHomeomorph f := hf.isLocalHomeomorph
  have hsep : IsSeparatedMap f := T2Space.isSeparatedMap f
  -- lift every segment through `e`
  have hex : ∀ y : V, ∃ g : ℝ → M, ContinuousOn g (Icc 0 1) ∧ g 0 = e ∧
      ∀ t ∈ Icc (0 : ℝ) 1, f (g t) = seg y.val t := by
    rintro ⟨y, hy⟩
    exact hexp.exists_pathLift hgM hf (hseg_C1 y hy) (hseg_fin y hy) (he.trans (hseg_0 y hy).symm)
  choose g hg_cont hg_0 hg_lift using hex
  -- the family of lifts as a joint map on `I × V`
  set G : unitInterval × V → M := fun q => g q.2 q.1.val with hG
  -- the family of segments as a bundled continuous map
  set F : C(unitInterval × V, M') := ⟨fun q => seg q.2.val q.1.val, hseg_cont⟩ with hF
  have hG_lifts : f ∘ G = F := by
    funext q
    exact hg_lift q.2 q.1.val q.1.property
  have hcont_0 : Continuous (fun a : V => G (0, a)) := by
    have h : (fun a : V => G (0, a)) = fun _ : V => e := by
      funext a; simp only [hG, Set.Icc.coe_zero]; exact hg_0 a
    rw [h]; exact continuous_const
  have hcont_A : ∀ a : V, Continuous (fun t : unitInterval => G (t, a)) := by
    intro a
    exact (hg_cont a).comp_continuous continuous_subtype_val (fun t => t.property)
  have hGcont : Continuous G := hlh.continuous_lift hsep F hG_lifts hcont_0 hcont_A
  -- the section
  refine ⟨fun y => if hy : y ∈ V then g ⟨y, hy⟩ 1 else e, ?_, ?_, ?_, ?_⟩
  · -- continuity on `V`
    rw [continuousOn_iff_continuous_restrict]
    have : (V.restrict fun y => if hy : y ∈ V then g ⟨y, hy⟩ 1 else e)
        = fun a : V => G (1, a) := by
      funext a
      simp only [Set.restrict_apply, a.property, dif_pos, hG, Set.Icc.coe_one, Subtype.coe_eta]
    rw [this]
    exact hGcont.comp (by fun_prop)
  · intro y hy
    simp only [hy, dif_pos]
    have := hg_lift ⟨y, hy⟩ 1 ⟨zero_le_one, le_rfl⟩
    rw [this, hseg_1 y hy]
  · -- `s x₀ = e` by uniqueness against the constant lift
    simp only [hx₀V, dif_pos]
    have huniq : Set.EqOn (g ⟨x₀, hx₀V⟩) (fun _ => e) (Icc (0 : ℝ) 1) :=
      IsLocalHomeomorph.eqOn_lift hlh isPreconnected_Icc (hg_cont ⟨x₀, hx₀V⟩) continuousOn_const
        (fun t ht => (hg_lift ⟨x₀, hx₀V⟩ t ht).trans (hseg_const₀ t ht))
        (fun _ _ => he) ⟨le_rfl, zero_le_one⟩ (hg_0 ⟨x₀, hx₀V⟩)
    exact huniq ⟨zero_le_one, le_rfl⟩
  · -- each section value is the endpoint of a segment lift through `e`
    intro y hy
    refine ⟨g ⟨y, hy⟩, hg_cont _, hg_0 _, ?_, hg_lift _⟩
    simp only [hy, dif_pos]

/-- **Math.** A straight chart segment between two points of a metric ball inside the
chart target is a `C¹` curve confined to the chart source, hence of finite length.
Used for both the forward segments `x₀ ↝ y` building the sections and the reverse
segments `y ↝ x₀` in the exhaustion step of Lemma 3.3. -/
theorem Geodesic.chartBallSegment_props [I'.Boundaryless]
    {x₀ : M'} {r : ℝ}
    (hballsub : Metric.ball (extChartAt I' x₀ x₀) r ⊆ (extChartAt I' x₀).target)
    {p q : E'} (hp : p ∈ Metric.ball (extChartAt I' x₀ x₀) r)
    (hq : q ∈ Metric.ball (extChartAt I' x₀ x₀) r) :
    ContMDiffOn 𝓘(ℝ, ℝ) I' 1
        (fun t : ℝ => (extChartAt I' x₀).symm (AffineMap.lineMap p q t)) (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        (extChartAt I' x₀).symm (AffineMap.lineMap p q t) ∈ (chartAt H' x₀).source) := by
  set c₁ := extChartAt I' x₀ with hc₁
  set L : ℝ → E' := fun t => AffineMap.lineMap p q t with hL
  have hLball : ∀ t ∈ Icc (0 : ℝ) 1, L t ∈ Metric.ball (c₁ x₀) r := fun t ht =>
    (convex_ball (c₁ x₀) r).lineMap_mem hp hq ht
  have hLtgt : ∀ t ∈ Icc (0 : ℝ) 1, L t ∈ c₁.target := fun t ht => hballsub (hLball t ht)
  have hsrc : ∀ t ∈ Icc (0 : ℝ) 1, c₁.symm (L t) ∈ (chartAt H' x₀).source := by
    intro t ht
    rw [← extChartAt_source (I := I') x₀]
    exact c₁.map_target (hLtgt t ht)
  have hLeq : L = fun t : ℝ => t • (q - p) + p := by
    funext t; simp only [hL, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hLcmdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E') 1 L (Icc 0 1) := by
    rw [hLeq]
    exact ((contDiff_id.smul contDiff_const).add contDiff_const).contDiffOn.contMDiffOn
  have hcmdiff : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 (fun t => c₁.symm (L t)) (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm (I := I') x₀).comp hLcmdiff hLtgt
  exact ⟨hcmdiff, hsrc⟩

/-- **Math.** **Evenly-covered chart-ball neighbourhood** (do Carmo Ch. 7, Lemma 3.3).
For a metric-expanding smooth local diffeomorphism `f : M → M'` out of a complete
Riemannian manifold, every point `x₀` in the image has an evenly covered neighbourhood:
over a chart ball `V ∋ x₀`, the disjoint continuous sections through the fibre points
trivialize `f`. This produces the `Trivialization (f ⁻¹' {x₀}) f` over `V`. -/
theorem DCExpandsMetric.exists_trivialization_at [ProperSpace M] [T2Space M'] [I'.Boundaryless]
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : IsLocalDiffeomorph I I' ∞ f) {x₀ : M'} (hx₀ : x₀ ∈ Set.range f) :
    ∃ t : Trivialization ↥(f ⁻¹' {x₀}) f, x₀ ∈ t.baseSet := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) := ⟨gN.toRiemannianMetric⟩
  have hlh : IsLocalHomeomorph f := hf.isLocalHomeomorph
  haveI hdisc : DiscreteTopology ↥(f ⁻¹' {x₀}) :=
    IsLocalHomeomorph.discreteTopology_fiber hlh x₀
  obtain ⟨e₀, he₀⟩ := hx₀
  haveI : Nonempty ↥(f ⁻¹' {x₀}) := ⟨⟨e₀, he₀⟩⟩
  haveI : Nonempty M := ⟨e₀⟩
  haveI : Nonempty (M' → M) := ⟨fun _ => e₀⟩
  -- chart ball `V` around `x₀`
  set c₁ := extChartAt I' x₀ with hc₁
  set b₀ := c₁ x₀ with hb₀
  obtain ⟨r, hr, hballsub⟩ := Metric.mem_nhds_iff.mp (extChartAt_target_mem_nhds (I := I') x₀)
  set V : Set M' := c₁.source ∩ c₁ ⁻¹' (Metric.ball b₀ r) with hV
  have hVopen : IsOpen V :=
    (continuousOn_extChartAt (I := I') x₀).isOpen_inter_preimage
      (isOpen_extChartAt_source x₀) Metric.isOpen_ball
  have hx₀V : x₀ ∈ V := ⟨mem_extChartAt_source (I := I') x₀, by
    rw [Set.mem_preimage, Metric.mem_ball, ← hb₀, dist_self]; exact hr⟩
  have hVsub : V ⊆ c₁.source := Set.inter_subset_left
  have hcy_ball : ∀ y : V, c₁ y.val ∈ Metric.ball b₀ r := fun y => y.property.2
  have hcy_cont : Continuous (fun y : V => c₁ y.val) :=
    continuousOn_iff_continuous_restrict.mp ((continuousOn_extChartAt (I := I') x₀).mono hVsub)
  -- the forward chart segment `x₀ ↝ y`
  set seg : M' → ℝ → M' := fun y t => c₁.symm (AffineMap.lineMap b₀ (c₁ y) t) with hseg
  have hsegprops : ∀ y ∈ V, ContMDiffOn 𝓘(ℝ, ℝ) I' 1 (seg y) (Icc 0 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, seg y t ∈ (chartAt H' x₀).source := fun y hy =>
    Geodesic.chartBallSegment_props hballsub (mem_ball_self hr) (hcy_ball ⟨y, hy⟩)
  have hseg_C1 : ∀ y ∈ V, ContMDiffOn 𝓘(ℝ, ℝ) I' 1 (seg y) (Icc 0 1) :=
    fun y hy => (hsegprops y hy).1
  have hseg_src : ∀ y ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, seg y t ∈ (chartAt H' x₀).source :=
    fun y hy => (hsegprops y hy).2
  have hseg_fin : ∀ y ∈ V, Manifold.pathELength I' (seg y) 0 1 ≠ ⊤ := fun y hy =>
    Geodesic.pathELength_ne_top_of_mapsTo_chartSource (α := x₀) zero_le_one
      (hseg_C1 y hy) (hseg_src y hy)
  have hseg_0 : ∀ y ∈ V, seg y 0 = x₀ := by
    intro y hy
    simp only [hseg, AffineMap.lineMap_apply_zero, hb₀]
    exact c₁.left_inv (mem_extChartAt_source (I := I') x₀)
  have hseg_1 : ∀ y ∈ V, seg y 1 = y := by
    intro y hy
    simp only [hseg, AffineMap.lineMap_apply_one]
    exact c₁.left_inv (hVsub hy)
  have hseg_const₀ : ∀ t ∈ Icc (0 : ℝ) 1, seg x₀ t = x₀ := by
    intro t ht
    simp only [hseg, ← hb₀, AffineMap.lineMap_same, AffineMap.const_apply]
    exact c₁.left_inv (mem_extChartAt_source (I := I') x₀)
  -- joint continuity of the forward segment family on `I × V`
  have hseg_cont : Continuous (fun q : unitInterval × V => seg q.2.val q.1.val) := by
    have hinner : Continuous
        (fun q : unitInterval × V => AffineMap.lineMap b₀ (c₁ q.2.val) q.1.val) := by
      have heq : (fun q : unitInterval × V => AffineMap.lineMap b₀ (c₁ q.2.val) q.1.val)
          = fun q => q.1.val • (c₁ q.2.val - b₀) + b₀ := by
        funext q; rw [AffineMap.lineMap_apply]; simp only [vsub_eq_sub, vadd_eq_add]
      rw [heq]
      exact ((continuous_subtype_val.comp continuous_fst).smul
        ((hcy_cont.comp continuous_snd).sub continuous_const)).add continuous_const
    have hinner_tgt : ∀ q : unitInterval × V,
        AffineMap.lineMap b₀ (c₁ q.2.val) q.1.val ∈ c₁.target := fun q =>
      hballsub ((convex_ball b₀ r).lineMap_mem (mem_ball_self hr) (hcy_ball q.2) q.1.property)
    exact (continuousOn_extChartAt_symm (I := I') x₀).comp_continuous hinner hinner_tgt
  -- sections through each fibre point
  have hsecEx : ∀ i : ↥(f ⁻¹' {x₀}), ∃ s : M' → M, ContinuousOn s V ∧ (∀ y ∈ V, f (s y) = y) ∧
      s x₀ = i.val ∧ ∀ y ∈ V, ∃ h : ℝ → M, ContinuousOn h (Icc 0 1) ∧ h 0 = i.val ∧ h 1 = s y ∧
        ∀ t ∈ Icc (0 : ℝ) 1, f (h t) = seg y t := fun i =>
    hexp.exists_section_of_segmentFamily hgM hf hx₀V seg hseg_cont hseg_C1 hseg_fin
      hseg_0 hseg_1 hseg_const₀ i.property
  choose sec hsec_cont hsec_lift hsec_x₀ hsec_P5 using hsecEx
  -- the sheets and their open-embedding sections
  set U : ↥(f ⁻¹' {x₀}) → Set M := fun i => sec i '' V with hU
  have hsi_emb : ∀ i : ↥(f ⁻¹' {x₀}), IsOpenEmbedding (V.restrict (sec i)) := by
    intro i
    refine hlh.isOpenEmbedding_of_comp ?_ (continuousOn_iff_continuous_restrict.mp (hsec_cont i))
    have : f ∘ V.restrict (sec i) = (Subtype.val : V → M') := by
      funext y; exact hsec_lift i y.val y.property
    rw [this]; exact hVopen.isOpenEmbedding_subtypeVal
  refine ⟨hVopen.trivializationDiscrete U V ?_ ?_ ?_ ?_ ?_, hx₀V⟩
  · -- open_iff
    intro i W hWV
    have heqset : f ⁻¹' W ∩ U i = (V.restrict (sec i)) '' (Subtype.val ⁻¹' W) := by
      ext m
      simp only [hU, Set.mem_inter_iff, Set.mem_preimage, Set.mem_image, Set.restrict_apply]
      constructor
      · rintro ⟨hmW, y, hyV, rfl⟩
        refine ⟨⟨y, hyV⟩, ?_, rfl⟩
        show y ∈ W
        rw [← hsec_lift i y hyV]; exact hmW
      · rintro ⟨⟨y, hyV⟩, hyW, rfl⟩
        refine ⟨?_, y, hyV, rfl⟩
        show f (sec i y) ∈ W
        rw [hsec_lift i y hyV]; exact hyW
    have himg : (Subtype.val : V → M') '' (Subtype.val ⁻¹' W) = W := by
      rw [Subtype.image_preimage_coe]; exact Set.inter_eq_right.mpr hWV
    rw [heqset]
    constructor
    · intro hW
      exact (hsi_emb i).isOpenMap _
        (hVopen.isOpenEmbedding_subtypeVal.continuous.isOpen_preimage W hW)
    · intro hOpen
      have h1 : IsOpen (Subtype.val ⁻¹' W : Set V) :=
        (hsi_emb i).isOpen_iff_image_isOpen.mpr hOpen
      have h2 := hVopen.isOpenEmbedding_subtypeVal.isOpenMap _ h1
      rwa [himg] at h2
  · -- inj
    intro i a ha b hb hfab
    obtain ⟨y₁, hy₁, rfl⟩ := ha
    obtain ⟨y₂, hy₂, rfl⟩ := hb
    rw [hsec_lift i y₁ hy₁, hsec_lift i y₂ hy₂] at hfab
    rw [hfab]
  · -- surj
    intro i y hy
    exact ⟨sec i y, ⟨y, hy, rfl⟩, hsec_lift i y hy⟩
  · -- disjoint
    intro i j hij
    show Disjoint (sec i '' V) (sec j '' V)
    rw [Set.disjoint_left]
    rintro m ⟨y, hy, rfl⟩ ⟨y', hy', hm⟩
    have hyy' : y' = y := by
      have h := hsec_lift j y' hy'; rw [hm, hsec_lift i y hy] at h; exact h.symm
    subst y'
    obtain ⟨hi, hi_cont, hi_0, hi_1, hi_lift⟩ := hsec_P5 i y hy
    obtain ⟨hj, hj_cont, hj_0, hj_1, hj_lift⟩ := hsec_P5 j y hy
    have hend : hi 1 = hj 1 := by rw [hi_1, hj_1, hm]
    have heqon := IsLocalHomeomorph.eqOn_lift hlh isPreconnected_Icc hi_cont hj_cont
      hi_lift hj_lift (t₀ := 1) ⟨zero_le_one, le_rfl⟩ hend
    have h0 := heqon (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    rw [hi_0, hj_0] at h0
    exact hij (Subtype.ext h0)
  · -- exhaustive
    intro m hm
    rw [Set.mem_preimage] at hm
    set y := f m with hy_def
    have hyV : y ∈ V := hm
    have hrmap : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) ∈ Icc (0 : ℝ) 1 :=
      fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
    -- reverse segment `y ↝ x₀` as a reflection of the forward segment `x₀ ↝ y`
    set rseg : ℝ → M' := fun t => seg y (1 - t) with hrseg
    have hrseg_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 rseg (Icc 0 1) :=
      (hseg_C1 y hyV).comp
        (contDiff_const.sub contDiff_id).contMDiff.contMDiffOn hrmap
    have hrseg_src : ∀ t ∈ Icc (0 : ℝ) 1, rseg t ∈ (chartAt H' x₀).source :=
      fun t ht => hseg_src y hyV (1 - t) (hrmap t ht)
    have hrseg_fin : Manifold.pathELength I' rseg 0 1 ≠ ⊤ :=
      Geodesic.pathELength_ne_top_of_mapsTo_chartSource (α := x₀) zero_le_one hrseg_C1 hrseg_src
    have hrseg_0 : rseg 0 = y := by simp only [hrseg, sub_zero]; exact hseg_1 y hyV
    have hmr : f m = rseg 0 := by rw [hrseg_0]
    obtain ⟨revh, revh_cont, revh_0, revh_lift⟩ :=
      hexp.exists_pathLift hgM hf hrseg_C1 hrseg_fin hmr
    -- the reversed lift traces the forward segment from `e₀' := revh 1`
    have he₀' : f (revh 1) = x₀ := by
      rw [revh_lift 1 ⟨zero_le_one, le_rfl⟩]
      simp only [hrseg, sub_self]; exact hseg_0 y hyV
    set i : ↥(f ⁻¹' {x₀}) := ⟨revh 1, he₀'⟩ with hi_def
    set fwdh : ℝ → M := fun t => revh (1 - t) with hfwdh
    have hfwdh_cont : ContinuousOn fwdh (Icc 0 1) :=
      revh_cont.comp (Continuous.continuousOn (by fun_prop)) hrmap
    have hfwdh_lift : ∀ t ∈ Icc (0 : ℝ) 1, f (fwdh t) = seg y t := by
      intro t ht
      simp only [hfwdh]
      rw [revh_lift (1 - t) (hrmap t ht)]
      simp only [hrseg, sub_sub_cancel]
    have hfwdh_0 : fwdh 0 = revh 1 := by simp only [hfwdh, sub_zero]
    -- identify `sec i y` with `m` by uniqueness of segment lifts
    obtain ⟨h, h_cont, h_0, h_1, h_lift⟩ := hsec_P5 i y hyV
    have heqon := IsLocalHomeomorph.eqOn_lift hlh isPreconnected_Icc h_cont hfwdh_cont
      h_lift hfwdh_lift (t₀ := 0) ⟨le_rfl, zero_le_one⟩ (h_0.trans hfwdh_0.symm)
    have hsecy : sec i y = m := by
      have hh := heqon (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
      rw [h_1] at hh
      rw [hh]; simp only [hfwdh, sub_self]; exact revh_0
    exact Set.mem_iUnion.mpr ⟨i, y, hyV, hsecy⟩

/-- **Math.** **do Carmo Ch. 7, Lemma 3.3.** A smooth local diffeomorphism
`f : M → M'` out of a complete Riemannian manifold `M` (metrically complete, so
`ProperSpace M` by Hopf–Rinow) which *expands the metric* (`|df_p(v)| ≥ |v|` for all
`p, v`) is a **covering map**. Every point in the image has an evenly covered chart
ball (`DCExpandsMetric.exists_trivialization_at`); points outside the image are handled
by the closed range (`DCExpandsMetric.isClosed_range`), feeding mathlib's
`IsCoveringMap.mk'`. -/
theorem DCExpandsMetric.isCoveringMap [ProperSpace M] [T2Space M'] [I'.Boundaryless]
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : IsLocalDiffeomorph I I' ∞ f) :
    IsCoveringMap f := by
  have hlh : IsLocalHomeomorph f := hf.isLocalHomeomorph
  haveI : ∀ x : M', DiscreteTopology ↥(f ⁻¹' {x}) := fun x =>
    IsLocalHomeomorph.discreteTopology_fiber hlh x
  refine IsCoveringMap.mk' f (fun x => ↥(f ⁻¹' {x})) ?_ (hexp.isClosed_range hgM hf)
  intro x hx
  exact ⟨(hexp.exists_trivialization_at hgM hf hx).choose,
    (hexp.exists_trivialization_at hgM hf hx).choose_spec⟩

end Riemannian
