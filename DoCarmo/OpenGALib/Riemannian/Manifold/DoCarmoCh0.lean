import OpenGALib.Riemannian.TangentBundle.TangentSmooth
import OpenGALib.Riemannian.Manifold.HadamardLemma
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.Dual

/-!
# do Carmo Chapter 0 interface

Thin, checked names for the differentiable-manifold primitives used by the
Chapter 0 blueprint. The definitions intentionally wrap Mathlib's manifold API
instead of introducing a parallel formalization.
-/

open scoped ContDiff Manifold Topology

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- do Carmo Ch.0, §2 (Def. 2.1): a *differentiable (`C^∞`) manifold* structure on `M`.
do Carmo defines it as a set `M` with a maximal family of injective parametrizations
`x_α : U_α ⊆ ℝⁿ → M` covering `M` whose transition maps `x_β⁻¹ ∘ x_α` are differentiable.
Mathlib packages exactly this data as a `ChartedSpace H M` (the family of parametrizations,
i.e. charts) together with `IsManifold I ∞ M` (the transition maps are `C^∞`); the maximal
atlas `IsManifold.maximalAtlas` supplies do Carmo's maximality clause (3). This predicate
is the `C^∞` smoothness condition on the given charted structure. -/
abbrev DCDifferentiableManifold : Prop := IsManifold I ∞ M

/-- do Carmo Ch.0 tangent space at a point, wired to Mathlib's tangent space. -/
abbrev DCTangentSpaceAt (p : M) : Type _ :=
  TangentSpace I p

/-- do Carmo Ch.0 differential of a smooth map at a point, wired to `mfderiv`. -/
abbrev DCDifferentialAt
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (f : M → M') (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I' (f p) :=
  mfderiv I I' f p

omit [CompleteSpace E] [IsManifold I ∞ M] in
/-- **do Carmo Ch.0, Prop. 2.7.** The differential `dφ_p : T_pM → T_{φ(p)}M'` computed
through a representing curve is well-defined, independent of the curve, and linear. Concretely:
for a differentiable curve `α` with `α 0 = p`, writing `β = φ ∘ α`, the velocity of `β` at
`0`, namely `dβ_0(1)`, equals `dφ_p` applied to the velocity `dα_0(1)` of `α`. Since the
right-hand side depends only on `p` and the velocity vector `dα_0(1)` — not on the choice of
representing curve `α` — this is exactly do Carmo's statement that `dφ_p(v) = β'(0)` is a
well-defined map; its linearity is carried by `mfderiv`, which is a continuous linear map. -/
theorem DCDifferentialAt_curve
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {φ : M → M'} {α : ℝ → M}
    (hφ : MDifferentiableAt I I' φ (α 0)) (hα : MDifferentiableAt 𝓘(ℝ, ℝ) I α 0) :
    mfderiv 𝓘(ℝ, ℝ) I' (φ ∘ α) 0 (1 : ℝ)
      = mfderiv I I' φ (α 0) (mfderiv 𝓘(ℝ, ℝ) I α 0 (1 : ℝ)) := by
  rw [mfderiv_comp (0 : ℝ) hφ hα]; rfl

/-- do Carmo Ch.0, §2 (Def. 2.5): a map `f : M → M'` is *differentiable at* `p`,
wired to Mathlib's `MDifferentiableAt`. In charts this is exactly do Carmo's
condition that the coordinate expression `y⁻¹ ∘ f ∘ x` is differentiable at
`x⁻¹(p)`, independent of the parametrizations. -/
abbrev DCDifferentiableAt
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (f : M → M') (p : M) : Prop :=
  MDifferentiableAt I I' f p

/-- do Carmo Ch.0 diffeomorphism, wired to Mathlib's `Diffeomorph`. -/
abbrev DCDiffeomorph
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] : Type _ :=
  Diffeomorph I I' M M' ∞

omit [CompleteSpace E] [IsManifold I ∞ M] in
/-- do Carmo Ch.0, §2: if `Φ` is a diffeomorphism then its differential
`dΦ_p : T_pM → T_{Φ(p)}M'` is a linear isomorphism at every point. -/
theorem DCDiffeomorph.mfderiv_bijective
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (Φ : DCDiffeomorph (I := I) (M := M) I' (M' := M')) (p : M) :
    Function.Bijective (mfderiv I I' Φ p) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by decide
  rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe (x := p) Φ hn]
  exact (Φ.mfderivToContinuousLinearEquiv hn p).bijective

/-- do Carmo Ch.0, §3 (Def. 3.1): `f : M → M'` is an *immersion* if its
differential `df_p` is injective at every point `p`. Wired to injectivity of
Mathlib's `mfderiv`. -/
def DCIsImmersion
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (f : M → M') : Prop :=
  ∀ p, Function.Injective (mfderiv I I' f p)

/-- do Carmo Ch.0, §3 (Def. 3.1): `f : M → M'` is an *embedding* if it is an
immersion and a homeomorphism onto its image (topological embedding). -/
def DCIsEmbedding
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (f : M → M') : Prop :=
  DCIsImmersion (I := I) (I' := I') f ∧ Topology.IsEmbedding f

/-! ### §3 (Prop. 3.7): an immersion is locally an embedding

The topological core of do Carmo's Proposition 3.7.  Wherever a map is an immersion
in Mathlib's sense (`Manifold.IsImmersionAt`, i.e. it has the local normal form
`u ↦ (u, 0)` in suitable charts around the point), it restricts to a *topological
embedding* on a neighbourhood: this is exactly the statement that the local inverse of
an immersion is continuous, which is the substantive part of "immersion `⇒` locally an
embedding".  The passage from do Carmo's pointwise injective-differential definition
(`DCIsImmersion`) to `IsImmersionAt` is the finite-dimensional splitting of an injective
`mfderiv`; Mathlib currently records that reduction as an open task, so the full
proposition is not yet wired.  The proof below is field- and dimension-agnostic. -/

section ImmersionLocalEmbedding

open Manifold Topology Set

universe u₀

variable {𝕜 : Type u₀} [NontriviallyNormedField 𝕜]
  {Em : Type u₀} [NormedAddCommGroup Em] [NormedSpace 𝕜 Em]
  {En : Type u₀} [NormedAddCommGroup En] [NormedSpace 𝕜 En]
  {Hm : Type*} [TopologicalSpace Hm] {Hn : Type*} [TopologicalSpace Hn]
  {Im : ModelWithCorners 𝕜 Em Hm} {In : ModelWithCorners 𝕜 En Hn}
  {Mm : Type*} [TopologicalSpace Mm] [ChartedSpace Hm Mm]
  {Nn : Type*} [TopologicalSpace Nn] [ChartedSpace Hn Nn]

omit [ChartedSpace Hm Mm] in
/-- An extended chart, restricted to the source of the underlying chart, is a topological
inducing map: the source of `M` carries the topology induced from the model space `Em`
through `c.extend Im`.  Reusable building block for chart-level topology arguments. -/
theorem isInducing_extend_restrict (c : OpenPartialHomeomorph Mm Hm) :
    Topology.IsInducing (c.source.restrict (c.extend Im)) := by
  have hval : Topology.IsInducing (Subtype.val : c.target → Hm) := IsInducing.subtypeVal
  have hhom : Topology.IsInducing c.toHomeomorphSourceTarget :=
    c.toHomeomorphSourceTarget.isInducing
  have hIm : Topology.IsInducing (Im : Hm → Em) := Im.isClosedEmbedding.isEmbedding.isInducing
  have hdom : Topology.IsInducing (c.source.restrict c) := by
    have h2 := hval.comp hhom; convert h2 using 1
  have heq : c.source.restrict (c.extend Im) = (Im : Hm → Em) ∘ (c.source.restrict c) := rfl
  rw [heq]; exact hIm.comp hdom

variable {n : WithTop ℕ∞} {f : Mm → Nn} {p : Mm}

/-- **do Carmo Ch.0, Prop. 3.7 (topological core).**  If `f` is a `C^n` immersion at `p`
(`Manifold.IsImmersionAt`), then there is an open neighbourhood `U` of `p` on which the
restriction of `f` is a topological embedding.  Thus every immersion is *locally* an
embedding.  The proof uses the local normal form `f = u ↦ (u, 0)` in charts: `f` restricted
to the domain chart is the composite of the chart (an inducing map into the model space),
the linear inclusion `u ↦ equiv (u, 0)` (an embedding), and the inverse of the codomain
chart, and it is injective because each of these is. -/
theorem isEmbedding_restrict_of_isImmersionAt (h : IsImmersionAt Im In n f p) :
    ∃ U : Set Mm, IsOpen U ∧ p ∈ U ∧ Topology.IsEmbedding (U.restrict f) := by
  refine ⟨h.domChart.source, h.domChart.open_source, h.mem_domChart_source, ?_⟩
  set U := h.domChart.source with hU
  -- Local normal form in charts (after peeling the codomain chart).
  have hnf2 : ∀ q ∈ U, h.codChart.extend In (f q) = h.equiv (h.domChart.extend Im q, 0) := by
    intro q hq
    have hqtarget : h.domChart.extend Im q ∈ (h.domChart.extend Im).target :=
      (h.domChart.extend Im).map_source (by rwa [OpenPartialHomeomorph.extend_source])
    have hw := h.writtenInCharts hqtarget
    simp only [Function.comp_apply] at hw
    rwa [OpenPartialHomeomorph.extend_left_inv _ hq] at hw
  have hmem : ∀ q : ↥U, f q ∈ h.codChart.source := fun q => h.source_subset_preimage_source q.2
  -- The linear inclusion `u ↦ equiv (u, 0)` is a topological embedding.
  have hincl : Topology.IsEmbedding (fun u : Em => h.equiv (u, 0)) :=
    (h.equiv.toHomeomorph.isEmbedding).comp (isEmbedding_prodMkLeft 0)
  have hg : Topology.IsInducing (h.codChart.source.restrict (h.codChart.extend In)) :=
    isInducing_extend_restrict _
  set f' : ↥U → ↥(h.codChart.source) := fun q => ⟨f q, hmem q⟩ with hf'
  -- `codChart.extend In ∘ f` is inducing, being an embedding after a chart.
  have hgf' : Topology.IsInducing (fun q : ↥U => h.codChart.extend In (f q)) := by
    have hcomp : (fun q : ↥U => h.codChart.extend In (f q))
        = (fun u : Em => h.equiv (u, 0)) ∘ (U.restrict (h.domChart.extend Im)) := by
      ext q; simp only [Function.comp_apply, Set.restrict_apply]; exact hnf2 q.1 q.2
    rw [hcomp]
    exact hincl.isInducing.comp (isInducing_extend_restrict _)
  -- Cancel the (inducing) codomain chart to see that `f` itself is inducing on `U`.
  have hf'ind : Topology.IsInducing f' := (Topology.IsInducing.of_comp_iff hg).mp hgf'
  have hind : Topology.IsInducing (U.restrict f) := by
    have hval : Topology.IsInducing (Subtype.val : ↥(h.codChart.source) → Nn) :=
      IsInducing.subtypeVal
    have := hval.comp hf'ind
    convert this using 1
  rw [Topology.isEmbedding_iff]
  refine ⟨hind, ?_⟩
  -- Injectivity: `equiv`, the inclusion and the chart are all injective.
  intro q₁ q₂ hq
  simp only [Set.restrict_apply] at hq
  have e1 := hnf2 q₁.1 q₁.2
  have e2 := hnf2 q₂.1 q₂.2
  rw [hq, e2] at e1
  have hpair := h.equiv.injective e1
  have hfst : h.domChart.extend Im q₁.1 = h.domChart.extend Im q₂.1 :=
    (congrArg Prod.fst hpair).symm
  have hs1 : q₁.1 ∈ (h.domChart.extend Im).source := by
    rw [OpenPartialHomeomorph.extend_source]; exact q₁.2
  have hs2 : q₂.1 ∈ (h.domChart.extend Im).source := by
    rw [OpenPartialHomeomorph.extend_source]; exact q₂.2
  exact Subtype.ext ((h.domChart.extend Im).injOn hs1 hs2 hfst)

end ImmersionLocalEmbedding

/-! ### §3 (Prop. 3.7): local immersion normal form in normed spaces

The analytic heart of "an immersion is locally an embedding", stated purely for maps
between finite-dimensional normed spaces (do Carmo's chart computation): if `dg_q` is
injective, extend `g` by a complement of its range and straighten it with the inverse
function theorem, so `g` is a topological embedding on a neighbourhood of `q`. -/

section ImmersionNormalForm

open Topology Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Local immersion normal form (normed-space core of Prop. 3.7).**  If `g : E → F` is
`C^∞` on an open set `s ∋ q` (with `E`, `F` finite-dimensional) and its Fréchet derivative
`L = dg_q` is injective, then `g` restricts to a *topological embedding* on a neighbourhood
of `q`.  Extend `g` to `Ext(x,t) = g(x) + t` on `E × (complement of range L)`; its
derivative at `(q,0)` is the linear isomorphism `L ⊕ ι`, so by the inverse function theorem
`Ext` is a local homeomorphism, and `g` is its restriction to the slice `t = 0`. -/
theorem isEmbedding_restrict_of_hasFDerivAt_injective
    {g : E → F} {L : E →L[ℝ] F} {q : E} {s : Set E}
    (hs : IsOpen s) (hq : q ∈ s) (hg : ContDiffOn ℝ ∞ g s)
    (hL : HasFDerivAt g L q) (hLinj : Function.Injective L) :
    ∃ V : Set E, IsOpen V ∧ q ∈ V ∧ IsEmbedding (V.restrict g) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hker : (L : E →ₗ[ℝ] F).ker = ⊥ := LinearMap.ker_eq_bot.mpr hLinj
  obtain ⟨G, hG⟩ := Submodule.exists_isCompl (LinearMap.range (L : E →ₗ[ℝ] F))
  haveI : CompleteSpace ↥G := FiniteDimensional.complete ℝ ↥G
  set equiv : (E × ↥G) ≃L[ℝ] F := L.coprodSubtypeLEquivOfIsCompl hG hker with hequiv
  have hcoe : (equiv : (E × ↥G) →L[ℝ] F) = L.coprod G.subtypeL := by
    rw [hequiv, ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl,
      ContinuousLinearEquiv.coe_ofBijective]
  -- The extension `Ext (x, t) = g x + t` and its derivative/smoothness at `(q, 0)`.
  set Ext : E × ↥G → F := fun z => g z.1 + (z.2 : F) with hExtdef
  have hgAt : ContDiffAt ℝ ∞ g q := (hg q hq).contDiffAt (hs.mem_nhds hq)
  have hExtAt : ContDiffAt ℝ ∞ Ext (q, (0 : ↥G)) := by
    refine ContDiffAt.add ?_ ?_
    · exact hgAt.comp (q, (0 : ↥G)) contDiffAt_fst
    · exact (G.subtypeL.contDiff.contDiffAt).comp (q, (0 : ↥G)) contDiffAt_snd
  have hDeriv : HasFDerivAt Ext (equiv : (E × ↥G) →L[ℝ] F) (q, (0 : ↥G)) := by
    have h1 : HasFDerivAt (fun z : E × ↥G => g z.1)
        (L.comp (ContinuousLinearMap.fst ℝ E ↥G)) (q, (0 : ↥G)) :=
      hL.comp (q, (0 : ↥G)) (hasFDerivAt_fst)
    have h2 : HasFDerivAt (fun z : E × ↥G => (z.2 : F))
        ((G.subtypeL).comp (ContinuousLinearMap.snd ℝ E ↥G)) (q, (0 : ↥G)) :=
      (G.subtypeL.hasFDerivAt).comp (q, (0 : ↥G)) (hasFDerivAt_snd)
    have hsum := h1.add h2
    have hCLM : (L.comp (ContinuousLinearMap.fst ℝ E ↥G)
        + G.subtypeL.comp (ContinuousLinearMap.snd ℝ E ↥G))
        = (equiv : (E × ↥G) →L[ℝ] F) := by
      rw [hcoe]; ext x <;> simp
    rw [hCLM] at hsum
    exact hsum
  -- Inverse function theorem: `Ext` is a local homeomorphism at `(q, 0)`.
  set φ := hExtAt.toOpenPartialHomeomorph Ext hDeriv hn with hφ
  have hφcoe : ⇑φ = Ext := hExtAt.toOpenPartialHomeomorph_coe hDeriv hn
  have hmem0 : (q, (0 : ↥G)) ∈ φ.source := hExtAt.mem_toOpenPartialHomeomorph_source hDeriv hn
  -- The slice inclusion `u ↦ (u, 0)` and the neighbourhood on which it lands in `φ.source`.
  set incl : E → E × ↥G := fun u => (u, (0 : ↥G)) with hincl
  have hincl_emb : IsEmbedding incl := isEmbedding_prodMkLeft (0 : ↥G)
  set V₀ : Set E := incl ⁻¹' φ.source with hV0
  have hV0_open : IsOpen V₀ := φ.open_source.preimage hincl_emb.continuous
  have hqV0 : q ∈ V₀ := hmem0
  refine ⟨V₀, hV0_open, hqV0, ?_⟩
  have hmaps : ∀ u : ↥V₀, incl u.1 ∈ φ.source := fun u => u.2
  -- `u ↦ (incl u.1)` is a topological embedding into `φ.source`.
  have hIncl_restr : IsEmbedding (fun u : ↥V₀ => incl u.1) :=
    hincl_emb.comp IsEmbedding.subtypeVal
  have hι : IsEmbedding (Set.codRestrict (fun u : ↥V₀ => incl u.1) φ.source hmaps) :=
    hIncl_restr.codRestrict φ.source hmaps
  -- `φ` restricted to its source is inducing (homeomorphism onto its target).
  have hφind : IsInducing (φ.source.restrict φ) := by
    have hval : IsInducing (Subtype.val : ↥φ.target → F) := IsInducing.subtypeVal
    have hhom : IsInducing φ.toHomeomorphSourceTarget :=
      φ.toHomeomorphSourceTarget.isInducing
    have hc := hval.comp hhom
    convert hc using 1
  -- Assemble: `V₀.restrict (φ ∘ incl)` is inducing and injective, hence an embedding.
  have hcomp_ind : IsInducing (fun u : ↥V₀ => φ (incl u.1)) := by
    have := hφind.comp hι.toIsInducing
    convert this using 1
  have hinj : Function.Injective (fun u : ↥V₀ => φ (incl u.1)) := by
    intro a b hab
    have he : incl a.1 = incl b.1 := φ.injOn (hmaps a) (hmaps b) hab
    exact Subtype.ext (congrArg Prod.fst he)
  have hEmb : IsEmbedding (fun u : ↥V₀ => φ (incl u.1)) := ⟨hcomp_ind, hinj⟩
  have hfun : V₀.restrict g = (fun u : ↥V₀ => φ (incl u.1)) := by
    funext u
    rw [hφcoe]
    show g u.1 = Ext (incl u.1)
    simp [hExtdef, hincl]
  rw [hfun]; exact hEmb

end ImmersionNormalForm

/-- The manifold Lie bracket of two smooth vector fields. -/
abbrev DCLieBracket (X Y : SmoothVectorField I M) (p : M) : TangentSpace I p :=
  VectorField.mlieBracket I X.toFun Y.toFun p

/-- The bracket field is differentiable at every point. -/
theorem DCLieBracket_smoothAt (X Y : SmoothVectorField I M) (p : M) :
    TangentSmoothAt (fun q => DCLieBracket X Y q) p := by
  haveI : IsManifold I (3 : ℕ∞ω) M := inferInstance
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  haveI : IsManifold I (((2 : ℕ∞) : ℕ∞ω) + 1) M := by
    show IsManifold I (3 : ℕ∞ω) M
    infer_instance
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) p := by
    exact (X.smooth p).of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) p := by
    exact (Y.smooth p).of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hbr : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((1 : ℕ∞) : ℕ∞ω)
      (fun y =>
        (⟨y, VectorField.mlieBracket I X.toFun Y.toFun y⟩ : TangentBundle I M)) p := by
    exact hX.mlieBracket_vectorField (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) hY
      (by norm_num)
  exact TangentSmoothAt.mk (hbr.mdifferentiableAt (by norm_num))

omit [CompleteSpace E] in
/-- Anticommutativity of the manifold Lie bracket. -/
theorem DCLieBracket_antisymm (X Y : SmoothVectorField I M) (p : M) :
    DCLieBracket X Y p = -DCLieBracket Y X p := by
  exact VectorField.mlieBracket_swap_apply

/-- Jacobi identity, in Mathlib's Leibniz form. -/
theorem DCLieBracket_jacobi (X Y Z : SmoothVectorField I M) (p : M) :
    VectorField.mlieBracket I X.toFun (VectorField.mlieBracket I Y.toFun Z.toFun) p =
      VectorField.mlieBracket I (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun p +
        VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I X.toFun Z.toFun) p := by
  haveI : IsManifold I (3 : ℕ∞ω) M := inferInstance
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hX2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) p := by
    exact (X.smooth p).of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hY2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) p := by
    exact (Y.smooth p).of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hZ2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, Z.toFun y⟩ : TangentBundle I M)) p := by
    exact (Z.smooth p).of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) p := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact hX2
  have hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) p := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact hY2
  have hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun y => (⟨y, Z.toFun y⟩ : TangentBundle I M)) p := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact hZ2
  exact VectorField.leibniz_identity_mlieBracket_apply
    (I := I) (U := X.toFun) (V := Y.toFun) (W := Z.toFun) hX hY hZ

/-- do Carmo Ch.0, Prop. 5.3(b): the bracket is `ℝ`-linear in its first slot,
`[aX+bY,Z] = a[X,Z] + b[Y,Z]`. -/
theorem DCLieBracket_linear_left (a b : ℝ) (X Y Z : SmoothVectorField I M) (p : M) :
    DCLieBracket (a • X + b • Y) Z p
      = a • DCLieBracket X Z p + b • DCLieBracket Y Z p := by
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  have hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) p := X.smoothAt p
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) p := Y.smoothAt p
  have haX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, (a • X.toFun) y⟩ : TangentBundle I M)) p := (a • X).smoothAt p
  have hbY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, (b • Y.toFun) y⟩ : TangentBundle I M)) p := (b • Y).smoothAt p
  show VectorField.mlieBracket I (a • X + b • Y).toFun Z.toFun p = _
  have hsum : (a • X + b • Y).toFun = a • X.toFun + b • Y.toFun := rfl
  rw [hsum, VectorField.mlieBracket_add_left haX hbY,
    VectorField.mlieBracket_const_smul_left hX,
    VectorField.mlieBracket_const_smul_left hY]

/-- do Carmo Ch.0, Prop. 5.3(d): the Leibniz rule
`[fX,gY] = fg[X,Y] + f·X(g)·Y − g·Y(f)·X`, where `X(g) = dg_p(X_p)`. -/
theorem DCLieBracket_leibniz (f g : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (X Y : SmoothVectorField I M) (p : M) :
    DCLieBracket (SmoothVectorField.smul f hf X) (SmoothVectorField.smul g hg Y) p
      = (f p * g p) • DCLieBracket X Y p
        + (f p * NormedSpace.fromTangentSpace (g p) (mfderiv I 𝓘(ℝ, ℝ) g p (X.toFun p)))
            • Y.toFun p
        - (g p * NormedSpace.fromTangentSpace (f p) (mfderiv I 𝓘(ℝ, ℝ) f p (Y.toFun p)))
            • X.toFun p := by
  haveI : IsManifold I (2 : ℕ∞ω) M := inferInstance
  have hfd : MDifferentiableAt I 𝓘(ℝ, ℝ) f p := hf.mdifferentiableAt (by simp)
  have hgd : MDifferentiableAt I 𝓘(ℝ, ℝ) g p := hg.mdifferentiableAt (by simp)
  have hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) p := X.smoothAt p
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) p := Y.smoothAt p
  have hgY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, (g • Y.toFun) y⟩ : TangentBundle I M)) p :=
    (SmoothVectorField.smul g hg Y).smoothAt p
  show VectorField.mlieBracket I (SmoothVectorField.smul f hf X).toFun
      (SmoothVectorField.smul g hg Y).toFun p = _
  have hlhs : (SmoothVectorField.smul f hf X).toFun = f • X.toFun := rfl
  have hrhs : (SmoothVectorField.smul g hg Y).toFun = g • Y.toFun := rfl
  rw [hlhs, hrhs, VectorField.mlieBracket_smul_left hfd hX,
    VectorField.mlieBracket_smul_right hgd hY]
  rw [show ((g • Y.toFun) p) = g p • Y.toFun p from rfl, map_smul, map_smul]
  module

/-- The Lie bracket of two smooth vector fields is itself differentiable as a
section of the tangent bundle (companion to `DCLieBracket_smoothAt`). -/
theorem DCLieBracket_mdifferentiableAt (X Y : SmoothVectorField I M) (p : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, VectorField.mlieBracket I X.toFun Y.toFun y⟩ : TangentBundle I M)) p := by
  haveI : IsManifold I (3 : ℕ∞ω) M := inferInstance
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I (((2 : ℕ∞) : ℕ∞ω) + 1) M := by
    show IsManifold I (3 : ℕ∞ω) M; infer_instance
  have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) p :=
    (X.smooth p).of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((2 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) p :=
    (Y.smooth p).of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hbr : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ((1 : ℕ∞) : ℕ∞ω)
      (fun y => (⟨y, VectorField.mlieBracket I X.toFun Y.toFun y⟩ : TangentBundle I M)) p :=
    hX.mlieBracket_vectorField (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) hY (by norm_num)
  exact hbr.mdifferentiableAt (by norm_num)

/-- do Carmo Ch.0, Prop. 5.3(c): the Jacobi identity in do Carmo's cyclic form
`[[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y] = 0`. Derived from Mathlib's Leibniz-form
identity together with anticommutativity of the bracket. -/
theorem DCLieBracket_jacobi_cyclic (X Y Z : SmoothVectorField I M) (p : M) :
    VectorField.mlieBracket I (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun p +
      VectorField.mlieBracket I (VectorField.mlieBracket I Y.toFun Z.toFun) X.toFun p +
        VectorField.mlieBracket I (VectorField.mlieBracket I Z.toFun X.toFun) Y.toFun p = 0 := by
  have hL := DCLieBracket_jacobi X Y Z p
  have s1 : VectorField.mlieBracket I (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun p
      = - VectorField.mlieBracket I Z.toFun (VectorField.mlieBracket I X.toFun Y.toFun) p :=
    VectorField.mlieBracket_swap_apply
  have s2 : VectorField.mlieBracket I (VectorField.mlieBracket I Y.toFun Z.toFun) X.toFun p
      = - VectorField.mlieBracket I X.toFun (VectorField.mlieBracket I Y.toFun Z.toFun) p :=
    VectorField.mlieBracket_swap_apply
  have s3 : VectorField.mlieBracket I (VectorField.mlieBracket I Z.toFun X.toFun) Y.toFun p
      = - VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I Z.toFun X.toFun) p :=
    VectorField.mlieBracket_swap_apply
  -- the mixed pair vanishes: [Y,[X,Z]] + [Y,[Z,X]] = [Y, [X,Z]+[Z,X]] = [Y,0] = 0
  have hadd : VectorField.mlieBracket I Y.toFun
        (VectorField.mlieBracket I X.toFun Z.toFun + VectorField.mlieBracket I Z.toFun X.toFun) p
      = VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I X.toFun Z.toFun) p
        + VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I Z.toFun X.toFun) p :=
    VectorField.mlieBracket_add_right
      (DCLieBracket_mdifferentiableAt X Z p) (DCLieBracket_mdifferentiableAt Z X p)
  have hzero : VectorField.mlieBracket I X.toFun Z.toFun + VectorField.mlieBracket I Z.toFun X.toFun
      = (0 : (x : M) → TangentSpace I x) := by
    funext x
    simp [VectorField.mlieBracket_swap_apply (V := X.toFun) (W := Z.toFun) (x := x)]
  have hmix : VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I X.toFun Z.toFun) p
        + VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I Z.toFun X.toFun) p = 0 := by
    rw [← hadd, hzero]; simp
  -- Leibniz form gives [X,[Y,Z]] = -[Z,[X,Y]] + [Y,[X,Z]]
  have hL' : VectorField.mlieBracket I X.toFun (VectorField.mlieBracket I Y.toFun Z.toFun) p
      = - VectorField.mlieBracket I Z.toFun (VectorField.mlieBracket I X.toFun Y.toFun) p
        + VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I X.toFun Z.toFun) p := by
    rw [hL, VectorField.mlieBracket_swap_apply
      (V := VectorField.mlieBracket I X.toFun Y.toFun) (W := Z.toFun)]
  rw [s1, s2, s3, hL']
  have e : (-VectorField.mlieBracket I Z.toFun (VectorField.mlieBracket I X.toFun Y.toFun) p +
      -(-VectorField.mlieBracket I Z.toFun (VectorField.mlieBracket I X.toFun Y.toFun) p +
          VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I X.toFun Z.toFun) p) +
      -VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I Z.toFun X.toFun) p) =
      -(VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I X.toFun Z.toFun) p +
          VectorField.mlieBracket I Y.toFun (VectorField.mlieBracket I Z.toFun X.toFun) p) := by
    abel
  rw [e, hmix, neg_zero]

/-- do Carmo Ch.0, Prop. 5.3: the four structural properties of the Lie bracket of
differentiable vector fields, bundled as a single proposition —
(a) anticommutativity, (b) `ℝ`-bilinearity in the first slot, (c) the cyclic
Jacobi identity, and (d) the Leibniz rule `[fX,gY] = fg[X,Y] + fX(g)Y − gY(f)X`.
Each conjunct is the corresponding narrow bracket lemma. -/
theorem DCLieBracket_properties :
    (∀ (X Y : SmoothVectorField I M) (p : M),
        DCLieBracket X Y p = -DCLieBracket Y X p) ∧
    (∀ (a b : ℝ) (X Y Z : SmoothVectorField I M) (p : M),
        DCLieBracket (a • X + b • Y) Z p
          = a • DCLieBracket X Z p + b • DCLieBracket Y Z p) ∧
    (∀ (X Y Z : SmoothVectorField I M) (p : M),
        VectorField.mlieBracket I (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun p +
          VectorField.mlieBracket I (VectorField.mlieBracket I Y.toFun Z.toFun) X.toFun p +
            VectorField.mlieBracket I (VectorField.mlieBracket I Z.toFun X.toFun) Y.toFun p = 0) ∧
    (∀ (f g : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
        (X Y : SmoothVectorField I M) (p : M),
        DCLieBracket (SmoothVectorField.smul f hf X) (SmoothVectorField.smul g hg Y) p
          = (f p * g p) • DCLieBracket X Y p
            + (f p * NormedSpace.fromTangentSpace (g p) (mfderiv I 𝓘(ℝ, ℝ) g p (X.toFun p)))
                • Y.toFun p
            - (g p * NormedSpace.fromTangentSpace (f p) (mfderiv I 𝓘(ℝ, ℝ) f p (Y.toFun p)))
                • X.toFun p) :=
  ⟨DCLieBracket_antisymm, DCLieBracket_linear_left, DCLieBracket_jacobi_cyclic,
    fun f g hf hg X Y p => DCLieBracket_leibniz f g hf hg X Y p⟩

omit [CompleteSpace E] in
/-- **do Carmo Ch.0, Lemma 5.2 (faithfulness of the action on functions).**
A tangent vector at `p` is determined by its action on differentiable real-valued
functions: if `u v : T_pM` satisfy `df_p(u) = df_p(v)` for every `f : M → ℝ`
differentiable at `p`, then `u = v`.

This is the injectivity direction of the vector-field$\leftrightarrow$derivation
correspondence that underlies the *uniqueness* clause of do Carmo's Lemma 5.2
(there is a unique field `Z` with `Zf = (XY-YX)f`). Mathlib carries no
vector-field$\leftrightarrow$derivation identification; we supply the principle
directly. The witnesses are the affine coordinate functions `q ↦ L(x(q))` for
continuous functionals `L` on the model space, obtained by post-composing the
chart `extChartAt I p`; since `d(extChartAt I p)_p = id` on `T_pM`, the differential
of such a coordinate function at `p` is exactly `L`, and continuous functionals
separate points of a normed space. -/
theorem tangentVector_eq_zero_of_forall_mfderiv {p : M} {u : TangentSpace I p}
    (h : ∀ f : M → ℝ, MDifferentiableAt I 𝓘(ℝ, ℝ) f p →
        mfderiv I 𝓘(ℝ, ℝ) f p u = 0) :
    u = 0 := by
  have key : ∀ L : E →L[ℝ] ℝ, L u = 0 := by
    intro L
    have hchart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) p :=
      (contMDiffAt_extChartAt (I := I) (x := p) (n := 1)).mdifferentiableAt (by norm_num)
    have hL : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (L : E → ℝ) (extChartAt I p p) :=
      (L.contMDiffAt (n := 1)).mdifferentiableAt (by norm_num)
    have hg : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q => L (extChartAt I p q)) p :=
      hL.comp p hchart
    have hval : mfderiv I 𝓘(ℝ, ℝ) (fun q => L (extChartAt I p q)) p u = L u := by
      rw [show (fun q => L (extChartAt I p q)) = (L : E → ℝ) ∘ (extChartAt I p) from rfl,
        mfderiv_comp (I := I) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, ℝ)) p hL hchart,
        ContinuousLinearMap.comp_apply, mfderiv_extChartAt_self,
        ContinuousLinearMap.mfderiv_eq]
      rfl
    rw [← hval]
    exact h _ hg
  exact (SeparatingDual.eq_zero_iff_forall_dual_eq_zero u).2 key

omit [CompleteSpace E] in
/-- The action-on-functions test separates tangent vectors: if `df_p(u) = df_p(v)`
for every real-valued `f` differentiable at `p`, then `u = v`. (The equality form of
`tangentVector_eq_zero_of_forall_mfderiv`.) -/
theorem tangentVector_eq_of_forall_mfderiv {p : M} {u v : TangentSpace I p}
    (h : ∀ f : M → ℝ, MDifferentiableAt I 𝓘(ℝ, ℝ) f p →
        mfderiv I 𝓘(ℝ, ℝ) f p u = mfderiv I 𝓘(ℝ, ℝ) f p v) :
    u = v := by
  rw [← sub_eq_zero]
  refine tangentVector_eq_zero_of_forall_mfderiv (fun f hf => ?_)
  rw [map_sub, h f hf, sub_self]

omit [CompleteSpace E] in
/-- **do Carmo Ch.0, Lemma 5.2 (uniqueness clause).**
Two sections of the tangent bundle that act identically on every differentiable
real-valued function are equal. In particular the bracket field `[X,Y]` is the
*unique* vector field `Z` with `Zf = (XY-YX)f`, completing the machine-checked
content of the uniqueness half of do Carmo's Lemma 5.2. -/
theorem tangentSection_eq_of_forall_mfderiv
    {Z₁ Z₂ : ∀ p : M, TangentSpace I p}
    (h : ∀ (f : M → ℝ) (p : M), MDifferentiableAt I 𝓘(ℝ, ℝ) f p →
        mfderiv I 𝓘(ℝ, ℝ) f p (Z₁ p) = mfderiv I 𝓘(ℝ, ℝ) f p (Z₂ p)) :
    Z₁ = Z₂ := by
  funext p
  exact tangentVector_eq_of_forall_mfderiv (fun f hf => h f p hf)

/-! ### do Carmo Ch.0, Lemma 5.2: the bracket characterization `[X,Y]f = X(Yf) − Y(Xf)`

On a boundaryless manifold we transport Mathlib's normed-space commutator identity
`VectorField.fderiv_apply_lieBracket` through the chart `extChartAt I p`, obtaining the
do-Carmo *existence characterization*: the bracket field `[X,Y]` (= `mlieBracket`) acts on a
smooth real function `f` as the commutator of the derivations `X` and `Y`. Together with the
uniqueness clause `tangentSection_eq_of_forall_mfderiv`, this is the machine-checked content of
`lem:dc-ch0-5-2`. -/

section BracketCharacterization

variable [I.Boundaryless]

omit [CompleteSpace E] in
/-- Chart chain rule: reading `f` through the chart at `p`, the ordinary derivative of the
coordinate representative `f ∘ x⁻¹` at `z` factors as `df` at `x⁻¹(z)` composed with `d(x⁻¹)`. -/
private theorem fderiv_comp_extChartAt_symm {f : M → ℝ} {p : M} {z : E}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I p).symm z))
    (hz : z ∈ (extChartAt I p).target) (w : E) :
    fderiv ℝ (f ∘ (extChartAt I p).symm) z w =
      mfderiv I 𝓘(ℝ, ℝ) f ((extChartAt I p).symm z)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z w) := by
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I p).symm z := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := p) hz
    rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hcomp := mfderiv_comp z hf hsymm
  rw [mfderiv_eq_fderiv] at hcomp
  rw [hcomp]
  rfl

omit [CompleteSpace E] in
/-- On a boundaryless model the chart-inverse differential is invertible at every target
point (the `range I = univ` collapse of `isInvertible_mfderivWithin_extChartAt_symm`). -/
private theorem isInvertible_mfderiv_extChartAt_symm {p : M} {z : E}
    (hz : z ∈ (extChartAt I p).target) :
    (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm z).IsInvertible := by
  have h := isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := p) hz
  rwa [I.range_eq_univ, mfderivWithin_univ] at h

omit [CompleteSpace E] in
/-- **Action transport.** Reading a real function `h` and a section `Z` through the chart at `p`,
the ordinary directional derivative of `h ∘ x⁻¹` along the chart-pullback of `Z` reproduces the
manifold derivation `Z h = dh(Z)` at the corresponding point. This is the chart transport of the
directional-derivative action, the engine of the bracket characterization. -/
private theorem mfderiv_action_eq_fderiv_pullback {h : M → ℝ} {p : M} {z : E}
    (hz : z ∈ (extChartAt I p).target)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h ((extChartAt I p).symm z))
    (Z : Π y : M, TangentSpace I y) :
    fderiv ℝ (h ∘ (extChartAt I p).symm) z
        (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z z) =
      mfderiv I 𝓘(ℝ, ℝ) h ((extChartAt I p).symm z) (Z ((extChartAt I p).symm z)) := by
  rw [fderiv_comp_extChartAt_symm hh hz, VectorField.mpullback_apply,
    (isInvertible_mfderiv_extChartAt_symm hz).self_apply_inverse]

/-- do Carmo's derivation action `Zf : q ↦ df_q(Z_q)` of a section `Z` on a real function `f`,
packaged as a genuine real-valued function via the canonical identification
`TangentSpace 𝓘(ℝ,ℝ) ≃ ℝ` (`NormedSpace.fromTangentSpace`). Definitionally, `DCApply f Z q`
is the tangent value `mfderiv I 𝓘(ℝ,ℝ) f q (Z q)`. -/
def DCApply (f : M → ℝ) (Z : Π y : M, TangentSpace I y) (q : M) : ℝ :=
  NormedSpace.fromTangentSpace (f q) (mfderiv I 𝓘(ℝ, ℝ) f q (Z q))

/-- **do Carmo Ch.0, Lemma 5.2 (existence characterization).**
On a boundaryless manifold the bracket field `[X,Y] = mlieBracket` acts on a smooth real function
`f` as the commutator of the derivations `X` and `Y`:
`[X,Y]f = X(Yf) − Y(Xf)`, i.e. `df([X,Y]) = d(df Y)(X) − d(df X)(Y)`.
Together with the uniqueness clause `tangentSection_eq_of_forall_mfderiv`, this is the
machine-checked content of do Carmo's Lemma 5.2: `Z = [X,Y]` is the unique field with
`Zf = (XY − YX)f`. The proof transports Mathlib's normed-space commutator identity
`VectorField.fderiv_apply_lieBracket` through the chart `extChartAt I p`. -/
theorem mfderiv_mlieBracket_eq_commutator (X Y : SmoothVectorField I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    DCApply f (VectorField.mlieBracket I X.toFun Y.toFun) p =
      DCApply (DCApply f Y.toFun) X.toFun p - DCApply (DCApply f X.toFun) Y.toFun p := by
  haveI hmsm : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  haveI : IsManifold I 2 M := by
    rw [minSmoothness_of_isRCLikeNormedField] at hmsm; exact hmsm
  -- Abbreviations: coordinate function `g` and chart-pullbacks `V`, `W` of the vector fields.
  have hpe : (extChartAt I p).symm (extChartAt I p p) = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source p)
  have hmem : extChartAt I p p ∈ (extChartAt I p).target := mem_extChartAt_target p
  have htopen : IsOpen (extChartAt I p).target := isOpen_extChartAt_target p
  set g : E → ℝ := f ∘ (extChartAt I p).symm with hg
  set V : E → E := VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm X.toFun with hVdef
  set W : E → E := VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Y.toFun with hWdef
  have hfmdiff : ∀ q, MDifferentiableAt I 𝓘(ℝ, ℝ) f q := fun q => (hf q).mdifferentiableAt (by decide)
  -- `g` is `C^∞` at `e₀`.
  have hgC : ContDiffAt ℝ ∞ g (extChartAt I p p) := by
    have h_symm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (Set.range I) (extChartAt I p p) :=
      contMDiffWithinAt_extChartAt_symm_range p hmem
    have hcd : ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I p).symm) (Set.range I) (extChartAt I p p) :=
      ((hf p).comp_contMDiffWithinAt_of_eq h_symm hpe).contDiffWithinAt
    rwa [I.range_eq_univ, contDiffWithinAt_univ] at hcd
  -- The chart-pullbacks `V`, `W` are differentiable at `e₀`.
  have hVdiff : DifferentiableAt ℝ V (extChartAt I p p) := by
    have hXm : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
        (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) Set.univ p :=
      ((X.smooth p).mdifferentiableAt (by decide)).mdifferentiableWithinAt
    have h := hXm.differentiableWithinAt_mpullbackWithin_vectorField
    rw [Set.preimage_univ, Set.univ_inter, I.range_eq_univ, differentiableWithinAt_univ,
      VectorField.mpullbackWithin_univ] at h
    exact h
  have hWdiff : DifferentiableAt ℝ W (extChartAt I p p) := by
    have hYm : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
        (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) Set.univ p :=
      ((Y.smooth p).mdifferentiableAt (by decide)).mdifferentiableWithinAt
    have h := hYm.differentiableWithinAt_mpullbackWithin_vectorField
    rw [Set.preimage_univ, Set.univ_inter, I.range_eq_univ, differentiableWithinAt_univ,
      VectorField.mpullbackWithin_univ] at h
    exact h
  -- **Left-hand side.** The bracket field in coordinates.
  have hLHS : mfderiv I 𝓘(ℝ, ℝ) f p (VectorField.mlieBracket I X.toFun Y.toFun p)
      = fderiv ℝ g (extChartAt I p p) (VectorField.lieBracket ℝ V W (extChartAt I p p)) := by
    have hact := mfderiv_action_eq_fderiv_pullback (h := f) (p := p) (z := extChartAt I p p)
      hmem (by rw [hpe]; exact hfmdiff p) (VectorField.mlieBracket I X.toFun Y.toFun)
    rw [hpe] at hact
    rw [← hact]
    congr 1
    rw [VectorField.mpullback_mlieBracket
        (hpe.symm ▸ (X.smooth p).mdifferentiableAt (by decide))
        (hpe.symm ▸ (Y.smooth p).mdifferentiableAt (by decide))
        ((contMDiffOn_extChartAt_symm p).contMDiffAt (htopen.mem_nhds hmem)) le_rfl,
      ← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin_univ]
  -- **Directional-derivative action in coordinates** (EventuallyEq near `e₀`).
  have hEA : ∀ (Z : SmoothVectorField I M),
      (fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Z.toFun q)) ∘ (extChartAt I p).symm
        =ᶠ[nhds (extChartAt I p p)]
          (fun z => fderiv ℝ g z (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z.toFun z)) := by
    intro Z
    filter_upwards [htopen.mem_nhds hmem] with z hz
    exact (mfderiv_action_eq_fderiv_pullback hz (hfmdiff _) Z.toFun).symm
  -- Each right-hand term matches a term of the normed-space commutator identity.
  have hterm : ∀ (Z₁ Z₂ : SmoothVectorField I M),
      mfderiv I 𝓘(ℝ, ℝ) (fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Z₂.toFun q)) p (Z₁.toFun p)
        = fderiv ℝ (fun z => fderiv ℝ g z
            (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z₂.toFun z))
            (extChartAt I p p)
            (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z₁.toFun (extChartAt I p p)) := by
    intro Z₁ Z₂
    -- `Z₂ f ∘ x⁻¹` is differentiable at `e₀`, hence `Z₂ f` is `MDifferentiable` at `p`.
    have hrhs_diff : DifferentiableAt ℝ
        (fun z => fderiv ℝ g z (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z₂.toFun z))
        (extChartAt I p p) := by
      have hZ₂diff : DifferentiableAt ℝ
          (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z₂.toFun) (extChartAt I p p) := by
        have hZm : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
            (fun y => (⟨y, Z₂.toFun y⟩ : TangentBundle I M)) Set.univ p :=
          ((Z₂.smooth p).mdifferentiableAt (by decide)).mdifferentiableWithinAt
        have h := hZm.differentiableWithinAt_mpullbackWithin_vectorField
        rw [Set.preimage_univ, Set.univ_inter, I.range_eq_univ, differentiableWithinAt_univ,
          VectorField.mpullbackWithin_univ] at h
        exact h
      have hfd : DifferentiableAt ℝ (fun z => fderiv ℝ g z) (extChartAt I p p) :=
        (hgC.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
      exact hfd.clm_apply hZ₂diff
    have hZ₂f_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Z₂.toFun q)) p := by
      have hcomp_diff : DifferentiableAt ℝ
          ((fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Z₂.toFun q)) ∘ (extChartAt I p).symm)
          (extChartAt I p p) :=
        hrhs_diff.congr_of_eventuallyEq (hEA Z₂)
      have hcomp_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
          ((fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Z₂.toFun q)) ∘ (extChartAt I p).symm)
          (extChartAt I p p) :=
        hcomp_diff.mdifferentiableAt
      have hchart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) p :=
        mdifferentiableAt_extChartAt (mem_chart_source H p)
      have hcong : ((fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Z₂.toFun q)) ∘ (extChartAt I p).symm)
          ∘ (extChartAt I p) =ᶠ[nhds p] (fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Z₂.toFun q)) := by
        filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p)]
          with q hq
        show mfderiv I 𝓘(ℝ, ℝ) f ((extChartAt I p).symm (extChartAt I p q))
            (Z₂.toFun ((extChartAt I p).symm (extChartAt I p q)))
          = mfderiv I 𝓘(ℝ, ℝ) f q (Z₂.toFun q)
        rw [(extChartAt I p).left_inv hq]
      exact (hcomp_mdiff.comp p hchart).congr_of_eventuallyEq hcong.symm
    -- transport the manifold derivative into coordinates and rewrite the inner function
    have hact := mfderiv_action_eq_fderiv_pullback
      (h := fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Z₂.toFun q))
      (p := p) (z := extChartAt I p p) hmem (by rw [hpe]; exact hZ₂f_mdiff) Z₁.toFun
    rw [hpe] at hact
    rw [← hact, (hEA Z₂).fderiv_eq]
  -- Assemble via the normed-space commutator identity. Convert the nested `DCApply` inner
  -- functions to the raw derivation action, unfold `DCApply` (definitionally the identity on the
  -- tangent value), rewrite each inner `mfderiv` into coordinates, and close with the
  -- normed-space commutator identity.
  have hYf : DCApply f Y.toFun = fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Y.toFun q) := rfl
  have hXf : DCApply f X.toFun = fun q => mfderiv I 𝓘(ℝ, ℝ) f q (X.toFun q) := rfl
  rw [hYf, hXf]
  simp only [DCApply]
  rw [hLHS, hterm X Y, hterm Y X]
  simp only [← hVdef, ← hWdef]
  rw [VectorField.fderiv_apply_lieBracket (n := ∞) hgC
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
    hWdiff hVdiff]
  rfl

end BracketCharacterization

section FlowLieDerivative

variable [I.Boundaryless]

/-- Evaluating a composition `A ∘ (t ↦ t • v)` at `t = 1` collapses to `A v`.  Auxiliary for
extracting the ordinary derivative of a curve-composite out of the manifold chain rule (which
returns the derivative as `A.comp ((1 : ℝ →L ℝ).smulRight v)`, the `HasFDerivAt` form).  Stated
for topological `ℝ`-modules so it applies to the tangent-space synonyms directly. -/
private theorem comp_smulRight_one_apply {F G : Type*}
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousSMul ℝ F]
    [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] (A : F →L[ℝ] G) (v : F) :
    (A.comp ((1 : ℝ →L[ℝ] ℝ).smulRight v)) (1 : ℝ) = A v := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul]

omit [CompleteSpace E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- `DCApply` unfolds definitionally to the raw tangent action `mfderiv f q (Z q)` (the
`NormedSpace.fromTangentSpace` identification of `TangentSpace 𝓘(ℝ,ℝ)` with `ℝ` is the
identity on values). -/
theorem DCApply_eq_mfderiv (f : M → ℝ) (Z : Π y : M, TangentSpace I y) (q : M) :
    DCApply f Z q = mfderiv I 𝓘(ℝ, ℝ) f q (Z q) := rfl

/-- **do Carmo Ch.0, §5 (local flow of a vector field).**
A *local flow* of the smooth vector field `X` near `p` is a map `φ : ℝ → M → M` with
`φ 0 = id`, each trajectory `t ↦ φ t q` an integral curve of `X` (`∂ₜφ = X∘φ`,
`φ(0,·)=id`), and joint `C^∞` dependence on `(t, q)`.  This is do Carmo's
`φ : (-δ,δ) × U → M` from the discussion preceding Prop. 5.4.  The *existence* of such a `φ`
for a smooth `X` is the smooth dependence-on-initial-conditions theorem (the variational
equation), which is not yet available from Mathlib's Picard–Lindelöf theory (that supplies
only existence, uniqueness, and continuous dependence); so here we take the flow as data. -/
structure IsLocalFlow (X : SmoothVectorField I M) (φ : ℝ → M → M) (p : M) : Prop where
  /-- The time-zero map is the identity. -/
  flow_zero : ∀ q, φ 0 q = q
  /-- Each trajectory `t ↦ φ t q` is an integral curve of `X` at time `0`. -/
  isIntegralCurve : ∀ q, IsMIntegralCurveAt (fun t => φ t q) X.toFun 0
  /-- Joint smoothness of the flow in `(time, base point)`. -/
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun tq : ℝ × M => φ tq.1 tq.2)

/-- The directional derivative `Yf : q ↦ df_q(Y_q)` of a smooth function `f` along a smooth
vector field `Y` is `MDifferentiable` at every point.  (This is the differentiability content
of the bracket-commutator characterisation `mfderiv_mlieBracket_eq_commutator`: reading `f`
through the chart, `f ∘ x⁻¹` is `C^∞` and the chart pullback of `Y` is differentiable, so
`Yf ∘ x⁻¹` is differentiable, hence `Yf` is `MDifferentiableAt`.) -/
theorem DCApply_mdifferentiableAt (Y : SmoothVectorField I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (DCApply f Y.toFun) p := by
  show MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Y.toFun q)) p
  have hpe : (extChartAt I p).symm (extChartAt I p p) = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source p)
  have hmem : extChartAt I p p ∈ (extChartAt I p).target := mem_extChartAt_target p
  have htopen : IsOpen (extChartAt I p).target := isOpen_extChartAt_target p
  set g : E → ℝ := f ∘ (extChartAt I p).symm with hg
  have hfmdiff : ∀ q, MDifferentiableAt I 𝓘(ℝ, ℝ) f q := fun q => (hf q).mdifferentiableAt (by decide)
  have hgC : ContDiffAt ℝ ∞ g (extChartAt I p p) := by
    have h_symm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (Set.range I) (extChartAt I p p) :=
      contMDiffWithinAt_extChartAt_symm_range p hmem
    have hcd : ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I p).symm) (Set.range I) (extChartAt I p p) :=
      ((hf p).comp_contMDiffWithinAt_of_eq h_symm hpe).contDiffWithinAt
    rwa [I.range_eq_univ, contDiffWithinAt_univ] at hcd
  have hEA : (fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Y.toFun q)) ∘ (extChartAt I p).symm
        =ᶠ[nhds (extChartAt I p p)]
          (fun z => fderiv ℝ g z (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Y.toFun z)) := by
    filter_upwards [htopen.mem_nhds hmem] with z hz
    exact (mfderiv_action_eq_fderiv_pullback hz (hfmdiff _) Y.toFun).symm
  have hrhs_diff : DifferentiableAt ℝ
      (fun z => fderiv ℝ g z (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Y.toFun z))
      (extChartAt I p p) := by
    have hZ₂diff : DifferentiableAt ℝ
        (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Y.toFun) (extChartAt I p p) := by
      have hZm : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E))
          (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) Set.univ p :=
        ((Y.smooth p).mdifferentiableAt (by decide)).mdifferentiableWithinAt
      have h := hZm.differentiableWithinAt_mpullbackWithin_vectorField
      rw [Set.preimage_univ, Set.univ_inter, I.range_eq_univ, differentiableWithinAt_univ,
        VectorField.mpullbackWithin_univ] at h
      exact h
    have hfd : DifferentiableAt ℝ (fun z => fderiv ℝ g z) (extChartAt I p p) :=
      (hgC.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
    exact hfd.clm_apply hZ₂diff
  have hcomp_diff : DifferentiableAt ℝ
      ((fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Y.toFun q)) ∘ (extChartAt I p).symm)
      (extChartAt I p p) :=
    hrhs_diff.congr_of_eventuallyEq hEA
  have hcomp_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      ((fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Y.toFun q)) ∘ (extChartAt I p).symm)
      (extChartAt I p p) :=
    hcomp_diff.mdifferentiableAt
  have hchart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) p :=
    mdifferentiableAt_extChartAt (mem_chart_source H p)
  have hcong : ((fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Y.toFun q)) ∘ (extChartAt I p).symm)
      ∘ (extChartAt I p) =ᶠ[nhds p] (fun q => mfderiv I 𝓘(ℝ, ℝ) f q (Y.toFun q)) := by
    filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p)]
      with q hq
    show mfderiv I 𝓘(ℝ, ℝ) f ((extChartAt I p).symm (extChartAt I p q))
        (Y.toFun ((extChartAt I p).symm (extChartAt I p q)))
      = mfderiv I 𝓘(ℝ, ℝ) f q (Y.toFun q)
    rw [(extChartAt I p).left_inv hq]
  exact (hcomp_mdiff.comp p hchart).congr_of_eventuallyEq hcong.symm

omit [CompleteSpace E] in
/-- Joint coordinate representative of the flow-composite `Ψ(t,z) = f(φ_t(x⁻¹ z))` is `C^∞`
at the base point `(0, x p)`.  This is the analytic input to do Carmo Prop. 5.4 that the
`IsLocalFlow` structure supplies as data: joint smoothness of `φ` in `(time, base point)`
(`hφ.smooth`), read through the chart at `p`, composed with the smooth `f`. -/
private theorem contDiffAt_flowChartComp {X : SmoothVectorField I M} {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M} {φ : ℝ → M → M} (hφ : IsLocalFlow X φ p) :
    ContDiffAt ℝ ∞
      (fun tz : ℝ × E => f (φ tz.1 ((extChartAt I p).symm tz.2)))
      (0, extChartAt I p p) := by
  set c : E := extChartAt I p p with hc
  have hmem : c ∈ (extChartAt I p).target := mem_extChartAt_target p
  have hpe : (extChartAt I p).symm c = p := (extChartAt I p).left_inv (mem_extChartAt_source p)
  -- chart inverse is `C^∞` at `c` (boundaryless ⇒ `range I = univ`)
  have hxsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm c := by
    have h : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (Set.range I) c :=
      contMDiffWithinAt_extChartAt_symm_range p hmem
    rwa [I.range_eq_univ, contMDiffWithinAt_univ] at h
  -- `Prod.map id x⁻¹` is `C^∞` at `(0, c)`
  have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
      (Prod.map (id : ℝ → ℝ) (extChartAt I p).symm) ((0 : ℝ), c) :=
    (contMDiffAt_id).prodMap hxsymm
  -- the given flow is jointly `C^∞`
  have hflow : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun tq : ℝ × M => φ tq.1 tq.2)
      (Prod.map (id : ℝ → ℝ) (extChartAt I p).symm ((0 : ℝ), c)) := hφ.smooth _
  -- compose flow with the chart map, then with `f`
  have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun tz : ℝ × E => f (φ tz.1 ((extChartAt I p).symm tz.2))) ((0 : ℝ), c) := by
    have hΦ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
        (fun tz : ℝ × E => φ tz.1 ((extChartAt I p).symm tz.2)) ((0 : ℝ), c) :=
      hflow.comp ((0 : ℝ), c) hmap
    have hfΦ := hf ((fun tz : ℝ × E => φ tz.1 ((extChartAt I p).symm tz.2)) ((0 : ℝ), c))
    exact hfΦ.comp ((0 : ℝ), c) hΦ
  -- convert `ContMDiffAt` over the product-of-self models to `ContDiffAt`
  rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hcomp

omit [CompleteSpace E] in
/-- **Bridge (chart slice ⇒ manifold derivation).**  Reading `Ψ(t,z) = f(φ_t(x⁻¹ z))` in the
chart at `p`, the partial `z`-derivative of `Ψ(t,·)` at `x p` along the chart-pullback of `Y`
reproduces the manifold derivation `Y(f∘φ_t)(p) = d(f∘φ_t)_p(Y_p)`.  This transports the
`E`-slice `fderiv` of the joint coordinate representative back to `mfderiv` on `M`, using
`mfderiv_action_eq_fderiv_pullback`; it is used both for `t` near `0` (the `A`-slope numerator)
and at `t = 0` (the base value). -/
private theorem flowChart_slice_eq_mfderiv (Y : SmoothVectorField I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M} {φ : ℝ → M → M}
    (hφsmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun tq : ℝ × M => φ tq.1 tq.2)) (t : ℝ)
    (hdiff : DifferentiableAt ℝ
        (fun tz : ℝ × E => f (φ tz.1 ((extChartAt I p).symm tz.2)))
        (t, extChartAt I p p)) :
    fderiv ℝ (fun tz : ℝ × E => f (φ tz.1 ((extChartAt I p).symm tz.2)))
          (t, extChartAt I p p)
          (0, VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Y.toFun (extChartAt I p p))
      = mfderiv I 𝓘(ℝ, ℝ) (fun q => f (φ t q)) p (Y.toFun p) := by
  set c : E := extChartAt I p p with hc
  have hmem : c ∈ (extChartAt I p).target := mem_extChartAt_target p
  have hpe : (extChartAt I p).symm c = p := (extChartAt I p).left_inv (mem_extChartAt_source p)
  -- `q ↦ f(φ t q)` is `MDifferentiableAt` at `p`
  have hφt : ContMDiffAt I I ∞ (fun q => φ t q) p := by
    have hcm : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ (fun tq : ℝ × M => φ tq.1 tq.2) (t, p) := hφsmooth _
    have hmk : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞ (fun q : M => (t, q)) p :=
      (contMDiffAt_const).prodMk contMDiffAt_id
    exact hcm.comp p hmk
  have hff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun q => f (φ t q)) p :=
    ((hf _).mdifferentiableAt (by decide)).comp p (hφt.mdifferentiableAt (by decide))
  -- slice: `fderiv Ψ (t,c) (0,w) = fderiv (Ψ(t,·)) c w`
  have hmk2 : HasFDerivAt (fun z : E => ((t, z) : ℝ × E))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) c :=
    (hasFDerivAt_const t c).prodMk (hasFDerivAt_id c)
  have hslice := hdiff.hasFDerivAt.comp c hmk2
  have happ : fderiv ℝ (fun tz : ℝ × E => f (φ tz.1 ((extChartAt I p).symm tz.2))) (t, c)
        (0, VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Y.toFun c)
      = fderiv ℝ ((fun q => f (φ t q)) ∘ (extChartAt I p).symm) c
          (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Y.toFun c) := by
    rw [show ((fun q => f (φ t q)) ∘ (extChartAt I p).symm)
          = (fun tz : ℝ × E => f (φ tz.1 ((extChartAt I p).symm tz.2))) ∘ (fun z : E => (t, z))
        from rfl, hslice.fderiv]
    rfl
  rw [happ, mfderiv_action_eq_fderiv_pullback hmem (by rw [hpe]; exact hff) Y.toFun, hpe]

/-- **L2 (the analytic residue of do Carmo Prop. 5.4 — flow-Hadamard term).**
The `B`-slope `t ↦ (Y(f∘φ_t)(p) − Yf(p))/t` converges to `Y(Xf)(p)`.  Reading everything in
the chart at `p`, the numerator is `G(t) − G(0)` where `G(t) = ∂_{vY} Ψ(t, ·)|_{x p}` is the
`vY`-directional derivative of the joint coordinate representative `Ψ(t,z) = f(φ_t(x⁻¹ z))`.
Since `Ψ` is jointly `C^∞` (the flow's joint smoothness `hφ.smooth` read through the chart,
`contDiffAt_flowChartComp`), the mixed second partial `∂_t ∂_{vY} Ψ` at `(0, x p)` equals
`∂_{vY} ∂_t Ψ` by symmetry of the second derivative (`ContDiffAt.isSymmSndFDerivAt`), and the
inner time-partial `∂_t Ψ(0, z) = df_{x⁻¹ z}(X)` is fixed by the integral-curve equation.  Hence
the slope tends to `∂_{vY}(Xf)(p) = Y(Xf)(p)`.  The differentiable dependence of `φ` on the base
point is supplied by `IsLocalFlow.smooth`, so no additional Mathlib flow infrastructure is
needed. -/
theorem DCLieBracket_flow_slope_right (X Y : SmoothVectorField I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M} {φ : ℝ → M → M} (hφ : IsLocalFlow X φ p) :
    Filter.Tendsto
      (fun t => (DCApply (fun q => f (φ t q)) Y.toFun p - DCApply f Y.toFun p) / t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (DCApply (DCApply f X.toFun) Y.toFun p)) := by
  set c : E := extChartAt I p p with hc
  set Ψ : ℝ × E → ℝ := fun tz => f (φ tz.1 ((extChartAt I p).symm tz.2)) with hΨdef
  set vY : E := VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Y.toFun c with hvYdef
  have hmem : c ∈ (extChartAt I p).target := mem_extChartAt_target p
  have hpe : (extChartAt I p).symm c = p := (extChartAt I p).left_inv (mem_extChartAt_source p)
  have hΨc : ContDiffAt ℝ ∞ Ψ (0, c) := contDiffAt_flowChartComp hf hφ
  have hΨdiff : DifferentiableAt ℝ Ψ (0, c) := hΨc.differentiableAt (by simp)
  -- `Ψ` is differentiable on a neighborhood of `(0,c)`
  have hev : ∀ᶠ y in 𝓝 ((0 : ℝ), c), DifferentiableAt ℝ Ψ y := by
    have h1 : ContDiffAt ℝ (1 : WithTop ℕ∞) Ψ (0, c) :=
      hΨc.of_le (WithTop.coe_le_coe.mpr le_top)
    exact (h1.eventually (by simp)).mono fun _ hy => hy.differentiableAt one_ne_zero
  -- second derivative and its symmetry
  have hle : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top
  have hsymm := hΨc.isSymmSndFDerivAt hle
  have hdiffD1 : DifferentiableAt ℝ (fun q => fderiv ℝ Ψ q) (0, c) :=
    (hΨc.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hD1 : HasFDerivAt (fun q => fderiv ℝ Ψ q) (fderiv ℝ (fun q => fderiv ℝ Ψ q) (0, c)) (0, c) :=
    hdiffD1.hasFDerivAt
  set sd := fderiv ℝ (fun q => fderiv ℝ Ψ q) (0, c) with hsd
  -- the `A`-slope function `G t = ∂_{vY} Ψ(t,·)(c)`, and its derivative at 0 via symmetry
  set G : ℝ → ℝ := fun t => fderiv ℝ Ψ (t, c) ((0 : ℝ), vY) with hGdef
  -- `P q = ∂_{vY} Ψ` and `Q q = ∂_t Ψ` (differentiable near `(0,c)`)
  have hPf : HasFDerivAt (fun q => fderiv ℝ Ψ q ((0 : ℝ), vY))
      ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), vY)).comp sd) (0, c) :=
    (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), vY)).hasFDerivAt.comp (0, c) hD1
  have hQf : HasFDerivAt (fun q => fderiv ℝ Ψ q ((1 : ℝ), (0 : E)))
      ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).comp sd) (0, c) :=
    (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).hasFDerivAt.comp (0, c) hD1
  have hγ : HasFDerivAt (fun t : ℝ => (t, c))
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) (0 : ℝ) :=
    (hasFDerivAt_id (0 : ℝ)).prodMk (hasFDerivAt_const c (0 : ℝ))
  -- `HasDerivAt G ((sd (1,0)) (0,vY)) 0`
  have hGderiv : HasDerivAt G (sd ((1 : ℝ), (0 : E)) ((0 : ℝ), vY)) 0 := by
    have h := (hPf.comp (0 : ℝ) hγ).hasDerivAt
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, hGdef] using h
  -- identify the derivative with the target via symmetry + the inner time-partial
  have hQ0 : (fun z : E => fderiv ℝ Ψ ((0 : ℝ), z) ((1 : ℝ), (0 : E)))
      =ᶠ[𝓝 c] (fun z : E => DCApply f X.toFun ((extChartAt I p).symm z)) := by
    -- `Ψ` is differentiable on a neighborhood of `(0,c)`, hence at `(0,z)` for `z` near `c`
    have hcont : Filter.Tendsto (fun z : E => ((0 : ℝ), z)) (𝓝 c) (𝓝 ((0 : ℝ), c)) := by
      have : Continuous (fun z : E => ((0 : ℝ), z)) := by fun_prop
      simpa using this.tendsto c
    filter_upwards [hcont.eventually hev] with z hz
    -- time-slice: `fderiv Ψ (0,z) (1,0) = deriv (fun t => Ψ(t,z)) 0`
    have hmk : HasFDerivAt (fun t : ℝ => (t, z))
        ((ContinuousLinearMap.id ℝ ℝ).prod 0) (0 : ℝ) :=
      (hasFDerivAt_id (0 : ℝ)).prodMk (hasFDerivAt_const z (0 : ℝ))
    have hslice := (hz.hasFDerivAt.comp (0 : ℝ) hmk).hasDerivAt
    -- integral-curve equation gives the value
    have hγc := (hφ.isIntegralCurve ((extChartAt I p).symm z)).hasMFDerivAt
    have hfz : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I p).symm z) :=
      (hf _).mdifferentiableAt (by decide)
    have hgz := hfz.hasMFDerivAt
    rw [← hφ.flow_zero ((extChartAt I p).symm z)] at hgz
    have hcompz := hgz.comp (0 : ℝ) hγc
    rw [hasMFDerivAt_iff_hasFDerivAt] at hcompz
    have hderivz := hcompz.hasDerivAt
    -- the derivative value at 0 is `df(X)` by the integral-curve equation (as in L1)
    have hHD : HasDerivAt (fun t => f (φ t ((extChartAt I p).symm z)))
        (DCApply f X.toFun ((extChartAt I p).symm z)) 0 := by
      rw [DCApply_eq_mfderiv]
      convert hderivz using 1
      rw [hφ.flow_zero]
      exact (comp_smulRight_one_apply _ _).symm
    calc fderiv ℝ Ψ ((0 : ℝ), z) ((1 : ℝ), (0 : E))
        = deriv (fun t => Ψ (t, z)) 0 := by
          simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
            ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using hslice.deriv.symm
      _ = DCApply f X.toFun ((extChartAt I p).symm z) := hHD.deriv
  -- assemble `HasDerivAt G target 0` by symmetry of the mixed second partial
  have htarget : sd ((1 : ℝ), (0 : E)) ((0 : ℝ), vY)
      = DCApply (DCApply f X.toFun) Y.toFun p := by
    rw [hsymm.eq ((1 : ℝ), (0 : E)) ((0 : ℝ), vY)]
    -- `sd (0,vY) (1,0) = fderiv Q (0,c) (0,vY)` where `Q q = ∂_t Ψ q`
    have hQfd : fderiv ℝ (fun q => fderiv ℝ Ψ q ((1 : ℝ), (0 : E))) (0, c)
        = (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).comp sd := hQf.fderiv
    have hstep1 : sd ((0 : ℝ), vY) ((1 : ℝ), (0 : E))
        = fderiv ℝ (fun q => fderiv ℝ Ψ q ((1 : ℝ), (0 : E))) (0, c) ((0 : ℝ), vY) := by
      rw [hQfd]; rfl
    -- slice: `fderiv Q (0,c) (0,vY) = fderiv (Q(0,·)) c vY`
    have hmkz : HasFDerivAt (fun z : E => ((0 : ℝ), z))
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) c :=
      (hasFDerivAt_const (0 : ℝ) c).prodMk (hasFDerivAt_id c)
    have hslicez := (hQf.differentiableAt.hasFDerivAt.comp c hmkz).fderiv
    have hstep2 : fderiv ℝ (fun q => fderiv ℝ Ψ q ((1 : ℝ), (0 : E))) (0, c) ((0 : ℝ), vY)
        = fderiv ℝ (fun z : E => fderiv ℝ Ψ ((0 : ℝ), z) ((1 : ℝ), (0 : E))) c vY := by
      rw [show (fun z : E => fderiv ℝ Ψ ((0 : ℝ), z) ((1 : ℝ), (0 : E)))
            = (fun q => fderiv ℝ Ψ q ((1 : ℝ), (0 : E))) ∘ (fun z : E => ((0 : ℝ), z)) from rfl,
        hslicez]
      rfl
    -- transport back to the manifold via the eventual identity and the action lemma
    have hstep3 : fderiv ℝ (fun z : E => fderiv ℝ Ψ ((0 : ℝ), z) ((1 : ℝ), (0 : E))) c vY
        = DCApply (DCApply f X.toFun) Y.toFun p := by
      rw [hQ0.fderiv_eq,
        show (fun z : E => DCApply f X.toFun ((extChartAt I p).symm z))
            = (DCApply f X.toFun) ∘ (extChartAt I p).symm from rfl,
        mfderiv_action_eq_fderiv_pullback hmem (by rw [hpe]; exact DCApply_mdifferentiableAt X hf _)
          Y.toFun, hpe]
      exact (DCApply_eq_mfderiv (DCApply f X.toFun) Y.toFun p).symm
    rw [hstep1, hstep2, hstep3]
  rw [htarget] at hGderiv
  -- bridge the slope to `G`, then use the derivative
  have hfeq0 : (fun q => f (φ 0 q)) = f := by funext q; rw [hφ.flow_zero q]
  have hAG : (fun t => DCApply (fun q => f (φ t q)) Y.toFun p) =ᶠ[𝓝 (0 : ℝ)] G := by
    have hcontt : Filter.Tendsto (fun t : ℝ => (t, c)) (𝓝 0) (𝓝 ((0 : ℝ), c)) := by
      have : Continuous (fun t : ℝ => (t, c)) := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [hcontt.eventually hev] with t ht
    show DCApply (fun q => f (φ t q)) Y.toFun p = fderiv ℝ Ψ (t, c) ((0 : ℝ), vY)
    rw [DCApply_eq_mfderiv]
    exact (flowChart_slice_eq_mfderiv Y hf hφ.smooth t ht).symm
  have hB : DCApply f Y.toFun p = G 0 := by
    show DCApply f Y.toFun p = fderiv ℝ Ψ (0, c) ((0 : ℝ), vY)
    rw [flowChart_slice_eq_mfderiv Y hf hφ.smooth 0 hΨdiff, hfeq0]
    exact DCApply_eq_mfderiv f Y.toFun p
  -- convert to slope tendsto
  have hslopeG := hasDerivAt_iff_tendsto_slope.mp hGderiv
  refine hslopeG.congr' ?_
  filter_upwards [self_mem_nhdsWithin, (hAG.filter_mono nhdsWithin_le_nhds)] with t ht htAG
  rw [slope_def_field, hB, htAG]
  ring

/-- **do Carmo Ch.0, Prop. 5.4 — the bracket as a Lie derivative along the flow.**
For a local flow `φ` of `X` near `p`, the bracket `[X,Y]` is recovered as the `t = 0`
derivative of the flow-transported field `Y − dφ_t Y`, tested against a smooth `f`.  In
derivation form,
`df_p([X,Y]) = lim_{t→0} (1/t)·(df_{φ_t p}(Y) − d(f∘φ_t)_p(Y))`, whose right-hand terms are
do Carmo's `(Yf)(φ_t p)` and `((dφ_t Y)f)(φ_t p) = Y(f∘φ_t)(p)`.  Splitting the difference
quotient around the common value `Yf(p)`, the first slope tends to `X(Yf)(p)` (derivative of
`Yf` along the integral curve of `X`, `DCLieBracket`'s `DCApply_mdifferentiableAt` + the
integral-curve equation) and the second to `Y(Xf)(p)` (`DCLieBracket_flow_slope_right`, via
Hadamard's lemma).  Their difference is `X(Yf)(p) − Y(Xf)(p) = [X,Y]f(p)` by
`mfderiv_mlieBracket_eq_commutator`. -/
theorem DCLieBracket_eq_flow_lieDerivative (X Y : SmoothVectorField I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M} {φ : ℝ → M → M} (hφ : IsLocalFlow X φ p) :
    Filter.Tendsto
      (fun t => (DCApply f Y.toFun (φ t p) - DCApply (fun q => f (φ t q)) Y.toFun p) / t)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (DCApply f (VectorField.mlieBracket I X.toFun Y.toFun) p)) := by
  have hcomm := mfderiv_mlieBracket_eq_commutator X Y hf p
  have hφ0 : φ 0 p = p := hφ.flow_zero p
  -- **L1**: the `A`-slope tends to `X(Yf)(p)`, i.e. the derivative of `Yf` along the flow.
  have hL1 : Filter.Tendsto
      (fun t => (DCApply f Y.toFun (φ t p) - DCApply f Y.toFun p) / t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (DCApply (DCApply f Y.toFun) X.toFun p)) := by
    have hYfp : MDifferentiableAt I 𝓘(ℝ, ℝ) (DCApply f Y.toFun) p :=
      DCApply_mdifferentiableAt Y hf p
    have hγ := (hφ.isIntegralCurve p).hasMFDerivAt
    have hg := hYfp.hasMFDerivAt
    rw [← hφ0] at hg
    have hcomp := hg.comp (0 : ℝ) hγ
    rw [hasMFDerivAt_iff_hasFDerivAt] at hcomp
    have hderiv := hcomp.hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hderiv
    have hfun : (fun t => (DCApply f Y.toFun (φ t p) - DCApply f Y.toFun p) / t)
        = slope (DCApply f Y.toFun ∘ fun t => φ t p) 0 := by
      funext t
      rw [slope_def_field, Function.comp_apply, Function.comp_apply, hφ0, sub_zero]
    rw [hfun]
    convert hderiv using 2
    rw [hφ0, DCApply_eq_mfderiv]
    exact (comp_smulRight_one_apply _ _).symm
  -- **L2**: the `B`-slope tends to `Y(Xf)(p)` (Hadamard-in-chart residue).
  have hL2 := DCLieBracket_flow_slope_right X Y hf hφ
  -- Split the difference quotient around the common value `Yf(p)` and combine.
  have hsplit : (fun t => (DCApply f Y.toFun (φ t p) - DCApply (fun q => f (φ t q)) Y.toFun p) / t)
      = fun t => (DCApply f Y.toFun (φ t p) - DCApply f Y.toFun p) / t
          - (DCApply (fun q => f (φ t q)) Y.toFun p - DCApply f Y.toFun p) / t := by
    funext t
    rw [div_sub_div_same]
    congr 1
    ring
  rw [hsplit, hcomm]
  exact hL1.sub hL2

end FlowLieDerivative

/-! ### §5 (Lem. 5.5): Hadamard's lemma

The analytic ingredient behind `prop:dc-ch0-5-4` (bracket as Lie derivative along
the flow): a differentiable `h(t,q)` with `h(0,q)=0` factors as `h(t,q)=t·g(t,q)`,
where the remainder `g(t,q)=∫₀¹ ∂ₜh(st,q) ds` satisfies `g(0,q)=∂ₜh(0,q)`. The
factoring and the value at `t=0` are unconditional; joint continuity of `g` holds
whenever the partial `∂ₜh` is jointly continuous, and joint *differentiability* of
`g` (needed to apply a vector field to `g(t,·)`) holds when `∂ₜh` is jointly `C¹`
over a finite-dimensional parameter space — matching do Carmo's smooth `U ⊆ ℝⁿ`.
See `OpenGALib/Riemannian/Manifold/HadamardLemma.lean`. -/
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
theorem DCHadamardFactor {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {h : ℝ → E → F} {pd : ℝ → E → F}
    (hderiv : ∀ q u, HasDerivAt (fun u => h u q) (pd u q) u)
    (hcont : ∀ q, Continuous fun u => pd u q) (h0 : ∀ q, h 0 q = 0) (t : ℝ) (q : E) :
    h t q = t • Hadamard.remainder pd t q ∧ Hadamard.remainder pd 0 q = pd 0 q :=
  ⟨Hadamard.eq_smul_remainder hderiv hcont h0 t q, Hadamard.remainder_zero pd q⟩

omit [CompleteSpace E] in
/-- do Carmo Ch.0, Lem. 5.5 (Hadamard's lemma), full form.  A map `h(t,q)` with
`h(0,q)=0` whose first-variable partial `∂ₜh = pd` is jointly `C¹` (over a
finite-dimensional parameter space `E`, matching do Carmo's `U ⊆ ℝⁿ`) factors as
`h(t,q)=t·g(t,q)` with `g` jointly **differentiable** and `g(0,q)=∂ₜh(0,q)`.  This
is the complete statement: existence of a differentiable remainder, closing the
differentiability content left open by the continuous factoring package. -/
theorem DCHadamardFactorDiff [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {h : ℝ → E → F} {pd : ℝ → E → F}
    (hderiv : ∀ q u, HasDerivAt (fun u => h u q) (pd u q) u)
    (hpd : ContDiff ℝ 1 (Function.uncurry pd)) (h0 : ∀ q, h 0 q = 0) :
    ∃ g : ℝ → E → F, Differentiable ℝ (Function.uncurry g)
      ∧ (∀ t q, h t q = t • g t q) ∧ (∀ q, g 0 q = pd 0 q) := by
  have hcont : ∀ q, Continuous fun u => pd u q := fun q =>
    hpd.continuous.comp (continuous_id.prodMk continuous_const)
  exact ⟨Hadamard.remainder pd, Hadamard.differentiable_remainder hpd,
    fun t q => Hadamard.eq_smul_remainder hderiv hcont h0 t q,
    fun q => Hadamard.remainder_zero pd q⟩

/-- do Carmo Ch.0, Example 4.1: the tangent bundle `TM`, wired to Mathlib's
`TangentBundle`. -/
abbrev DCTangentBundle : Type _ := TangentBundle I M

omit [CompleteSpace E] in
/-- do Carmo Ch.0, Example 4.1: the tangent bundle `TM` is itself a smooth
manifold, modelled on `H × E` (dimension `2n` when `M` has dimension `n`). -/
theorem DCTangentBundle.isManifold :
    IsManifold (I.prod 𝓘(ℝ, E)) ∞ (DCTangentBundle (I := I) (M := M)) :=
  inferInstance

/-- do Carmo Ch.0, §4 (Def. 4.4): `M` is *orientable* if it admits a
differentiable structure — a family `𝒜` of charts covering `M`, contained in the
maximal `C^∞` atlas — all of whose transition maps have everywhere-positive
Jacobian determinant. A mathlib chart plays the role of do Carmo's parametrization
`x_α` read backwards (a chart is `x_α⁻¹`), so the change of coordinates
`x_β⁻¹ ∘ x_α` is represented on the model space `E` by
`(f.extend I) ∘ (f'.extend I).symm`. Its Fréchet derivative is the differential of
do Carmo's change of coordinates, and requiring `0 < det` on every overlap is
exactly do Carmo's orientation condition (i). Finite-dimensionality of `E` makes
the determinant meaningful, matching do Carmo's `ℝⁿ`-modelled manifolds. -/
def DCIsOrientable [FiniteDimensional ℝ E] : Prop :=
  ∃ 𝒜 : Set (OpenPartialHomeomorph M H),
    𝒜 ⊆ IsManifold.maximalAtlas I ∞ M ∧
    (⋃ f ∈ 𝒜, (f : OpenPartialHomeomorph M H).source) = Set.univ ∧
    ∀ f ∈ 𝒜, ∀ f' ∈ 𝒜, ∀ x ∈ ((f'.extend I).symm.trans (f.extend I)).source,
      0 < (fderiv ℝ (↑(f.extend I) ∘ ↑(f'.extend I).symm) x).det

/-- do Carmo Ch.0 smooth partition of unity, wired to Mathlib's structure. -/
abbrev DCSmoothPartitionOfUnity (ι : Type*) (s : Set M := Set.univ) : Type _ :=
  SmoothPartitionOfUnity ι I M s

omit [CompleteSpace E] [IsManifold I ∞ M] in
/-- A smooth partition of unity sums to one on the set it covers. -/
theorem DCSmoothPartitionOfUnity.sum_eq_one {ι : Type*} {s : Set M}
    (ρ : DCSmoothPartitionOfUnity (I := I) (M := M) ι s) {p : M} (hp : p ∈ s) :
    ∑ᶠ i, ρ i p = 1 :=
  SmoothPartitionOfUnity.sum_eq_one ρ hp

omit [CompleteSpace E] in
/-- do Carmo Ch.0, Thm. 5.6 (existence direction): a Hausdorff, `σ`-compact
(i.e. countable-basis) finite-dimensional smooth manifold admits, for every open
cover `U` of a closed set `s`, a smooth partition of unity subordinate to `U`.
This is the analytic content of do Carmo's partition-of-unity theorem; the
topological hypotheses are exactly Hausdorff + countable basis. -/
theorem DCSmoothPartitionOfUnity.exists_isSubordinate
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    {ι : Type*} {s : Set M} (hs : IsClosed s) (U : ι → Set M)
    (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ ρ : DCSmoothPartitionOfUnity (I := I) (M := M) ι s, ρ.IsSubordinate U :=
  SmoothPartitionOfUnity.exists_isSubordinate (I := I) hs U ho hU

/-! ### Thm. 5.6, "only if" direction: second countability forced by a partition of unity

do Carmo's Theorem 5.6 is an *equivalence*: a manifold `M` admits a differentiable
partition of unity iff every connected component of `M` is Hausdorff and has a
countable basis.  The "if" direction is `exists_isSubordinate` above.  Here we
machine-check the topological heart of the harder "only if" direction — that a
partition of unity forces each component to be second countable.

do Carmo's partition of unity `{f_α}` comes with a locally finite family of
coordinate neighborhoods `{V_α}` (axiom (2)) whose union is `M` (because
`∑_α f_α = 1` puts every point in some `supp f_α ⊆ V_α`), each `V_α` being
homeomorphic to an open subset of `ℝⁿ` and hence `σ`-compact.  The general
topological fact below turns exactly this data — on a *connected* space — into
`σ`-compactness; combined with `ChartedSpace.secondCountable_of_sigmaCompact`
this yields second countability of each component. -/

section SigmaCompactFromCover

variable {X : Type*} [TopologicalSpace X] {ι : Type*}

/-- **A connected space carrying a locally finite open cover by `σ`-compact sets is
`σ`-compact.**  This is the topological core of the "only if" direction of do Carmo's
Theorem 5.6.  Local finiteness makes each `σ`-compact cover member meet only countably
many others, so the family reachable (through chains of overlaps) from any fixed index
is countable.  The union of that reachable family is open (a union of opens), closed
(any boundary point lies in a cover member meeting the union, hence in the reachable
family), so clopen — thus everything, by connectedness — and it is a countable union of
`σ`-compact sets, whence the whole space is `σ`-compact. -/
theorem sigmaCompactSpace_of_locallyFinite_isSigmaCompact_cover
    [PreconnectedSpace X] {V : ι → Set X}
    (hopen : ∀ i, IsOpen (V i)) (hsc : ∀ i, IsSigmaCompact (V i))
    (hlf : LocallyFinite V) (hcov : ⋃ i, V i = Set.univ) :
    SigmaCompactSpace X := by
  classical
  by_cases hex : ∃ i₀, (V i₀).Nonempty
  · obtain ⟨i₀, hi₀⟩ := hex
    -- Each cover member meets only countably many others (local finiteness + `σ`-compact).
    have hnbhd : ∀ i, {j | (V i ∩ V j).Nonempty}.Countable := by
      intro i
      obtain ⟨K, hKc, hKU⟩ := hsc i
      have hsub : {j | (V i ∩ V j).Nonempty} ⊆ ⋃ n, {j | (V j ∩ K n).Nonempty} := by
        intro j hj
        obtain ⟨x, hxi, hxj⟩ := hj
        rw [← hKU] at hxi
        obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxi
        exact Set.mem_iUnion.mpr ⟨n, ⟨x, hxj, hxn⟩⟩
      refine (Set.countable_iUnion (fun n => ?_)).mono hsub
      exact (hlf.finite_nonempty_inter_compact (hKc n)).countable
    -- The family reachable from `i₀` through chains of overlaps, built layer by layer.
    set nbhd : ι → Set ι := fun i => {j | (V i ∩ V j).Nonempty} with hnbhd_def
    set step : Set ι → Set ι := fun S => S ∪ ⋃ i ∈ S, nbhd i with hstep_def
    set A : ℕ → Set ι := fun n => step^[n] {i₀} with hA_def
    have hAsucc : ∀ n, A (n + 1) = step (A n) := fun n => Function.iterate_succ_apply' _ _ _
    have hAcount : ∀ n, (A n).Countable := by
      intro n
      induction n with
      | zero => exact Set.countable_singleton _
      | succ k ih =>
        rw [hAsucc]
        exact ih.union (ih.biUnion (fun i _ => hnbhd i))
    set Areach : Set ι := ⋃ n, A n with hAreach_def
    have hAreach_count : Areach.Countable := Set.countable_iUnion hAcount
    have hi₀A : i₀ ∈ Areach := Set.mem_iUnion.mpr ⟨0, Set.mem_singleton _⟩
    have hclosed_under : ∀ {i j : ι}, i ∈ Areach → (V i ∩ V j).Nonempty → j ∈ Areach := by
      intro i j hi hij
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hi
      refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
      rw [hAsucc]
      exact Or.inr (Set.mem_biUnion hn hij)
    -- The union over the reachable family is clopen.
    set U : Set X := ⋃ i ∈ Areach, V i with hU_def
    have hUopen : IsOpen U := isOpen_biUnion (fun i _ => hopen i)
    have hUne : U.Nonempty := by
      obtain ⟨x, hx⟩ := hi₀; exact ⟨x, Set.mem_biUnion hi₀A hx⟩
    have hUclosed : IsClosed U := by
      rw [← closure_subset_iff_isClosed]
      intro x hx
      have hxuniv : x ∈ ⋃ i, V i := hcov ▸ Set.mem_univ x
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxuniv
      obtain ⟨y, hyj, hyU⟩ := mem_closure_iff.mp hx (V j) (hopen j) hxj
      obtain ⟨i, hiA, hyi⟩ := Set.mem_iUnion₂.mp hyU
      exact Set.mem_biUnion (hclosed_under hiA ⟨y, hyi, hyj⟩) hxj
    have hUuniv : U = Set.univ := (IsClopen.eq_univ ⟨hUclosed, hUopen⟩ hUne)
    have hSC : IsSigmaCompact U := isSigmaCompact_biUnion hAreach_count (fun i _ => hsc i)
    rw [hUuniv] at hSC
    exact isSigmaCompact_univ_iff.mp hSC
  · -- No cover member is nonempty: the whole space is empty, hence `σ`-compact.
    simp only [not_exists, Set.not_nonempty_iff_eq_empty] at hex
    have huniv : (Set.univ : Set X) = ∅ := by
      rw [← hcov, Set.iUnion_eq_empty]
      exact hex
    refine isSigmaCompact_univ_iff.mp ?_
    rw [huniv]; exact isSigmaCompact_empty

end SigmaCompactFromCover

/-- **do Carmo Ch.0, Thm. 5.6 ("only if" direction, second-countability half).**  A
*connected* manifold `M` (charted over a second-countable model `H`) that carries a
locally finite open cover by `σ`-compact sets is second countable.  do Carmo's
partition of unity supplies exactly such a cover: its coordinate neighborhoods `{V_α}`
are locally finite (axiom (2)), cover `M` (since `∑_α f_α = 1`), and are each `σ`-compact
(being homeomorphic to open subsets of `ℝⁿ`).  Thus a connected manifold admitting a
differentiable partition of unity has a countable basis — the "only if" direction of the
theorem, applied component by component.  (The complementary claim that a partition of
unity also forces each component to be Hausdorff is the Brickell–Clark input that is not
wired here.) -/
theorem DCSecondCountable_of_locallyFinite_isSigmaCompact_cover
    [PreconnectedSpace M] [SecondCountableTopology H]
    {ι : Type*} {V : ι → Set M} (hopen : ∀ i, IsOpen (V i))
    (hsc : ∀ i, IsSigmaCompact (V i)) (hlf : LocallyFinite V)
    (hcov : ⋃ i, V i = Set.univ) :
    SecondCountableTopology M := by
  haveI : SigmaCompactSpace M :=
    sigmaCompactSpace_of_locallyFinite_isSigmaCompact_cover hopen hsc hlf hcov
  exact ChartedSpace.secondCountable_of_sigmaCompact H M

omit [CompleteSpace E] [IsManifold I ∞ M] in
/-- **do Carmo Ch.0, Thm. 5.6 ("only if" direction) from an honest partition of unity.**
A *connected* manifold `M` (charted over a second-countable model `H`) that admits a
differentiable partition of unity `ρ` subordinate to a locally finite family `{V_α}` of
`σ`-compact coordinate neighborhoods is second countable.  This is the faithful form of do
Carmo's "only if" second-countability conclusion: the covering hypothesis is now *derived*
from the partition itself, since `∑_α ρ_α ≡ 1` forces every point into some
`supp ρ_α ⊆ tsupport ρ_α ⊆ V_α`.  (The complementary Hausdorff-forcing half of "only if"
remains the Brickell–Clark input, not wired here.) -/
theorem DCSecondCountable_of_partitionOfUnity
    [PreconnectedSpace M] [SecondCountableTopology H]
    {ι : Type*} (ρ : DCSmoothPartitionOfUnity (I := I) (M := M) ι Set.univ)
    {V : ι → Set M} (hopen : ∀ i, IsOpen (V i)) (hsc : ∀ i, IsSigmaCompact (V i))
    (hlf : LocallyFinite V) (hsub : ρ.IsSubordinate V) :
    SecondCountableTopology M := by
  have hcov : ⋃ i, V i = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro p
    have hsum : ∑ᶠ i, ρ i p = 1 := ρ.sum_eq_one (Set.mem_univ p)
    have hne : ∃ i, ρ i p ≠ 0 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      simp only [h, finsum_zero] at hsum
      exact one_ne_zero hsum.symm
    obtain ⟨i, hi⟩ := hne
    have hmem : p ∈ tsupport (ρ i) := subset_closure hi
    exact Set.mem_iUnion.mpr ⟨i, hsub i hmem⟩
  exact DCSecondCountable_of_locallyFinite_isSigmaCompact_cover (H := H) hopen hsc hlf hcov

omit [CompleteSpace E] [IsManifold I ∞ M] in
/-- **do Carmo Ch.0, Thm. 5.6 ("only if" direction, Hausdorff half).**  A manifold `M`
admitting a differentiable partition of unity `ρ` subordinate to a family `{V_α}` of open
Hausdorff coordinate neighborhoods is itself Hausdorff.  This is the half do Carmo delegates
to Brickell–Clark; the partition of unity provides exactly the missing separation data.

Given two points `p ≠ q` with no disjoint neighborhoods, the filter `𝓝 p ⊓ 𝓝 q` is proper,
so every continuous `ρ_α` — being determined as a limit along that filter — satisfies
`ρ_α p = ρ_α q`.  Since `∑_α ρ_α ≡ 1`, some `ρ_α` is nonzero at `p`, hence also at `q`;
thus both points lie in `supp ρ_α ⊆ V_α`.  But `V_α` is an *open Hausdorff* coordinate
neighborhood, so `p` and `q` are separated inside `V_α` by sets that are open in `M` — a
contradiction.  Hence `M` is Hausdorff. -/
theorem t2Space_of_partitionOfUnity
    {ι : Type*} (ρ : DCSmoothPartitionOfUnity (I := I) (M := M) ι Set.univ)
    {V : ι → Set M} (hopen : ∀ i, IsOpen (V i)) (hT2 : ∀ i, T2Space (V i))
    (hsub : ρ.IsSubordinate V) :
    T2Space M := by
  refine t2Space_iff_disjoint_nhds.mpr (fun p q hpq => ?_)
  by_contra hcon
  haveI : (𝓝 p ⊓ 𝓝 q).NeBot := ⟨fun h => hcon (disjoint_iff.mpr h)⟩
  -- Every partition function takes the same value at `p` and `q`.
  have hagree : ∀ i, ρ i p = ρ i q := by
    intro i
    have hcont : Continuous (ρ i) := (ρ.toFun i).2.continuous
    exact tendsto_nhds_unique
      ((hcont.tendsto p).mono_left inf_le_left)
      ((hcont.tendsto q).mono_left inf_le_right)
  -- `∑_α ρ_α(p) = 1` puts `p`, hence also `q`, into one coordinate neighborhood `V i`.
  have hsum : ∑ᶠ i, ρ i p = 1 := ρ.sum_eq_one (Set.mem_univ p)
  have hne : ∃ i, ρ i p ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    simp only [h, finsum_zero] at hsum
    exact one_ne_zero hsum.symm
  obtain ⟨i, hi⟩ := hne
  have hpV : p ∈ V i := hsub i (subset_closure hi)
  have hqi : ρ i q ≠ 0 := (hagree i) ▸ hi
  have hqV : q ∈ V i := hsub i (subset_closure hqi)
  -- Separate `p`, `q` inside the open Hausdorff neighborhood `V i`, then push up to `M`.
  haveI := hT2 i
  obtain ⟨u, v, hu, hv, hpu, hqv, huv⟩ :=
    t2_separation (X := V i) (x := ⟨p, hpV⟩) (y := ⟨q, hqV⟩)
      (by simpa only [ne_eq, Subtype.mk.injEq] using hpq)
  have hemb : Topology.IsOpenEmbedding (Subtype.val : V i → M) :=
    (hopen i).isOpenEmbedding_subtypeVal
  have hpU : p ∈ Subtype.val '' u := ⟨⟨p, hpV⟩, hpu, rfl⟩
  have hqW : q ∈ Subtype.val '' v := ⟨⟨q, hqV⟩, hqv, rfl⟩
  have hdisjUV : Disjoint (Subtype.val '' u) (Subtype.val '' v) :=
    Set.disjoint_image_of_injective Subtype.val_injective huv
  exact hcon (Filter.disjoint_of_disjoint_of_mem hdisjUV
    ((hemb.isOpenMap u hu).mem_nhds hpU) ((hemb.isOpenMap v hv).mem_nhds hqW))

omit [CompleteSpace E] [IsManifold I ∞ M] in
/-- **do Carmo Ch.0, Thm. 5.6, complete "only if" direction.**  A *connected* manifold `M`
charted over a second-countable model `H` that admits a differentiable partition of unity
`ρ` subordinate to a locally finite family `{V_α}` of open, Hausdorff, `σ`-compact
coordinate neighborhoods satisfies *both* manifold topology axioms: `M` is Hausdorff and has
a countable basis.  Combined with `DCSmoothPartitionOfUnity.exists_isSubordinate` (the "if"
direction), this is the full content of do Carmo's Theorem 5.6, applied component by
component.  Both halves are now machine-checked; nothing is delegated to Brickell–Clark. -/
theorem DCManifoldAxioms_of_partitionOfUnity
    [PreconnectedSpace M] [SecondCountableTopology H]
    {ι : Type*} (ρ : DCSmoothPartitionOfUnity (I := I) (M := M) ι Set.univ)
    {V : ι → Set M} (hopen : ∀ i, IsOpen (V i)) (hsc : ∀ i, IsSigmaCompact (V i))
    (hT2 : ∀ i, T2Space (V i)) (hlf : LocallyFinite V) (hsub : ρ.IsSubordinate V) :
    T2Space M ∧ SecondCountableTopology M :=
  ⟨t2Space_of_partitionOfUnity ρ hopen hT2 hsub,
    DCSecondCountable_of_partitionOfUnity ρ hopen hsc hlf hsub⟩

/-! ### §2 (Thm. 2.10): the inverse function theorem on manifolds

do Carmo's Theorem 2.10 states that if `dφ_p` is an isomorphism then `φ` is a local
diffeomorphism at `p`.  Mathlib records this as an open `TODO` in
`Mathlib.Geometry.Manifold.LocalDiffeomorph`.  The reduction to the normed-space
inverse function theorem uses two structural facts, packaged here as reusable
local-diffeomorphism lemmas: an extended chart (and its inverse) is a local
diffeomorphism onto the model space, and being a local diffeomorphism at a point is
stable under passing to a locally equal map. -/

/-- Composition of `C^n` local diffeomorphisms. If `f` is a `C^n` local diffeomorphism at `x`
and `g` is a `C^n` local diffeomorphism at `f x`, then `g ∘ f` is a `C^n` local diffeomorphism
at `x`. -/
theorem IsLocalDiffeomorphAt.comp
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
    {N₁ : Type*} [TopologicalSpace N₁] [ChartedSpace H₁ N₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
    {N₂ : Type*} [TopologicalSpace N₂] [ChartedSpace H₂ N₂]
    {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    {H₃ : Type*} [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
    {N₃ : Type*} [TopologicalSpace N₃] [ChartedSpace H₃ N₃]
    {n : WithTop ℕ∞} {g : N₂ → N₃} {f : N₁ → N₂} {x : N₁}
    (hg : IsLocalDiffeomorphAt I₂ I₃ n g (f x)) (hf : IsLocalDiffeomorphAt I₁ I₂ n f x) :
    IsLocalDiffeomorphAt I₁ I₃ n (g ∘ f) x := by
  obtain ⟨Φ, hyΦ, hgΦ⟩ := hg
  obtain ⟨Ψ, hxΨ, hfΨ⟩ := hf
  have hΨx : Ψ x = f x := (hfΨ hxΨ).symm
  have hxΦ : Ψ x ∈ Φ.source := hΨx ▸ hyΦ
  refine ⟨{ toPartialEquiv := Ψ.toPartialEquiv.trans Φ.toPartialEquiv
            open_source := by
              rw [PartialEquiv.trans_source]
              exact Ψ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
                Ψ.open_source Φ.open_source
            open_target := by
              rw [PartialEquiv.trans_target]
              exact Φ.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage
                Φ.open_target Ψ.open_target
            contMDiffOn_toFun := by
              rw [PartialEquiv.trans_source]
              simp only [PartialEquiv.coe_trans]
              exact Φ.contMDiffOn_toFun.comp
                (Ψ.contMDiffOn_toFun.mono Set.inter_subset_left) (fun z hz => hz.2)
            contMDiffOn_invFun := by
              rw [PartialEquiv.trans_target]
              show ContMDiffOn I₃ I₁ n
                (Ψ.toPartialEquiv.invFun ∘ Φ.toPartialEquiv.invFun) _
              exact Ψ.contMDiffOn_invFun.comp
                (Φ.contMDiffOn_invFun.mono Set.inter_subset_left) (fun z hz => hz.2) },
    ?_, ?_⟩
  · show x ∈ (Ψ.toPartialEquiv.trans Φ.toPartialEquiv).source
    rw [PartialEquiv.trans_source]; exact ⟨hxΨ, hxΦ⟩
  · intro z hz
    show (g ∘ f) z = (Ψ.toPartialEquiv.trans Φ.toPartialEquiv) z
    rw [PartialEquiv.trans_source] at hz
    simp only [Function.comp_apply, PartialEquiv.coe_trans]
    rw [hfΨ hz.1, hgΦ hz.2]

/-- An extended chart is a topological embedding on its source: `M`'s source carries the
topology induced from the model space `E` through `extChartAt I x`.  Universe-general
companion to `isInducing_extend_restrict`, stated directly for `extChartAt`. -/
theorem isInducing_extChartAt_source_restrict
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    Topology.IsInducing ((extChartAt I x).source.restrict (extChartAt I x)) := by
  have hsrc : ∀ z : ↥(extChartAt I x).source, z.1 ∈ (chartAt H x).source := by
    intro z; rw [← extChartAt_source (I := I)]; exact z.2
  have hhom : Topology.IsInducing (chartAt H x).toHomeomorphSourceTarget :=
    (chartAt H x).toHomeomorphSourceTarget.isInducing
  have hval : Topology.IsInducing (Subtype.val : ↥(chartAt H x).target → H) :=
    Topology.IsInducing.subtypeVal
  have hsource_ind : Topology.IsInducing ((chartAt H x).source.restrict (chartAt H x)) := by
    have h2 := hval.comp hhom; convert h2 using 1
  have hincl : Topology.IsEmbedding
      (fun z : ↥(extChartAt I x).source => (⟨z.1, hsrc z⟩ : ↥(chartAt H x).source)) :=
    Topology.IsEmbedding.subtypeVal.codRestrict (chartAt H x).source hsrc
  have hI : Topology.IsInducing (I : H → E) :=
    I.isClosedEmbedding.isEmbedding.isInducing
  have hcomp := (hI.comp hsource_ind).comp hincl.toIsInducing
  convert hcomp using 1

section InverseFunctionTheorem

variable [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

omit [CompleteSpace E] [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace E']
  [I'.Boundaryless] [IsManifold I' ∞ M'] in
/-- Being a `C^∞` local diffeomorphism at a point is stable under passing to a map that
agrees with it on a neighbourhood. -/
theorem IsLocalDiffeomorphAt.congr_of_eventuallyEq {f f₁ : M → M'} {x : M}
    (hf : IsLocalDiffeomorphAt I I' ∞ f x) (h : f₁ =ᶠ[𝓝 x] f) :
    IsLocalDiffeomorphAt I I' ∞ f₁ x := by
  obtain ⟨Φ, hxΦ, hEq⟩ := hf
  rw [Filter.eventuallyEq_iff_exists_mem] at h
  obtain ⟨O, hO_mem, hO⟩ := h
  obtain ⟨U, hU_sub, hU_open, hxU⟩ := mem_nhds_iff.1 hO_mem
  have hcont_symm : ContinuousOn Φ.toPartialEquiv.symm Φ.toPartialEquiv.target :=
    Φ.contMDiffOn_invFun.continuousOn
  refine ⟨{ toPartialEquiv := Φ.toPartialEquiv.restr U
            open_source := by
              rw [PartialEquiv.restr_source]; exact Φ.open_source.inter hU_open
            open_target := by
              rw [PartialEquiv.restr_target]
              exact hcont_symm.isOpen_inter_preimage Φ.open_target hU_open
            contMDiffOn_toFun := by
              rw [PartialEquiv.restr_source]
              exact Φ.contMDiffOn_toFun.mono Set.inter_subset_left
            contMDiffOn_invFun := by
              rw [PartialEquiv.restr_target]
              exact Φ.contMDiffOn_invFun.mono Set.inter_subset_left }, ?_, ?_⟩
  · show x ∈ (Φ.toPartialEquiv.restr U).source
    rw [PartialEquiv.restr_source]; exact ⟨hxΦ, hxU⟩
  · intro y hy
    rw [PartialEquiv.restr_source] at hy
    show f₁ y = Φ.toPartialEquiv y
    rw [hO (hU_sub hy.2)]; exact hEq hy.1

omit [CompleteSpace E] in
/-- An extended chart is a `C^∞` local diffeomorphism onto the model space at each of its
points. -/
theorem isLocalDiffeomorphAt_extChartAt {x : M} :
    IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ (extChartAt I x) x :=
  ⟨{ toPartialEquiv := (extChartAt I x)
     open_source := isOpen_extChartAt_source x
     open_target := isOpen_extChartAt_target x
     contMDiffOn_toFun := by rw [extChartAt_source]; exact contMDiffOn_extChartAt
     contMDiffOn_invFun := contMDiffOn_extChartAt_symm x },
    mem_extChartAt_source x, Set.eqOn_refl _ _⟩

omit [CompleteSpace E] in
/-- The inverse of an extended chart is a `C^∞` local diffeomorphism from the model space
back to the manifold at each point of its domain. -/
theorem isLocalDiffeomorphAt_extChartAt_symm {x : M} {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm y :=
  ⟨{ toPartialEquiv := (extChartAt I x).symm
     open_source := isOpen_extChartAt_target x
     open_target := isOpen_extChartAt_source x
     contMDiffOn_toFun := contMDiffOn_extChartAt_symm x
     contMDiffOn_invFun := by
       simp only [PartialEquiv.symm_target]
       rw [extChartAt_source]; exact contMDiffOn_extChartAt },
    hy, Set.eqOn_refl _ _⟩

/-- **Normed-space inverse function theorem, local-diffeomorphism form.**  If `g` is
`C^∞` on an open set `U ∋ a` and its Fréchet derivative at `a` is a continuous linear
equivalence, then `g` is a `C^∞` local diffeomorphism (in the trivial manifold model) at
`a`. This is the analytic core behind the manifold inverse function theorem
`thm:dc-ch0-2-10`: the manifold statement follows by transporting this through charts. -/
theorem isLocalDiffeomorphAt_of_hasFDerivAt_equiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
    {g : F → F'} {a : F} {g' : F ≃L[ℝ] F'} {U : Set F}
    (hU : IsOpen U) (haU : a ∈ U) (hg : ContDiffOn ℝ ∞ g U)
    (hg' : HasFDerivAt g (g' : F →L[ℝ] F') a) :
    IsLocalDiffeomorphAt 𝓘(ℝ, F) 𝓘(ℝ, F') ∞ g a := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have h1n : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
  have hgAt : ContDiffAt ℝ ∞ g a := (hg a haU).contDiffAt (hU.mem_nhds haU)
  -- The open set of points of `U` where `g` has an invertible derivative.
  have hGopen : IsOpen (Set.range ((↑) : (F ≃L[ℝ] F') → F →L[ℝ] F')) :=
    ContinuousLinearEquiv.isOpen
  have hfderiv_cont : ContinuousOn (fderiv ℝ g) U :=
    hg.continuousOn_fderiv_of_isOpen hU h1n
  set S : Set F := U ∩ (fderiv ℝ g) ⁻¹' (Set.range ((↑) : (F ≃L[ℝ] F') → F →L[ℝ] F'))
    with hSdef
  have hSopen : IsOpen S := hfderiv_cont.isOpen_inter_preimage hU hGopen
  have haS : a ∈ S := ⟨haU, by
    rw [Set.mem_preimage, hg'.fderiv]; exact ⟨g', rfl⟩⟩
  -- Local data at every point of `S`.
  have hS_data : ∀ x ∈ S, ContDiffAt ℝ ∞ g x ∧
      ∃ e : F ≃L[ℝ] F', HasFDerivAt g (e : F →L[ℝ] F') x := by
    intro x hx
    have hgx : ContDiffAt ℝ ∞ g x := (hg x hx.1).contDiffAt (hU.mem_nhds hx.1)
    obtain ⟨e, he⟩ := hx.2
    refine ⟨hgx, e, ?_⟩
    have hd : HasFDerivAt g (fderiv ℝ g x) x := (hgx.differentiableAt hn).hasFDerivAt
    rwa [← he] at hd
  -- The inverse-function-theorem partial homeomorph at `a`, restricted to `S`.
  set φ := hgAt.toOpenPartialHomeomorph g hg' hn with hφ
  have hφcoe : ⇑φ = g := hgAt.toOpenPartialHomeomorph_coe hg' hn
  have haφ : a ∈ φ.source := hgAt.mem_toOpenPartialHomeomorph_source hg' hn
  set ψ := φ.restrOpen S hSopen with hψ
  have hψsrc : ψ.source = φ.source ∩ S := φ.restrOpen_source S hSopen
  have hψtgt : ψ.target = φ.target ∩ ⇑φ.symm ⁻¹' S := by
    rw [hψ, OpenPartialHomeomorph.restrOpen_toPartialEquiv]
    exact PartialEquiv.restr_target _ _
  refine ⟨{ toPartialEquiv := ψ.toPartialEquiv
            open_source := ψ.open_source
            open_target := ψ.open_target
            contMDiffOn_toFun := ?_
            contMDiffOn_invFun := ?_ }, ?_, ?_⟩
  · rw [contMDiffOn_iff_contDiffOn]
    have hsub : ψ.source ⊆ U := by rw [hψsrc]; exact fun x hx => hx.2.1
    exact (hg.mono hsub)
  · rw [contMDiffOn_iff_contDiffOn]
    intro y hy
    rw [hψtgt] at hy
    have hyt : y ∈ φ.target := hy.1
    have hxS : ⇑φ.symm y ∈ S := hy.2
    obtain ⟨hgx, e, hex⟩ := hS_data _ hxS
    have hgx' : ContDiffAt ℝ ∞ (⇑φ) (φ.symm y) := by rw [hφcoe]; exact hgx
    have hex' : HasFDerivAt (⇑φ) (e : F →L[ℝ] F') (φ.symm y) := by rw [hφcoe]; exact hex
    exact (φ.contDiffAt_symm hyt hex' hgx').contDiffWithinAt
  · rw [hψsrc]; exact ⟨haφ, haS⟩
  · intro x hx; rfl

/-- **do Carmo Ch.0, Thm. 2.10 — the manifold inverse function theorem.**  If `f : M → M'`
is `C^∞` and its differential `df_p : T_pM → T_{f p}M'` is a continuous linear equivalence,
then `f` is a `C^∞` local diffeomorphism at `p`. Mathlib records this statement as an open
`TODO`; the proof transports the normed-space inverse function theorem
`isLocalDiffeomorphAt_of_hasFDerivAt_equiv` through the charts at `p` and `f p` using the
chart local-diffeomorphisms and their composition. -/
theorem isLocalDiffeomorphAt_of_mfderiv_equiv {f : M → M'} {p : M}
    (hf : ContMDiff I I' ∞ f) {g' : E ≃L[ℝ] E'}
    (hg' : mfderiv I I' f p = (g' : E →L[ℝ] E')) :
    IsLocalDiffeomorphAt I I' ∞ f p := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  set x₀ := extChartAt I p p with hx₀
  set g := writtenInExtChartAt I I' p f with hgdef
  have hfp : MDifferentiableAt I I' f p := hf.mdifferentiableAt hn
  -- The differential of `f` at `p` is the Fréchet derivative of the chart representative.
  have hmf : mfderiv I I' f p = fderiv ℝ g x₀ := by
    rw [hfp.mfderiv, I.range_eq_univ, fderivWithin_univ]
  have hgdiff : DifferentiableAt ℝ g x₀ := by
    have h := hfp.differentiableWithinAt_writtenInExtChartAt
    rwa [I.range_eq_univ, differentiableWithinAt_univ] at h
  have hHF : HasFDerivAt g (g' : E →L[ℝ] E') x₀ := by
    have h := hgdiff.hasFDerivAt
    rw [show fderiv ℝ g x₀ = (g' : E →L[ℝ] E') by rw [← hmf, hg']] at h
    exact h
  -- The chart representative is `C^∞` on an open neighbourhood of `x₀`.
  set s : Set E := (extChartAt I p).target ∩
    (extChartAt I p).symm ⁻¹' (f ⁻¹' (extChartAt I' (f p)).source) with hsdef
  have hpre_open : IsOpen (f ⁻¹' (extChartAt I' (f p)).source) :=
    hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source (f p))
  have hs_open : IsOpen s :=
    (continuousOn_extChartAt_symm p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) hpre_open
  have hx₀s : x₀ ∈ s := by
    refine ⟨mem_extChartAt_target p, ?_⟩
    rw [Set.mem_preimage, hx₀, (extChartAt I p).left_inv (mem_extChartAt_source p)]
    exact mem_extChartAt_source (f p)
  have hg_cd : ContDiffOn ℝ ∞ g s := by
    rw [← contMDiffOn_iff_contDiffOn]
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I p).symm s :=
      (contMDiffOn_extChartAt_symm p).mono Set.inter_subset_left
    have hf_univ : ContMDiffOn I I' ∞ f Set.univ := hf.contMDiffOn
    have hfs : ContMDiffOn 𝓘(ℝ, E) I' ∞ (f ∘ (extChartAt I p).symm) s :=
      hf_univ.comp hsymm (fun x _ => Set.mem_univ _)
    apply (contMDiffOn_extChartAt (I := I') (x := f p)).comp hfs
    intro y hy
    show f ((extChartAt I p).symm y) ∈ (chartAt H' (f p)).source
    rw [← extChartAt_source I']
    exact hy.2
  -- Analytic inverse function theorem in the model space.
  have hg_ld : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E') ∞ g x₀ :=
    isLocalDiffeomorphAt_of_hasFDerivAt_equiv hs_open hx₀s hg_cd hHF
  -- Assemble `f = chart⁻¹ ∘ g ∘ chart` from the three local diffeomorphisms.
  have hc1 : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ (extChartAt I p) p :=
    isLocalDiffeomorphAt_extChartAt
  have comp1 : IsLocalDiffeomorphAt I 𝓘(ℝ, E') ∞ (g ∘ extChartAt I p) p :=
    IsLocalDiffeomorphAt.comp hg_ld hc1
  have hpt : (g ∘ extChartAt I p) p = extChartAt I' (f p) (f p) := by
    have hli : (extChartAt I p).symm (extChartAt I p p) = p :=
      (extChartAt I p).left_inv (mem_extChartAt_source p)
    simp only [Function.comp_apply, hgdef, writtenInExtChartAt, hli]
  have hc2 : IsLocalDiffeomorphAt 𝓘(ℝ, E') I' ∞ (extChartAt I' (f p)).symm
      ((g ∘ extChartAt I p) p) := by
    rw [hpt]
    exact isLocalDiffeomorphAt_extChartAt_symm (mem_extChartAt_target (f p))
  have comp2 : IsLocalDiffeomorphAt I I' ∞
      ((extChartAt I' (f p)).symm ∘ (g ∘ extChartAt I p)) p :=
    IsLocalDiffeomorphAt.comp hc2 comp1
  refine IsLocalDiffeomorphAt.congr_of_eventuallyEq comp2 ?_
  have h1 : ∀ᶠ z in 𝓝 p, z ∈ (extChartAt I p).source := extChartAt_source_mem_nhds p
  have h2 : ∀ᶠ z in 𝓝 p, f z ∈ (extChartAt I' (f p)).source :=
    hf.continuous.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (f p))
  filter_upwards [h1, h2] with z hz1 hz2
  show f z = (extChartAt I' (f p)).symm (g (extChartAt I p z))
  rw [hgdef, writtenInExtChartAt, Function.comp_apply, Function.comp_apply,
    (extChartAt I p).left_inv hz1, (extChartAt I' (f p)).left_inv hz2]

open Topology in
omit [CompleteSpace E] [CompleteSpace E'] [I'.Boundaryless] in
/-- **do Carmo Ch.0, Prop. 3.7 — every immersion is locally an embedding.**  If
`f : M → M'` is `C^∞` and an immersion (its differential `df_q` is injective at every point),
then every `p ∈ M` has an open neighbourhood `V` on which `f` restricts to a *topological
embedding*.  The proof transports do Carmo's chart computation: in extended charts `f`
becomes a map `g : E → E'` with `dg` injective, to which the normed-space local immersion
normal form `isEmbedding_restrict_of_hasFDerivAt_injective` applies; the resulting embedding
is carried back to `M` through the (inducing) coordinate charts. -/
theorem DCIsImmersion.exists_isEmbedding_restrict
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    {f : M → M'} (hf : ContMDiff I I' ∞ f)
    (himm : DCIsImmersion (I := I) (I' := I') f) (p : M) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ IsEmbedding (V.restrict f) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  set x₀ := extChartAt I p p with hx₀
  set g := writtenInExtChartAt I I' p f with hgdef
  have hfp : MDifferentiableAt I I' f p := hf.mdifferentiableAt hn
  have hmf : mfderiv I I' f p = fderiv ℝ g x₀ := by
    rw [hfp.mfderiv, I.range_eq_univ, fderivWithin_univ]
  have hgdiff : DifferentiableAt ℝ g x₀ := by
    have h := hfp.differentiableWithinAt_writtenInExtChartAt
    rwa [I.range_eq_univ, differentiableWithinAt_univ] at h
  have hHF : HasFDerivAt g (fderiv ℝ g x₀) x₀ := hgdiff.hasFDerivAt
  have hLinj : Function.Injective (fderiv ℝ g x₀) := by rw [← hmf]; exact himm p
  -- The chart representative `g` is `C^∞` on an open neighbourhood `s` of `x₀`.
  set s : Set E := (extChartAt I p).target ∩
    (extChartAt I p).symm ⁻¹' (f ⁻¹' (extChartAt I' (f p)).source) with hsdef
  have hpre_open : IsOpen (f ⁻¹' (extChartAt I' (f p)).source) :=
    hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source (f p))
  have hs_open : IsOpen s :=
    (continuousOn_extChartAt_symm p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) hpre_open
  have hx₀s : x₀ ∈ s := by
    refine ⟨mem_extChartAt_target p, ?_⟩
    rw [Set.mem_preimage, hx₀, (extChartAt I p).left_inv (mem_extChartAt_source p)]
    exact mem_extChartAt_source (f p)
  have hg_cd : ContDiffOn ℝ ∞ g s := by
    rw [← contMDiffOn_iff_contDiffOn]
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I p).symm s :=
      (contMDiffOn_extChartAt_symm p).mono Set.inter_subset_left
    have hf_univ : ContMDiffOn I I' ∞ f Set.univ := hf.contMDiffOn
    have hfs : ContMDiffOn 𝓘(ℝ, E) I' ∞ (f ∘ (extChartAt I p).symm) s :=
      hf_univ.comp hsymm (fun x _ => Set.mem_univ _)
    apply (contMDiffOn_extChartAt (I := I') (x := f p)).comp hfs
    intro y hy
    show f ((extChartAt I p).symm y) ∈ (chartAt H' (f p)).source
    rw [← extChartAt_source I']
    exact hy.2
  -- Normed-space local immersion normal form.
  obtain ⟨V₀, hV0_open, hx₀V0, hEmb0⟩ :=
    isEmbedding_restrict_of_hasFDerivAt_injective hs_open hx₀s hg_cd hHF hLinj
  -- The neighbourhood in `M`.
  set U : Set M := (extChartAt I p).source ∩ f ⁻¹' (extChartAt I' (f p)).source with hUdef
  have hU_open : IsOpen U :=
    (isOpen_extChartAt_source p).inter hpre_open
  have hcontU : ContinuousOn (extChartAt I p) U :=
    (continuousOn_extChartAt p).mono Set.inter_subset_left
  set V : Set M := U ∩ (extChartAt I p) ⁻¹' V₀ with hVdef
  have hV_open : IsOpen V := hcontU.isOpen_inter_preimage hU_open hV0_open
  have hpV : p ∈ V :=
    ⟨⟨mem_extChartAt_source p, mem_extChartAt_source (f p)⟩, hx₀V0⟩
  refine ⟨V, hV_open, hpV, ?_⟩
  -- Membership projections for points of `V`.
  have hcsrc : ∀ z : ↥V, z.1 ∈ (extChartAt I p).source := fun z => z.2.1.1
  have hfmem : ∀ z : ↥V, f z.1 ∈ (extChartAt I' (f p)).source := fun z => z.2.1.2
  have hcmem : ∀ z : ↥V, extChartAt I p z.1 ∈ V₀ := fun z => z.2.2
  -- On `V`, `g ∘ (extChartAt I p) = (extChartAt I' (f p)) ∘ f`.
  have hgc : ∀ z : ↥V, g (extChartAt I p z.1) = extChartAt I' (f p) (f z.1) := by
    intro z
    have : g (extChartAt I p z.1)
        = extChartAt I' (f p) (f ((extChartAt I p).symm (extChartAt I p z.1))) := rfl
    rw [this, (extChartAt I p).left_inv (hcsrc z)]
  -- Both extended charts are inducing on their sources.
  have hc_ind : IsInducing ((extChartAt I p).source.restrict (extChartAt I p)) :=
    isInducing_extChartAt_source_restrict (I := I) p
  have hc'_ind :
      IsInducing ((extChartAt I' (f p)).source.restrict (extChartAt I' (f p))) :=
    isInducing_extChartAt_source_restrict (I := I') (f p)
  -- `z ↦ extChartAt I p z` is inducing on `V`, and corestricts to `V₀`.
  have hincl_src : IsEmbedding
      (fun z : ↥V => (⟨z.1, hcsrc z⟩ : ↥(extChartAt I p).source)) :=
    IsEmbedding.subtypeVal.codRestrict (extChartAt I p).source hcsrc
  have hcV_ind : IsInducing (fun z : ↥V => extChartAt I p z.1) :=
    hc_ind.comp hincl_src.toIsInducing
  have hj : IsInducing (fun z : ↥V => (⟨extChartAt I p z.1, hcmem z⟩ : ↥V₀)) :=
    hcV_ind.codRestrict hcmem
  -- Compose with the normed-space embedding, then rewrite `g ∘ c = c' ∘ f`.
  have hgcV_ind : IsInducing (fun z : ↥V => g (extChartAt I p z.1)) :=
    hEmb0.toIsInducing.comp hj
  have hc'f_ind : IsInducing (fun z : ↥V => extChartAt I' (f p) (f z.1)) := by
    have heq : (fun z : ↥V => extChartAt I' (f p) (f z.1))
        = (fun z : ↥V => g (extChartAt I p z.1)) := by funext z; exact (hgc z).symm
    rw [heq]; exact hgcV_ind
  -- Cancel the (inducing) codomain chart, then the subtype inclusion.
  have hf'_ind : IsInducing
      (fun z : ↥V => (⟨f z.1, hfmem z⟩ : ↥(extChartAt I' (f p)).source)) := by
    have hcomp : (fun z : ↥V => extChartAt I' (f p) (f z.1))
        = (extChartAt I' (f p)).source.restrict (extChartAt I' (f p))
          ∘ (fun z : ↥V => (⟨f z.1, hfmem z⟩ : ↥(extChartAt I' (f p)).source)) := rfl
    rw [hcomp] at hc'f_ind
    exact (hc'_ind.of_comp_iff).mp hc'f_ind
  have hVf_ind : IsInducing (V.restrict f) := by
    have h := IsInducing.subtypeVal.comp hf'_ind
    exact h
  -- Injectivity on `V`.
  have hVf_inj : Function.Injective (V.restrict f) := by
    intro a b hab
    have hg_eq : g (extChartAt I p a.1) = g (extChartAt I p b.1) := by
      rw [hgc a, hgc b]; exact congrArg (extChartAt I' (f p)) hab
    have hV0_eq : (⟨extChartAt I p a.1, hcmem a⟩ : ↥V₀)
        = ⟨extChartAt I p b.1, hcmem b⟩ := hEmb0.injective hg_eq
    have hc_eq : extChartAt I p a.1 = extChartAt I p b.1 := congrArg Subtype.val hV0_eq
    exact Subtype.ext ((extChartAt I p).injOn (hcsrc a) (hcsrc b) hc_eq)
  exact ⟨hVf_ind, hVf_inj⟩

end InverseFunctionTheorem

end Riemannian
