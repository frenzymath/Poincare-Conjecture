/-
Appendix A, Theorem A.14: **the inverse function theorem for manifolds**.

Lee states it as: if `F : M → N` is smooth and `dF_p` is invertible at `p`, then
`F` restricts to a diffeomorphism between connected neighbourhoods of `p` and
`F p`.  In his book this is quoted from the *Smooth Manifolds* volume rather
than proved, and the blueprint node accordingly carried `\uses{\cite{LeeSM}}`.

Mathlib does not have it either.  `Mathlib/Geometry/Manifold/LocalDiffeomorph.lean`
defines `IsLocalDiffeomorphAt` and then lists, verbatim, in its own `## TODO`:

> * if `f` is `C^n` at `x` and `mfderiv I J n f x` is a linear isomorphism,
>   `f` is a local diffeomorphism at `x` (using the inverse function theorem).

That TODO is `isLocalDiffeomorphAt_of_contMDiff_mfderiv_isInvertible` below.

## Why this is not a two-line consequence of the Euclidean inverse function theorem

The Euclidean theorem in the pin is `ContDiffAt.toOpenPartialHomeomorph`, and the
smoothness of the inverse it produces is `ContDiffAt.to_localInverse`, which
concludes `ContDiffAt 𝕂 n (localInverse …) (f a)` — smoothness **at the single
point** `f a`.  A `PartialDiffeomorph`, which is what `IsLocalDiffeomorphAt`
unfolds to, instead demands `ContMDiffOn` of *both* branches on *open* source and
target.  That gap is real and cannot be closed by a lemma: for `n = ∞`,
`ContDiffAt 𝕂 ∞ f a` does **not** imply `ContDiffOn 𝕂 ∞ f u` for any
neighbourhood `u` of `a` (the witnessing neighbourhoods supplied by
`ContDiffAt` may shrink with the order, and `ContDiffAt.contDiffOn` correspondingly
carries a side condition excluding `∞`).

So the inverse has to be shown smooth at *every* point of the target
separately, which needs the derivative to stay invertible on a whole
neighbourhood, not just at `a`.  That is supplied by `ContinuousLinearEquiv.isOpen`
— invertible operators are an open subset of the operator space — together with
continuity of `x ↦ fderiv 𝕂 g x`, which is where the hypothesis "`g` is `C^n` on a
neighbourhood of `a`", rather than merely `ContDiffAt` at `a`, is genuinely used.
The route is therefore:

1. shrink to an open `s ∋ a` on which `g` is `C^n` *and* `fderiv 𝕂 g` is invertible
   at every point (`exists_open_subset_with_invertible_fderiv`);
2. restrict the Euclidean inverse-function homeomorphism to `s`, and run
   `OpenPartialHomeomorph.contDiffAt_symm` at each point of the restricted
   target, which is open, to get `ContDiffOn` of the inverse branch
   (`contDiffOn_symm_of_restricted`);
3. package that as a model-space `PartialDiffeomorph`, and conjugate it back
   through `extChartAt` to a `PartialDiffeomorph` on `M`.

## Why `IsInteriorPoint` and not `Boundaryless`

The chart representative's derivative is `fderivWithin` over `range I`, and it
collapses to the honest `fderiv` exactly when `range I` is a neighbourhood of the
chart point — i.e. at an *interior* point of the model.  Stating the hypothesis as
`I.IsInteriorPoint p` rather than `[I.Boundaryless]` is a strengthening: it lets
the theorem apply at interior points of a manifold *with* boundary, and
`BoundarylessManifold.isInteriorPoint` discharges it in the boundaryless case.
The statement is genuinely false at a boundary point, so some such hypothesis is
required.  Only the *source* model is constrained; `N` may have boundary.

## Provenance

The proof is vendored from the workspace's `LeeSmooth` project (Lee, *Introduction
to Smooth Manifolds*, Theorem 4.5, `LeeSmoothLib/Ch04/Sec04_22/Theorem_4_5.lean`),
which is where this material belongs mathematically — Lee's *Riemannian Manifolds*
Appendix A is a summary of that volume.  Cross-project `lake` dependencies are
banned in this workspace (see I-0109), and the two projects are on different
mathlib revisions, so the argument is re-checked and maintained here rather than
imported.  `LeeRiemannian`'s copy is the one this project's blueprint cites.
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.LocalDiffeomorph

namespace LeeLib.AppendixA

open Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

section LocalInverseFunction

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-! ### The chart representative

`mfderiv` is *defined* as `fderivWithin 𝕜 (writtenInExtChartAt I J p f) (range I) (extChartAt I p p)`,
so at an interior point — where `range I` is a genuine neighbourhood — every hypothesis about
`mfderiv` *is* the corresponding hypothesis about the chart representative's `fderiv`. -/

omit [CompleteSpace E] in
/-- At an interior point, the manifold derivative is an ordinary derivative of the chart
representative. -/
theorem writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint
    {f : M → N} {p : M} {f' : TangentSpace I p →L[𝕜] TangentSpace J (f p)}
    (hp : I.IsInteriorPoint p) (hf : HasMFDerivAt I J f p f') :
    HasFDerivAt (writtenInExtChartAt I J p f : E → F) f' (extChartAt I p p) :=
  hf.2.hasFDerivAt (range_mem_nhds_isInteriorPoint hp)

omit [CompleteSpace E] in
/-- At an interior point, the chart representative of a `C^n` map is `C^n` in the ordinary sense. -/
theorem writtenInExtChartAt_contDiffAt_of_isInteriorPoint
    {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n N] {f : M → N} {p : M}
    (hp : I.IsInteriorPoint p) (hf : ContMDiffAt I J n f p) :
    ContDiffAt 𝕜 n (writtenInExtChartAt I J p f : E → F) (extChartAt I p p) := by
  rw [contMDiffAt_iff_of_mem_source (I := I) (I' := J) (x := p) (y := f p)
    (x' := p) (f := f) (mem_chart_source H p) (mem_chart_source G (f p))] at hf
  exact hf.2.contDiffAt (range_mem_nhds_isInteriorPoint hp)

omit [CompleteSpace E] in
/-- The chart representative of a globally `C^n` map is `C^n` on the whole chart domain where both
preferred extended charts are defined.  This is the "smooth on a neighbourhood, not merely at a
point" input that the openness argument below needs. -/
theorem writtenInExtChartAt_contDiffOn_of_contMDiff
    {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n N] {f : M → N} {p : M}
    (hf : ContMDiff I J n f) :
    ContDiffOn 𝕜 n (writtenInExtChartAt I J p f : E → F)
      ((extChartAt I p).target ∩
        (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source) := by
  set s : Set M := (extChartAt I p).source ∩ f ⁻¹' (extChartAt J (f p)).source with hs_def
  have hs : s ⊆ (extChartAt I p).source := fun _ hx => hx.1
  have hmaps : MapsTo f s (extChartAt J (f p)).source := fun _ hx => hx.2
  have hchart : ContDiffOn 𝕜 n (writtenInExtChartAt I J p f : E → F) ((extChartAt I p) '' s) :=
    (contMDiffOn_iff_of_subset_source' (I := I) (I' := J) (n := n)
      (x := p) (y := f p) (f := f) hs hmaps).1 hf.contMDiffOn
  have himage : (extChartAt I p) '' s =
      (extChartAt I p).target ∩ (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source := by
    simpa [hs_def, Function.comp, extChartAt_target, extChartAt_coe_symm] using
      (extChartAt I p).image_source_inter_eq' (f ⁻¹' (extChartAt J (f p)).source)
  rw [himage] at hchart
  simpa using hchart

omit [CompleteSpace E] in
/-- At an interior point, the ordinary derivative of the chart representative *is* the manifold
derivative. -/
theorem writtenInExtChartAt_fderiv_eq_mfderiv_of_isInteriorPoint
    {f : M → N} {p : M} (hp : I.IsInteriorPoint p) (hmd : MDifferentiableAt I J f p) :
    fderiv 𝕜 (writtenInExtChartAt I J p f : E → F) (extChartAt I p p) = mfderiv I J f p := by
  calc
    fderiv 𝕜 (writtenInExtChartAt I J p f : E → F) (extChartAt I p p)
      = fderivWithin 𝕜 (writtenInExtChartAt I J p f : E → F) (range I) (extChartAt I p p) :=
        (fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hp)).symm
    _ = mfderiv I J f p := by simpa using (hmd.mfderiv (I := I) (I' := J) (f := f) (x := p)).symm

/-! ### Invertibility is an open condition -/

/-- Invertible continuous linear maps form an open subset of the operator space.  This is
`ContinuousLinearEquiv.isOpen` restated for `ContinuousLinearMap.IsInvertible`, and it is what lets
the derivative be kept invertible on a whole neighbourhood. -/
theorem isOpen_setOf_isInvertible : IsOpen {A : E →L[𝕜] F | A.IsInvertible} := by
  simpa [ContinuousLinearMap.IsInvertible] using
    (ContinuousLinearEquiv.isOpen : IsOpen (range (fun e : E ≃L[𝕜] F => (e : E →L[𝕜] F))))

/-- Shrink a neighbourhood so that the derivative stays invertible on the whole of a smaller *open*
set.  Continuity of `fderiv 𝕜 g` — which needs `g` to be `C^n` on a neighbourhood, not just at the
point — meets openness of the invertible locus. -/
theorem exists_open_subset_with_invertible_fderiv
    {n : WithTop ℕ∞} {g : E → F} {a : E} {Ω : Set E}
    (hΩ : Ω ∈ 𝓝 a) (hgΩ : ContDiffOn 𝕜 n g Ω) (hn : n ≠ 0)
    (haInv : (fderiv 𝕜 g a).IsInvertible) :
    ∃ s : Set E, IsOpen s ∧ a ∈ s ∧ s ⊆ Ω ∧ ContDiffOn 𝕜 n g s ∧
      ∀ x ∈ s, (fderiv 𝕜 g x).IsInvertible := by
  obtain ⟨t, ht_subset, ht_open, ha_t⟩ := mem_nhds_iff.mp hΩ
  have hcont_t : ContinuousOn (fderiv 𝕜 g) t :=
    (hgΩ.mono ht_subset).continuousOn_fderiv_of_isOpen ht_open
      (ENat.one_le_iff_ne_zero_withTop.mpr hn)
  have hpre_inv : (fderiv 𝕜 g) ⁻¹' {A : E →L[𝕜] F | A.IsInvertible} ∈ 𝓝 a :=
    (hcont_t.continuousAt (ht_open.mem_nhds ha_t)).preimage_mem_nhds
      ((isOpen_setOf_isInvertible (𝕜 := 𝕜) (E := E) (F := F)).mem_nhds haInv)
  obtain ⟨u, hu_subset, hu_open, ha_u⟩ := mem_nhds_iff.mp hpre_inv
  exact ⟨t ∩ u, ht_open.inter hu_open, ⟨ha_t, ha_u⟩, fun _ hx => ht_subset hx.1,
    hgΩ.mono fun _ hx => ht_subset hx.1, fun _ hx => hu_subset hx.2⟩

/-- **The inverse branch is smooth on the whole restricted target.**  Once the source is restricted
to an open set on which the derivative stays invertible, `OpenPartialHomeomorph.contDiffAt_symm`
applies at *every* point of the (open) restricted target, and pointwise `ContDiffAt` on an open set
is `ContDiffOn`.  This is the step that `ContDiffAt.to_localInverse` cannot supply. -/
theorem contDiffOn_symm_of_restricted
    {n : WithTop ℕ∞} {g : E → F} {a : E} {f' : E ≃L[𝕜] F}
    (hgAt : ContDiffAt 𝕜 n g a) (hg_fderiv : HasFDerivAt g (f' : E →L[𝕜] F) a) (hn : n ≠ 0)
    {s : Set E} (hs_open : IsOpen s)
    (hg_s : ContDiffOn 𝕜 n g s) (hInv_s : ∀ x ∈ s, (fderiv 𝕜 g x).IsInvertible) :
    ContDiffOn 𝕜 n (hgAt.toOpenPartialHomeomorph g hg_fderiv hn).symm
      ((hgAt.toOpenPartialHomeomorph g hg_fderiv hn).restr s).target := by
  set R := hgAt.toOpenPartialHomeomorph g hg_fderiv hn with hR_def
  rw [(R.restr s).open_target.contDiffOn_iff]
  intro y hy
  have hy' : y ∈ R.target ∧ R.symm y ∈ s := by
    simpa [OpenPartialHomeomorph.restr, hs_open.interior_eq, mem_inter_iff, mem_preimage] using hy
  -- `contDiffAt_symm` is applied at `y` itself; its hypotheses are about `R.symm y`, which lies in
  -- `s`, so both the invertible derivative and the smoothness of `g` are available there.
  have hx : R.symm y ∈ s := hy'.2
  have hx_cont : ContDiffAt 𝕜 n g (R.symm y) := (hg_s _ hx).contDiffAt (hs_open.mem_nhds hx)
  have hx_deriv : HasFDerivAt g (fderiv 𝕜 g (R.symm y)) (R.symm y) :=
    (hx_cont.differentiableAt hn).hasFDerivAt
  have hx_deriv' : HasFDerivAt g
      ((Classical.choose (hInv_s _ hx) : E ≃L[𝕜] F) : E →L[𝕜] F) (R.symm y) := by
    simpa [Classical.choose_spec (hInv_s _ hx)] using hx_deriv
  exact R.contDiffAt_symm hy'.1 hx_deriv' hx_cont

/-- The Euclidean inverse function theorem, packaged as a model-space `PartialDiffeomorph` whose
source sits inside a prescribed neighbourhood and whose target sits inside a prescribed set.  The
two containment conclusions are what make the conjugation back through charts possible. -/
theorem exists_model_partialDiffeomorph
    {n : WithTop ℕ∞} {g : E → F} {a : E} {Ω : Set E} {T : Set F} {f' : E ≃L[𝕜] F}
    (hΩ : Ω ∈ 𝓝 a) (hgΩ : ContDiffOn 𝕜 n g Ω) (hgT : MapsTo g Ω T)
    (hgAt : ContDiffAt 𝕜 n g a) (hg_fderiv : HasFDerivAt g (f' : E →L[𝕜] F) a) (hn : n ≠ 0)
    (haInv : (fderiv 𝕜 g a).IsInvertible) :
    ∃ Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n,
      a ∈ Ψ.source ∧ Ψ.source ⊆ Ω ∧ Ψ.target ⊆ T ∧ EqOn g Ψ Ψ.source := by
  set R := hgAt.toOpenPartialHomeomorph g hg_fderiv hn with hR_def
  have haR : a ∈ R.source := hgAt.mem_toOpenPartialHomeomorph_source hg_fderiv hn
  obtain ⟨s, hs_open, ha_s, hs_subset, hg_s, hInv_s⟩ :=
    exists_open_subset_with_invertible_fderiv (𝕜 := 𝕜) (E := E) (F := F) (g := g) (a := a)
      (Ω := Ω ∩ R.source) (Filter.inter_mem hΩ (R.open_source.mem_nhds haR))
      (hgΩ.mono inter_subset_left) hn haInv
  have hs_Ω : s ⊆ Ω := fun _ hx => (hs_subset hx).1
  have hs_R : s ⊆ R.source := fun _ hx => (hs_subset hx).2
  have hsource_restr : (R.restr s).source = s := by
    rw [R.restr_source' s hs_open]; exact inter_eq_right.mpr hs_R
  have hsymm : ContDiffOn 𝕜 n R.symm (R.restr s).target :=
    contDiffOn_symm_of_restricted (𝕜 := 𝕜) (E := E) (F := F) (g := g) (a := a)
      hgAt hg_fderiv hn hs_open hg_s hInv_s
  refine ⟨{ toPartialEquiv := (R.restr s).toPartialEquiv
            open_source := (R.restr s).open_source
            open_target := (R.restr s).open_target
            contMDiffOn_toFun := by
              rw [hsource_restr]
              simpa [hR_def, ContDiffAt.toOpenPartialHomeomorph_coe] using hg_s.contMDiffOn
            contMDiffOn_invFun := by simpa [hR_def] using hsymm.contMDiffOn }, ?_, ?_, ?_, ?_⟩
  · show a ∈ (R.restr s).source
    rwa [hsource_restr]
  · show (R.restr s).source ⊆ Ω
    rw [hsource_restr]; exact hs_Ω
  · intro y hy
    have hy' : y ∈ R.target ∧ R.symm y ∈ s := by
      simpa [OpenPartialHomeomorph.restr, hs_open.interior_eq, mem_inter_iff, mem_preimage] using hy
    have hy_eq : g (R.symm y) = y := by
      simpa [hR_def, ContDiffAt.toOpenPartialHomeomorph_coe] using R.right_inv hy'.1
    simpa [hy_eq] using hgT (hs_Ω hy'.2)
  · intro x _
    simp [hR_def, ContDiffAt.toOpenPartialHomeomorph_coe]

/-! ### Conjugating back through the charts -/

omit [CompleteSpace E] in
/-- A model-space `PartialDiffeomorph` for the chart representative transports back to a
`PartialDiffeomorph` on `M`, by conjugating with `extChartAt` on both sides. -/
theorem exists_partialDiffeomorph_of_writtenInExtChartAt
    {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n N] {f : M → N} {p : M}
    {Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n}
    (hpΨ : extChartAt I p p ∈ Ψ.source)
    (hsource : Ψ.source ⊆ (extChartAt I p).target ∩
      (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source)
    (htarget : Ψ.target ⊆ (extChartAt J (f p)).target)
    (hEq : EqOn (writtenInExtChartAt I J p f) Ψ Ψ.source) :
    ∃ Φ : PartialDiffeomorph I J M N n, p ∈ Φ.source ∧ EqOn f Φ Φ.source := by
  set Γ : PartialEquiv M N :=
    (extChartAt I p).trans (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm) with hΓ_def
  have hinner_source : (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).source = Ψ.source := by
    ext y
    simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage]
    exact ⟨fun hy => hy.1, fun hy => ⟨hy, htarget (Ψ.map_source hy)⟩⟩
  have hΓ_source : Γ.source = (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' Ψ.source := by
    rw [hΓ_def, PartialEquiv.trans_source, hinner_source]
  have hinner_target : (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).target =
      (extChartAt J (f p)).source ∩ (extChartAt J (f p)) ⁻¹' Ψ.target := by
    rw [PartialEquiv.trans_target]; rfl
  have hΓ_target : Γ.target = (extChartAt J (f p)).source ∩ (extChartAt J (f p)) ⁻¹' Ψ.target := by
    rw [← hinner_target]
    ext y
    simp only [hΓ_def, PartialEquiv.trans_target, mem_inter_iff, mem_preimage]
    refine ⟨fun hy => hy.1, fun hy => ⟨hy, ?_⟩⟩
    -- The inverse image already lands in the source chart's target, by `hsource`.
    have hy_source : (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).symm y ∈ Ψ.source := by
      rw [← hinner_source]
      exact (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).map_target hy
    exact (hsource hy_source).1
  have hmid_to : ContMDiffOn 𝓘(𝕜, E) J n ((extChartAt J (f p)).symm ∘ Ψ) Ψ.source :=
    (contMDiffOn_extChartAt_symm (I := J) (n := n) (f p)).comp Ψ.contMDiffOn_toFun
      fun _ hx => htarget (Ψ.map_source hx)
  have hmid_inv : ContMDiffOn 𝓘(𝕜, F) I n ((extChartAt I p).symm ∘ Ψ.symm) Ψ.target :=
    (contMDiffOn_extChartAt_symm (I := I) (n := n) p).comp Ψ.contMDiffOn_invFun
      fun _ hy => (hsource (Ψ.map_target hy)).1
  refine ⟨{ toPartialEquiv := Γ
            open_source := by
              rw [hΓ_source]
              exact (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
                (isOpen_extChartAt_source (I := I) p) Ψ.open_source
            open_target := by
              rw [hΓ_target]
              exact (continuousOn_extChartAt (I := J) (f p)).isOpen_inter_preimage
                (isOpen_extChartAt_source (I := J) (f p)) Ψ.open_target
            contMDiffOn_toFun := by
              rw [hΓ_source]
              simpa [hΓ_def, Function.comp_assoc] using
                hmid_to.comp' (contMDiffOn_extChartAt (I := I) (n := n) (x := p))
            contMDiffOn_invFun := by
              rw [hΓ_target]
              simpa [hΓ_def, Function.comp_assoc] using
                hmid_inv.comp' (contMDiffOn_extChartAt (I := J) (n := n) (x := f p)) }, ?_, ?_⟩
  · show p ∈ Γ.source
    rw [hΓ_source]
    exact ⟨mem_extChartAt_source (I := I) p, hpΨ⟩
  · intro x hx
    have hx' : x ∈ (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' Ψ.source := by
      rw [← hΓ_source]; exact hx
    have hxΨ : extChartAt I p x ∈ Ψ.source := hx'.2
    have hx_left : (extChartAt I p).symm (extChartAt I p x) = x := (extChartAt I p).left_inv hx'.1
    have hfx_source : f x ∈ (extChartAt J (f p)).source := by
      have hpre : f ((extChartAt I p).symm (extChartAt I p x)) ∈ (extChartAt J (f p)).source := by
        simpa [Function.comp] using (hsource hxΨ).2
      rwa [hx_left] at hpre
    have hwritten : writtenInExtChartAt I J p f (extChartAt I p x) = extChartAt J (f p) (f x) := by
      show extChartAt J (f p) (f ((extChartAt I p).symm (extChartAt I p x))) = _
      rw [hx_left]
    show f x = Γ x
    calc f x = (extChartAt J (f p)).symm (extChartAt J (f p) (f x)) :=
            ((extChartAt J (f p)).left_inv hfx_source).symm
      _ = (extChartAt J (f p)).symm (writtenInExtChartAt I J p f (extChartAt I p x)) := by
            rw [hwritten]
      _ = (extChartAt J (f p)).symm (Ψ (extChartAt I p x)) := by rw [hEq hxΨ]
      _ = Γ x := by simp [hΓ_def, PartialEquiv.trans_apply]

/-! ### The theorem -/

/-- **The inverse function theorem for manifolds** (Lee, Theorem A.14), in the form of mathlib's own
`LocalDiffeomorph` TODO: *if `f` is `C^n` and `mfderiv I J f p` is invertible at an interior point
`p`, then `f` is a `C^n` local diffeomorphism at `p`.*

The `IsInteriorPoint` hypothesis is necessary — the statement is false at a boundary point — and it
is discharged by `BoundarylessManifold.isInteriorPoint` whenever the source model is boundaryless.
Only the source model is constrained; `N` may have boundary. -/
theorem isLocalDiffeomorphAt_of_contMDiff_mfderiv_isInvertible
    {n : WithTop ℕ∞} (hn : n ≠ 0) [IsManifold I n M] [IsManifold J n N] {f : M → N} {p : M}
    (hp : I.IsInteriorPoint p) (hf : ContMDiff I J n f) (hfp : (mfderiv I J f p).IsInvertible) :
    IsLocalDiffeomorphAt I J n f p := by
  set g : E → F := writtenInExtChartAt I J p f with hg_def
  set a : E := extChartAt I p p with ha_def
  set Ω : Set E := (extChartAt I p).target ∩
    (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source with hΩ_def
  set T : Set F := (extChartAt J (f p)).target with hT_def
  have hmd : MDifferentiableAt I J f p := hf.contMDiffAt.mdifferentiableAt hn
  have hΩ_target : (extChartAt I p).target ∈ 𝓝 a := by
    rw [ha_def, ← nhdsWithin_eq_nhds.2 (range_mem_nhds_isInteriorPoint hp)]
    exact extChartAt_target_mem_nhdsWithin (I := I) p
  have hΩ_source : (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source ∈ 𝓝 a := by
    simpa [ha_def, Function.comp] using (extChartAt_preimage_mem_nhds (I := I) (x := p)
      (hf.contMDiffAt.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := J) (f p))))
  have hΩ : Ω ∈ 𝓝 a := Filter.inter_mem hΩ_target hΩ_source
  have hgΩ : ContDiffOn 𝕜 n g Ω := by
    simpa [hg_def, hΩ_def] using
      writtenInExtChartAt_contDiffOn_of_contMDiff (I := I) (J := J) (n := n) (f := f) (p := p) hf
  have hgT : MapsTo g Ω T := by
    simpa [hg_def, hΩ_def, hT_def] using
      (writtenInExtChartAt_mapsTo (I := I) (I' := J) (x := p) (f := f))
  have hgAt : ContDiffAt 𝕜 n g a := by
    simpa [hg_def, ha_def] using writtenInExtChartAt_contDiffAt_of_isInteriorPoint
      (I := I) (J := J) (n := n) (f := f) (p := p) hp hf.contMDiffAt
  have hfderiv_eq : fderiv 𝕜 g a = mfderiv I J f p :=
    writtenInExtChartAt_fderiv_eq_mfderiv_of_isInteriorPoint (I := I) (J := J) hp hmd
  have haInv_chart : (fderiv 𝕜 g a).IsInvertible := by rw [hfderiv_eq]; exact hfp
  have hg_fderiv : HasFDerivAt g ((Classical.choose hfp : E ≃L[𝕜] F) : E →L[𝕜] F) a := by
    have hbase : HasFDerivAt g (mfderiv I J f p) a :=
      writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint (I := I) (J := J) (f := f) (p := p) hp
        hmd.hasMFDerivAt
    rw [← Classical.choose_spec hfp] at hbase
    simpa using hbase
  obtain ⟨Ψ, hpΨ, hsource, htarget, hEq⟩ :=
    exists_model_partialDiffeomorph (𝕜 := 𝕜) (E := E) (F := F) (g := g) (a := a) (Ω := Ω) (T := T)
      (f' := Classical.choose hfp) hΩ hgΩ hgT hgAt hg_fderiv hn haInv_chart
  obtain ⟨Φ, hpΦ, hΦ⟩ := exists_partialDiffeomorph_of_writtenInExtChartAt
    (I := I) (J := J) (f := f) (p := p) (Ψ := Ψ) hpΨ hsource htarget hEq
  exact ⟨Φ, hpΦ, hΦ⟩

end LocalInverseFunction

/-! ## Lee's statement: connected neighbourhoods

Lee's A.14 asks for a diffeomorphism between *connected* neighbourhoods, which is slightly more than
`IsLocalDiffeomorphAt` gives.  The gap is closed by passing to the connected component of the source
inside a local-diffeomorphism neighbourhood, which is open because a manifold is locally connected,
and carrying it over to the target along the diffeomorphism itself.

This section is over `ℝ`, which is where `LocallyConnectedSpace E` is available as an instance (it
is *not* found for a general `RCLike` scalar field), so that Lee's statement needs no hypothesis
beyond his own. -/

section ConnectedNeighborhoods

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- Restricting a `PartialDiffeomorph` to an open subset of its source gives a genuine
diffeomorphism onto the corresponding open image. -/
theorem exists_diffeomorph_image_of_isOpen_subset_source
    (Φ : PartialDiffeomorph I J M N ∞) {s : Set M} (hs : IsOpen s) (hsub : s ⊆ Φ.source) :
    ∃ V : TopologicalSpace.Opens N,
      ∃ Ψ : (⟨s, hs⟩ : TopologicalSpace.Opens M) ≃ₘ⟮I, J⟯ V,
        ∀ x : (⟨s, hs⟩ : TopologicalSpace.Opens M), (Ψ x : N) = Φ x := by
  set U : TopologicalSpace.Opens M := ⟨s, hs⟩ with hU_def
  set V : TopologicalSpace.Opens N :=
    ⟨Φ '' s, Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hs hsub⟩ with hV_def
  set e : U ≃ₜ V := Φ.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource hsub rfl with he_def
  refine ⟨V, { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }, fun _ => rfl⟩
  · intro x
    refine (ContMDiffAt.subtypeVal_comp_iff V (fun y : U ↦ e y) x).1 ?_
    refine (contMDiffAt_subtype_iff (U := U) (f := Φ) (x := x)).2 ?_
    exact Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsub x.2))
  · intro y
    refine (ContMDiffAt.subtypeVal_comp_iff U (fun z : V ↦ e.symm z) y).1 ?_
    refine (contMDiffAt_subtype_iff (U := V) (f := Φ.symm) (x := y)).2 ?_
    obtain ⟨x, hx, hy⟩ := y.2
    simpa [hy] using
      Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds (Φ.map_source (hsub hx)))

/-- A local diffeomorphism at `x` restricts to a diffeomorphism between *connected* open
neighbourhoods of `x` and `f x`. -/
theorem IsLocalDiffeomorphAt.exists_isConnected_diffeomorph [LocallyConnectedSpace M]
    {f : M → N} {x : M} (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    ∃ U : TopologicalSpace.Opens M, x ∈ (U : Set M) ∧ IsConnected (U : Set M) ∧
      ∃ V : TopologicalSpace.Opens N, f x ∈ (V : Set N) ∧ IsConnected (V : Set N) ∧
        ∃ Φ : U ≃ₘ⟮I, J⟯ V, ∀ y : U, (Φ y : N) = f y := by
  obtain ⟨Φ₀, hx, hEq⟩ := hf
  -- The connected component of `x` in `Φ₀.source` is open because `M` is locally connected.
  set s : Set M := connectedComponentIn Φ₀.source x with hs_def
  have hs_open : IsOpen s := Φ₀.open_source.connectedComponentIn
  have hx_mem : x ∈ s := mem_connectedComponentIn hx
  have hs_subset : s ⊆ Φ₀.source := connectedComponentIn_subset _ _
  have hs_connected : IsConnected s := isConnected_connectedComponentIn_iff.mpr hx
  obtain ⟨V, Φ, hΦ⟩ :=
    exists_diffeomorph_image_of_isOpen_subset_source (I := I) (J := J) Φ₀ hs_open hs_subset
  refine ⟨⟨s, hs_open⟩, hx_mem, hs_connected, V, ?_, ?_, Φ, fun y => ?_⟩
  · have hΦx : (Φ ⟨x, hx_mem⟩ : N) = f x := by rw [hΦ]; exact (hEq (hs_subset hx_mem)).symm
    exact hΦx ▸ (Φ ⟨x, hx_mem⟩).2
  · -- Connectedness transfers to the image along the homeomorphism underlying `Φ`.
    letI : ConnectedSpace (⟨s, hs_open⟩ : TopologicalSpace.Opens M) :=
      isConnected_iff_connectedSpace.mp hs_connected
    letI : ConnectedSpace V := (Φ.toHomeomorph.connectedSpace_iff).1 inferInstance
    exact isConnected_iff_connectedSpace.mpr inferInstance
  · rw [hΦ]; exact (hEq (hs_subset y.2)).symm

/-- **The inverse function theorem for manifolds** (Lee, Theorem A.14), verbatim in his form:
*if `f : M → N` is smooth and `df_p` is invertible at `p`, then there are connected neighbourhoods
`U` of `p` and `V` of `f p` such that `f|_U : U → V` is a diffeomorphism.*

Local connectedness of `M`, which Lee leaves implicit, is derived rather than assumed: a
boundaryless model is homeomorphic to its normed model space, which is locally connected, and local
connectedness passes to any charted space over it. -/
theorem exists_isConnected_diffeomorph_of_mfderiv_isInvertible [CompleteSpace E] [I.Boundaryless]
    [IsManifold I ∞ M] [IsManifold J ∞ N] {f : M → N} {p : M}
    (hf : ContMDiff I J ∞ f) (hfp : (mfderiv I J f p).IsInvertible) :
    ∃ U : TopologicalSpace.Opens M, p ∈ (U : Set M) ∧ IsConnected (U : Set M) ∧
      ∃ V : TopologicalSpace.Opens N, f p ∈ (V : Set N) ∧ IsConnected (V : Set N) ∧
        ∃ Φ : U ≃ₘ⟮I, J⟯ V, ∀ y : U, (Φ y : N) = f y := by
  letI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  letI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  -- `IsLocalDiffeomorphAt` is a `def` for an `∃`, so dot notation would resolve against `Exists`.
  exact IsLocalDiffeomorphAt.exists_isConnected_diffeomorph
    (isLocalDiffeomorphAt_of_contMDiff_mfderiv_isInvertible (I := I) (J := J) (n := ∞)
      (by simp) BoundarylessManifold.isInteriorPoint hf hfp)

end ConnectedNeighborhoods

end

end LeeLib.AppendixA
