import PetersenLib.Foundations.ParametricIntegral
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smoothness of a manifold-parametrised Bochner integral over a compact parameter manifold

This file lifts the pure-normed `contDiffOn_parametricIntegral`
(`PetersenLib.Foundations.ParametricIntegral`) to **manifolds**: if a scalar family
`f : Γ → M → ℝ` is jointly `C^∞` on `univ ×ˢ U` (with `U ⊆ M` open) and `Γ` is a compact,
boundaryless, second-countable parameter manifold carrying a finite measure `μ`, then

  `p ↦ ∫_Γ f γ p dμ(γ)`

is `C^∞` on `U` (`contMDiffOn_integral_scalar`).

The proof descends both the base point (via `extChartAt I p₀`) and — for the joint continuity
of the `x`-derivatives that `contDiffOn_parametricIntegral` requires — the parameter (via
`extChartAt J γ₀`, glued over the group's chart cover), reducing everything to the normed
statement.  It is scalar-valued on purpose: the vector-bundle client (Petersen Ex 1.6.26) cannot
integrate an `E →L[ℝ] E →L[ℝ] ℝ`-valued family directly, because `ContinuousENorm` does not
synthesise on the two-level operator space (`Integrable` of such a family is unstatable); it must
integrate the finitely many *scalar* coordinate entries and reassemble them with
`contMDiffOn_bilin_of_apply`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Exercise 1.6.26.
-/

open MeasureTheory Filter Set
open scoped Manifold Topology ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace PetersenLib

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HF : Type*} [TopologicalSpace HF] {J : ModelWithCorners ℝ F HF}
  {Γ : Type*} [TopologicalSpace Γ] [ChartedSpace HF Γ] [IsManifold J ∞ Γ] [J.Boundaryless]
    [CompactSpace Γ] [MeasurableSpace Γ] [BorelSpace Γ] [SecondCountableTopology Γ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {μ : Measure Γ} [IsFiniteMeasure μ]

/-- **Manifold scalar parametric integral (smoothness at a point).**  If `(γ, p) ↦ f γ p` is
jointly `C^∞` on `univ ×ˢ U` with `U` open and `p₀ ∈ U`, then the average `p ↦ ∫_Γ f γ p dμ` is
`C^∞` at `p₀`.  Proof: read the base point in the chart `extChartAt I p₀` and apply the normed
`contDiffOn_parametricIntegral`; the joint continuity of the chart-`x`-derivatives is assembled
over the group's own chart cover from `continuousOn_iteratedFDeriv_partial_prod`. -/
theorem contMDiffAt_integral_scalar {f : Γ → M → ℝ} {U : Set M} (hU : IsOpen U)
    {p₀ : M} (hp₀ : p₀ ∈ U)
    (hf : ContMDiffOn (J.prod I) 𝓘(ℝ, ℝ) ∞ (fun q : Γ × M => f q.1 q.2) (univ ×ˢ U)) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun p => ∫ γ, f γ p ∂μ) p₀ := by
  set cM := extChartAt I p₀ with hcM
  -- the open chart-domain slab in `E`
  set s : Set E := cM.target ∩ cM.symm ⁻¹' U with hs
  have hp₀src : p₀ ∈ cM.source := mem_extChartAt_source p₀
  have hcMsymm : ContinuousOn cM.symm cM.target :=
    (contMDiffOn_extChartAt_symm (n := ∞) p₀).continuousOn
  have hsopen : IsOpen s := hcMsymm.isOpen_inter_preimage (isOpen_extChartAt_target p₀) hU
  have hξ₀s : cM p₀ ∈ s := by
    refine ⟨cM.map_source hp₀src, ?_⟩
    simp only [mem_preimage, cM.left_inv hp₀src]; exact hp₀
  -- The charted family `F γ ξ = f γ (cM.symm ξ)` satisfies the two normed hypotheses.
  have hdiff : ∀ γ : Γ, ContDiffOn ℝ ∞ (fun ξ => f γ (cM.symm ξ)) s := by
    intro γ
    have hfγ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun p => f γ p) U := by
      have h1 : ContMDiff I J ∞ (fun _ : M => γ) := contMDiff_const
      have h2 : ContMDiff I I ∞ (id : M → M) := contMDiff_id
      exact hf.comp (h1.prodMk h2).contMDiffOn (fun p hp => ⟨mem_univ γ, hp⟩)
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ cM.symm s :=
      (contMDiffOn_extChartAt_symm p₀).mono inter_subset_left
    have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun ξ => f γ (cM.symm ξ)) s :=
      hfγ.comp hsymm (fun ξ hξ => hξ.2)
    exact contMDiffOn_iff_contDiffOn.mp hcomp
  have hcont : ∀ m : ℕ, ContinuousOn
      (fun q : Γ × E => iteratedFDeriv ℝ m (fun ξ => f q.1 (cM.symm ξ)) q.2) (univ ×ˢ s) := by
    intro m x hx
    obtain ⟨-, hxs⟩ := hx
    set γ₀ := x.1 with hγ₀
    set cΓ := extChartAt J γ₀ with hcΓ
    have huΓ : IsOpen cΓ.target := isOpen_extChartAt_target γ₀
    -- the jointly charted map on `cΓ.target ×ˢ s`
    set gch : F × E → ℝ := fun r => f (cΓ.symm r.1) (cM.symm r.2) with hgch
    have hgchCD : ContDiffOn ℝ ∞ gch (cΓ.target ×ˢ s) := by
      -- keep the domain `F × E` self-charted (normed projections), so `contMDiffOn_iff_contDiffOn`
      -- applies at the end without a `ModelProd` charted-space mismatch
      have hfst : ContMDiffOn 𝓘(ℝ, F × E) 𝓘(ℝ, F) ∞ Prod.fst (cΓ.target ×ˢ s) :=
        (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
      have hsnd : ContMDiffOn 𝓘(ℝ, F × E) 𝓘(ℝ, E) ∞ Prod.snd (cΓ.target ×ˢ s) :=
        (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
      have hg1 : ContMDiffOn 𝓘(ℝ, F × E) J ∞ (fun r : F × E => cΓ.symm r.1) (cΓ.target ×ˢ s) :=
        (contMDiffOn_extChartAt_symm (n := ∞) γ₀).comp hfst (fun r hr => hr.1)
      have hg2 : ContMDiffOn 𝓘(ℝ, F × E) I ∞ (fun r : F × E => cM.symm r.2) (cΓ.target ×ˢ s) :=
        ((contMDiffOn_extChartAt_symm (n := ∞) p₀).mono inter_subset_left).comp hsnd
          (fun r hr => hr.2)
      have hcomp : ContMDiffOn 𝓘(ℝ, F × E) 𝓘(ℝ, ℝ) ∞ gch (cΓ.target ×ˢ s) :=
        hf.comp (hg1.prodMk hg2) (fun r hr => ⟨mem_univ _, hr.2.2⟩)
      exact contMDiffOn_iff_contDiffOn.mp hcomp
    have hpp := continuousOn_iteratedFDeriv_partial_prod huΓ hsopen hgchCD m
    -- transport from chart coordinates back to the group variable
    set Φ : Γ × E → F × E := fun q => (cΓ q.1, q.2) with hΦ
    have hcΓcont : ContinuousOn cΓ cΓ.source := by
      rw [hcΓ, extChartAt_source]
      exact (contMDiffOn_extChartAt (I := J) (n := ∞) (x := γ₀)).continuousOn
    have hΦcont : ContinuousOn Φ (cΓ.source ×ˢ s) :=
      (hcΓcont.comp continuousOn_fst (fun q hq => hq.1)).prodMk continuousOn_snd
    have hΦmaps : MapsTo Φ (cΓ.source ×ˢ s) (cΓ.target ×ˢ s) := by
      rintro ⟨g, ξ⟩ ⟨hg, hξ⟩
      exact ⟨cΓ.map_source hg, hξ⟩
    have hcompCont : ContinuousOn
        (fun q : Γ × E => iteratedFDeriv ℝ m (fun ξ => f q.1 (cM.symm ξ)) q.2)
        (cΓ.source ×ˢ s) := by
      refine (hpp.comp hΦcont hΦmaps).congr fun q hq => ?_
      have hq1 : q.1 ∈ cΓ.source := hq.1
      simp only [Function.comp_apply, hΦ, hgch]
      congr 1
      funext ξ
      rw [cΓ.left_inv hq1]
    -- `cΓ.source ×ˢ s` is an open neighbourhood of `x` inside `univ ×ˢ s`
    have hxV : x ∈ cΓ.source ×ˢ s := ⟨mem_extChartAt_source (I := J) γ₀, hxs⟩
    have hVopen : IsOpen (cΓ.source ×ˢ s) := (isOpen_extChartAt_source γ₀).prod hsopen
    have hcAt : ContinuousAt
        (fun q : Γ × E => iteratedFDeriv ℝ m (fun ξ => f q.1 (cM.symm ξ)) q.2) x :=
      (continuousWithinAt_iff_continuousAt (hVopen.mem_nhds hxV)).mp (hcompCont x hxV)
    exact hcAt.continuousWithinAt
  -- the charted integral is `C^∞` at `cM p₀`
  have hHdiff : ContDiffAt ℝ ∞ (fun ξ => ∫ γ, f γ (cM.symm ξ) ∂μ) (cM p₀) :=
    (contDiffOn_parametricIntegral hsopen hdiff hcont).contDiffAt (hsopen.mem_nhds hξ₀s)
  -- pull back to the manifold
  have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      ((fun ξ => ∫ γ, f γ (cM.symm ξ) ∂μ) ∘ cM) p₀ :=
    (hHdiff.contMDiffAt).comp p₀ contMDiffAt_extChartAt
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I) p₀] with p hp
  simp only [Function.comp_apply]
  rw [(extChartAt I p₀).left_inv hp]

/-- **Manifold scalar parametric integral (smoothness on an open set).**  `C^∞` version of
`contMDiffAt_integral_scalar` on the whole open set `U`. -/
theorem contMDiffOn_integral_scalar {f : Γ → M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (J.prod I) 𝓘(ℝ, ℝ) ∞ (fun q : Γ × M => f q.1 q.2) (univ ×ˢ U)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun p => ∫ γ, f γ p ∂μ) U :=
  fun _p₀ hp₀ => (contMDiffAt_integral_scalar hU hp₀ hf).contMDiffWithinAt

/-- **Reassembling a `C^∞` bilinear-form-valued map from its scalar entries.**  On a
finite-dimensional model space `E`, a map `g : M → (E →L[ℝ] E →L[ℝ] ℝ)` is `C^∞` on the open set
`U` as soon as each scalar entry `p ↦ g p v w` is.  Proof: read the base point in a chart and
apply `contDiffOn_clm_apply` twice (finite-dimensionality of `E`).  This is what lets the vector
client average the scalar coordinate entries separately and reassemble the smooth section,
sidestepping the two-level operator `ContinuousENorm` gap. -/
theorem contMDiffOn_bilin_of_apply {g : M → (E →L[ℝ] E →L[ℝ] ℝ)} {U : Set M} (hU : IsOpen U)
    (h : ∀ v w : E, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun p => g p v w) U) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ g U := by
  intro p₀ hp₀
  apply ContMDiffAt.contMDiffWithinAt
  set cM := extChartAt I p₀ with hcM
  set s : Set E := cM.target ∩ cM.symm ⁻¹' U with hs
  have hp₀src : p₀ ∈ cM.source := mem_extChartAt_source p₀
  have hcMsymm : ContinuousOn cM.symm cM.target :=
    (contMDiffOn_extChartAt_symm (n := ∞) p₀).continuousOn
  have hsopen : IsOpen s := hcMsymm.isOpen_inter_preimage (isOpen_extChartAt_target p₀) hU
  have hξ₀s : cM p₀ ∈ s := by
    refine ⟨cM.map_source hp₀src, ?_⟩
    simp only [mem_preimage, cM.left_inv hp₀src]; exact hp₀
  have hĝ : ContDiffAt ℝ ∞ (fun ξ => g (cM.symm ξ)) (cM p₀) := by
    refine (?_ : ContDiffOn ℝ ∞ (fun ξ => g (cM.symm ξ)) s).contDiffAt (hsopen.mem_nhds hξ₀s)
    rw [contDiffOn_clm_apply]
    intro v
    rw [contDiffOn_clm_apply]
    intro w
    have hfγ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun ξ => g (cM.symm ξ) v w) s :=
      (h v w).comp ((contMDiffOn_extChartAt_symm (n := ∞) p₀).mono inter_subset_left)
        (fun ξ hξ => hξ.2)
    exact contMDiffOn_iff_contDiffOn.mp hfγ
  have hcomp : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      ((fun ξ => g (cM.symm ξ)) ∘ cM) p₀ :=
    (hĝ.contMDiffAt).comp p₀ contMDiffAt_extChartAt
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I) p₀] with p hp
  simp only [Function.comp_apply]
  rw [(extChartAt I p₀).left_inv hp]

end PetersenLib
