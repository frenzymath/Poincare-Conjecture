import MorganTianLib.Ch01.CutLocusAgreement
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open Set Filter Metric Riemannian MeasureTheory
open scoped ContDiff Manifold Topology Bundle ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic
open Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace M]

section

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
  (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
  (p : M)

def segmentDomainOpens : TopologicalSpace.Opens E :=
  ⟨segmentDomain (I := I) g hg p, isOpen_segmentDomain (I := I) g hg p⟩

def cutLocusComplementOpens : TopologicalSpace.Opens M :=
  ⟨(cutLocus (I := I) g hg p)ᶜ, (isClosed_cutLocus (I := I) g hg p).isOpen_compl⟩

local notation "U" => segmentDomainOpens (I := I) g hg p
local notation "V" => cutLocusComplementOpens (I := I) g hg p

def expSegmentEquiv : U ≃ V := by
  let f : U → V := fun v =>
    ⟨expMapGlobal (I := I) g hg p (v : E), by
      change expMapGlobal (I := I) g hg p (v : E) ∉
        cutLocus (I := I) g hg p
      rw [cutLocus_eq_compl_image_segmentDomain (I := I) g hg p]
      intro hv
      exact hv.2 ⟨(v : E), v.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w hvw
      apply Subtype.ext
      apply injOn_expMapGlobal_segmentDomain (I := I) g hg p v.property w.property
      exact congrArg Subtype.val hvw
    · intro q
      have hq : (q : M) ∉ cutLocus (I := I) g hg p := q.property
      obtain ⟨v, hv, hev, _⟩ :=
        exists_mem_segmentDomain_expMapGlobal_eq (I := I) g hg p hq
      exact ⟨⟨v, hv⟩, Subtype.ext hev⟩
  exact Equiv.ofBijective f hf

theorem expSegmentEquiv_apply (v : U) :
    expSegmentEquiv (I := I) g hg p v =
      ⟨expMapGlobal (I := I) g hg p (v : E), by
        change expMapGlobal (I := I) g hg p (v : E) ∉
          cutLocus (I := I) g hg p
        rw [cutLocus_eq_compl_image_segmentDomain (I := I) g hg p]
        intro hv
        exact hv.2 ⟨(v : E), v.property, rfl⟩⟩ := by
  rfl

theorem expSegmentEquiv_contMDiff :
    ContMDiff 𝓘(ℝ, E) I ∞ (expSegmentEquiv (I := I) g hg p) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  have hfun :
      (Subtype.val ∘ expSegmentEquiv (I := I) g hg p) =
        (fun w => expMapGlobal (I := I) g hg p w) ∘
          (Subtype.val : segmentDomainOpens (I := I) g hg p → E) := by
    funext v
    rfl
  rw [hfun]
  exact (Riemannian.Exponential.contMDiff_expMapGlobal g hg p).comp
    (contMDiff_subtype_val :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (Subtype.val : segmentDomainOpens (I := I) g hg p → E))

theorem expSegmentEquiv_contMDiff_symm :
    ContMDiff I 𝓘(ℝ, E) ∞ (expSegmentEquiv (I := I) g hg p).symm := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  intro y
  let v : U := (expSegmentEquiv (I := I) g hg p).symm y
  have hvU : (v : E) ∈ segmentDomain (I := I) g hg p := v.property
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (fun w : E => expMapGlobal (I := I) g hg p (w : TangentSpace I p)) (v : E) :=
    (segmentDomain_subset_bookSegmentDomain (I := I) g hg p hvU).2.2
  have hvexp : expMapGlobal (I := I) g hg p (v : E) = (y : M) := by
    have h := congrArg Subtype.val
      ((expSegmentEquiv (I := I) g hg p).apply_symm_apply y)
    simpa only [expSegmentEquiv_apply] using h
  have hylocal : (y : M) ∈ hloc.localInverse.source := by
    rw [← hvexp]
    exact hloc.localInverse_mem_source
  have hlocal_y : hloc.localInverse (y : M) = (v : E) := by
    rw [← hvexp]
    exact hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hlocal_smooth : ContMDiffAt I 𝓘(ℝ, E) ∞
      hloc.localInverse (y : M) := by
    rw [← hvexp]
    exact hloc.localInverse_contMDiffAt
  have hsource : hloc.localInverse.source ∈ 𝓝 (y : M) :=
    hloc.localInverse_open_source.mem_nhds hylocal
  have hUmem : hloc.localInverse (y : M) ∈
      segmentDomain (I := I) g hg p := by
    rw [hlocal_y]
    exact hvU
  have hU : (fun z : M => hloc.localInverse z) ⁻¹'
      segmentDomain (I := I) g hg p ∈ 𝓝 (y : M) :=
    hlocal_smooth.continuousAt.preimage_mem_nhds
      ((isOpen_segmentDomain (I := I) g hg p).mem_nhds hUmem)
  have hboth : hloc.localInverse.source ∩
      ((fun z : M => hloc.localInverse z) ⁻¹'
        segmentDomain (I := I) g hg p) ∈ 𝓝 (y : M) :=
    inter_mem hsource hU
  have hboth' : (Subtype.val : V → M) ⁻¹'
      (hloc.localInverse.source ∩
        ((fun z : M => hloc.localInverse z) ⁻¹'
          segmentDomain (I := I) g hg p)) ∈ 𝓝 y :=
    (continuous_subtype_val : Continuous (Subtype.val : V → M)).continuousAt.preimage_mem_nhds hboth
  have heq : (Subtype.val ∘ (expSegmentEquiv (I := I) g hg p).symm) =ᶠ[𝓝 y]
      (hloc.localInverse ∘ (Subtype.val : V → M)) := by
    filter_upwards [hboth'] with y' hy'
    have hysource : (y' : M) ∈ hloc.localInverse.source := hy'.1
    have hwU : hloc.localInverse (y' : M) ∈
        segmentDomain (I := I) g hg p := hy'.2
    have hexp : expMapGlobal (I := I) g hg p
        (hloc.localInverse (y' : M) : E) = (y' : M) := by
      simpa only [Function.comp_apply] using hloc.localInverse_right_inv hysource
    have hmap : expSegmentEquiv (I := I) g hg p
        ⟨hloc.localInverse (y' : M), hwU⟩ = y' := by
      apply Subtype.ext
      simpa only [expSegmentEquiv_apply] using hexp
    have hinv : (expSegmentEquiv (I := I) g hg p).symm y' =
        ⟨hloc.localInverse (y' : M), hwU⟩ :=
      (expSegmentEquiv (I := I) g hg p).injective
        ((expSegmentEquiv (I := I) g hg p).apply_symm_apply y' |>.trans hmap.symm)
    exact congrArg Subtype.val hinv
  have hli : ContMDiffAt I 𝓘(ℝ, E) ∞
      (hloc.localInverse ∘ (Subtype.val : V → M)) y :=
    hlocal_smooth.comp y contMDiff_subtype_val.contMDiffAt
  exact hli.congr_of_eventuallyEq heq

/-- **Math.** The exponential map restricts to a smooth diffeomorphism from the
open metric segment domain onto the complement of the cut locus. -/
def expMapGlobal_segmentDomain_diffeomorph :
    (segmentDomainOpens (I := I) g hg p) ≃ₘ⟮𝓘(ℝ, E), I⟯
      (cutLocusComplementOpens (I := I) g hg p) :=
  { toEquiv := expSegmentEquiv (I := I) g hg p
    contMDiff_toFun := expSegmentEquiv_contMDiff (I := I) g hg p
    contMDiff_invFun := expSegmentEquiv_contMDiff_symm (I := I) g hg p }

theorem expMapGlobal_segmentDomain_diffeomorph_apply (v :
    segmentDomainOpens (I := I) g hg p) :
    expMapGlobal_segmentDomain_diffeomorph (I := I) g hg p v =
      ⟨expMapGlobal (I := I) g hg p (v : E), by
        change expMapGlobal (I := I) g hg p (v : E) ∉
          cutLocus (I := I) g hg p
        rw [cutLocus_eq_compl_image_segmentDomain (I := I) g hg p]
        intro hv
        exact hv.2 ⟨(v : E), v.property, rfl⟩⟩ := by
  rfl

end

end MorganTianLib

end
