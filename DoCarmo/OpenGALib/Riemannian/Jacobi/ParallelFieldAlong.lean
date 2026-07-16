import OpenGALib.Riemannian.Jacobi.JacobiChartTransfer
import OpenGALib.Riemannian.Jacobi.PairJacobiField
import OpenGALib.Riemannian.Jacobi.ParallelFrame
import OpenGALib.Riemannian.Jacobi.JacobiExistence

/-!
# Parallel transport of a vector field along a geodesic — the manifold level

do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.6 (parallel transport) and Ch. 5,
Example 2.3 (the parallel field `w(t)` used to write the constant-curvature Jacobi
fields).  The chart-fixed parallel-transport theory already lives in
`OpenGALib/Riemannian/Geodesic/CovariantDerivative.lean`
(`exists_isParallelCoord_Icc`, `isParallelSol_eqOn_Icc`) and
`OpenGALib/Riemannian/Jacobi/ParallelFrame.lean`
(`chartMetricInner_const_of_parallelSol`), but only for a curve that stays inside
one chart.  This file lifts parallel transport to the **manifold level**, exactly
as `JacobiManifold.lean`/`JacobiExistence.lean` do for the Jacobi pair system: the
own-foot field `w : ℝ → E` (each `w τ` read as an element of `T_{γ τ} M`) is
*parallel along `γ`* if, near every time, its chart reading solves the
parallel-transport ODE `ẇ = −Γ(u̇, w)(u)`.  Because the notion is chart-local it
is meaningful for a geodesic that leaves any single chart — the situation of do
Carmo's antipodal example on `S^n` (Example 3.3), where the geodesic from `p` to
its antipode traverses half the sphere.

## Contents

* `IsParallelSolOn` — the chart-level parallel-transport ODE certificate.
* `IsParallelSolOn.transfer` — chart-change covariance: a chart-`α` parallel
  certificate transfers to any other chart `β` containing the same piece of `γ`
  (the first Jacobi equation of `IsJacobiFieldOn.transfer`, specialized).
* `exists_isParallelSol_Icc_of_curve` — chart-level existence discharging the
  ODE-coefficient continuity/bound hypotheses for a `C¹` chart curve.
* `IsParallelFieldAlongOn` — the manifold-level parallel field predicate.
* `IsParallelFieldAlongOn.isParallelSolOn_of_mem_source` — localization into one
  chart on a subinterval.
* `exists_parallelFieldAlongOn` — **existence** of a manifold parallel field with
  prescribed initial value along a geodesic, by a supremum walk gluing single-chart
  solutions through the chart-change covariance.
* `IsParallelFieldAlongOn.metricInner_const` — **parallel transport is an
  isometry**: the intrinsic pairing of two parallel fields is constant along `γ`.
* `isParallelFieldAlongOn_velocity` — the geodesic velocity `γ'` is a parallel
  field (do Carmo Remark 2.2 first field, covariant-derivative clause).

Blueprint: `ex:dc-ch5-2-3`, `ex:dc-ch5-3-3`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.6; Ch. 5, Example 2.3.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The chart-level parallel-transport certificate -/

/-- **Math.** **The chart-level parallel-transport ODE certificate.** In the chart
at `α`, along the chart curve `u`, the coordinate field `w` is *parallel* on `[a, b]`
if it solves `ẇ(t) = −Γ(u̇(t), w(t))(u(t))` there (as `HasDerivWithinAt` on
`Icc a b`, the shape produced by `exists_isParallelCoord_Icc`).  This is do Carmo's
`∇w = 0`. -/
def IsParallelSolOn (g : RiemannianMetric I M) (α : M) (u w : ℝ → E) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, HasDerivWithinAt w
    (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (w t) (u t)) (Icc a b) t

/-- **Math.** Restriction of the chart parallel certificate to a subinterval. -/
theorem IsParallelSolOn.mono {g : RiemannianMetric I M} {α : M} {u w : ℝ → E} {a b a' b' : ℝ}
    (h : IsParallelSolOn (I := I) g α u w a b) (ha : a ≤ a') (hb : b' ≤ b) :
    IsParallelSolOn (I := I) g α u w a' b' :=
  fun t ht => (h t (Icc_subset_Icc ha hb ht)).mono (Icc_subset_Icc ha hb)

/-- **Math.** The chart parallel certificate only depends on the values of the field
on the interval. -/
theorem IsParallelSolOn.congr {g : RiemannianMetric I M} {α : M} {u w w' : ℝ → E} {a b : ℝ}
    (h : IsParallelSolOn (I := I) g α u w a b) (hw : ∀ t ∈ Icc a b, w' t = w t) :
    IsParallelSolOn (I := I) g α u w' a b := by
  intro t ht
  rw [hw t ht]
  exact (h t ht).congr (fun y hy => hw y hy) (hw t ht)

/-! ### Chart-level existence for a `C¹` chart curve -/

/-- **Math.** **Existence of parallel transport along a `C¹` chart curve** with
prescribed initial value — the coefficient continuity/bound hypotheses of
`exists_isParallelCoord_Icc` discharged for a curve staying over the interior of the
chart target (`continuousOn_chartChristoffelContractionRight_comp` + compactness). -/
theorem exists_isParallelSol_Icc_of_curve (g : RiemannianMetric I M) (α : M) {u : ℝ → E}
    {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn (deriv u) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target) (w₀ : E) :
    ∃ w : ℝ → E, w a = w₀ ∧ IsParallelSolOn (I := I) g α u w a b := by
  have hcont := continuousOn_chartChristoffelContractionRight_comp (I := I) g α hu hu' hmem
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨w, hw0, hwd⟩ := exists_isParallelCoord_Icc (I := I) g α u hab w₀
    (K := ⟨max C 0, le_max_right _ _⟩) hcont (fun t ht => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hC t ht).trans (le_max_left _ _))
  exact ⟨w, hw0, hwd⟩

/-! ### Chart-change covariance of the parallel certificate -/

section Transfer

variable [I.Boundaryless]

/-- **Math.** **Chart-change covariance of parallel transport.** Along a geodesic
lying in the sources of two charts `α`, `β`, a chart-`α` parallel certificate for the
own-foot field `w` yields the chart-`β` certificate.  This is the first Jacobi
equation of `IsJacobiFieldOn.transfer` specialized to `∇w = 0` (no `DJ`, no
curvature): the inhomogeneous second-derivative term of the transition map produced
by the product rule cancels against the transformation law of the Christoffel
contraction (`chartChristoffelContraction_change`). -/
theorem IsParallelSolOn.transfer
    {g : RiemannianMetric I M} {γ : ℝ → M} {w : ℝ → E} {α β : M} {a b : ℝ}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsrcα : ∀ τ ∈ Icc a b, γ τ ∈ (chartAt H α).source)
    (hsrcβ : ∀ τ ∈ Icc a b, γ τ ∈ (chartAt H β).source)
    (h : IsParallelSolOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (chartVectorRep (I := I) γ α w) a b) :
    IsParallelSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
      (chartVectorRep (I := I) γ β w) a b := by
  intro τ hτ
  have hxα := hsrcα τ hτ
  have hxβ := hsrcβ τ hτ
  have hcτ := hγc τ hτ
  have hyT : extChartAt I α (γ τ) ∈ chartTransitionSource (I := I) (M := M) α β :=
    extChartAt_mem_chartTransitionSource (I := I) hxα hxβ
  have hsymm : (extChartAt I α).symm (extChartAt I α (γ τ)) = γ τ :=
    (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hxα)
  have hu : HasDerivAt (fun σ => extChartAt I α (γ σ))
      (deriv (fun σ => extChartAt I α (γ σ)) τ) τ := by
    have hev := (hgeo τ hτ).eventually_hasDerivAt_extChartAt hcτ hxα
    exact hev.self_of_nhds.differentiableAt.hasDerivAt
  have hTd : HasFDerivAt (chartTransition (I := I) α β)
      (tangentCoordChange I α β (γ τ)) (extChartAt I α (γ τ)) := by
    have h0 := hasFDerivAt_chartTransition (I := I) hyT
    rwa [hsymm] at h0
  have hev_mem : ∀ᶠ σ in 𝓝 τ,
      γ σ ∈ (chartAt H α).source ∧ γ σ ∈ (chartAt H β).source := by
    have h₁ : γ ⁻¹' (chartAt H α).source ∈ 𝓝 τ :=
      hcτ.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hxα)
    have h₂ : γ ⁻¹' (chartAt H β).source ∈ 𝓝 τ :=
      hcτ.preimage_mem_nhds ((chartAt H β).open_source.mem_nhds hxβ)
    filter_upwards [h₁, h₂] with σ h1 h2
    exact ⟨h1, h2⟩
  have hrep : chartVectorRep (I := I) γ β w =ᶠ[𝓝 τ]
      fun σ => fderiv ℝ (chartTransition (I := I) α β)
        (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α w σ) := by
    filter_upwards [hev_mem] with σ hσ
    have hyσ : extChartAt I α (γ σ)
        ∈ chartTransitionSource (I := I) (M := M) α β :=
      extChartAt_mem_chartTransitionSource (I := I) hσ.1 hσ.2
    have hsymmσ : (extChartAt I α).symm (extChartAt I α (γ σ)) = γ σ :=
      (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hσ.1)
    have hfdσ : fderiv ℝ (chartTransition (I := I) α β)
        (extChartAt I α (γ σ)) = tangentCoordChange I α β (γ σ) := by
      rw [fderiv_chartTransition (I := I) hyσ, hsymmσ]
    show chartVectorRep (I := I) γ β w σ
      = fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α w σ)
    rw [hfdσ, chartVectorRep_apply, chartVectorRep_apply]
    exact (tangentCoordChange_comp (I := I)
      ⟨⟨mem_extChartAt_source (I := I) (γ σ),
        by rw [extChartAt_source]; exact hσ.1⟩,
        by rw [extChartAt_source]; exact hσ.2⟩).symm
  have hC' : HasDerivAt (fun σ => fderiv ℝ (chartTransition (I := I) α β)
        (extChartAt I α (γ σ)))
      (fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
        (extChartAt I α (γ τ))
        (deriv (fun σ => extChartAt I α (γ σ)) τ)) τ :=
    (hasFDerivAt_fderiv_chartTransition (I := I) hyT).comp_hasDerivAt τ hu
  have huβ : HasDerivAt (fun σ => extChartAt I β (γ σ))
      (tangentCoordChange I α β (γ τ)
        (deriv (fun σ => extChartAt I α (γ σ)) τ)) τ := by
    have hcomp := hTd.comp_hasDerivAt τ hu
    have hcong : (fun σ => extChartAt I β (γ σ)) =ᶠ[𝓝 τ]
        fun σ => chartTransition (I := I) α β (extChartAt I α (γ σ)) := by
      filter_upwards [hev_mem] with σ hσ
      exact (chartTransition_extChartAt (I := I) hσ.1).symm
    exact hcomp.congr_of_eventuallyEq hcong
  have hfd : fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
      = tangentCoordChange I α β (γ τ) := hTd.fderiv
  have hwτ : chartVectorRep (I := I) γ β w τ
      = fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α w τ) := hrep.self_of_nhds
  have hval := (hC'.hasDerivWithinAt.clm_apply
    (h τ hτ)).congr_of_eventuallyEq
    (hrep.filter_mono nhdsWithin_le_nhds) hrep.self_of_nhds
  have heq : -Geodesic.chartChristoffelContraction (I := I) g β
        (deriv (fun σ => extChartAt I β (γ σ)) τ)
        (chartVectorRep (I := I) γ β w τ) (extChartAt I β (γ τ))
      = fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
          (extChartAt I α (γ τ))
          (deriv (fun σ => extChartAt I α (γ σ)) τ)
          (chartVectorRep (I := I) γ α w τ)
        + fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
          (-Geodesic.chartChristoffelContraction (I := I) g α
              (deriv (fun σ => extChartAt I α (γ σ)) τ)
              (chartVectorRep (I := I) γ α w τ)
              (extChartAt I α (γ τ))) := by
    rw [hfd, map_neg,
      chartChristoffelContraction_change (I := I) g β α hxβ hxα
        (deriv (fun σ => extChartAt I α (γ σ)) τ)
        (chartVectorRep (I := I) γ α w τ),
      huβ.deriv, hwτ, hfd]
    abel
  rw [heq]
  exact hval

end Transfer

/-! ### The manifold-level parallel field predicate -/

/-- **Math.** **Parallel field along a curve, manifold form.** An own-foot field
`w : ℝ → E` along `γ` (each `w τ` read as an element of `T_{γ τ} M`) is *parallel on
`[a, b]`* if near every time `t₀ ∈ [a, b]` there are a chart basepoint `α` and a
subinterval `[a', b'] ∋ t₀` whose `γ`-image lies in the chart at `α`, on which the
chart reading of `w` solves the parallel-transport ODE (`IsParallelSolOn`).  The
notion is chart-local, so it is meaningful for curves that leave any single chart. -/
def IsParallelFieldAlongOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (w : ℝ → E) (a b : ℝ) : Prop :=
  ∀ t₀ ∈ Icc a b, ∃ (α : M) (a' b' : ℝ), a' < b' ∧ t₀ ∈ Icc a' b' ∧
    Icc a' b' ⊆ Icc a b ∧ Icc a' b' ∈ 𝓝[Icc a b] t₀ ∧
    (∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H α).source) ∧
    IsParallelSolOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (chartVectorRep (I := I) γ α w) a' b'

/-! ### Localization of a manifold parallel field into one chart -/

section Localize

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Localization.** A manifold parallel field restricts, on any
subinterval whose `γ`-image lies in the source of one chart `β`, to a chart-`β`
certificate on the whole subinterval: each chart-local witness transfers to `β`
(`IsParallelSolOn.transfer`) and the certificates glue by locality of
`HasDerivWithinAt`. -/
theorem IsParallelFieldAlongOn.isParallelSolOn_of_mem_source
    {g : RiemannianMetric I M} {γ : ℝ → M} {w : ℝ → E} {a b : ℝ}
    (hPar : IsParallelFieldAlongOn (I := I) g γ w a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {β : M} {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (hsrcβ : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H β).source) :
    IsParallelSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
      (chartVectorRep (I := I) γ β w) c d := by
  have key : ∀ t ∈ Icc c d, ∃ a' b' : ℝ, t ∈ Icc a' b' ∧
      Icc a' b' ⊆ Icc c d ∧ Icc a' b' ∈ 𝓝[Icc c d] t ∧
      IsParallelSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
        (chartVectorRep (I := I) γ β w) a' b' := by
    intro t ht
    obtain ⟨α', a₁, b₁, hab₁, ht₁, hsub₁, hnbhd₁, hsrc₁, hPar₁⟩ := hPar t (hsub ht)
    refine ⟨max a₁ c, min b₁ d, ⟨max_le ht₁.1 ht.1, le_min ht₁.2 ht.2⟩, ?_, ?_, ?_⟩
    · exact Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
    · obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hnbhd₁
      refine mem_nhdsWithin.2 ⟨U, hUopen, htU, fun σ hσ => ?_⟩
      have hσ₁ : σ ∈ Icc a₁ b₁ := hUsub ⟨hσ.1, hsub hσ.2⟩
      exact ⟨max_le hσ₁.1 hσ.2.1, le_min hσ₁.2 hσ.2.2⟩
    · have hgeo' : IsGeodesicOn (I := I) g γ (Icc (max a₁ c) (min b₁ d)) :=
        fun τ hτ => hgeo τ (hsub ⟨le_trans (le_max_right _ _) hτ.1,
          le_trans hτ.2 (min_le_right _ _)⟩)
      have hγc' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d), ContinuousAt γ τ :=
        fun τ hτ => hγc τ (hsub ⟨le_trans (le_max_right _ _) hτ.1,
          le_trans hτ.2 (min_le_right _ _)⟩)
      have hsrcα' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d),
          γ τ ∈ (chartAt H α').source :=
        fun τ hτ => hsrc₁ τ ⟨le_trans (le_max_left _ _) hτ.1,
          le_trans hτ.2 (min_le_left _ _)⟩
      have hsrcβ' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d),
          γ τ ∈ (chartAt H β).source :=
        fun τ hτ => hsrcβ τ ⟨le_trans (le_max_right _ _) hτ.1,
          le_trans hτ.2 (min_le_right _ _)⟩
      exact (hPar₁.mono (le_max_left _ _) (min_le_left _ _)).transfer
        hgeo' hγc' hsrcα' hsrcβ'
  intro t ht
  obtain ⟨a', b', ht', _hsub', hnbhd', hcert⟩ := key t ht
  exact (hcert t ht').mono_of_mem_nhdsWithin hnbhd'

/-- **Math.** A single-chart parallel field with prescribed chart reading at the
left endpoint, returned as an intrinsic own-foot field along `γ`: solve the chart
parallel ODE (`exists_isParallelSol_Icc_of_curve`) and read the solution back to the
feet of `γ`. -/
theorem exists_intrinsic_chart_parallel
    {g : RiemannianMetric I M} {γ : ℝ → M} {l r : ℝ} {β : M}
    (hlr : l ≤ r)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc l r))
    (hγc : ∀ t ∈ Icc l r, ContinuousAt γ t)
    (hsrc : ∀ τ ∈ Icc l r, γ τ ∈ (chartAt H β).source)
    (P0 : E) :
    ∃ w : ℝ → E,
      IsParallelSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
        (chartVectorRep (I := I) γ β w) l r
      ∧ chartVectorRep (I := I) γ β w l = P0
      ∧ (∀ τ ∈ Icc l r, w τ
          = tangentCoordChange I β (γ τ) (γ τ)
              (chartVectorRep (I := I) γ β w τ)) := by
  have hu_cont : ContinuousOn (fun τ => extChartAt I β (γ τ)) (Icc l r) := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc τ hτ)).comp
        (hγc τ hτ)).continuousWithinAt
  have hu'_cont : ContinuousOn (deriv (fun τ => extChartAt I β (γ τ)))
      (Icc l r) := fun τ hτ =>
    (hgeo.continuousAt_deriv_extChartAt hτ (hγc τ hτ) (hsrc τ hτ)).continuousWithinAt
  have hmem : ∀ τ ∈ Icc l r, (fun τ' => extChartAt I β (γ τ')) τ
      ∈ interior (extChartAt I β).target := by
    intro τ hτ
    rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
    exact (extChartAt I β).map_source (by rw [extChartAt_source]; exact hsrc τ hτ)
  obtain ⟨wc, hwcl, hsys⟩ :=
    exists_isParallelSol_Icc_of_curve (I := I) g β hlr hu_cont hu'_cont hmem P0
  refine ⟨fun τ => tangentCoordChange I β (γ τ) (γ τ) (wc τ), ?_, ?_, ?_⟩
  · refine hsys.congr ?_
    intro τ hτ
    show tangentCoordChange I (γ τ) β (γ τ)
      (tangentCoordChange I β (γ τ) (γ τ) (wc τ)) = wc τ
    exact tangentCoordChange_realize_self (I := I) (hsrc τ hτ) (wc τ)
  · show tangentCoordChange I (γ l) β (γ l)
      (tangentCoordChange I β (γ l) (γ l) (wc l)) = P0
    rw [tangentCoordChange_realize_self (I := I) (hsrc l (left_mem_Icc.2 hlr)) (wc l)]
    exact hwcl
  · intro τ hτ
    show tangentCoordChange I β (γ τ) (γ τ) (wc τ)
      = tangentCoordChange I β (γ τ) (γ τ)
          (tangentCoordChange I (γ τ) β (γ τ)
            (tangentCoordChange I β (γ τ) (γ τ) (wc τ)))
    rw [tangentCoordChange_realize_self (I := I) (hsrc τ hτ) (wc τ)]

end Localize

/-! ### Existence of a manifold parallel field with prescribed initial value -/

section Existence

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Existence of parallel transport along a geodesic** with prescribed
initial value (do Carmo Ch. 2, Prop. 2.6, manifold form).  The geodesic may cross
arbitrarily many charts: the solution is continued by a supremum walk, gluing
single-chart parallel fields by ODE uniqueness through the chart-change covariance of
the parallel-transport ODE (`IsParallelSolOn.transfer`).  This is the parallel field
`w(t)` of do Carmo's constant-curvature Jacobi fields (Example 2.3), the missing
ingredient of the antipodal example (Example 3.3).

Blueprint: `ex:dc-ch5-2-3`, `ex:dc-ch5-3-3`. -/
theorem exists_parallelFieldAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (w₀ : E) :
    ∃ w : ℝ → E, IsParallelFieldAlongOn (I := I) g γ w a b ∧ w a = w₀ := by
  classical
  -- a uniform chart interval around each time
  have hchart : ∀ c0 ∈ Icc a b, ∃ ε > (0 : ℝ),
      ∀ σ ∈ Icc (c0 - ε) (c0 + ε), γ σ ∈ (chartAt H (γ c0)).source := by
    intro c0 hc0
    have h1 := (hγc c0 hc0).preimage_mem_nhds
      ((chartAt H (γ c0)).open_source.mem_nhds (mem_chart_source H (γ c0)))
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 h1
    refine ⟨ε / 2, by linarith, fun σ hσ => hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have h2 : |σ - c0| ≤ ε / 2 := abs_le.2 ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    linarith
  -- the set of right endpoints up to which a solution exists
  set S : Set ℝ := {c | c ∈ Ioc a b ∧ ∃ w : ℝ → E,
    IsParallelFieldAlongOn (I := I) g γ w a c ∧ w a = w₀} with hS
  -- initial step: a single-chart solution near `a`
  obtain ⟨ε₀, hε₀, hball₀⟩ := hchart a ⟨le_refl a, hab.le⟩
  have hstep0 : min b (a + ε₀) ∈ S := by
    set r₀ := min b (a + ε₀) with hr₀
    have har₀ : a < r₀ := lt_min hab (by linarith)
    have hr₀b : r₀ ≤ b := min_le_left _ _
    have hsub₀ : Icc a r₀ ⊆ Icc a b := Icc_subset_Icc le_rfl hr₀b
    have hsrc₀ : ∀ τ ∈ Icc a r₀, γ τ ∈ (chartAt H (γ a)).source :=
      fun τ hτ => hball₀ τ ⟨by linarith [hτ.1], le_trans hτ.2
        (le_trans (min_le_right _ _) (by linarith))⟩
    obtain ⟨w1, hcert1, hw1l, _hwred⟩ :=
      exists_intrinsic_chart_parallel (I := I) har₀.le
        (fun τ hτ => hgeo τ (hsub₀ hτ)) (fun τ hτ => hγc τ (hsub₀ hτ)) hsrc₀ (w₀ : E)
    have hw1a : w1 a = w₀ := by
      have h1 : chartVectorRep (I := I) γ (γ a) w1 a = w1 a := by
        rw [chartVectorRep_apply]
        exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) (γ a))
      rw [← h1, hw1l]
    refine ⟨⟨har₀, hr₀b⟩, w1, ?_, hw1a⟩
    intro t₀ ht₀
    exact ⟨γ a, a, r₀, har₀, ht₀, subset_rfl, self_mem_nhdsWithin, hsrc₀, hcert1⟩
  have hne : S.Nonempty := ⟨_, hstep0⟩
  have hbdd : BddAbove S := ⟨b, fun s hs => hs.1.2⟩
  set c := sSup S with hc
  have hac : a < c := lt_of_lt_of_le (lt_min hab (by linarith)) (le_csSup hbdd hstep0)
  have hcb : c ≤ b := csSup_le hne fun s hs => hs.1.2
  -- chart at the supremum
  obtain ⟨ε, hε, hball⟩ := hchart c ⟨hac.le, hcb⟩
  -- a solved endpoint close below the supremum
  have hδ : (0 : ℝ) < min ε (c - a) := lt_min hε (by linarith)
  obtain ⟨c', hc'S, hc'lt⟩ :=
    exists_lt_of_lt_csSup hne (show c - min ε (c - a) < sSup S by rw [← hc]; linarith)
  have hc'le : c' ≤ c := le_csSup hbdd hc'S
  obtain ⟨hc'Ioc, w1, hPar1, hw1a⟩ := hc'S
  -- the gluing window
  set l := max a (c - ε) with hl
  set r := min b (c + ε) with hr
  have hlc' : l < c' := max_lt hc'Ioc.1 (by have := min_le_left ε (c - a); linarith)
  have hcr : c ≤ r := le_min hcb (by linarith)
  have hlc : l < c := lt_of_lt_of_le hlc' hc'le
  have hlr : l < r := lt_of_lt_of_le hlc hcr
  have hla : a ≤ l := le_max_left _ _
  have hrb : r ≤ b := min_le_left _ _
  have hsub_lr : Icc l r ⊆ Icc a b := Icc_subset_Icc hla hrb
  have hsrc_lr : ∀ τ ∈ Icc l r, γ τ ∈ (chartAt H (γ c)).source :=
    fun τ hτ => hball τ ⟨le_trans (by have := le_max_right a (c - ε); linarith) hτ.1,
      le_trans hτ.2 (min_le_right _ _)⟩
  have hgeo_lr : IsGeodesicOn (I := I) g γ (Icc l r) := fun τ hτ => hgeo τ (hsub_lr hτ)
  have hγc_lr : ∀ τ ∈ Icc l r, ContinuousAt γ τ := fun τ hτ => hγc τ (hsub_lr hτ)
  -- localize the old solution into the chart at `γ c` on `[l, c']`
  have hsub_ac' : Icc a c' ⊆ Icc a b := Icc_subset_Icc le_rfl hc'Ioc.2
  have hsub_lc' : Icc l c' ⊆ Icc l r := Icc_subset_Icc le_rfl (le_trans hc'le hcr)
  have hloc := hPar1.isParallelSolOn_of_mem_source
    (fun τ hτ => hgeo τ (hsub_ac' hτ)) (fun τ hτ => hγc τ (hsub_ac' hτ))
    (Icc_subset_Icc hla le_rfl) (fun τ hτ => hsrc_lr τ (hsub_lc' hτ))
  -- solve in the chart at `γ c` on `[l, r]` with matched data at `l`
  obtain ⟨w2, hcert2, hw2l, _hwred2⟩ :=
    exists_intrinsic_chart_parallel (I := I) hlr.le hgeo_lr hγc_lr hsrc_lr
      (chartVectorRep (I := I) γ (γ c) w1 l)
  -- coefficient bound for uniqueness on `[l, c']`
  have hu_cont : ContinuousOn (fun τ => extChartAt I (γ c) (γ τ)) (Icc l c') := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc_lr τ (hsub_lc' hτ))).comp
        (hγc_lr τ (hsub_lc' hτ))).continuousWithinAt
  have hu'_cont : ContinuousOn (deriv (fun τ => extChartAt I (γ c) (γ τ))) (Icc l c') :=
    fun τ hτ => (hgeo_lr.continuousAt_deriv_extChartAt (hsub_lc' hτ)
      (hγc_lr τ (hsub_lc' hτ)) (hsrc_lr τ (hsub_lc' hτ))).continuousWithinAt
  have hmem : ∀ τ ∈ Icc l c', (fun τ' => extChartAt I (γ c) (γ τ')) τ
      ∈ interior (extChartAt I (γ c)).target := by
    intro τ hτ
    rw [(isOpen_extChartAt_target (I := I) (γ c)).interior_eq]
    exact (extChartAt I (γ c)).map_source
      (by rw [extChartAt_source]; exact hsrc_lr τ (hsub_lc' hτ))
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_chartChristoffelContractionRight_comp (I := I) g (γ c) hu_cont hu'_cont hmem)
  have hKnn : ∀ t ∈ Icc l c', ‖chartChristoffelContractionRight (I := I) g (γ c)
      (deriv (fun τ => extChartAt I (γ c) (γ τ)) t) (extChartAt I (γ c) (γ t))‖₊
      ≤ (⟨max K 0, le_max_right _ _⟩ : ℝ≥0) := fun t ht => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact (hK t ht).trans (le_max_left _ _)
  -- ODE uniqueness: the two chart readings agree on `[l, c']`
  have hEq := isParallelSol_eqOn_Icc (I := I) g (γ c) (fun τ => extChartAt I (γ c) (γ τ)) hKnn
    hloc (hcert2.mono le_rfl (le_trans hc'le hcr)) hw2l.symm
  have hweq : ∀ τ ∈ Icc l c', w1 τ = w2 τ := by
    intro τ hτ
    have h1 := hEq hτ
    have h2 := congrArg (tangentCoordChange I (γ c) (γ τ) (γ τ)) h1
    rwa [chartVectorRep_apply, chartVectorRep_apply,
      tangentCoordChange_readback (I := I) (hsrc_lr τ (hsub_lc' hτ)) (w1 τ),
      tangentCoordChange_readback (I := I) (hsrc_lr τ (hsub_lc' hτ)) (w2 τ)] at h2
  -- the glued field
  set wg : ℝ → E := fun τ => if τ ≤ c' then w1 τ else w2 τ with hwg
  have hwg_eq_w1 : ∀ τ ∈ Icc a c', wg τ = w1 τ := fun τ hτ => if_pos hτ.2
  have hwg_eq_w2 : ∀ τ ∈ Icc l r, wg τ = w2 τ := by
    intro τ hτ
    by_cases hτc : τ ≤ c'
    · show (if τ ≤ c' then w1 τ else w2 τ) = w2 τ
      rw [if_pos hτc]; exact hweq τ ⟨hτ.1, hτc⟩
    · show (if τ ≤ c' then w1 τ else w2 τ) = w2 τ
      rw [if_neg hτc]
  -- the glued field is parallel on `[a, r]`
  have hAlong : IsParallelFieldAlongOn (I := I) g γ wg a r := by
    intro t₀ ht₀
    by_cases ht₀c : t₀ < c'
    · obtain ⟨α', a₁, b₁, hab₁, ht₁, hsub₁, hnbhd₁, hsrc₁, hPar₁⟩ := hPar1 t₀ ⟨ht₀.1, ht₀c.le⟩
      refine ⟨α', a₁, b₁, hab₁, ht₁,
        hsub₁.trans (Icc_subset_Icc le_rfl (le_trans hc'le hcr)), ?_, hsrc₁, ?_⟩
      · obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hnbhd₁
        refine mem_nhdsWithin.2 ⟨U ∩ Iio c', hUopen.inter isOpen_Iio, ⟨htU, ht₀c⟩,
          fun σ hσ => ?_⟩
        exact hUsub ⟨hσ.1.1, ⟨hσ.2.1, hσ.1.2.le⟩⟩
      · refine hPar₁.congr ?_
        intro τ hτ
        rw [chartVectorRep_apply, chartVectorRep_apply, hwg_eq_w1 τ (hsub₁ hτ)]
    · rw [not_lt] at ht₀c
      refine ⟨γ c, l, r, hlr, ⟨le_trans hlc'.le ht₀c, ht₀.2⟩, Icc_subset_Icc hla le_rfl,
        ?_, hsrc_lr, ?_⟩
      · refine mem_nhdsWithin.2 ⟨Ioi l, isOpen_Ioi, lt_of_lt_of_le hlc' ht₀c, fun σ hσ => ?_⟩
        exact ⟨hσ.1.le, hσ.2.2⟩
      · refine hcert2.congr ?_
        intro τ hτ
        rw [chartVectorRep_apply, chartVectorRep_apply, hwg_eq_w2 τ hτ]
  have hwga : wg a = w₀ := by
    have h1 : wg a = w1 a := hwg_eq_w1 a ⟨le_refl a, hc'Ioc.1.le⟩
    rw [h1, hw1a]
  have hrS : r ∈ S := ⟨⟨lt_of_lt_of_le hac hcr, hrb⟩, wg, hAlong, hwga⟩
  rcases lt_or_eq_of_le hcb with hlt | heqb
  · exfalso
    have h1 : r ≤ c := le_csSup hbdd hrS
    have h2 : c < r := lt_min hlt (by linarith)
    linarith
  · have hrb' : r = b := by rw [hr, ← heqb]; exact min_eq_left (by linarith)
    obtain ⟨_, w, hPar, hwa⟩ := hrS
    exact ⟨w, hrb' ▸ hPar, hwa⟩

end Existence

/-! ### Parallel transport is an isometry (manifold form) -/

section Isometry

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Parallel transport preserves the metric** (do Carmo Ch. 2, Cor. 3.3,
manifold form).  The intrinsic pairing `⟨v(t), w(t)⟩_g` of two parallel fields along a
geodesic `γ` is constant, equal to its value at `a`.  The pairing has zero derivative
at every point — chart-locally it is the chart Gram pairing of the two chart readings,
whose derivative vanishes by the metric-compatibility product rule
(`hasDerivAt_chartMetricInner_along`) since both readings are parallel
(`covariantDerivCoord = 0`) — and it is continuous, so monotone and antitone, hence
constant.

Blueprint: `ex:dc-ch5-2-3`, `ex:dc-ch5-3-3`. -/
theorem IsParallelFieldAlongOn.metricInner_const
    {g : RiemannianMetric I M} {γ : ℝ → M} {v w : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hv : IsParallelFieldAlongOn (I := I) g γ v a b)
    (hw : IsParallelFieldAlongOn (I := I) g γ w a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    g.metricInner (γ t) (v t : TangentSpace I (γ t)) (w t)
      = g.metricInner (γ a) (v a : TangentSpace I (γ a)) (w a) := by
  classical
  set φ : ℝ → ℝ := fun s => g.metricInner (γ s) (v s : TangentSpace I (γ s)) (w s) with hφ
  -- continuity of `φ` on `[a, b]`, chart-locally
  have hφc : ContinuousOn φ (Icc a b) := by
    intro t₀ ht₀
    obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, _⟩ := hv t₀ ht₀
    have hvloc := hv.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc (β := α)
    have hwloc := hw.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc (β := α)
    have hu_cont : ContinuousOn (fun τ => extChartAt I α (γ τ)) (Icc a' b') := by
      intro τ hτ
      exact ((continuousAt_extChartAt' (I := I)
        (by rw [extChartAt_source]; exact hsrc τ hτ)).comp
          (hγc τ (hsub hτ))).continuousWithinAt
    have hmemT : ∀ τ ∈ Icc a' b', (fun τ' => extChartAt I α (γ τ')) τ
        ∈ (extChartAt I α).target := fun τ hτ =>
      (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc τ hτ)
    have hvc : ContinuousOn (chartVectorRep (I := I) γ α v) (Icc a' b') :=
      fun τ hτ => (hvloc τ hτ).continuousWithinAt
    have hwc : ContinuousOn (chartVectorRep (I := I) γ α w) (Icc a' b') :=
      fun τ hτ => (hwloc τ hτ).continuousWithinAt
    have hψc := continuousOn_chartMetricInner_pairing (I := I) g α hu_cont hmemT hvc hwc
    have hφ_within : ContinuousWithinAt φ (Icc a' b') t₀ :=
      (hψc t₀ ht').congr (fun τ hτ => metricInner_eq_chartMetricInner_rep (I := I) g (hsrc τ hτ) v w)
        (metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t₀ ht') v w)
    exact hφ_within.mono_of_mem_nhdsWithin hnbhd
  -- zero derivative of `φ` at each interior point, chart-locally
  have hderiv : ∀ s ∈ interior (Icc a b),
      HasDerivWithinAt φ 0 (interior (Icc a b)) s := by
    intro s hs
    have hsmem : s ∈ Icc a b := interior_subset hs
    obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, _⟩ := hv s hsmem
    have hvloc := hv.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc (β := α)
    have hwloc := hw.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc (β := α)
    -- the chart interval is a full neighbourhood of the interior point
    have hnbhd_full : Icc a' b' ∈ 𝓝 s := by
      rw [nhdsWithin_eq_nhds.2 (mem_interior_iff_mem_nhds.1 hs)] at hnbhd
      exact hnbhd
    set u : ℝ → E := fun τ => extChartAt I α (γ τ) with hu_def
    have hVd : HasDerivAt (chartVectorRep (I := I) γ α v)
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u s)
          (chartVectorRep (I := I) γ α v s) (u s)) s :=
      (hvloc s ht').hasDerivAt hnbhd_full
    have hWd : HasDerivAt (chartVectorRep (I := I) γ α w)
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u s)
          (chartVectorRep (I := I) γ α w s) (u s)) s :=
      (hwloc s ht').hasDerivAt hnbhd_full
    have hu_diff : DifferentiableAt ℝ u s :=
      hgeo.differentiableAt_extChartAt hsmem (hγc s hsmem) (hsrc s ht')
    have hmemT : u s ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc s ht')
    have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u s) :=
      fun i j => differentiableAt_chartGramOnE (I := I) g α hmemT i j
    have hbase : (extChartAt I α).symm (u s)
        ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      symm_extChartAt_mem_baseSet (I := I) (hsrc s ht')
    have hcV : covariantDerivCoord (I := I) g α u (chartVectorRep (I := I) γ α v) s = 0 := by
      rw [covariantDerivCoord_def, hVd.deriv]; abel
    have hcW : covariantDerivCoord (I := I) g α u (chartVectorRep (I := I) γ α w) s = 0 := by
      rw [covariantDerivCoord_def, hWd.deriv]; abel
    have hmain := hasDerivAt_chartMetricInner_along (I := I) g α u
      (chartVectorRep (I := I) γ α v) (chartVectorRep (I := I) γ α w)
      hu_diff hVd.differentiableAt hWd.differentiableAt hG hbase
    have hval : chartMetricInner (I := I) g α (u s)
          (covariantDerivCoord (I := I) g α u (chartVectorRep (I := I) γ α v) s)
          (chartVectorRep (I := I) γ α w s)
        + chartMetricInner (I := I) g α (u s) (chartVectorRep (I := I) γ α v s)
          (covariantDerivCoord (I := I) g α u (chartVectorRep (I := I) γ α w) s) = 0 := by
      rw [hcV, hcW, chartMetricInner_zero_left, chartMetricInner_zero_right, add_zero]
    rw [hval] at hmain
    -- `φ` agrees with the chart pairing near `s`
    have hcong : φ =ᶠ[𝓝 s] fun σ => chartMetricInner (I := I) g α (u σ)
        (chartVectorRep (I := I) γ α v σ) (chartVectorRep (I := I) γ α w σ) := by
      filter_upwards [hnbhd_full] with σ hσ
      exact metricInner_eq_chartMetricInner_rep (I := I) g (hsrc σ hσ) v w
    exact ((hmain.congr_of_eventuallyEq hcong).hasDerivWithinAt).mono interior_subset
  have hmono : MonotoneOn φ (Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hφc hderiv (fun s _ => le_refl 0)
  have hanti : AntitoneOn φ (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hφc hderiv (fun s _ => le_refl 0)
  have haq : a ∈ Icc a b := ⟨le_rfl, hab⟩
  exact le_antisymm (hanti haq ht ht.1) (hmono haq ht ht.1)

end Isometry

end Riemannian.Jacobi

end
