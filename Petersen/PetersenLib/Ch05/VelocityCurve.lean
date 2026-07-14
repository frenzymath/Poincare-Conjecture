import PetersenLib.Ch05.ChartTransition
import PetersenLib.Ch05.Geodesics

/-!
# Petersen Ch. 5, §5.2 — continuity of the velocity curve of a geodesic

The **velocity curve** of a curve `γ : ℝ → M` is the lift
`t ↦ (γ(t), γ̇(t)) ∈ TM`, with the velocity read in the canonical chart at the
moving foot (`geodesicVelocityCurve`).  Along a continuous geodesic the
velocity curve is continuous (`continuousOn_geodesicVelocityCurve`): in a
fixed chart `α` near a base time, the velocity transfer of the geodesic-ODE
chart-transition law (`chartReading_geodesicODE_transfer`) identifies the
trivialization fibre coordinate of the velocity with the derivative of the
fixed-chart reading `u = φ_α ∘ γ`, and the geodesic equation makes `u̇`
differentiable, hence continuous.

This is the input that makes the velocity track
`{(γ(t), γ̇(t)) : t ∈ [a, b]}` of a geodesic over a compact time interval a
compact subset of `TM` — the starting point of the flow-box subdivision in
Petersen's Lemma 5.2.6 (`lem:pet-ch5-uniform-neighborhood`), and of the
exponential-map material of §5.5.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The **velocity curve** of `γ : ℝ → M`: the tangent-bundle lift
`t ↦ (γ(t), γ̇(t)) ∈ TM`, the velocity being read in the canonical chart at the
moving foot `γ t` (the canonical identification `T_{γ t}M ≅ E`). -/
def geodesicVelocityCurve (γ : ℝ → M) : ℝ → TangentBundle I M := fun t =>
  ⟨γ t, (deriv (Geodesic.chartLocalCurve (I := I) γ t) t : E)⟩

@[simp] lemma geodesicVelocityCurve_proj (γ : ℝ → M) (t : ℝ) :
    (geodesicVelocityCurve (I := I) γ t).proj = γ t := rfl

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** **The velocity curve of a geodesic is continuous.**  Along a
continuous geodesic on an open time set, `t ↦ (γ(t), γ̇(t)) ∈ TM` is
continuous: near a base time `t₀` the trivialization fibre coordinate of the
velocity at `α = γ t₀` is the derivative `u̇` of the fixed-chart reading
`u = φ_α ∘ γ` (velocity transfer of the chart-transition law), and the
geodesic equation makes `u̇` differentiable. -/
theorem continuousOn_geodesicVelocityCurve (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hcont : ContinuousOn γ J)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ J) :
    ContinuousOn (geodesicVelocityCurve (I := I) γ) J := by
  intro t₀ ht₀
  refine ContinuousAt.continuousWithinAt ?_
  set α : M := γ t₀ with hα_def
  set u : ℝ → E := fun s => extChartAt I α (γ s) with hu_def
  set e := trivializationAt E (TangentSpace I) α with he_def
  -- an open interval around `t₀` where the feet stay in the chart at `α`
  have hct₀ : ContinuousAt γ t₀ := hcont.continuousAt (hJ.mem_nhds ht₀)
  have hev_src : ∀ᶠ s in 𝓝 t₀, s ∈ J ∧ γ s ∈ (extChartAt I α).source := by
    filter_upwards [hJ.mem_nhds ht₀, hct₀.eventually_mem
      ((isOpen_extChartAt_source α).mem_nhds
        (by rw [hα_def]; exact mem_extChartAt_source (I := I) (γ t₀)))] with s h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨J', hJ'all, hJ'o, htJ'⟩ := eventually_nhds_iff.mp hev_src
  -- the velocity transfer at each time of `J'`
  have key : ∀ s ∈ J',
      deriv u s = tangentCoordChange I (γ s) α (γ s)
        (deriv (Geodesic.chartLocalCurve (I := I) γ s) s) ∧
      DifferentiableAt ℝ (deriv u) s := by
    intro s hs
    obtain ⟨hsJ, hs_src⟩ := hJ'all s hs
    obtain ⟨v, a, hv, hevd, ha, heq⟩ := hγ s hsJ
    have hcs : ContinuousAt γ s := hcont.continuousAt (hJ.mem_nhds hsJ)
    have hev : ∀ᶠ r in 𝓝 s,
        γ r ∈ (extChartAt I (γ s)).source ∩ (extChartAt I α).source := by
      filter_upwards [hcs.eventually_mem ((isOpen_extChartAt_source (γ s)).mem_nhds
        (mem_extChartAt_source (I := I) (γ s))),
        hJ'o.mem_nhds hs] with r h1 h2
      exact ⟨h1, (hJ'all r h2).2⟩
    have heq' : a + Geodesic.chartChristoffelContraction (I := I) g (γ s)
        (deriv (fun s' => extChartAt I (γ s) (γ s')) s)
        (deriv (fun s' => extChartAt I (γ s) (γ s')) s)
        (extChartAt I (γ s) (γ s)) = 0 := by
      have hvd : deriv (fun s' => extChartAt I (γ s) (γ s')) s = v := hv.deriv
      rw [hvd]
      exact heq
    obtain ⟨-, hvel, hB2⟩ := chartReading_geodesicODE_transfer (I := I) g
      (α := γ s) (β := α) hev hevd ha heq'
    exact ⟨hvel, hB2.differentiableAt⟩
  -- the velocity curve factors through the inverse trivialization near `t₀`
  have hbase : ∀ s ∈ J', γ s ∈ e.baseSet := by
    intro s hs
    rw [he_def, TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
    exact (hJ'all s hs).2
  have hfactor : ∀ s ∈ J', geodesicVelocityCurve (I := I) γ s
      = e.toOpenPartialHomeomorph.symm (γ s, deriv u s) := by
    intro s hs
    have hsrc : geodesicVelocityCurve (I := I) γ s ∈ e.source :=
      e.mem_source.mpr (hbase s hs)
    have happ : e (geodesicVelocityCurve (I := I) γ s) = (γ s, deriv u s) := by
      refine Prod.ext (e.coe_fst' (hbase s hs)) ?_
      show (e (geodesicVelocityCurve (I := I) γ s)).2 = deriv u s
      have hfib : (e (geodesicVelocityCurve (I := I) γ s)).2
          = tangentCoordChange I (γ s) α (γ s)
            (deriv (Geodesic.chartLocalCurve (I := I) γ s) s) := by
        show (e (⟨γ s, (deriv (Geodesic.chartLocalCurve (I := I) γ s) s : E)⟩ :
          TangentBundle I M)).2 = _
        rfl
      rw [hfib, ← (key s hs).1]
    rw [← happ, e.symm_apply_apply hsrc]
  -- continuity of the factored expression at `t₀`
  have hderiv_cont : ContinuousAt (deriv u) t₀ :=
    ((key t₀ htJ').2).continuousAt
  have hpair : ContinuousAt (fun s => ((γ s, deriv u s) : M × E)) t₀ :=
    hct₀.prodMk hderiv_cont
  have htarget : ((γ t₀, deriv u t₀) : M × E) ∈ e.target :=
    e.mem_target.mpr (hbase t₀ htJ')
  have hsymm_cont : ContinuousAt e.toOpenPartialHomeomorph.symm (γ t₀, deriv u t₀) :=
    e.toOpenPartialHomeomorph.continuousOn_symm.continuousAt
      (e.open_target.mem_nhds htarget)
  have hcomp : ContinuousAt
      (fun s => e.toOpenPartialHomeomorph.symm (γ s, deriv u s)) t₀ :=
    ContinuousAt.comp (x := t₀) hsymm_cont hpair
  exact hcomp.congr
    (Filter.eventuallyEq_of_mem (hJ'o.mem_nhds htJ') fun s hs => (hfactor s hs).symm)

/-- **Math.** The **velocity track** of a continuous geodesic over a compact time
set is a compact subset of `TM`.  (The starting point of the flow-box
subdivision of Petersen's Lemma 5.2.6.) -/
theorem isCompact_geodesicVelocityCurve_image (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hcont : ContinuousOn γ J)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ J)
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ J) :
    IsCompact (geodesicVelocityCurve (I := I) γ '' K) :=
  hK.image_of_continuousOn
    ((continuousOn_geodesicVelocityCurve (I := I) g hJ hcont hγ).mono hKJ)

end Boundaryless

end PetersenLib
