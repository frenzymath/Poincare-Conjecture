/- Vendored from DoCarmo `OpenGALib/Riemannian/Geodesic/IntrinsicUniqueness.lean`.
   Namespace `Riemannian` mapped to `PetersenLib`; engineering infrastructure only,
   not a blueprint node. -/
import PetersenLib.Vendored.OpenGA.Geodesic.EquationTransfer
import PetersenLib.Vendored.OpenGA.Geodesic.ChartFlow
import PetersenLib.Vendored.OpenGA.Geodesic.HopfRinow.ConstantSpeed

set_option linter.unusedSectionVars false

/-!
# Uniqueness of intrinsic geodesics

Two intrinsic geodesics (curves satisfying the moving-foot geodesic equation
`HasGeodesicEquationAt` at every time of an open preconnected set `s`) that
share their position and chart velocity at one time `t₀ ∈ s` agree on all of
`s` (do Carmo Ch. 3, the uniqueness clause of Theorem 2.2, globalised to the
intrinsic predicate; the statement Ch. 7's Hopf–Rinow gluing consumes).

Proof layout:

* **Local step.** Near any time where the two curves share position and chart
  velocity, read both in the fixed chart at the common foot: by
  `HasGeodesicEquationAt.solvesGeodesicODEAt` (`EquationTransfer.lean`) both
  chart readings `u₁, u₂` solve the second-order geodesic ODE near that time,
  so their first-order lifts `ζᵢ = (uᵢ, uᵢ')` solve the coordinate spray ODE
  `ζ' = F(ζ)`, `F(x, w) = (w, -Γ(w, w)(x))`. `F` is `C¹` on the chart target
  (`contDiffOn_geodesicSprayCoord_prod`, `ChartFlow.lean`), hence locally
  Lipschitz, and Grönwall uniqueness (`ODE_solution_unique_of_mem_Icc`) forces
  `ζ₁ = ζ₂` on a neighbourhood; chart injectivity returns `γ₁ = γ₂` there.

* **Open-closed propagation.** The set
  `{t ∈ s | γ₁ =ᶠ[𝓝 t] γ₂}` is open by definition and relatively closed by
  the local step: at a boundary point `t*`, continuity gives `γ₁ t* = γ₂ t*`,
  and the chart velocities agree because the difference of chart readings is
  differentiable at `t*` and vanishes on a set accumulating at `t*` (its
  derivative is a limit of vanishing difference quotients — the slope
  argument). Preconnectedness of `s` concludes.

* **Caveat (why `[T2Space M]`).** The position match `γ₁ t* = γ₂ t*` at a
  boundary point is uniqueness of limits in `M` and genuinely needs the
  Hausdorff hypothesis carried by
  `IsGeodesicOn.eqOn_of_deriv_chartReading_eq`: on the line with two
  origins, two geodesics can agree off a single time and pass through the
  two origins there, so the global theorem is false for non-Hausdorff `M`.
  The separation property enters *only* through the closure-point position
  match `eq_at_closure_eventuallyEq_of_t2`; the clopen propagation itself
  (`eqOn_of_deriv_chartReading_eq_aux`) is separation-free. The downstream
  consumer (`Completeness.lean`, Hopf–Rinow) works with `[MetricSpace M]`,
  where `T2Space M` is an instance.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **Local uniqueness of intrinsic geodesics.** If two intrinsic
geodesics on an open set `s` share their position and their chart-`β`
velocity reading at a time `t₀ ∈ s` (for any chart basepoint `β` whose
source contains the common foot), they agree on a neighbourhood of `t₀`. -/
theorem IsGeodesicOn.eventuallyEq_of_deriv_chartReading_eq
    {g : RiemannianMetric I M} {γ₁ γ₂ : ℝ → M} {s : Set ℝ} {t₀ : ℝ} {β : M}
    (hs : IsOpen s)
    (h₁ : IsGeodesicOn (I := I) g γ₁ s) (h₂ : IsGeodesicOn (I := I) g γ₂ s)
    (hc₁ : ContinuousOn γ₁ s) (hc₂ : ContinuousOn γ₂ s)
    (ht₀ : t₀ ∈ s) (heq0 : γ₁ t₀ = γ₂ t₀)
    (hβ : γ₁ t₀ ∈ (chartAt H β).source)
    (hv : deriv (chartReading (I := I) β γ₁) t₀
        = deriv (chartReading (I := I) β γ₂) t₀) :
    γ₁ =ᶠ[𝓝 t₀] γ₂ := by
  classical
  set u₁ : ℝ → E := chartReading (I := I) β γ₁ with hu₁_def
  set u₂ : ℝ → E := chartReading (I := I) β γ₂ with hu₂_def
  set F : E × E → E × E := fun z => geodesicSprayCoord (I := I) g β z.1 z.2 with hF_def
  set ζ₁ : ℝ → E × E := fun τ => (u₁ τ, deriv u₁ τ) with hζ₁_def
  set ζ₂ : ℝ → E × E := fun τ => (u₂ τ, deriv u₂ τ) with hζ₂_def
  -- both curves eventually stay in the chart source
  have hβ₂ : γ₂ t₀ ∈ (chartAt H β).source := by rw [← heq0]; exact hβ
  have hsrc₁ : ∀ᶠ τ in 𝓝 t₀, γ₁ τ ∈ (chartAt H β).source :=
    (hc₁.continuousAt (hs.mem_nhds ht₀)).eventually_mem
      ((chartAt H β).open_source.mem_nhds hβ)
  have hsrc₂ : ∀ᶠ τ in 𝓝 t₀, γ₂ τ ∈ (chartAt H β).source :=
    (hc₂.continuousAt (hs.mem_nhds ht₀)).eventually_mem
      ((chartAt H β).open_source.mem_nhds hβ₂)
  -- near `t₀`, the first-order lifts solve the coordinate spray ODE
  have hode₁ : ∀ᶠ τ in 𝓝 t₀, HasDerivAt ζ₁ (F (ζ₁ τ)) τ := by
    filter_upwards [hs.mem_nhds ht₀, hsrc₁] with τ hτs hτsrc
    obtain ⟨hev, a, ha, haeq⟩ :=
      (h₁ τ hτs).solvesGeodesicODEAt (hc₁.continuousAt (hs.mem_nhds hτs)) hτsrc
    have hu' : HasDerivAt u₁ (deriv u₁ τ) τ := hev.self_of_nhds
    have ha' : HasDerivAt (deriv u₁)
        (-chartChristoffelContraction (I := I) g β
          (deriv u₁ τ) (deriv u₁ τ) (u₁ τ)) τ := by
      rwa [eq_neg_of_add_eq_zero_left haeq] at ha
    exact hu'.prodMk ha'
  have hode₂ : ∀ᶠ τ in 𝓝 t₀, HasDerivAt ζ₂ (F (ζ₂ τ)) τ := by
    filter_upwards [hs.mem_nhds ht₀, hsrc₂] with τ hτs hτsrc
    obtain ⟨hev, a, ha, haeq⟩ :=
      (h₂ τ hτs).solvesGeodesicODEAt (hc₂.continuousAt (hs.mem_nhds hτs)) hτsrc
    have hu' : HasDerivAt u₂ (deriv u₂ τ) τ := hev.self_of_nhds
    have ha' : HasDerivAt (deriv u₂)
        (-chartChristoffelContraction (I := I) g β
          (deriv u₂ τ) (deriv u₂ τ) (u₂ τ)) τ := by
      rwa [eq_neg_of_add_eq_zero_left haeq] at ha
    exact hu'.prodMk ha'
  -- the lifts share their initial value
  have hζeq0 : ζ₁ t₀ = ζ₂ t₀ := by
    have h1 : u₁ t₀ = u₂ t₀ := by
      simp only [hu₁_def, hu₂_def, chartReading_def, heq0]
    exact Prod.ext h1 hv
  -- the spray is `C¹` near the initial lifted point, hence locally Lipschitz
  have hz₀target : ζ₁ t₀ ∈ (extChartAt I β).target ×ˢ (univ : Set E) :=
    ⟨(extChartAt I β).map_source (by rw [extChartAt_source]; exact hβ), mem_univ _⟩
  have hFc1 : ContDiffAt ℝ 1 F (ζ₁ t₀) := by
    have hopen : IsOpen ((extChartAt I β).target ×ˢ (univ : Set E)) :=
      (isOpen_extChartAt_target β).prod isOpen_univ
    exact ((contDiffOn_geodesicSprayCoord_prod (I := I) g β).contDiffAt
      (hopen.mem_nhds hz₀target)).of_le (by norm_num)
  obtain ⟨K, sLip, hsLip, hlip⟩ := hFc1.exists_lipschitzOnWith
  -- the lifts eventually stay in the Lipschitz region
  have hζ₁mem : ∀ᶠ τ in 𝓝 t₀, ζ₁ τ ∈ sLip :=
    (hode₁.self_of_nhds).continuousAt.eventually_mem hsLip
  have hζ₂mem : ∀ᶠ τ in 𝓝 t₀, ζ₂ τ ∈ sLip :=
    (hode₂.self_of_nhds).continuousAt.eventually_mem (hζeq0 ▸ hsLip)
  -- choose a compact time window inside all the eventual conditions
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hode₁.and (hode₂.and (hζ₁mem.and (hζ₂mem.and (hsrc₁.and hsrc₂)))))
  have hIccball : Icc (t₀ - ε / 2) (t₀ + ε / 2) ⊆ Metric.ball t₀ ε := by
    intro τ hτ
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have ht₀Ioo : t₀ ∈ Ioo (t₀ - ε / 2) (t₀ + ε / 2) := ⟨by linarith, by linarith⟩
  -- Grönwall uniqueness for the first-order system
  have heqIcc : Set.EqOn ζ₁ ζ₂ (Icc (t₀ - ε / 2) (t₀ + ε / 2)) := by
    refine ODE_solution_unique_of_mem_Icc (v := fun _ => F) (s := fun _ => sLip)
      (fun τ _ => hlip) ht₀Ioo ?_ ?_ ?_ ?_ ?_ ?_ hζeq0
    · exact fun τ hτ => ((hball τ (hIccball hτ)).1.continuousAt).continuousWithinAt
    · exact fun τ hτ => (hball τ (hIccball (Ioo_subset_Icc_self hτ))).1
    · exact fun τ hτ => (hball τ (hIccball (Ioo_subset_Icc_self hτ))).2.2.1
    · exact fun τ hτ => ((hball τ (hIccball hτ)).2.1.continuousAt).continuousWithinAt
    · exact fun τ hτ => (hball τ (hIccball (Ioo_subset_Icc_self hτ))).2.1
    · exact fun τ hτ => (hball τ (hIccball (Ioo_subset_Icc_self hτ))).2.2.2.1
  -- return to the manifold through the chart
  have hIoo : Ioo (t₀ - ε / 2) (t₀ + ε / 2) ∈ 𝓝 t₀ := Ioo_mem_nhds ht₀Ioo.1 ht₀Ioo.2
  filter_upwards [hIoo] with τ hτ
  have hu : u₁ τ = u₂ τ := congrArg Prod.fst (heqIcc (Ioo_subset_Icc_self hτ))
  have h1 : γ₁ τ ∈ (extChartAt I β).source := by
    rw [extChartAt_source]
    exact (hball τ (hIccball (Ioo_subset_Icc_self hτ))).2.2.2.2.1
  have h2 : γ₂ τ ∈ (extChartAt I β).source := by
    rw [extChartAt_source]
    exact (hball τ (hIccball (Ioo_subset_Icc_self hτ))).2.2.2.2.2
  calc γ₁ τ = (extChartAt I β).symm (u₁ τ) := ((extChartAt I β).left_inv h1).symm
    _ = (extChartAt I β).symm (u₂ τ) := by rw [hu]
    _ = γ₂ τ := (extChartAt I β).left_inv h2

/-- **Math.** Auxiliary for the closedness step of the clopen propagation, isolating
the only place where a separation property of `M` enters: two curves continuous at
a time `t` adherent to the set where they eventually agree take the same value at
`t`, by uniqueness of limits along the (nontrivial) filter of approach times.

Without a separation hypothesis the statement is false (line with two origins). -/
private lemma eq_at_closure_eventuallyEq_of_t2 [T2Space M]
    {γ₁ γ₂ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (hc₁ : ContinuousOn γ₁ s) (hc₂ : ContinuousOn γ₂ s)
    (hts : t ∈ s) (htc : t ∈ closure {τ | γ₁ =ᶠ[𝓝 τ] γ₂}) :
    γ₁ t = γ₂ t := by
  set S : Set ℝ := {τ | γ₁ =ᶠ[𝓝 τ] γ₂} with hS_def
  haveI hne : (𝓝[S] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp htc
  have h₁t : Tendsto γ₁ (𝓝[S] t) (𝓝 (γ₁ t)) :=
    (hc₁.continuousAt (hs.mem_nhds hts)).tendsto.mono_left nhdsWithin_le_nhds
  have h₂t : Tendsto γ₂ (𝓝[S] t) (𝓝 (γ₂ t)) :=
    (hc₂.continuousAt (hs.mem_nhds hts)).tendsto.mono_left nhdsWithin_le_nhds
  have heq : γ₁ =ᶠ[𝓝[S] t] γ₂ := by
    filter_upwards [eventually_mem_nhdsWithin] with τ hτ
    exact (hτ : γ₁ =ᶠ[𝓝 τ] γ₂).eq_of_nhds
  exact tendsto_nhds_unique (h₁t.congr' heq) h₂t

/-- **Math.** The open-closed propagation core of intrinsic geodesic uniqueness,
with the closure-point position match supplied as a hypothesis `hclosurePos` —
the only step of the clopen argument that needs a separation property of `M`.
The agreement set `{t | γ₁ =ᶠ[𝓝 t] γ₂}` is open by definition of eventual
equality, contains `t₀` by the local theorem, and is relatively closed in `s`:
at a closure point the positions agree by `hclosurePos`, and the chart
velocities agree because the difference of the chart readings at the common
foot is differentiable there and vanishes on a set of times accumulating at
the point (its derivative is the limit of vanishing slopes). -/
private theorem eqOn_of_deriv_chartReading_eq_aux
    {g : RiemannianMetric I M} {γ₁ γ₂ : ℝ → M} {s : Set ℝ} {t₀ : ℝ} {β : M}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (h₁ : IsGeodesicOn (I := I) g γ₁ s) (h₂ : IsGeodesicOn (I := I) g γ₂ s)
    (hc₁ : ContinuousOn γ₁ s) (hc₂ : ContinuousOn γ₂ s)
    (ht₀ : t₀ ∈ s) (heq0 : γ₁ t₀ = γ₂ t₀)
    (hβ : γ₁ t₀ ∈ (chartAt H β).source)
    (hv : deriv (chartReading (I := I) β γ₁) t₀
        = deriv (chartReading (I := I) β γ₂) t₀)
    (hclosurePos : ∀ t ∈ s, t ∈ closure {τ | γ₁ =ᶠ[𝓝 τ] γ₂} → γ₁ t = γ₂ t) :
    Set.EqOn γ₁ γ₂ s := by
  classical
  -- the set of times where the curves eventually agree
  set S : Set ℝ := {t | γ₁ =ᶠ[𝓝 t] γ₂} with hS_def
  -- `S` is open: eventual equality propagates to nearby base times
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact Filter.eventually_iff.mp (ht : γ₁ =ᶠ[𝓝 t] γ₂).eventually_nhds
  -- `t₀ ∈ S` by local uniqueness
  have ht₀S : t₀ ∈ S :=
    IsGeodesicOn.eventuallyEq_of_deriv_chartReading_eq hs h₁ h₂ hc₁ hc₂ ht₀ heq0 hβ hv
  -- relative closedness: closure points of `S` inside `s` belong to `S`
  have hclosed : closure S ∩ s ⊆ S := by
    rintro t ⟨htc, hts⟩
    by_cases htS : t ∈ S
    · exact htS
    -- position match at the closure point
    have hpos : γ₁ t = γ₂ t := hclosurePos t hts htc
    -- chart readings at the common foot
    set β' : M := γ₁ t with hβ'_def
    set w₁ : ℝ → E := chartReading (I := I) β' γ₁ with hw₁_def
    set w₂ : ℝ → E := chartReading (I := I) β' γ₂ with hw₂_def
    -- both readings are differentiable at `t`
    have hd₁ : HasDerivAt w₁ (deriv w₁ t) t :=
      (hasGeodesicEquationAt_iff_solvesGeodesicODEAt.mp (h₁ t hts)).1.self_of_nhds
    have hd₂ : HasDerivAt w₂ (deriv w₂ t) t := by
      have hsol := hasGeodesicEquationAt_iff_solvesGeodesicODEAt.mp (h₂ t hts)
      rw [← hpos] at hsol
      exact hsol.1.self_of_nhds
    -- the difference of the readings vanishes on `S` and at `t` …
    have hδ : HasDerivAt (fun τ => w₁ τ - w₂ τ) (deriv w₁ t - deriv w₂ t) t :=
      hd₁.sub hd₂
    -- … so its derivative is a limit of vanishing slopes along `𝓝[S] t`
    haveI hne : (𝓝[S \ {t}] t).NeBot := by
      rw [Set.diff_singleton_eq_self htS]
      exact mem_closure_iff_nhdsWithin_neBot.mp htc
    have hslope : Tendsto (slope (fun τ => w₁ τ - w₂ τ) t) (𝓝[S \ {t}] t)
        (𝓝 (deriv w₁ t - deriv w₂ t)) :=
      (hasDerivAt_iff_tendsto_slope.mp hδ).mono_left
        (nhdsWithin_mono t fun τ hτ => hτ.2)
    have hzero : ∀ᶠ τ in 𝓝[S \ {t}] t,
        slope (fun τ => w₁ τ - w₂ τ) t τ = 0 := by
      filter_upwards [eventually_mem_nhdsWithin] with τ hτ
      have hτeq : γ₁ τ = γ₂ τ := (hτ.1 : γ₁ =ᶠ[𝓝 τ] γ₂).eq_of_nhds
      have hγt : γ₁ t = γ₂ t := hβ'_def.symm.trans hpos
      have h1 : w₁ τ - w₂ τ = 0 := by
        simp [hw₁_def, hw₂_def, chartReading_def, hτeq]
      have h2 : w₁ t - w₂ t = 0 := by
        simp [hw₁_def, hw₂_def, chartReading_def, hγt]
      simp only [slope_def_module, h1, h2, sub_zero, smul_zero]
    have hslope0 : Tendsto (slope (fun τ => w₁ τ - w₂ τ) t) (𝓝[S \ {t}] t)
        (𝓝 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hzero] with τ h
      exact h.symm
    have hveq : deriv w₁ t = deriv w₂ t :=
      sub_eq_zero.mp (tendsto_nhds_unique hslope hslope0)
    -- local uniqueness at `t` puts `t` in `S`
    exact IsGeodesicOn.eventuallyEq_of_deriv_chartReading_eq hs h₁ h₂ hc₁ hc₂ hts
      hpos (mem_chart_source H β') hveq
  -- preconnectedness propagates `S` to all of `s`
  have hsS : s ⊆ S :=
    hconn.subset_of_closure_inter_subset hS_open ⟨t₀, ht₀, ht₀S⟩ hclosed
  exact fun t ht => ((hsS ht) : γ₁ =ᶠ[𝓝 t] γ₂).eq_of_nhds

/-- **Math.** **Uniqueness of intrinsic geodesics** (do Carmo Ch. 3, uniqueness in
Theorem 2.2, intrinsic interval form). Two continuous intrinsic geodesics on
an open preconnected set `s` of times that share their position and chart
velocity at one time `t₀ ∈ s` coincide on `s`. The Hausdorff hypothesis is
necessary: on the line with two origins, two geodesics can agree off a
single time and pass through the two origins there. -/
theorem IsGeodesicOn.eqOn_of_deriv_chartReading_eq [T2Space M]
    {g : RiemannianMetric I M} {γ₁ γ₂ : ℝ → M} {s : Set ℝ} {t₀ : ℝ} {β : M}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (h₁ : IsGeodesicOn (I := I) g γ₁ s) (h₂ : IsGeodesicOn (I := I) g γ₂ s)
    (hc₁ : ContinuousOn γ₁ s) (hc₂ : ContinuousOn γ₂ s)
    (ht₀ : t₀ ∈ s) (heq0 : γ₁ t₀ = γ₂ t₀)
    (hβ : γ₁ t₀ ∈ (chartAt H β).source)
    (hv : deriv (chartReading (I := I) β γ₁) t₀
        = deriv (chartReading (I := I) β γ₂) t₀) :
    Set.EqOn γ₁ γ₂ s :=
  eqOn_of_deriv_chartReading_eq_aux hs hconn h₁ h₂ hc₁ hc₂ ht₀ heq0 hβ hv
    fun _ hts htc => eq_at_closure_eventuallyEq_of_t2 hs hc₁ hc₂ hts htc

end Geodesic
end PetersenLib

end
