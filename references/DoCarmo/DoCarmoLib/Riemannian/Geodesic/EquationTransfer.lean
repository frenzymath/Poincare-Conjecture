import DoCarmoLib.Riemannian.Connection.ChartChristoffelChange
import DoCarmoLib.Riemannian.Geodesic.Equation


/-!
# Chart-independence of the geodesic equation

The moving-foot geodesic predicate `HasGeodesicEquationAt g γ t₀` reads the
second-order geodesic equation in the canonical chart at the foot `γ t₀`. This
file proves that the equation can equivalently be read in *any* chart whose
source contains the foot: the second-order geodesic operator
`u'' + Γ_α(u', u')(u)` transforms under a chart transition by the (invertible)
transition derivative alone, because the inhomogeneous second-derivative terms
produced by the chain rule cancel against the transformation law of the
Christoffel contraction (`chartChristoffelContraction_change`, do Carmo Ch. 2,
Eq. (Christoffel transformation); the toll-gate identity of inbox I-0100).

Main definitions and results:

* `SolvesGeodesicODEAt g α γ t₀` — the curve's reading
  `u = extChartAt I α ∘ γ` in the FIXED chart at `α` is differentiable near
  `t₀`, its derivative is differentiable at `t₀`, and the second-order
  geodesic identity `u''(t₀) + Γ_α(u'(t₀), u'(t₀))(u(t₀)) = 0` holds.
* `SolvesGeodesicODEAt.transfer` — the **change-of-chart theorem**: if the
  foot `γ t₀` lies in both chart sources and `γ` is continuous at `t₀`, the
  chart-`α` reading solves the geodesic ODE iff the chart-`β` reading does.
* `hasGeodesicEquationAt_iff_solvesGeodesicODEAt` — the moving-foot predicate
  is the fixed-chart predicate anchored at the foot itself.
* `HasGeodesicEquationAt.solvesGeodesicODEAt` /
  `SolvesGeodesicODEAt.hasGeodesicEquationAt` — the two transfer corollaries
  used by the intrinsic geodesic theory: a geodesic solves the honest
  second-order ODE in every chart containing its foot, and a solution of the
  ODE in one chart is a geodesic.

These are the bridges that let interval-level geodesic theory (uniqueness,
gluing, maximal extension — do Carmo Ch. 7, Theorem 2.8 c) ⟹ d)) move between
overlapping charts, replacing the single-chart-anchored witness framework of
`MaximalInterval.lean`.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** The chart-`α` reading of a curve `γ : ℝ → M`: the `E`-valued curve
`u(τ) = φ_α(γ(τ))`. For `α = γ t` this is `chartLocalCurve γ t`
(definitionally). -/
def chartReading (α : M) (γ : ℝ → M) : ℝ → E :=
  fun τ => extChartAt I α (γ τ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] in
@[simp] lemma chartReading_def (α : M) (γ : ℝ → M) (τ : ℝ) :
    chartReading (I := I) α γ τ = extChartAt I α (γ τ) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] in
/-- **Math.** The chart-`α` reading anchored at the foot is the chart-local curve. -/
lemma chartReading_foot (γ : ℝ → M) (t : ℝ) :
    chartReading (I := I) (γ t) γ = chartLocalCurve (I := I) γ t := rfl

/-- **Math.** `γ` **solves the second-order geodesic ODE in the chart at `α`
near `t₀`**: the chart reading `u = φ_α ∘ γ` is differentiable on a
neighbourhood of `t₀`, its derivative is differentiable at `t₀`, and the
geodesic identity `u''(t₀) + Γ_α(u'(t₀), u'(t₀))(u(t₀)) = 0` holds (do Carmo
Ch. 3, Definition 2.1, read in the fixed chart at `α`). -/
def SolvesGeodesicODEAt (g : RiemannianMetric I M) (α : M) (γ : ℝ → M)
    (t₀ : ℝ) : Prop :=
  (∀ᶠ τ in 𝓝 t₀, HasDerivAt (chartReading (I := I) α γ)
      (deriv (chartReading (I := I) α γ) τ) τ) ∧
  ∃ a : E, HasDerivAt (deriv (chartReading (I := I) α γ)) a t₀ ∧
    a + chartChristoffelContraction (I := I) g α
        (deriv (chartReading (I := I) α γ) t₀)
        (deriv (chartReading (I := I) α γ) t₀)
        (chartReading (I := I) α γ t₀) = 0

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The moving-foot geodesic equation at `t₀` is exactly the fixed-chart
second-order geodesic ODE anchored at the foot `γ t₀` itself. -/
theorem hasGeodesicEquationAt_iff_solvesGeodesicODEAt
    {g : RiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ} :
    HasGeodesicEquationAt (I := I) g γ t₀ ↔
      SolvesGeodesicODEAt (I := I) g (γ t₀) γ t₀ := by
  constructor
  · rintro ⟨v, a, hv, hev, ha, heq⟩
    refine ⟨hev, a, ha, ?_⟩
    have hvd : deriv (chartLocalCurve (I := I) γ t₀) t₀ = v := hv.deriv
    show a + chartChristoffelContraction (I := I) g (γ t₀)
        (deriv (chartLocalCurve (I := I) γ t₀) t₀)
        (deriv (chartLocalCurve (I := I) γ t₀) t₀)
        (chartLocalCurve (I := I) γ t₀ t₀) = 0
    rw [hvd]
    exact heq
  · rintro ⟨hev, a, ha, heq⟩
    exact ⟨deriv (chartLocalCurve (I := I) γ t₀) t₀, a, hev.self_of_nhds, hev, ha, heq⟩

section Transfer

variable {g : RiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ} {α β : M}

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Change of chart for the second-order geodesic ODE** (the
consequence of the Christoffel transformation law
`chartChristoffelContraction_change`). If `γ` is continuous at `t₀`, its foot
`γ t₀` lies in the chart sources at `α` and at `β`, and the chart-`α` reading
of `γ` solves the geodesic ODE near `t₀`, then so does the chart-`β` reading.

Chain rule: with `τ = chartTransition α β` and `A = Dτ(u_α(t₀))`,
`u_β = τ ∘ u_α` near `t₀`, so `u_β' = Dτ(u_α)·u_α'` and
`u_β''(t₀) = D²τ(v, v) + A(u_α''(t₀))` where `v = u_α'(t₀)`. The
transformation law `A(Γ_α(v, v)) = Γ_β(Av, Av) + D²τ(v, v)` then makes the
geodesic operator transform by `A` alone:
`u_β'' + Γ_β(u_β', u_β') = A(u_α'' + Γ_α(u_α', u_α')) = 0`. -/
theorem SolvesGeodesicODEAt.transfer
    (hcont : ContinuousAt γ t₀)
    (hα : γ t₀ ∈ (chartAt H α).source) (hβ : γ t₀ ∈ (chartAt H β).source)
    (h : SolvesGeodesicODEAt (I := I) g α γ t₀) :
    SolvesGeodesicODEAt (I := I) g β γ t₀ := by
  classical
  obtain ⟨hev, a, ha, heq⟩ := h
  set u : ℝ → E := chartReading (I := I) α γ with hu_def
  set w : ℝ → E := chartReading (I := I) β γ with hw_def
  set T : E → E := chartTransition (I := I) (M := M) α β with hT_def
  -- the foot stays in both chart sources near `t₀`
  have hmem : ∀ᶠ τ in 𝓝 t₀,
      γ τ ∈ (chartAt H α).source ∧ γ τ ∈ (chartAt H β).source := by
    have : (chartAt H α).source ∩ (chartAt H β).source ∈ 𝓝 (γ t₀) :=
      (((chartAt H α).open_source).inter (chartAt H β).open_source).mem_nhds ⟨hα, hβ⟩
    exact hcont.preimage_mem_nhds this
  -- the α-reading lies in the transition overlap near `t₀`
  have hsrc : ∀ᶠ τ in 𝓝 t₀,
      u τ ∈ chartTransitionSource (I := I) (M := M) α β := by
    filter_upwards [hmem] with τ hτ
    exact extChartAt_mem_chartTransitionSource (I := I) hτ.1 hτ.2
  -- the β-reading is the transition applied to the α-reading, near `t₀`
  have hw_eq : ∀ᶠ τ in 𝓝 t₀, w τ = T (u τ) := by
    filter_upwards [hmem] with τ hτ
    exact (chartTransition_extChartAt (I := I) (β := α) (α := β) hτ.1).symm
  -- eventual differentiability of the β-reading with the chain-rule formula
  have hw_deriv : ∀ᶠ τ in 𝓝 t₀,
      HasDerivAt w (fderiv ℝ T (u τ) (deriv u τ)) τ := by
    filter_upwards [hev, hsrc, hw_eq.eventually_nhds] with τ hτ hτsrc hτeq
    have hT : HasFDerivAt T (fderiv ℝ T (u τ)) (u τ) := by
      have := hasFDerivAt_chartTransition (I := I) (β := α) (α := β) hτsrc
      rwa [← fderiv_chartTransition (I := I) (β := α) (α := β) hτsrc] at this
    exact (hT.comp_hasDerivAt τ hτ).congr_of_eventuallyEq hτeq
  have hw_ev : ∀ᶠ τ in 𝓝 t₀, HasDerivAt w (deriv w τ) τ := by
    filter_upwards [hw_deriv] with τ hτ
    exact hτ.deriv ▸ hτ
  -- the first-derivative formula, as an eventual equality of functions
  have hw_deriv_eq : (fun τ => deriv w τ)
      =ᶠ[𝓝 t₀] fun τ => fderiv ℝ T (u τ) (deriv u τ) := by
    filter_upwards [hw_deriv] with τ hτ
    exact hτ.deriv
  -- data at the base time
  have ht₀src : u t₀ ∈ chartTransitionSource (I := I) (M := M) α β :=
    hsrc.self_of_nhds
  have hu' : HasDerivAt u (deriv u t₀) t₀ := hev.self_of_nhds
  set v : E := deriv u t₀ with hv_def
  set A : E →L[ℝ] E := fderiv ℝ T (u t₀) with hA_def
  set D2 : E →L[ℝ] E →L[ℝ] E := fderiv ℝ (fderiv ℝ T) (u t₀) with hD2_def
  -- second derivative of the β-reading at `t₀`
  have hc : HasDerivAt (fun τ => fderiv ℝ T (u τ)) (D2 v) t₀ :=
    (hasFDerivAt_fderiv_chartTransition (I := I) (β := α) (α := β)
      ht₀src).comp_hasDerivAt t₀ hu'
  have hΦ : HasDerivAt (fun τ => fderiv ℝ T (u τ) (deriv u τ))
      (D2 v v + A a) t₀ := by
    have := hc.clm_apply ha
    simpa [hA_def, hv_def] using this
  have hw_snd : HasDerivAt (deriv w) (D2 v v + A a) t₀ :=
    hΦ.congr_of_eventuallyEq hw_deriv_eq
  -- the β-chart velocity at the base time
  have hw_v : deriv w t₀ = A v := hw_deriv_eq.self_of_nhds
  -- identify `A` with the tangent coordinate change at the foot
  have hAtcc : A = tangentCoordChange I α β (γ t₀) := by
    rw [hA_def, fderiv_chartTransition (I := I) (β := α) (α := β) ht₀src]
    congr 1
    exact (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hα)
  -- the Christoffel transformation law at the foot
  have hlaw := chartChristoffelContraction_change (I := I) g β α
    (x := γ t₀) hβ hα v v
  -- `hlaw : tangentCoordChange I α β (γ t₀) (Γ_α(v,v)(φ_α (γ t₀)))
  --   = Γ_β(Av, Av)(φ_β (γ t₀)) + D²T(φ_α (γ t₀)) v v`
  refine ⟨hw_ev, D2 v v + A a, hw_snd, ?_⟩
  rw [hw_v]
  have hArw : tangentCoordChange I α β (γ t₀) = A := hAtcc.symm
  have hD2rw : fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
      (extChartAt I α (γ t₀)) = D2 := rfl
  rw [hArw, hD2rw] at hlaw
  -- from the α-chart identity, `a = -Γ_α(v,v)(u t₀)`
  have haval : a = - chartChristoffelContraction (I := I) g α v v (u t₀) :=
    eq_neg_of_add_eq_zero_left heq
  show D2 v v + A a + chartChristoffelContraction (I := I) g β (A v) (A v) (w t₀) = 0
  have hwt₀ : w t₀ = extChartAt I β (γ t₀) := rfl
  have hut₀ : u t₀ = extChartAt I α (γ t₀) := rfl
  rw [haval, map_neg, hwt₀]
  have hlaw' : A (chartChristoffelContraction (I := I) g α v v (u t₀))
      = chartChristoffelContraction (I := I) g β (A v) (A v)
          (extChartAt I β (γ t₀)) + D2 v v := by
    rw [hut₀]; exact hlaw
  rw [hlaw']
  abel

end Transfer

section Corollaries

variable {g : RiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** A geodesic solves the honest second-order geodesic ODE in *every*
chart whose source contains its foot (do Carmo Ch. 3, the coordinate form of
Definition 2.1, in an arbitrary chart). -/
theorem HasGeodesicEquationAt.solvesGeodesicODEAt
    (h : HasGeodesicEquationAt (I := I) g γ t₀) (hcont : ContinuousAt γ t₀)
    {β : M} (hβ : γ t₀ ∈ (chartAt H β).source) :
    SolvesGeodesicODEAt (I := I) g β γ t₀ :=
  (hasGeodesicEquationAt_iff_solvesGeodesicODEAt.mp h).transfer hcont
    (mem_chart_source H (γ t₀)) hβ

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** A curve solving the second-order geodesic ODE in one chart
containing its foot satisfies the intrinsic (moving-foot) geodesic equation. -/
theorem SolvesGeodesicODEAt.hasGeodesicEquationAt {α : M}
    (h : SolvesGeodesicODEAt (I := I) g α γ t₀) (hcont : ContinuousAt γ t₀)
    (hα : γ t₀ ∈ (chartAt H α).source) :
    HasGeodesicEquationAt (I := I) g γ t₀ :=
  hasGeodesicEquationAt_iff_solvesGeodesicODEAt.mpr
    (h.transfer hcont hα (mem_chart_source H (γ t₀)))

end Corollaries

end Geodesic
end Riemannian

end
