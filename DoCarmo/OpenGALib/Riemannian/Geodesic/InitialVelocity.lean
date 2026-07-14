import OpenGALib.Riemannian.Geodesic.Homogeneity

set_option linter.unusedSectionVars false

/-!
# Initial velocity and the geodesic equation at the initial time

For a geodesic witness with initial data `(p, v)` — a base curve `γ` lifted to an
integral curve `f` of the chart-`p`-fixed geodesic spray with `f 0 = ⟨p, v⟩` — we
extract the *analytic* content of the initial datum:

* `IsGeodesicOnWithInitial.hasDerivAt_extChartAt_zero` — read in the chart at
  `p`, the curve `γ` has derivative `v` at `t = 0`: the geodesic really leaves
  `p` with velocity `v`.
* `IsGeodesicOnWithInitial.hasGeodesicEquationAt_zero` — `γ` satisfies the
  intrinsic (moving-foot) geodesic equation `HasGeodesicEquationAt g γ 0` at the
  initial time. This bridges the spray/integral-curve formulation of geodesics
  back to the second-order geodesic equation of
  \S`Geodesic/Equation.lean`, at the initial time.

The mechanism: the tangent-bundle chart of `TM` at `f 0 = ⟨p, v⟩` is based at the
foot `p`, so mathlib's chart reading of the integral-curve property
(`IsMIntegralCurveAt.eventually_hasDerivAt`) is exactly the first-order system

`(x'(s), w'(s)) = (w(s), -Γ_p(w(s), w(s))(x(s)))`

for the pair `x = φ_p ∘ γ`, `w = ` chart-`p` fibre coordinate of `f`: the
`tangentCoordChange` appearing in the chart reading is precisely the
trivialization of `T(TM)` at `⟨p, 0⟩`, under which the spray reads as its
coordinate fibre value (`trivializationAt_apply_geodesicVectorFieldChart`).

Under the chart-validity clause of `maximalGeodesic_structure_of_footInSource`,
the same statements transfer to the canonical maximal geodesic
(`hasDerivAt_extChartAt_maximalGeodesic`,
`hasGeodesicEquationAt_maximalGeodesic_zero`), via agreement of witnesses
(`maximalGeodesic_eq_witness`).
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section CoordinateBridges

variable [I.Boundaryless]

/-- **Math.** The chart-`α` fibre coordinate of a tangent vector attached at `α`
itself is the vector: the trivialization at a point is the identity on the fibre
over that point. -/
lemma chartFiberCoord_mk (α : M) (w : TangentSpace I α) :
    chartFiberCoord (I := I) α (⟨α, w⟩ : TangentBundle I M) = w := by
  have h : chartFiberCoord (I := I) α (⟨α, w⟩ : TangentBundle I M) =
      tangentCoordChange I α α α w := rfl
  rw [h]
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source α)

/-- **Math.** One level up: the trivialization of `T(TM)` at `⟨α, 0⟩` is the identity
on the fibre over any point `⟨α, w⟩` with the same foot `α` (the charts of `TM`
at `⟨α, w⟩` and `⟨α, 0⟩` coincide, both being based at the foot `α`). -/
lemma trivializationAt_tangent_tangent_mk_snd (α : M) (w : E)
    (V : TangentSpace I.tangent (⟨α, w⟩ : TangentBundle I M)) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)
      (⟨⟨α, w⟩, V⟩ : TangentBundle I.tangent (TangentBundle I M))).2 = V := by
  have h : (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨α, (0 : E)⟩ : TangentBundle I M)
        (⟨⟨α, w⟩, V⟩ : TangentBundle I.tangent (TangentBundle I M))).2 =
      tangentCoordChange I.tangent (⟨α, w⟩ : TangentBundle I M)
        (⟨α, w⟩ : TangentBundle I M) (⟨α, w⟩ : TangentBundle I M) V := rfl
  rw [h]
  exact tangentCoordChange_self (I := I.tangent) (mem_extChartAt_source _)

/-- **Math.** Over its own foot, the chart-fixed geodesic spray in definitional
coordinates IS its coordinate fibre value: at a point `⟨α, w⟩` attached at the
chart basepoint `α`, the trivialization of `T(TM)` at `⟨α, 0⟩` is the identity. -/
lemma geodesicVectorFieldChart_mk (g : RiemannianMetric I M) (α : M) (w : E) :
    geodesicVectorFieldChart (I := I) g α (⟨α, w⟩ : TangentBundle I M) =
      geodesicVectorFieldChartFiber (I := I) g α (⟨α, w⟩ : TangentBundle I M) := by
  have hmem : (⟨α, w⟩ : TangentBundle I M) ∈ geodesicChartDomain (I := I) α :=
    mem_geodesicChartDomain_of_proj (mem_chart_source H α)
  have h2 := trivializationAt_tangent_tangent_mk_snd (I := I) α w
    (geodesicVectorFieldChart (I := I) g α (⟨α, w⟩ : TangentBundle I M))
  rw [trivializationAt_apply_geodesicVectorFieldChart (I := I) g α hmem] at h2
  exact h2.symm

/-- **Math.** The coordinate change from the chart of `TM` at a point `q` to the
chart at the basepoint (any point with foot `α`) sends the definitional
presentation of the chart-fixed geodesic spray to its coordinate fibre value. -/
lemma tangentCoordChange_geodesicVectorFieldChart
    (g : RiemannianMetric I M) (α : M) (w₀ : TangentSpace I α)
    {q : TangentBundle I M} (hq : q ∈ geodesicChartDomain (I := I) α) :
    tangentCoordChange I.tangent q (⟨α, w₀⟩ : TangentBundle I M) q
        (geodesicVectorFieldChart (I := I) g α q) =
      geodesicVectorFieldChartFiber (I := I) g α q := by
  have h : tangentCoordChange I.tangent q (⟨α, w₀⟩ : TangentBundle I M) q
        (geodesicVectorFieldChart (I := I) g α q) =
      (trivializationAt (E × E) (TangentSpace I.tangent)
          (⟨α, (0 : E)⟩ : TangentBundle I M)
        (⟨q, geodesicVectorFieldChart (I := I) g α q⟩ :
          TangentBundle I.tangent (TangentBundle I M))).2 := rfl
  rw [h, trivializationAt_apply_geodesicVectorFieldChart (I := I) g α hq]

end CoordinateBridges

section EventualSystem

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **The chart-`p` reading of a geodesic lift solves the first-order
geodesic system.** If `f` is an integral curve of the chart-`p`-fixed geodesic
spray at `0` with `f 0 = ⟨p, v⟩`, then near `0` the pair
`u ↦ (φ_p(γ u), w(u))` — base chart reading and fibre coordinate — is
differentiable with derivative the spray's coordinate fibre value
`(w(s), -Γ_p(w(s), w(s))(x(s)))` at each time `s`. -/
theorem eventually_hasDerivAt_geodesic_reading
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {f : ℝ → TangentBundle I M}
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hint : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt
      (fun u => (extChartAt I p ((f u).proj), chartFiberCoord (I := I) p (f u)))
      (geodesicVectorFieldChartFiber (I := I) g p (f s)) s := by
  classical
  have hev := hint.eventually_hasDerivAt
  rw [hf0] at hev
  have hcont : ContinuousAt f 0 := hint.continuousAt
  have hdom : ∀ᶠ u in 𝓝 (0 : ℝ), f u ∈ geodesicChartDomain (I := I) p := by
    have hopen : geodesicChartDomain (I := I) (M := M) p ∈ 𝓝 (f 0) := by
      refine (geodesicChartDomain_isOpen (I := I) (M := M) p).mem_nhds ?_
      rw [hf0]
      exact mem_geodesicChartDomain_of_proj (mem_chart_source H p)
    exact hcont.eventually_mem hopen
  have hdom' : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ u in 𝓝 s,
      f u ∈ geodesicChartDomain (I := I) p := hdom.eventually_nhds
  filter_upwards [hev, hdom, hdom'] with s hs hsdom hsdom'
  have hval : tangentCoordChange I.tangent (f s) (⟨p, v⟩ : TangentBundle I M) (f s)
      (geodesicVectorFieldChart (I := I) g p (f s)) =
      geodesicVectorFieldChartFiber (I := I) g p (f s) :=
    tangentCoordChange_geodesicVectorFieldChart (I := I) g p v hsdom
  rw [hval] at hs
  have hfun : (fun u => extChartAt I.tangent (⟨p, v⟩ : TangentBundle I M) (f u))
      =ᶠ[𝓝 s] (fun u =>
        (extChartAt I p ((f u).proj), chartFiberCoord (I := I) p (f u))) := by
    filter_upwards [hsdom'] with u hu
    exact extChartAt_tangent_apply (I := I) (⟨p, v⟩ : TangentBundle I M)
      (r := f u) (by
        rw [TangentBundle.trivializationAt_baseSet]
        exact proj_mem_chartAt_source_of_mem_geodesicChartDomain (I := I) hu)
  exact hs.congr_of_eventuallyEq hfun.symm

end EventualSystem

section InitialData

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **A geodesic leaves `p` with velocity `v`.** For a geodesic witness
with initial data `(p, v)` defined on a neighbourhood of `0`, the chart-`p`
reading `s ↦ φ_p(γ s)` has derivative `v` at `s = 0`. -/
theorem IsGeodesicOnWithInitial.hasDerivAt_extChartAt_zero
    {g : RiemannianMetric I M} {γ : ℝ → M} {J : Set ℝ} {p : M}
    {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p v) (hJ : J ∈ 𝓝 (0 : ℝ)) :
    HasDerivAt (fun s => extChartAt I p (γ s)) v 0 := by
  classical
  obtain ⟨f, hproj, hf0, hint⟩ := hγ
  have hat : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0 :=
    hint.isMIntegralCurveAt hJ
  have h0 := (eventually_hasDerivAt_geodesic_reading (I := I) g p v hf0
    hat).self_of_nhds
  have hfst := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt 0 h0
  have hfun : (⇑(ContinuousLinearMap.fst ℝ E E) ∘ fun u =>
      (extChartAt I p ((f u).proj), chartFiberCoord (I := I) p (f u))) =
      (fun s => extChartAt I p (γ s)) := by
    funext u
    show extChartAt I p ((f u).proj) = extChartAt I p (γ u)
    rw [hproj u]
  rw [hfun] at hfst
  have hval : (ContinuousLinearMap.fst ℝ E E)
      (geodesicVectorFieldChartFiber (I := I) g p (f 0)) = v := by
    show (geodesicVectorFieldChartFiber (I := I) g p (f 0)).1 = v
    rw [hf0]
    show chartFiberCoord (I := I) p (⟨p, v⟩ : TangentBundle I M) = v
    exact chartFiberCoord_mk (I := I) p v
  rw [hval] at hfst
  exact hfst

/-- **Math.** **A geodesic witness satisfies the intrinsic geodesic equation at the
initial time.** This bridges the spray/integral-curve formulation back to the
second-order moving-foot geodesic equation, at `t = 0`: the chart-`p` reading
`x = φ_p ∘ γ` satisfies `x'' + Γ_p(x', x')(x) = 0` at `0`, which is
`HasGeodesicEquationAt g γ 0` since the chart at the foot `γ 0 = p` is the
chart at `p`. -/
theorem IsGeodesicOnWithInitial.hasGeodesicEquationAt_zero
    {g : RiemannianMetric I M} {γ : ℝ → M} {J : Set ℝ} {p : M}
    {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p v) (hJ : J ∈ 𝓝 (0 : ℝ)) :
    HasGeodesicEquationAt (I := I) g γ 0 := by
  classical
  have hstart : γ 0 = p := hγ.start_eq
  obtain ⟨f, hproj, hf0, hint⟩ := hγ
  have hat : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0 :=
    hint.isMIntegralCurveAt hJ
  have hev := eventually_hasDerivAt_geodesic_reading (I := I) g p v hf0 hat
  -- the base reading and the fibre coordinate
  set x : ℝ → E := fun s => extChartAt I p (γ s) with hx_def
  set w : ℝ → E := fun s => chartFiberCoord (I := I) p (f s) with hw_def
  -- the pair function of `hev` is `fun u => (x u, w u)`
  have hpair_eq : (fun u =>
      (extChartAt I p ((f u).proj), chartFiberCoord (I := I) p (f u))) =
      (fun u => (x u, w u)) := by
    funext u
    show (extChartAt I p ((f u).proj), _) = (extChartAt I p (γ u), _)
    rw [hproj u]
  rw [hpair_eq] at hev
  -- first component: `x` has eventual derivative `w`
  have hx_ev : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt x (w s) s := by
    filter_upwards [hev] with s hs
    have := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt s hs
    exact this
  -- second component: `w` has derivative the Christoffel term at `0`
  have hw0 : HasDerivAt w
      ((geodesicVectorFieldChartFiber (I := I) g p (f 0)).2) 0 := by
    have hs := hev.self_of_nhds
    have := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt 0 hs
    exact this
  -- the chart-local curve of the geodesic equation is `x`
  have hlocal : chartLocalCurve (I := I) γ 0 = x := by
    funext s
    show extChartAt I (γ 0) (γ s) = extChartAt I p (γ s)
    rw [hstart]
  -- initial fibre coordinate is `v`
  have hw0_val : w 0 = v := by
    show chartFiberCoord (I := I) p (f 0) = v
    rw [hf0]
    exact chartFiberCoord_mk (I := I) p v
  -- assemble the four clauses
  refine ⟨v, (geodesicVectorFieldChartFiber (I := I) g p (f 0)).2, ?_, ?_, ?_, ?_⟩
  · -- velocity at 0
    rw [hlocal]
    have := hx_ev.self_of_nhds
    rwa [hw0_val] at this
  · -- eventual differentiability
    rw [hlocal]
    filter_upwards [hx_ev] with s hs
    rwa [← hs.deriv] at hs
  · -- second derivative at 0
    rw [hlocal]
    have hderiv_ev : deriv x =ᶠ[𝓝 (0 : ℝ)] w := by
      filter_upwards [hx_ev] with s hs
      exact hs.deriv
    exact hw0.congr_of_eventuallyEq hderiv_ev
  · -- the geodesic equation at 0
    show (geodesicVectorFieldChartFiber (I := I) g p (f 0)).2 +
      chartChristoffelContraction (I := I) g (γ 0) v v
        (extChartAt I (γ 0) (γ 0)) = 0
    have hsnd : (geodesicVectorFieldChartFiber (I := I) g p (f 0)).2 =
        - chartChristoffelContraction (I := I) g p v v (extChartAt I p p) := by
      show (geodesicVectorFieldChartFiber (I := I) g p (f 0)).2 = _
      rw [hf0]
      show - chartChristoffelContraction (I := I) g p
          (chartFiberCoord (I := I) p (⟨p, v⟩ : TangentBundle I M))
          (chartFiberCoord (I := I) p (⟨p, v⟩ : TangentBundle I M))
          (extChartAt I p ((⟨p, v⟩ : TangentBundle I M).proj)) = _
      rw [chartFiberCoord_mk (I := I) p v]
    rw [hsnd, hstart]
    exact neg_add_cancel _

end InitialData

section EquationCongruence

/-- **Math.** The moving-foot geodesic equation at time `t` only depends on the curve
near `t`: it transfers across eventual equality of curves. -/
theorem hasGeodesicEquationAt_congr_of_eventuallyEq
    {g : RiemannianMetric I M} {γ₁ γ₂ : ℝ → M} {t : ℝ}
    (hev : γ₂ =ᶠ[𝓝 t] γ₁) (h : HasGeodesicEquationAt (I := I) g γ₁ t) :
    HasGeodesicEquationAt (I := I) g γ₂ t := by
  obtain ⟨v, a, h1, h2, h3, h4⟩ := h
  have hpt : γ₂ t = γ₁ t := hev.self_of_nhds
  have hloc : chartLocalCurve (I := I) γ₂ t =ᶠ[𝓝 t]
      chartLocalCurve (I := I) γ₁ t := by
    filter_upwards [hev] with s hs
    show extChartAt I (γ₂ t) (γ₂ s) = extChartAt I (γ₁ t) (γ₁ s)
    rw [hpt, hs]
  have hderiv : deriv (chartLocalCurve (I := I) γ₂ t) =ᶠ[𝓝 t]
      deriv (chartLocalCurve (I := I) γ₁ t) := hloc.deriv
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · exact h1.congr_of_eventuallyEq hloc
  · have hloc' : ∀ᶠ s in 𝓝 t, chartLocalCurve (I := I) γ₂ t =ᶠ[𝓝 s]
        chartLocalCurve (I := I) γ₁ t := hloc.eventually_nhds
    filter_upwards [h2, hloc', hderiv] with s hs hsloc hsd
    rw [hsd]
    exact hs.congr_of_eventuallyEq hsloc
  · exact (h3.congr_of_eventuallyEq hderiv)
  · rwa [hpt]

end EquationCongruence

section MaximalGeodesicTransfer

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The canonical maximal geodesic agrees with every witness** on the
witness's interval, under the chart-validity clause that all witnesses with
initial data `(p, v)` keep their foot in the chart at `p`. This is the
uniqueness statement that makes `maximalGeodesic` canonical. -/
theorem maximalGeodesic_eq_witness
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    (hsrc : ∀ (γ' : ℝ → M) (J' : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ' J' p v →
        ∀ s ∈ J', γ' s ∈ (chartAt H p).source)
    {γ₀ : ℝ → M} {J₀ : Set ℝ}
    (hγ₀ : IsGeodesicOnWithInitial (I := I) g γ₀ J₀ p v)
    (hJo : IsOpen J₀) (hJc : IsPreconnected J₀) (h0 : (0 : ℝ) ∈ J₀)
    {s : ℝ} (hs : s ∈ J₀) :
    maximalGeodesic (I := I) g p v s = γ₀ s := by
  classical
  have hmem : s ∈ maximalGeodesicInterval (I := I) g p v :=
    ⟨γ₀, J₀, hJo, hJc, h0, hs, hγ₀⟩
  rw [maximalGeodesic_of_mem (I := I) hmem]
  obtain ⟨J₁, hJ₁o, hJ₁c, h0₁, hs₁, hγ₁⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v hmem
  have heq := IsGeodesicOnWithInitial.eqOn (I := I) hγ₁ hγ₀
    (hJ₁o.inter hJo)
    ((hJ₁c.ordConnected.inter hJc.ordConnected).isPreconnected)
    ⟨h0₁, h0⟩ inter_subset_left inter_subset_right
    (fun t ht => hsrc _ _ hγ₁ t (inter_subset_left ht))
  exact heq ⟨hs₁, hs⟩

/-- **Math.** Near `0`, the canonical maximal geodesic coincides with the chosen
local witness (under the chart-validity clause). -/
theorem maximalGeodesic_eventuallyEq_witness
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    (hsrc : ∀ (γ' : ℝ → M) (J' : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ' J' p v →
        ∀ s ∈ J', γ' s ∈ (chartAt H p).source) :
    ∃ (γ₀ : ℝ → M) (J₀ : Set ℝ), IsGeodesicOnWithInitial (I := I) g γ₀ J₀ p v ∧
      J₀ ∈ 𝓝 (0 : ℝ) ∧ maximalGeodesic (I := I) g p v =ᶠ[𝓝 (0 : ℝ)] γ₀ := by
  classical
  have h0 := zero_mem_maximalGeodesicInterval (I := I) g p v
  obtain ⟨J₀, hJo, hJc, h0₀, _, hγ₀⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v h0
  refine ⟨_, J₀, hγ₀, hJo.mem_nhds h0₀, ?_⟩
  filter_upwards [hJo.mem_nhds h0₀] with s hs
  exact maximalGeodesic_eq_witness (I := I) hsrc hγ₀ hJo hJc h0₀ hs

/-- **Math.** **The canonical maximal geodesic leaves `p` with velocity `v`**: read
in the chart at `p`, `s ↦ φ_p(γ(s, p, v))` has derivative `v` at `s = 0` (under
the chart-validity clause for `(p, v)`-witnesses). -/
theorem hasDerivAt_extChartAt_maximalGeodesic
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    (hsrc : ∀ (γ' : ℝ → M) (J' : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ' J' p v →
        ∀ s ∈ J', γ' s ∈ (chartAt H p).source) :
    HasDerivAt (fun s => extChartAt I p (maximalGeodesic (I := I) g p v s)) v 0 := by
  obtain ⟨γ₀, J₀, hγ₀, hJ₀, hev⟩ :=
    maximalGeodesic_eventuallyEq_witness (I := I) hsrc
  have h0 := hγ₀.hasDerivAt_extChartAt_zero (I := I) hJ₀
  refine h0.congr_of_eventuallyEq ?_
  filter_upwards [hev] with s hs
  rw [hs]

/-- **Math.** **The canonical maximal geodesic satisfies the intrinsic geodesic
equation at the initial time** (under the chart-validity clause for
`(p, v)`-witnesses). -/
theorem hasGeodesicEquationAt_maximalGeodesic_zero
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    (hsrc : ∀ (γ' : ℝ → M) (J' : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ' J' p v →
        ∀ s ∈ J', γ' s ∈ (chartAt H p).source) :
    HasGeodesicEquationAt (I := I) g (maximalGeodesic (I := I) g p v) 0 := by
  obtain ⟨γ₀, J₀, hγ₀, hJ₀, hev⟩ :=
    maximalGeodesic_eventuallyEq_witness (I := I) hsrc
  have h0 := hγ₀.hasGeodesicEquationAt_zero (I := I) hJ₀
  exact hasGeodesicEquationAt_congr_of_eventuallyEq (I := I) hev h0

end MaximalGeodesicTransfer

end Geodesic
end Riemannian

end
