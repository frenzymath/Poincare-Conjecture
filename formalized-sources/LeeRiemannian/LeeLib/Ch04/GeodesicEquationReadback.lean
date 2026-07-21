/-
Chapter 4, "Connections", §"Geodesics": the geodesic-equation readback.

The geodesic-spray development (`LeeLib.Ch04.GeodesicSpray`) produces geodesics as
base projections of integral curves of the spray `geodesicVectorFieldChart` (Theorem
4.27, existence).  This file closes the loop back to Lee's *definition* of a geodesic
(`LeeLib.Ch04.Geodesic`): a spray geodesic really satisfies Lee's geodesic equation
`D_t γ' = 0`, i.e. `chartAcceleration = 0`, read in the chart at its foot.

For an integral curve `f` of the chart-`p`-fixed geodesic spray with `f 0 = ⟨p, v⟩`,
the tangent-bundle chart of `TM` at `f 0 = ⟨p, v⟩` is based at the foot `p`, so
mathlib's chart reading of the integral-curve property
(`IsMIntegralCurveAt.eventually_hasDerivAt`) is exactly the first-order system

  `(x'(s), w'(s)) = (w(s), -Γ_p(w(s), w(s))(γ(s)))`,

for the pair `x = φ_p ∘ γ` (base chart image) and `w =` chart-`p` fibre coordinate
of `f`: the `tangentCoordChange` appearing there is the trivialization of `T(TM)` at
`⟨p, 0⟩`, under which the spray reads as its coordinate fibre value
(`trivializationAt_apply_geodesicVectorFieldChart`).  Eliminating `w = x'` gives Lee's
second-order geodesic equation `x'' + Γ_p(x', x')(γ) = 0` at the initial time.

Main results (for `IsSprayGeodesicOnWithInitial cov b γ J p v`, `hJ : J ∈ 𝓝 0`):
* `hasDerivAt_extChartAt_zero` — the chart-`p` reading `s ↦ φ_p(γ s)` has derivative
  `v` at `0`: the geodesic leaves `p` with velocity `v`.
* `chartAcceleration_zero` — Lee's geodesic equation at the initial time,
  `chartAcceleration cov (trivializationAt.. p) b (φ_p ∘ γ) γ 0 = 0`.

Ported from DoCarmo `DoCarmoLib/Riemannian/Geodesic/InitialVelocity.lean`, with the
metric Levi-Civita spray replaced by the abstract connection's `chartGamma` (which the
spray `geodesicSprayFiber` is built from, evaluated at the manifold point `p.proj`
directly — no `extChartAt`-of-the-foot layer).  Chart-local like the rest of the `D_t`
development: it gives the geodesic equation at the initial time, not the global
`IsGeodesicInChart` (which the cross-chart gluing, deferred, would upgrade it to).
-/
import LeeLib.Ch04.GeodesicSpray
import LeeLib.Ch04.Geodesic

namespace LeeLib.Ch04

open Bundle Module Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι] {b : Basis ι ℝ E}

/-- The tangent-bundle chart of `TM` at a basepoint `β : TM` reads as a product: the
base chart image of the foot paired with the fibre coordinate in the trivialization at
`β.proj`.  (General fact about the tangent bundle, independent of any connection.) -/
theorem extChartAt_tangent_apply (β : TangentBundle I M) {r : TangentBundle I M}
    (hr : r.proj ∈ (trivializationAt E (TangentSpace I) β.proj).baseSet) :
    extChartAt I.tangent β r =
      (extChartAt I β.proj r.proj, (trivializationAt E (TangentSpace I) β.proj r).2) := by
  classical
  rw [FiberBundle.extChartAt (IB := I) (F := E) (E := TangentSpace I) β]
  have hr_src : r ∈ (trivializationAt E (TangentSpace I) β.proj).source :=
    (trivializationAt E (TangentSpace I) β.proj).mem_source.mpr hr
  have hfst : ((trivializationAt E (TangentSpace I) β.proj) r).1 = r.proj :=
    (trivializationAt E (TangentSpace I) β.proj).coe_fst hr_src
  simp only [PartialEquiv.coe_trans, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    Function.comp_apply]
  rfl

/-- The chart-`α` fibre coordinate of a tangent vector attached at `α` itself is the
vector: the trivialization at a point is the identity on the fibre over that point. -/
theorem sprayFiberCoord_mk (α : M) (w : TangentSpace I α) :
    sprayFiberCoord (I := I) α (⟨α, w⟩ : TangentBundle I M) = w := by
  have h : sprayFiberCoord (I := I) α (⟨α, w⟩ : TangentBundle I M) =
      tangentCoordChange I α α α w := rfl
  rw [h]
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source α)

/-- One level up: the trivialization of `T(TM)` at `⟨α, 0⟩` is the identity on the fibre
over any point `⟨α, w⟩` with the same foot `α`. -/
theorem trivializationAt_tangent_tangent_mk_snd (α : M) (w : E)
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

/-- The coordinate change from the chart of `TM` at a point `q` to the chart at the
basepoint (any point with foot `α`) sends the geodesic spray to its coordinate fibre
value `geodesicSprayFiber` — the trivialization of `T(TM)` at `⟨α, 0⟩` returns it by
construction (`trivializationAt_apply_geodesicVectorFieldChart`). -/
theorem tangentCoordChange_geodesicVectorFieldChart
    (cov : Connection I E (TangentSpace I : M → Type _)) (α : M) (w₀ : TangentSpace I α)
    {q : TangentBundle I M} (hq : q ∈ geodesicChartDomain (I := I) α) :
    tangentCoordChange I.tangent q (⟨α, w₀⟩ : TangentBundle I M) q
        (geodesicVectorFieldChart cov b α q) =
      geodesicSprayFiber cov b α q := by
  have h : tangentCoordChange I.tangent q (⟨α, w₀⟩ : TangentBundle I M) q
        (geodesicVectorFieldChart cov b α q) =
      (trivializationAt (E × E) (TangentSpace I.tangent)
          (⟨α, (0 : E)⟩ : TangentBundle I M)
        (⟨q, geodesicVectorFieldChart cov b α q⟩ :
          TangentBundle I.tangent (TangentBundle I M))).2 := rfl
  rw [h, trivializationAt_apply_geodesicVectorFieldChart cov b α hq]

/-- **The chart-`p` reading of a geodesic lift solves the first-order geodesic system.**
If `f` is an integral curve of the chart-`p`-fixed geodesic spray at `0` with
`f 0 = ⟨p, v⟩`, then near `0` the pair `u ↦ (φ_p(γ u), w(u))` — base chart reading and
chart-`p` fibre coordinate — is differentiable with derivative the spray's coordinate
fibre value `(w(s), -Γ_p(w(s), w(s))(γ(s)))` at each time `s`. -/
theorem eventually_hasDerivAt_geodesic_reading
    (cov : Connection I E (TangentSpace I : M → Type _)) (p : M) (v : TangentSpace I p)
    {f : ℝ → TangentBundle I M}
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M))
    (hint : IsMIntegralCurveAt f (geodesicVectorFieldChart cov b p) 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt
      (fun u => (extChartAt I p ((f u).proj), sprayFiberCoord (I := I) p (f u)))
      (geodesicSprayFiber cov b p (f s)) s := by
  classical
  have hev := hint.eventually_hasDerivAt
  rw [hf0] at hev
  have hcont : ContinuousAt f 0 := hint.continuousAt
  have hdom : ∀ᶠ u in 𝓝 (0 : ℝ), f u ∈ geodesicChartDomain (I := I) p := by
    have hopen : geodesicChartDomain (I := I) (M := M) p ∈ 𝓝 (f 0) := by
      refine (geodesicChartDomain_isOpen (I := I) (M := M) p).mem_nhds ?_
      rw [hf0]
      exact mem_chart_source H p
    exact hcont.eventually_mem hopen
  have hdom' : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ u in 𝓝 s,
      f u ∈ geodesicChartDomain (I := I) p := hdom.eventually_nhds
  filter_upwards [hev, hdom, hdom'] with s hs hsdom hsdom'
  have hval : tangentCoordChange I.tangent (f s) (⟨p, v⟩ : TangentBundle I M) (f s)
      (geodesicVectorFieldChart cov b p (f s)) =
      geodesicSprayFiber cov b p (f s) :=
    tangentCoordChange_geodesicVectorFieldChart cov p v hsdom
  rw [hval] at hs
  have hfun : (fun u => extChartAt I.tangent (⟨p, v⟩ : TangentBundle I M) (f u))
      =ᶠ[𝓝 s] (fun u =>
        (extChartAt I p ((f u).proj), sprayFiberCoord (I := I) p (f u))) := by
    filter_upwards [hsdom'] with u hu
    refine extChartAt_tangent_apply (⟨p, v⟩ : TangentBundle I M) (r := f u) ?_
    rw [TangentBundle.trivializationAt_baseSet]
    exact hu
  exact hs.congr_of_eventuallyEq hfun.symm

section InitialData

/-- **A geodesic leaves `p` with velocity `v`.**  For a spray geodesic with initial data
`(p, v)` on a neighbourhood of `0`, the chart-`p` reading `s ↦ φ_p(γ s)` has derivative
`v` at `s = 0`. -/
theorem IsSprayGeodesicOnWithInitial.hasDerivAt_extChartAt_zero
    {cov : Connection I E (TangentSpace I : M → Type _)} {γ : ℝ → M} {J : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsSprayGeodesicOnWithInitial cov b γ J p v) (hJ : J ∈ 𝓝 (0 : ℝ)) :
    HasDerivAt (fun s => extChartAt I p (γ s)) v 0 := by
  classical
  obtain ⟨f, hproj, hf0, hint⟩ := hγ
  have hat : IsMIntegralCurveAt f (geodesicVectorFieldChart cov b p) 0 :=
    hint.isMIntegralCurveAt hJ
  have h0 := (eventually_hasDerivAt_geodesic_reading cov p v hf0 hat).self_of_nhds
  have hfst := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt 0 h0
  have hfun : (⇑(ContinuousLinearMap.fst ℝ E E) ∘ fun u =>
      (extChartAt I p ((f u).proj), sprayFiberCoord (I := I) p (f u))) =
      (fun s => extChartAt I p (γ s)) := by
    funext u
    show extChartAt I p ((f u).proj) = extChartAt I p (γ u)
    rw [hproj u]
  rw [hfun] at hfst
  have hval : (ContinuousLinearMap.fst ℝ E E)
      (geodesicSprayFiber cov b p (f 0)) = v := by
    show (geodesicSprayFiber cov b p (f 0)).1 = v
    rw [hf0]
    exact sprayFiberCoord_mk (I := I) p v
  rw [hval] at hfst
  exact hfst

/-- **A spray geodesic satisfies Lee's geodesic equation at the initial time.**  This
bridges the spray / integral-curve formulation of Theorem 4.27 back to Lee's definition
of a geodesic (`D_t γ' = 0`): the chart-`p` reading `x = φ_p ∘ γ` has vanishing
acceleration `x'' + Γ_p(x', x')(γ) = 0` at `t = 0`, i.e.
`chartAcceleration cov (trivializationAt.. p) b (φ_p ∘ γ) γ 0 = 0`, with the chart at
the foot `γ 0 = p`. -/
theorem IsSprayGeodesicOnWithInitial.chartAcceleration_zero
    {cov : Connection I E (TangentSpace I : M → Type _)} {γ : ℝ → M} {J : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsSprayGeodesicOnWithInitial cov b γ J p v) (hJ : J ∈ 𝓝 (0 : ℝ)) :
    chartAcceleration cov (trivializationAt E (TangentSpace I) p) b
      (fun s => extChartAt I p (γ s)) γ 0 = 0 := by
  classical
  have hstart : γ 0 = p := hγ.start_eq
  obtain ⟨f, hproj, hf0, hint⟩ := hγ
  have hat : IsMIntegralCurveAt f (geodesicVectorFieldChart cov b p) 0 :=
    hint.isMIntegralCurveAt hJ
  have hev := eventually_hasDerivAt_geodesic_reading cov p v hf0 hat
  set x : ℝ → E := fun s => extChartAt I p (γ s) with hx_def
  set w : ℝ → E := fun s => sprayFiberCoord (I := I) p (f s) with hw_def
  have hpair_eq : (fun u =>
      (extChartAt I p ((f u).proj), sprayFiberCoord (I := I) p (f u))) =
      (fun u => (x u, w u)) := by
    funext u
    show (extChartAt I p ((f u).proj), _) = (extChartAt I p (γ u), _)
    rw [hproj u]
  rw [hpair_eq] at hev
  -- first component: `x` has eventual derivative `w`
  have hx_ev : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt x (w s) s := by
    filter_upwards [hev] with s hs
    exact (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt s hs
  -- second component: `w` has derivative the Christoffel term at `0`
  have hw0 : HasDerivAt w ((geodesicSprayFiber cov b p (f 0)).2) 0 := by
    have hs := hev.self_of_nhds
    exact (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt 0 hs
  have hw0_val : w 0 = v := by
    show sprayFiberCoord (I := I) p (f 0) = v
    rw [hf0]
    exact sprayFiberCoord_mk (I := I) p v
  have hderiv_ev : deriv x =ᶠ[𝓝 (0 : ℝ)] w := by
    filter_upwards [hx_ev] with s hs
    exact hs.deriv
  have hdx0 : deriv x 0 = v := by rw [(hx_ev.self_of_nhds).deriv, hw0_val]
  have hddx0 : deriv (deriv x) 0 = (geodesicSprayFiber cov b p (f 0)).2 := by
    rw [hderiv_ev.deriv_eq, hw0.deriv]
  have hsnd : (geodesicSprayFiber cov b p (f 0)).2 =
      - chartGamma cov (trivializationAt E (TangentSpace I) p) b v v p := by
    show (geodesicSprayFiber cov b p (f 0)).2 = _
    rw [hf0]
    show - chartGamma cov (trivializationAt E (TangentSpace I) p) b
        (sprayFiberCoord (I := I) p (⟨p, v⟩ : TangentBundle I M))
        (sprayFiberCoord (I := I) p (⟨p, v⟩ : TangentBundle I M))
        ((⟨p, v⟩ : TangentBundle I M).proj) = _
    rw [sprayFiberCoord_mk (I := I) p v]
  rw [chartAcceleration_def, hddx0, hsnd, hdx0, hstart]
  exact neg_add_cancel _

end InitialData

end

end LeeLib.Ch04
