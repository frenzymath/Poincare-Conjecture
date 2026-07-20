import DoCarmoLib.Riemannian.Jacobi.GeodesicTranslation
import DoCarmoLib.Riemannian.Jacobi.StateTransition
import DoCarmoLib.Riemannian.Geodesic.Completeness
import DoCarmoLib.Riemannian.Geodesic.IntrinsicUniqueness

/-!
# Poincaré Ch. 1, §1.4 — the geodesic with a prescribed chart state

The flow chain of `cor:dc-ch5-2-5` computes, for every chart
state `z` near the state of `γ` at time `0`, an *orbit* whose `i`-th entry is the
chart-`β i` state, at the partition time `τ i`, of a geodesic emanating from `z`
(`hasStrictFDerivAt_comp_chain_nbhd`, `exists_geodesic_flowstep_partition`). Each
piece supplies its *own* local geodesic, produced by its own local flow. To read
the endpoint of the chain as `exp_p` of a nearby initial vector, these per-piece
geodesics must be recognized as pieces of **one** geodesic.

Rather than gluing them by a sSup walk, we let *uniqueness* do the work: on a
complete manifold every chart state is the initial datum of a geodesic defined on
all of `ℝ`, and any two geodesics sharing a chart state at one time coincide
everywhere. So each piece's local geodesic is a restriction of the single global
geodesic determined by the initial state, and the induction along the orbit
becomes a chain of uniqueness statements.

* `exists_geodesic_chartState` — on a complete manifold, for any chart `β`, time
  `a`, foot `x` in the chart source, and chart velocity `w`, a global geodesic `c`
  with `c a = x` and `(φ_β ∘ c)'(a) = w`.
* `eq_of_chartState_eq` — two global geodesics with the same chart-`β` state at a
  common time are equal.

The velocity is prescribed in an *arbitrary* chart `β`, not in the chart at the
foot `x`: that is the vocabulary the flow chain speaks (`jacobiVarPair`,
`stateTransition`), and DoCarmoLib's intrinsic uniqueness
(`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) already compares chart velocities in
an arbitrary chart. The translation between the two readings is the tangent
coordinate-change cocycle.

Blueprint: `cor:dc-ch5-2-5`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4;
do Carmo, *Riemannian Geometry*, Ch. 3 and Ch. 7 (Hopf–Rinow).
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **Geodesics are determined by one chart state.** Two geodesics
defined on all of `ℝ` which pass through the same point at the same time `a`, with
the same chart-`β` velocity there, are equal.

This is DoCarmoLib's intrinsic uniqueness
(`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) on the preconnected open set
`univ`; `MetricSpace M` supplies the `T2Space M` it needs.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem eq_of_chartState_eq (g : RiemannianMetric I M) {c₁ c₂ : ℝ → M}
    (h₁ : IsGeodesic (I := I) g c₁) (hc₁ : Continuous c₁)
    (h₂ : IsGeodesic (I := I) g c₂) (hc₂ : Continuous c₂)
    {a : ℝ} {β : M} (hβ : c₁ a ∈ (chartAt H β).source)
    (hpos : c₁ a = c₂ a)
    (hvel : deriv (fun t => extChartAt I β (c₁ t)) a
      = deriv (fun t => extChartAt I β (c₂ t)) a) :
    c₁ = c₂ := by
  have heq : Set.EqOn c₁ c₂ (univ : Set ℝ) :=
    IsGeodesicOn.eqOn_of_deriv_chartReading_eq (β := β) isOpen_univ isPreconnected_univ
      (fun t _ => h₁ t) (fun t _ => h₂ t) hc₁.continuousOn hc₂.continuousOn
      (mem_univ a) hpos hβ hvel
  exact funext fun t => heq (mem_univ t)

/-- **Math.** **Existence of the geodesic with a prescribed chart state.** On a
complete Riemannian manifold, given a chart basepoint `β`, a time `a`, a foot `x`
in the source of the chart at `β`, and a chart-`β` velocity `w : E`, there is a
geodesic `c : ℝ → M`, defined on all of `ℝ`, with `c a = x` and chart-`β` velocity
`w` at `a`.

Construction: Hopf–Rinow (`DoCarmoLib`'s `exists_global_geodesic`) produces a
geodesic through `x` whose velocity is prescribed *in the chart at `x` itself*, so
the requested chart-`β` velocity `w` is first converted to the chart-`x` reading
`v = C_{β→x} w` by the tangent coordinate change; the resulting geodesic is then
translated in time by `a`. That the chart-`β` velocity of the translate at `a` is
`w` again is the cocycle `C_{x→β} ∘ C_{β→x} = C_{β→β} = id` at the foot `x`.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem exists_geodesic_chartState (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (β : M) (a : ℝ) {x : M} (hx : x ∈ (chartAt H β).source) (w : E) :
    ∃ c : ℝ → M, Continuous c ∧ IsGeodesic (I := I) g c ∧ c a = x ∧
      deriv (fun t => extChartAt I β (c t)) a = w := by
  classical
  -- the chart-`x` reading of the vector whose chart-`β` reading is `w`
  set v : TangentSpace I x := tangentCoordChange I β x x w with hvdef
  obtain ⟨c₀, hc₀0, hc₀v, hc₀cont, hc₀geo⟩ :=
    Riemannian.Geodesic.exists_global_geodesic (I := I) g hg x v
  -- the time translate `c t = c₀ (-a + t)`, so that `c a = c₀ 0 = x`
  refine ⟨fun t => c₀ (-a + t), hc₀cont.comp (by fun_prop), ?_, ?_, ?_⟩
  · -- a geodesic: translation invariance of the geodesic equation
    exact fun σ => HasGeodesicEquationAt.comp_const_add g (hc₀geo (-a + σ))
  · -- passes through `x` at time `a`
    show c₀ (-a + a) = x
    rw [neg_add_cancel]; exact hc₀0
  · -- chart-`β` velocity `w` at time `a`
    set c : ℝ → M := fun t => c₀ (-a + t) with hcdef
    have hca : c a = x := by show c₀ (-a + a) = x; rw [neg_add_cancel]; exact hc₀0
    have hcgeo : IsGeodesic (I := I) g c := fun σ =>
      HasGeodesicEquationAt.comp_const_add g (hc₀geo (-a + σ))
    have hccont : Continuous c := hc₀cont.comp (by fun_prop)
    -- the chart-`x` velocity of `c` at `a` is `v`
    have hvx : deriv (fun t => extChartAt I x (c t)) a = v := by
      have hbridge : deriv (fun t => extChartAt I x (c₀ (-a + t))) a
          = deriv (fun s => extChartAt I x (c₀ s)) (-a + a) :=
        deriv_comp_const_add (fun s => extChartAt I x (c₀ s)) (-a) a
      rw [hcdef]
      rw [hbridge, neg_add_cancel]
      exact hc₀v.deriv
    -- transport the velocity from the chart at `x` to the chart at `β`
    have hxx : c a ∈ (chartAt H x).source := by rw [hca]; exact mem_chart_source H x
    have hxβ : c a ∈ (chartAt H β).source := by rw [hca]; exact hx
    have hchange := deriv_extChartAt_eq_tangentCoordChange (I := I) (g := g)
      (fun t _ => hcgeo t) (mem_univ a) hccont.continuousAt hxx hxβ
    rw [hchange, hvx, hca, hvdef]
    -- the cocycle `C_{x→β} ∘ C_{β→x} = C_{β→β} = id` at the foot `x`
    have hmem : x ∈ (extChartAt I β).source ∩ (extChartAt I x).source
        ∩ (extChartAt I β).source := by
      refine ⟨⟨?_, mem_extChartAt_source x⟩, ?_⟩
      · rw [extChartAt_source]; exact hx
      · rw [extChartAt_source]; exact hx
    rw [tangentCoordChange_comp (I := I) hmem]
    exact tangentCoordChange_self (I := I) (by rw [extChartAt_source]; exact hx)

/-- **Math.** **The chart junction reads any geodesic's chart state, not just the
reference one.** If `c` is a geodesic whose foot at time `t` lies in the sources of
both charts, then `stateTransition β β'` sends the chart-`β` state of `c` at `t` to
its chart-`β'` state at `t`.

`exists_geodesic_junction_step` establishes this for the *reference* geodesic `γ` at
the partition times. Rung 4 needs it for the geodesics `c_z` emanating from all
*nearby* initial states `z` — the odd links of the chain must transport those too.
Since the statement quantifies over an arbitrary geodesic `c`, it applies verbatim
to each `c_z`, and the only side condition is that `c_z`'s foot still lies in both
chart sources, which holds for `z` near the reference state because both sources are
open.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem stateTransition_chartState (g : RiemannianMetric I M) {c : ℝ → M} {s : Set ℝ}
    (hgeo : IsGeodesicOn (I := I) g c s) {t : ℝ} (ht : t ∈ s) (hcont : ContinuousAt c t)
    {β β' : M} (hβ : c t ∈ (chartAt H β).source) (hβ' : c t ∈ (chartAt H β').source) :
    stateTransition (I := I) β β'
        (extChartAt I β (c t), deriv (fun u => extChartAt I β (c u)) t)
      = (extChartAt I β' (c t), deriv (fun u => extChartAt I β' (c u)) t) := by
  rw [stateTransition_apply_state (I := I) β β' hβ hβ',
    deriv_extChartAt_eq_tangentCoordChange (I := I) hgeo ht hcont hβ hβ']

end Riemannian.Jacobi

end
