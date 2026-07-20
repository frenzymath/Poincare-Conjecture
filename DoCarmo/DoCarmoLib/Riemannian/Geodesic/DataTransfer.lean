import DoCarmoLib.Riemannian.Geodesic.HopfRinow.ConstantSpeed

/-!
# Transfer of chart-read geodesic velocity data between charts
(do Carmo Ch. 7, proof of Theorem 2.8, f) ⟹ b))

For a curve satisfying the intrinsic geodesic equation, the velocity reading
in any chart containing the foot is the `tangentCoordChange` of the reading in
any other such chart — pure first-order calculus, packaged here in the three
forms consumed by the Hopf–Rinow endpoint-continuity argument:

* `HasGeodesicEquationAt.deriv_extChartAt_transfer` — the α-chart and β-chart
  velocity readings of a geodesic at a common time differ by the tangent
  coordinate change at the foot;
* `tendsto_tangentCoordChange_of_tendsto` — the tangent coordinate change is
  jointly continuous in the foot and the vector: convergent feet and vectors
  give convergent coordinate changes;
* `tendsto_deriv_extChartAt_transfer` — the composite: if a sequence of
  geodesics converges to a limit geodesic at time `t` (feet in `M`,
  velocities read in an α-chart), then the velocities read in any β-chart
  containing the limit foot converge as well.
-/


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Chart-to-chart transfer of the geodesic velocity reading.** If
`σ` solves the geodesic equation at `t` and its foot `σ t` lies in the charts
at `α` and at `β`, then the β-chart velocity reading is the tangent coordinate
change (the derivative of the chart transition at the foot) of the α-chart
velocity reading. Both sides are the coordinate change of the moving-foot
chart velocity, and the coordinate changes compose. -/
theorem HasGeodesicEquationAt.deriv_extChartAt_transfer
    {g : RiemannianMetric I M} {σ : ℝ → M} {t : ℝ} {α β : M}
    (h : HasGeodesicEquationAt (I := I) g σ t) (hcont : ContinuousAt σ t)
    (hα : σ t ∈ (chartAt H α).source) (hβ : σ t ∈ (chartAt H β).source) :
    deriv (fun τ => extChartAt I β (σ τ)) t
      = tangentCoordChange I α β (σ t)
          (deriv (fun τ => extChartAt I α (σ τ)) t) := by
  have hα' : σ t ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hα
  have hβ' : σ t ∈ (extChartAt I β).source := by rw [extChartAt_source]; exact hβ
  have hself : σ t ∈ (extChartAt I (σ t)).source := mem_extChartAt_source (σ t)
  rw [h.deriv_extChartAt_eq hcont hβ, h.deriv_extChartAt_eq hcont hα,
    tangentCoordChange_comp (I := I) ⟨⟨hself, hα'⟩, hβ'⟩]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** **Joint sequential continuity of the tangent coordinate change.**
If the feet `zs n` converge to a foot `x` lying in the charts at `α` and at
`β`, and the vectors `us n` converge to `u`, then the coordinate changes
`tangentCoordChange I α β (zs n) (us n)` converge to
`tangentCoordChange I α β x u`: the coordinate change is continuous in the
foot on the common chart source (operator-norm topology) and evaluation is a
continuous bilinear map. -/
theorem tendsto_tangentCoordChange_of_tendsto {α β : M}
    {zs : ℕ → M} {x : M} (hzs : Filter.Tendsto zs Filter.atTop (nhds x))
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    {us : ℕ → E} {u : E} (hus : Filter.Tendsto us Filter.atTop (nhds u)) :
    Filter.Tendsto (fun n => tangentCoordChange I α β (zs n) (us n))
      Filter.atTop (nhds (tangentCoordChange I α β x u)) := by
  have hmem : (extChartAt I α).source ∩ (extChartAt I β).source ∈ 𝓝 x :=
    IsOpen.mem_nhds ((isOpen_extChartAt_source _).inter (isOpen_extChartAt_source _))
      ⟨by rw [extChartAt_source]; exact hxα, by rw [extChartAt_source]; exact hxβ⟩
  have hA : Filter.Tendsto (fun n => tangentCoordChange I α β (zs n))
      Filter.atTop (𝓝 (tangentCoordChange I α β x)) :=
    ((continuousOn_tangentCoordChange (I := I) α β).continuousAt hmem).tendsto.comp hzs
  exact (isBoundedBilinearMap_apply.continuous.tendsto
    (tangentCoordChange I α β x, u)).comp (hA.prodMk_nhds hus)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Transfer of velocity convergence between charts.** If a
sequence of geodesics at time `t` has feet converging to the foot of a limit
geodesic and α-chart velocity readings converging to the limit's α-chart
reading, then the β-chart velocity readings converge to the limit's β-chart
reading, for any β-chart containing the limit foot. Eventually the feet lie
in both chart sources, so each β-reading is the coordinate change of the
α-reading, and the coordinate change is jointly sequentially continuous. -/
theorem tendsto_deriv_extChartAt_transfer
    {g : RiemannianMetric I M} {γs : ℕ → ℝ → M} {γlim : ℝ → M} {t : ℝ} {α β : M}
    (hgeo : ∀ n, HasGeodesicEquationAt (I := I) g (γs n) t)
    (hcont : ∀ n, ContinuousAt (γs n) t)
    (hglim : HasGeodesicEquationAt (I := I) g γlim t)
    (hclim : ContinuousAt γlim t)
    (hα : γlim t ∈ (chartAt H α).source) (hβ : γlim t ∈ (chartAt H β).source)
    (hpos : Filter.Tendsto (fun n => γs n t) Filter.atTop (nhds (γlim t)))
    (hvel : Filter.Tendsto (fun n => deriv (fun τ => extChartAt I α (γs n τ)) t)
      Filter.atTop (nhds (deriv (fun τ => extChartAt I α (γlim τ)) t))) :
    Filter.Tendsto (fun n => deriv (fun τ => extChartAt I β (γs n τ)) t)
      Filter.atTop (nhds (deriv (fun τ => extChartAt I β (γlim τ)) t)) := by
  have hev : ∀ᶠ n in Filter.atTop,
      γs n t ∈ (chartAt H α).source ∩ (chartAt H β).source :=
    hpos.eventually_mem (IsOpen.mem_nhds
      ((chartAt H α).open_source.inter (chartAt H β).open_source) ⟨hα, hβ⟩)
  have heq : (fun n => tangentCoordChange I α β (γs n t)
        (deriv (fun τ => extChartAt I α (γs n τ)) t))
      =ᶠ[Filter.atTop] fun n => deriv (fun τ => extChartAt I β (γs n τ)) t := by
    filter_upwards [hev] with n hn
    exact ((hgeo n).deriv_extChartAt_transfer (hcont n) hn.1 hn.2).symm
  rw [hglim.deriv_extChartAt_transfer hclim hα hβ]
  exact (tendsto_tangentCoordChange_of_tendsto hpos hα hβ hvel).congr' heq

end Geodesic
end Riemannian
