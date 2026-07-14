import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Locally constant charted space

The `IsLocallyConstantChartedSpace` typeclass: in every neighbourhood of
every basepoint, `chartAt H` is constant. Standard Mathlib examples
(Euclidean spaces, single-chart-per-region atlases) satisfy this. The
class is needed because Mathlib's `ChartedSpace` only requires local
compatibility of chart *transitions*, not local constancy of the
chart-selection function `chartAt H : M → PartialHomeomorph M H` —
without local constancy, parametric chart-derivatives are not
generally smooth.

Plus a strict-interior nbhd-propagation lemma consumed by the Bochner
stack (`extChartAt_self_eventually_mem_closure_interior_range`).
-/

open scoped Manifold Topology

class IsLocallyConstantChartedSpace
    (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop where
  /-- `chartAt H b = chartAt H b₀` eventually as `b → b₀`. -/
  chartAt_eventually_eq : ∀ b₀ : M, ∀ᶠ b in 𝓝 b₀, chartAt H b = chartAt H b₀

theorem chartAt_eventually_eq_of_locallyConstant
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsLocallyConstantChartedSpace H M] (b₀ : M) :
    ∀ᶠ b in 𝓝 b₀, chartAt H b = chartAt H b₀ :=
  IsLocallyConstantChartedSpace.chartAt_eventually_eq b₀

/-- **Eng.** `H` over itself satisfies `IsLocallyConstantChartedSpace`
(charts are constantly `PartialHomeomorph.refl H`). -/
instance instIsLocallyConstantChartedSpace_self
    (H : Type*) [TopologicalSpace H] :
    IsLocallyConstantChartedSpace H H where
  chartAt_eventually_eq _ := Filter.Eventually.of_forall (fun _ => rfl)

/-- **Math.** **Strict-interior propagation to nbhd-closure-interior**. If $x \in M$
maps strictly into the interior of $\mathrm{range}\,I$ under `extChartAt I x`,
then in a neighbourhood of $x$, every point $y$ also maps into
$\overline{\mathrm{interior}(\mathrm{range}\,I)}$.

Proof: chart constancy (`chartAt_eventually_eq_of_locallyConstant`) gives
`extChartAt I y = extChartAt I x` eventually; continuity of `extChartAt I x`
at $x$ pulls back the nbhd `interior (Set.range I)` of `extChartAt I x x`
to a nbhd of $x$ in $M$; combining, $\mathrm{extChartAt}\,I\,y\,y =
\mathrm{extChartAt}\,I\,x\,y \in \mathrm{interior}(\mathrm{range}\,I)
\subseteq \overline{\mathrm{interior}(\mathrm{range}\,I)}$ eventually.

Used by `Bochner` to propagate `h_interior` from a single point to a
neighbourhood, which is required to discharge the `h_eventual_sym`
hypothesis of the Hess-sym swap via pointwise `hessianBilin_symm`. -/
theorem extChartAt_self_eventually_mem_closure_interior_range
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsLocallyConstantChartedSpace H M] {x : M}
    (h_strict : extChartAt I x x ∈ interior (Set.range I)) :
    ∀ᶠ y in 𝓝 x, extChartAt I y y ∈ closure (interior (Set.range I)) := by
  -- Step 1: chart constancy ⇒ extChartAt constancy eventually.
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_ext_eq : ∀ᶠ y in 𝓝 x, extChartAt I y = extChartAt I x := by
    filter_upwards [h_chart_eq] with y hy
    rw [extChartAt, extChartAt, hy]
  -- Step 2: continuity of `extChartAt I x` at `x` pulls back the open set
  -- `interior (Set.range I)` (a nbhd of `extChartAt I x x`) to a nbhd of `x`.
  have h_pullback : ∀ᶠ y in 𝓝 x, extChartAt I x y ∈ interior (Set.range I) :=
    (continuousAt_extChartAt (I := I) x).preimage_mem_nhds
      (isOpen_interior.mem_nhds h_strict)
  -- Step 3: combine — at every eventual `y`, `extChartAt I y y = extChartAt I x y`,
  -- which lies in `interior (range I) ⊆ closure (interior (range I))`.
  filter_upwards [h_ext_eq, h_pullback] with y hy_ext hy_int
  rw [hy_ext]
  exact subset_closure hy_int
