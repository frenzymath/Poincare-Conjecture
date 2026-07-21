import DoCarmoLib.Riemannian.Variation.SurfaceSymmetryManifold
import DoCarmoLib.Riemannian.Jacobi.SurfaceCurvatureCommutation
import DoCarmoLib.Riemannian.Jacobi.CartanCurvatureBridge

/-!
# The surface curvature commutation at the manifold level (do Carmo Ch. 4, `lem:dc-ch4-4-1`)

do Carmo, *Riemannian Geometry*, Ch. 4, Lemma 4.1 (the Ricci identity on a parametrized
surface), read on a surface `f : ℝ × ℝ → M` **valued in the manifold** — the form Ch. 9 §2
uses at the curvature substitution in the proof of the second variation formula
(`prop:dc-ch9-2-8`).

`Jacobi/SurfaceCurvatureCommutation.lean` proves the same identity for a surface
`f : ℝ × ℝ → E` read in one fixed chart, with `D/∂s`, `D/∂t` the coordinate operators
`Jacobi.surfaceCovariantDerivS`/`surfaceCovariantDerivT` and the curvature as the
coordinate contraction `Jacobi.chartCurvatureContraction2`.  This file carries the identity
across to objects that do not mention a chart: the two velocity fields are `mfderiv`-based,
the four (iterated) covariant derivatives are `IsCovariantDerivFieldAlongOn` pairs, and the
curvature is the intrinsic `curvatureFormAt` of do Carmo's Ch. 4 Def. 2.1 convention.

This mirrors `Variation/SurfaceSymmetryManifold.lean`, which transports the *symmetry*
lemma (Ch. 3 Lemma 3.4, no curvature) by the same route; here the transported identity is
the Ricci identity, whose right-hand side is the curvature.

## The curvature bridge (first, self-contained)

The only genuinely new arithmetic beyond the symmetry transfer is the identification of the
chart curvature contraction with the intrinsic curvature form.  This is the general
(`R(X, Y)Z`, off-diagonal) analogue of the Jacobi-configuration bridge
`Jacobi.chartMetricInner_chartCurvatureEndo_chartVectorRep_eq_curvatureFormAt`
(`CartanCurvatureBridge.lean`), proved by the same two facts:
`Jacobi.curvatureFormAt_chartFrame` (the manifold ↔ chart bridge, which carries the
do Carmo ↔ Morgan–Tian sign) and `Jacobi.curvatureFormAt_antisymm_fst` (which cancels it),
plus the reindexing `Jacobi.chartCurvatureContraction2_eq_chartCurvature` and the readback
`Jacobi.chartFrameRealize_tangentCoordChange`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 4, Lemma 4.1; used at Ch. 9 §2 in the proof
of `prop:dc-ch9-2-8`.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi Riemannian.Geodesic Riemannian.Exponential Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### The general curvature bridge: chart contraction paired = intrinsic curvature form -/

/-- **Math.** do Carmo Ch. 4, Lemma 4.1 (right-hand side), intrinsic reading, in coordinate
form.  For coordinate vectors `x, y, z, w : E` read in the chart at `α` around `q`, the chart
curvature contraction `ℛ_chart(x, y)z` paired against `w` under the chart Gram form is the
intrinsic curvature `(0,4)` form of the chart-frame realizations, in **do Carmo's** sign:
`⟨ℛ_chart(x, y)z, w⟩_α = R(x̂, ŷ, ẑ, ŵ)`.

The general (`R(X, Y)Z`, off-diagonal) analogue of
`chartMetricInner_chartCurvatureEndo_eq_curvatureFormAt` (`CartanCurvatureBridge.lean`),
which handles only the Jacobi configuration `x = z`.  The sign chain is the same: the
manifold ↔ chart bridge `curvatureFormAt_chartFrame` carries the do Carmo ↔ Morgan–Tian
minus, and antisymmetry in the first pair (`curvatureFormAt_antisymm_fst`) cancels it. -/
theorem chartMetricInner_chartCurvatureContraction2_eq_curvatureFormAt (g : RiemannianMetric I M)
    (α : M) (x y z w : E) {q : M} (hq : q ∈ (chartAt H α).source)
    {yq : E} (hyq : yq = extChartAt I α q) :
    chartMetricInner (I := I) g α yq
        (chartCurvatureContraction2 (I := I) g α x y z yq) w
      = g.leviCivitaConnection.curvatureFormAt g q
          (∑ i, Geodesic.chartCoord (E := E) i x • chartBasisVecFiber (I := I) α i q)
          (∑ i, Geodesic.chartCoord (E := E) i y • chartBasisVecFiber (I := I) α i q)
          (∑ i, Geodesic.chartCoord (E := E) i z • chartBasisVecFiber (I := I) α i q)
          (∑ i, Geodesic.chartCoord (E := E) i w • chartBasisVecFiber (I := I) α i q) := by
  subst hyq
  have hy_int : extChartAt I α q ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source (by rwa [extChartAt_source])
  rw [chartCurvatureContraction2_eq_chartCurvature (I := I) g α x y z hy_int]
  -- the manifold ↔ chart bridge on the realizations of `(y, x, z, w)` — carries a sign
  have hbridge := curvatureFormAt_chartFrame (I := I) g hq y x z w
  -- antisymmetry in the first pair moves `y` past `x`, cancelling that sign
  have hanti := curvatureFormAt_antisymm_fst (I := I) g q
    (∑ i, Geodesic.chartCoord (E := E) i y • chartBasisVecFiber (I := I) α i q)
    (∑ i, Geodesic.chartCoord (E := E) i x • chartBasisVecFiber (I := I) α i q)
    (∑ i, Geodesic.chartCoord (E := E) i z • chartBasisVecFiber (I := I) α i q)
    (∑ i, Geodesic.chartCoord (E := E) i w • chartBasisVecFiber (I := I) α i q)
  linear_combination hbridge - hanti

/-- **Math.** do Carmo Ch. 4, Lemma 4.1 (right-hand side), intrinsic reading.  For
**intrinsic** vectors `X, Y, Z, W ∈ T_qM`, the chart curvature contraction of their chart
readings, paired against the reading of `W`, is exactly the intrinsic curvature `(0,4)` form
`R(X, Y, Z, W)` — do Carmo's `⟨R(X, Y)Z, W⟩`, with no chart-frame realizations left in the
statement.  Composite of
`chartMetricInner_chartCurvatureContraction2_eq_curvatureFormAt` with the readback
`chartFrameRealize_tangentCoordChange`. -/
theorem chartMetricInner_chartCurvatureContraction2_chartVectorRep_eq_curvatureFormAt
    (g : RiemannianMetric I M) (α : M) {q : M} (hq : q ∈ (chartAt H α).source)
    (X Y Z W : TangentSpace I q) :
    chartMetricInner (I := I) g α (extChartAt I α q)
        (chartCurvatureContraction2 (I := I) g α
          (tangentCoordChange I q α q X) (tangentCoordChange I q α q Y)
          (tangentCoordChange I q α q Z) (extChartAt I α q))
        (tangentCoordChange I q α q W)
      = g.leviCivitaConnection.curvatureFormAt g q X Y Z W := by
  rw [chartMetricInner_chartCurvatureContraction2_eq_curvatureFormAt (I := I) g α
      (tangentCoordChange I q α q X) (tangentCoordChange I q α q Y)
      (tangentCoordChange I q α q Z) (tangentCoordChange I q α q W) hq rfl,
    chartFrameRealize_tangentCoordChange (I := I) α hq X,
    chartFrameRealize_tangentCoordChange (I := I) α hq Y,
    chartFrameRealize_tangentCoordChange (I := I) α hq Z,
    chartFrameRealize_tangentCoordChange (I := I) α hq W]

/-! ### The surface Ricci identity, metric-paired, with the intrinsic curvature -/

/-- **Math.** do Carmo Ch. 4, Lemma 4.1 (`lem:dc-ch4-4-1`), **metric-paired form with the
intrinsic curvature**.  For a `C²` parametrized surface `f : ℝ² → E` and field `V` read in
the chart at `α`, the commutator of the two covariant derivatives, paired against a chart
vector `w`, is the intrinsic curvature `(0,4)` form of the chart-frame realizations of the
two velocities `∂f/∂s`, `∂f/∂t`, the field `V`, and `w`:
$$
\Big\langle\frac{D}{\partial t}\frac{D}{\partial s}V - \frac{D}{\partial s}\frac{D}{\partial t}V,\ w\Big\rangle
  = R\Big(\widehat{\tfrac{\partial f}{\partial s}},\ \widehat{\tfrac{\partial f}{\partial t}},\ \widehat V,\ \widehat w\Big).
$$

This composes the chart-level commutation `Jacobi.surface_covariant_commutator_of_eventually`
with the curvature bridge `chartMetricInner_chartCurvatureContraction2_eq_curvatureFormAt`;
it is the geometric substitution do Carmo makes at the curvature step of `prop:dc-ch9-2-8`,
in do Carmo's Ch. 4 Def. 2.1 curvature sign (`⟨R(∂f/∂s, ∂f/∂t)V, w⟩`).  The velocities and
field survive only as chart readings; the fully chart-free, `IsCovariantDerivFieldAlongOn`
form is the transfer that mirrors `covariantDerivS_velT_eq_covariantDerivT_velS`. -/
theorem chartMetricInner_surface_covariant_commutator_eq_curvatureFormAt
    (g : RiemannianMetric I M) (α : M) (f V : ℝ × ℝ → E)
    (Df DV : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E))
    (D2f D2V : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E) (s₀ t₀ : ℝ) (w : E)
    (hf : ∀ᶠ p in nhds (s₀, t₀), HasFDerivAt f (Df p) p) (hf2 : HasFDerivAt Df D2f (s₀, t₀))
    (hV : ∀ᶠ p in nhds (s₀, t₀), HasFDerivAt V (DV p) p) (hV2 : HasFDerivAt DV D2V (s₀, t₀))
    {q : M} (hq : q ∈ (chartAt H α).source) (hfoot : f (s₀, t₀) = extChartAt I α q) :
    chartMetricInner (I := I) g α (f (s₀, t₀))
        (surfaceCovariantDerivT (I := I) g α f
            (surfaceCovariantDerivS (I := I) g α f V) (s₀, t₀)
          - surfaceCovariantDerivS (I := I) g α f
            (surfaceCovariantDerivT (I := I) g α f V) (s₀, t₀))
        w
      = g.leviCivitaConnection.curvatureFormAt g q
          (∑ i, Geodesic.chartCoord (E := E) i (Df (s₀, t₀) (1, 0)) • chartBasisVecFiber (I := I) α i q)
          (∑ i, Geodesic.chartCoord (E := E) i (Df (s₀, t₀) (0, 1)) • chartBasisVecFiber (I := I) α i q)
          (∑ i, Geodesic.chartCoord (E := E) i (V (s₀, t₀)) • chartBasisVecFiber (I := I) α i q)
          (∑ i, Geodesic.chartCoord (E := E) i w • chartBasisVecFiber (I := I) α i q) := by
  have hmem : f (s₀, t₀) ∈ interior (extChartAt I α).target := by
    rw [hfoot, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source (by rwa [extChartAt_source])
  rw [surface_covariant_commutator_of_eventually (I := I) g α f V Df DV D2f D2V s₀ t₀
      hf hf2 hV hV2 hmem,
    chartMetricInner_chartCurvatureContraction2_eq_curvatureFormAt (I := I) g α
      (Df (s₀, t₀) (1, 0)) (Df (s₀, t₀) (0, 1)) (V (s₀, t₀)) w hq hfoot]

end Riemannian.Variation
