import OpenGALib.Riemannian.Jacobi.JacobiSectionalCurvature
import OpenGALib.Riemannian.Manifold.DoCarmoCh6ConstantCurvature

/-!
# do Carmo Ch. 5, §2, Example 2.3 — Jacobi fields on a space of constant curvature

do Carmo Ex. 2.3: on a manifold of constant sectional curvature `K₀`, a Jacobi field `J` normal
to a unit-speed geodesic `γ` satisfies `R(γ', J)γ' = K₀ J`, so the Jacobi equation becomes the
scalar equation `D²J/dt² + K₀ J = 0`.

This file develops the **curvature reduction** feeding that example:

* `curvatureFormAt_isConstantCurvature` — the pointwise `(0,4)` reading of do Carmo Lemma 3.4
  (`lem:dc-ch4-3-4`): for a constant-curvature connection the curvature form is the model form
  `⟨R(x, y)z, t⟩ = K₀(⟨x, z⟩⟨y, t⟩ − ⟨y, z⟩⟨x, t⟩)` at every point.
* `chartCurvatureOp_isConstantCurvature` — the Jacobi-equation curvature operator in constant
  curvature: `ℛ_chart(u̇, w)u̇ = K₀ w` for `w ⟂ u̇`, `|u̇| = 1` (do Carmo `R(γ', J)γ' = K₀ J`).
  Both statements are read in the fixed chart at `p`; the operator identity uses the frame
  bridge of `cor:dc-ch5-2-9` and positive-definiteness of the chart Gram form
  (`chartMetricInner_pos`) for nondegeneracy.

Blueprint: `ex:dc-ch5-2-3` (curvature reduction).

Reference: do Carmo, *Riemannian Geometry*, Ch. 5, Example 2.3.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### The pointwise constant-curvature `(0,4)` form (do Carmo Lemma 3.4, pointwise) -/

/-- **Math.** **do Carmo Ch. 4, Lemma 3.4, pointwise form.**  For a connection of constant
sectional curvature `K₀`, the pointwise curvature `(0,4)` form is the model form
`⟨R(x, y)z, t⟩_g = K₀(⟨x, z⟩⟨y, t⟩ − ⟨y, z⟩⟨x, t⟩)` at every point `q`.  This is the
field-level `IsConstantCurvature` hypothesis read at a point through smooth extensions of the
four tangent vectors (`curvatureOperatorAt_eq`). -/
theorem curvatureFormAt_isConstantCurvature (g : RiemannianMetric I M) {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀) (q : M)
    (x y z t : TangentSpace I q) :
    g.leviCivitaConnection.curvatureFormAt g q x y z t
      = K₀ * (g.metricInner q x z * g.metricInner q y t
          - g.metricInner q y z * g.metricInner q x t) := by
  rw [AffineConnection.curvatureFormAt,
    g.leviCivitaConnection.curvatureOperatorAt_eq q
      (AffineConnection.extendField_apply q x) (AffineConnection.extendField_apply q y)
      (AffineConnection.extendField_apply q z)]
  have h := hK (AffineConnection.extendField q x) (AffineConnection.extendField q y)
    (AffineConnection.extendField q z) (AffineConnection.extendField q t) q
  simp only [AffineConnection.extendField_apply] at h
  exact h

/-! ### Nondegeneracy of the chart Gram form -/

/-- **Math.** The chart Gram form is nondegenerate: two coordinate vectors that pair equally with
every vector are equal.  (Positive definiteness `chartMetricInner_pos`: test against the
difference.) -/
theorem eq_of_chartMetricInner_eq (g : RiemannianMetric I M) {α p : M}
    (hp : p ∈ (chartAt H α).source) {a b : E}
    (h : ∀ z : E, chartMetricInner (I := I) g α (extChartAt I α p) a z
      = chartMetricInner (I := I) g α (extChartAt I α p) b z) :
    a = b := by
  by_contra hne
  have hbase : (extChartAt I α).symm (extChartAt I α p)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet := symm_extChartAt_mem_baseSet (I := I) hp
  have hsub : chartMetricInner (I := I) g α (extChartAt I α p) (a - b) (a - b) = 0 := by
    have hlin : chartMetricInner (I := I) g α (extChartAt I α p) (a - b) (a - b)
        = chartMetricInner (I := I) g α (extChartAt I α p) a (a - b)
          - chartMetricInner (I := I) g α (extChartAt I α p) b (a - b) := by
      rw [sub_eq_add_neg a b, chartMetricInner_add_left, chartMetricInner_neg_left]; ring
    rw [hlin, h (a - b), sub_self]
  exact absurd hsub (chartMetricInner_pos (I := I) g α hbase (sub_ne_zero.mpr hne)).ne'

/-! ### The Jacobi-equation curvature operator in constant curvature (do Carmo Ex. 2.3) -/

/-- **Math.** **do Carmo Ch. 5, Example 2.3 (curvature reduction).**  On a manifold of constant
sectional curvature `K₀`, the Jacobi-equation curvature operator `ℛ_chart(u̇, ·)u̇` acts as
multiplication by `K₀` on vectors orthogonal to a unit velocity: for `w` with
`⟨w, u̇⟩ = 0` and `⟨u̇, u̇⟩ = 1` (do Carmo's `J ⟂ γ'`, `|γ'| = 1`) read in the fixed chart at `p`,

  `chartCurvatureOp g p u t₀ w = K₀ • w`,

i.e. do Carmo's `R(γ', J)γ' = K₀ J`.  Hence the Jacobi equation reduces to the scalar system
`D²J/dt² + K₀ J = 0`.  Proof: the operator is `ℛ_chart(u̇, w)u̇ = chartCurvature (u t₀) w u̇ u̇`;
pairing with an arbitrary `z` and using the manifold ↔ chart frame bridge
(`curvatureFormAt_chartFrame`), the pointwise constant-curvature form
(`curvatureFormAt_isConstantCurvature`), and orthonormality collapses the model form to
`K₀ ⟨w, z⟩`; nondegeneracy (`eq_of_chartMetricInner_eq`) then gives the operator identity. -/
theorem chartCurvatureOp_isConstantCurvature (g : RiemannianMetric I M) {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀) (p : M) (u : ℝ → E) (t₀ : ℝ) (w : E)
    {q : M} (hq : q ∈ (chartAt H p).source) (hu : u t₀ = extChartAt I p q)
    (hunit : chartMetricInner (I := I) g p (u t₀) (deriv u t₀) (deriv u t₀) = 1)
    (hperp : chartMetricInner (I := I) g p (u t₀) w (deriv u t₀) = 0) :
    chartCurvatureOp (I := I) g p u t₀ w = K₀ • w := by
  have hy_int : u t₀ ∈ interior (extChartAt I p).target := by
    rw [hu, (isOpen_extChartAt_target (I := I) p).interior_eq]
    exact (extChartAt I p).map_source (by rwa [extChartAt_source])
  -- pair the operator with an arbitrary `z`, then use nondegeneracy
  refine eq_of_chartMetricInner_eq (I := I) g hq (a := chartCurvatureOp (I := I) g p u t₀ w)
    (b := K₀ • w) (fun z => ?_)
  rw [← hu]
  -- the operator is the chart curvature contraction
  rw [chartCurvatureOp_eq_chartCurvature (I := I) g p u t₀ w hy_int]
  -- the manifold ↔ chart frame bridge, evaluated on `(w, u̇, u̇, z)`
  have hbridge := curvatureFormAt_chartFrame (I := I) g hq w (deriv u t₀) (deriv u t₀) z
  -- the constant-curvature model form on the frame realizations
  have hcc := curvatureFormAt_isConstantCurvature (I := I) g hK q
    (∑ a, Geodesic.chartCoord (E := E) a w • chartBasisVecFiber (I := I) p a q)
    (∑ b, Geodesic.chartCoord (E := E) b (deriv u t₀) • chartBasisVecFiber (I := I) p b q)
    (∑ c, Geodesic.chartCoord (E := E) c (deriv u t₀) • chartBasisVecFiber (I := I) p c q)
    (∑ d, Geodesic.chartCoord (E := E) d z • chartBasisVecFiber (I := I) p d q)
  rw [metricInner_chartFrameRealize (I := I) g hq w (deriv u t₀),
    metricInner_chartFrameRealize (I := I) g hq (deriv u t₀) z,
    metricInner_chartFrameRealize (I := I) g hq (deriv u t₀) (deriv u t₀),
    metricInner_chartFrameRealize (I := I) g hq w z, ← hu, hperp, hunit] at hcc
  -- `hcc : curvatureForm(Fw,Fu̇,Fu̇,Fz) = K₀ (0 · ⟨u̇,z⟩ − 1 · ⟨w,z⟩)`
  rw [hcc, ← hu] at hbridge
  -- `hbridge : K₀(0·⟨u̇,z⟩ − 1·⟨w,z⟩) = −⟨chartCurvature (u t₀) w u̇ u̇, z⟩`
  rw [chartMetricInner_smul_left]
  linear_combination hbridge

end Riemannian.Jacobi

end
