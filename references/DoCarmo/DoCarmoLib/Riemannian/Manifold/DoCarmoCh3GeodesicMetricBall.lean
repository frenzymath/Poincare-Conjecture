import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3UniformInterval
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.GramBound
import DoCarmoLib.Riemannian.Geodesic.IntrinsicUniqueness

/-!
# Do Carmo Ch. 3: a uniform metric ball of geodesic initial data

This module converts the model-space velocity neighborhood in the chart-local
geodesic flow into a base-uniform ball for the Riemannian norm.  It is the
remaining topological and metric bridge in the explicit initial-data domain of
do Carmo's local geodesic theorem.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A fixed-chart geodesic is continuous on its time set: it is the chart inverse of
its differentiable chart reading. -/
theorem IsChartGeodesicOn.continuousOn [I.Boundaryless]
    {g : RiemannianMetric I M} {β : M} {γ : ℝ → M} {J : Set ℝ}
    (h : IsChartGeodesicOn (I := I) g β γ J) :
    ContinuousOn γ J := by
  obtain ⟨hmem, hd1, -⟩ := h
  intro t ht
  have hsrc : γ t ∈ (extChartAt I β).source := by
    rw [extChartAt_source I]
    exact hmem t ht
  have hread : ContinuousAt
      (fun s => (extChartAt I β).symm (extChartAt I β (γ s))) t := by
    refine ContinuousAt.comp ?_ (hd1 t ht).continuousAt
    refine (continuousOn_extChartAt_symm β).continuousAt ?_
    exact (isOpen_extChartAt_target β).mem_nhds ((extChartAt I β).map_source hsrc)
  refine hread.continuousWithinAt.congr (fun s hs => ?_) ?_
  · exact ((extChartAt I β).left_inv (by
      rw [extChartAt_source I]
      exact hmem s hs)).symm
  · exact ((extChartAt I β).left_inv hsrc).symm

/-- **Math.** On an open time set, the fixed-chart geodesic equation implies the intrinsic
moving-foot geodesic equation.  Thus every chart geodesic is a continuous intrinsic geodesic
curve on that set. -/
theorem IsChartGeodesicOn.isGeodesicCurveOn [I.Boundaryless]
    {g : RiemannianMetric I M} {β : M} {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (h : IsChartGeodesicOn (I := I) g β γ J) :
    Geodesic.IsGeodesicCurveOn (I := I) g γ J := by
  have hc : ContinuousOn γ J := h.continuousOn
  refine ⟨hc, ?_⟩
  intro t ht
  apply Geodesic.SolvesGeodesicODEAt.hasGeodesicEquationAt
  · refine ⟨?_, _, ?_, neg_add_cancel _⟩
    · filter_upwards [hJ.mem_nhds ht] with s hs
      rw [show Geodesic.chartReading (I := I) β γ =
        (fun s => extChartAt I β (γ s)) by rfl]
      exact h.2.1 s hs
    · rw [show Geodesic.chartReading (I := I) β γ =
        (fun s => extChartAt I β (γ s)) by rfl]
      exact h.2.2 t ht
  · exact hc.continuousAt (hJ.mem_nhds ht)
  · exact h.1 t ht

namespace GeodesicLocal

/-- **Math.** A model-space velocity neighborhood contains a uniform
Riemannian ball over all base points in a smaller neighborhood.  More
precisely, if `W` is a neighborhood of zero in the model fiber, then near
`p` there is a fixed positive `rho` such that every tangent vector with
`g(v,v) < rho` has chart-`p` fiber coordinate in `W`.

The proof uses the local lower bound of the chart Gram form. -/
theorem exists_chartFiberCoord_mem_of_metricInner_lt
    (g : RiemannianMetric I M) [I.Boundaryless] (p : M)
    {W : Set E} (hW : W ∈ 𝓝 (0 : E)) :
    ∃ V ∈ 𝓝 p, ∃ ρ > 0, ∀ q ∈ V, ∀ v : TangentSpace I q,
      g.metricInner q v v < ρ →
        Geodesic.chartFiberCoord (E := E) (I := I) p
          (⟨q, v⟩ : TangentBundle I M) ∈ W := by
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
  obtain ⟨c, Y, hc, hY, -, hbound⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  let V : Set M := (extChartAt I p).source ∩ extChartAt I p ⁻¹' Y
  have hV : V ∈ 𝓝 p :=
    Filter.inter_mem (extChartAt_source_mem_nhds p)
      ((continuousAt_extChartAt p).preimage_mem_nhds hY)
  refine ⟨V, hV, ε ^ 2 / c, div_pos (sq_pos_of_pos hε) hc, ?_⟩
  intro q hq v hv
  have hqsrc : q ∈ (chartAt H p).source := by
    rw [← extChartAt_source I]
    exact hq.1
  let w : E := Geodesic.chartFiberCoord (E := E) (I := I) p
    (⟨q, v⟩ : TangentBundle I M)
  have hbase : q ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hqsrc
  have hread :
      (trivializationAt E (TangentSpace I) p).symm q w = v := by
    exact Bundle.Trivialization.symm_apply_apply_mk
      (trivializationAt E (TangentSpace I) p) hbase v
  have hmetric :
      chartMetricInner (I := I) g p (extChartAt I p q) w w =
        g.metricInner q v v := by
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p hqsrc, hread]
  have hwbound := hbound (extChartAt I p q) hq.2 w
  rw [hmetric] at hwbound
  have hsq : ‖w‖ ^ 2 < ε ^ 2 := calc
    ‖w‖ ^ 2 ≤ c * g.metricInner q v v := hwbound
    _ < c * (ε ^ 2 / c) := mul_lt_mul_of_pos_left hv hc
    _ = ε ^ 2 := by field_simp
  have hwnorm : ‖w‖ < ε := by
    nlinarith [norm_nonneg w]
  apply hεW
  rw [mem_ball, dist_zero_right]
  exact hwnorm

/-- **Math.** **Uniform local geodesic family on a metric velocity ball.**
The chart-local flow can be restricted to a fixed Riemannian metric ball of
initial velocities over a neighborhood of `p`.  The returned family is smooth
in the chart coordinates on its model-space window, and is unique among chart
geodesics with the same initial position and chart velocity. -/
theorem geodesic_local_existence_metricBall
    (g : RiemannianMetric I M) [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] (p : M) :
    ∃ δ > 0, ∃ V ∈ 𝓝 p, ∃ W ∈ 𝓝 (0 : E), ∃ ρ > 0,
      ∃ c : M → E → ℝ → M,
        (∀ q ∈ V, ∀ v : TangentSpace I q,
          g.metricInner q v v < ρ →
            IsChartGeodesicOn (I := I) g p
                (c q (Geodesic.chartFiberCoord (E := E) (I := I) p
                  (⟨q, v⟩ : TangentBundle I M))) (Ioo (-δ) δ) ∧
            c q (Geodesic.chartFiberCoord (E := E) (I := I) p
              (⟨q, v⟩ : TangentBundle I M)) 0 = q ∧
            HasDerivAt
              (fun s => extChartAt I p
                (c q (Geodesic.chartFiberCoord (E := E) (I := I) p
                  (⟨q, v⟩ : TangentBundle I M)) s))
              (Geodesic.chartFiberCoord (E := E) (I := I) p
                (⟨q, v⟩ : TangentBundle I M)) 0 ∧
            (∀ γ : ℝ → M,
              IsChartGeodesicOn (I := I) g p γ (Ioo (-δ) δ) →
              γ 0 = q →
              HasDerivAt (fun s => extChartAt I p (γ s))
                (Geodesic.chartFiberCoord (E := E) (I := I) p
                  (⟨q, v⟩ : TangentBundle I M)) 0 →
              Set.EqOn γ
                (c q (Geodesic.chartFiberCoord (E := E) (I := I) p
                  (⟨q, v⟩ : TangentBundle I M))) (Ioo (-δ) δ))) ∧
        ContDiffOn ℝ ∞
          (fun xwt : (E × E) × ℝ =>
            extChartAt I p
              (c ((extChartAt I p).symm xwt.1.1) xwt.1.2 xwt.2))
          (((extChartAt I p '' V) ×ˢ W) ×ˢ Ioo (-δ) δ) := by
  obtain ⟨δ, hδ, V₁, hV₁, V₂, hV₂, c, hc, hcsmooth⟩ :=
    geodesic_local_existence (I := I) g p (0 : E)
  obtain ⟨V₃, hV₃, ρ, hρ, hcoord⟩ :=
    exists_chartFiberCoord_mem_of_metricInner_lt (I := I) g p hV₂
  let V : Set M := V₁ ∩ V₃
  have hV : V ∈ 𝓝 p := Filter.inter_mem hV₁ hV₃
  refine ⟨δ, hδ, V, hV, V₂, hV₂, ρ, hρ, c, ?_, ?_⟩
  · intro q hq v hv
    let w : E := Geodesic.chartFiberCoord (E := E) (I := I) p
      (⟨q, v⟩ : TangentBundle I M)
    have hw : w ∈ V₂ := hcoord q hq.2 v hv
    have hmain := hc q hq.1 w hw
    have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [w] using hmain.1
    · simpa [w] using hmain.2.1
    · simpa [w] using hmain.2.2
    · intro γ hγ hγ0 hγv
      have hvel :
          deriv (fun s => extChartAt I p (c q w s)) 0 =
            deriv (fun s => extChartAt I p (γ s)) 0 :=
        (hmain.2.2).deriv.trans hγv.deriv.symm
      have hpos : c q w 0 = γ 0 := hmain.2.1.trans hγ0.symm
      have heq := geodesic_local_uniqueness (I := I) g p
        isOpen_Ioo ordConnected_Ioo isOpen_Ioo ordConnected_Ioo
        hmain.1 hγ ⟨h0, h0⟩ hpos hvel
      intro t ht
      exact (heq ⟨ht, ht⟩).symm
  · apply hcsmooth.mono
    exact Set.prod_mono
      (Set.prod_mono (Set.image_mono inter_subset_left) subset_rfl)
      subset_rfl

/-- **Math.** **do Carmo Ch. 3, Proposition 2.7 (uniform interval of definition).**
Near every point `p`, all initial tangent vectors in one fixed positive Riemannian metric ball
generate geodesics on `(-2, 2)`.  The family is jointly smooth in the base point, chart-fiber
velocity, and time.  Each member has the prescribed intrinsic initial data and is unique among
continuous intrinsic geodesics on that interval with the same data.

The fixed time window comes from `geodesic_local_existence_fixedInterval`; the uniform metric
ball is inserted into its model-fiber neighborhood by
`exists_chartFiberCoord_mem_of_metricInner_lt`. -/
theorem geodesic_local_existence_fixedInterval_metricBall
    (g : RiemannianMetric I M) [I.Boundaryless] [CompleteSpace E]
    [T2Space M] [T2Space (TangentBundle I M)] (p : M) :
    ∃ V ∈ 𝓝 p, ∃ ε > 0, ∃ W ∈ 𝓝 (0 : E), ∃ c : M → E → ℝ → M,
      (∀ q ∈ V, ∀ v : TangentSpace I q,
        g.metricInner q v v < ε ^ 2 →
          let w := Geodesic.chartFiberCoord (E := E) (I := I) p
            (⟨q, v⟩ : TangentBundle I M)
          w ∈ W ∧
          Geodesic.IsGeodesicCurveOn (I := I) g (c q w) (Ioo (-2) 2) ∧
          c q w 0 = q ∧
          HasDerivAt (fun s => extChartAt I p (c q w s)) w 0 ∧
          ∀ γ : ℝ → M,
            Geodesic.IsGeodesicCurveOn (I := I) g γ (Ioo (-2) 2) →
            γ 0 = q →
            HasDerivAt (fun s => extChartAt I p (γ s)) w 0 →
            Set.EqOn γ (c q w) (Ioo (-2) 2)) ∧
      ContDiffOn ℝ ∞
        (fun xwt : (E × E) × ℝ =>
          extChartAt I p
            (c ((extChartAt I p).symm xwt.1.1) xwt.1.2 xwt.2))
        (((extChartAt I p '' V) ×ˢ W) ×ˢ Ioo (-2) 2) := by
  obtain ⟨V₁, hV₁, W, hW, c, hc, hcsmooth⟩ :=
    geodesic_local_existence_fixedInterval (I := I) g p
  obtain ⟨V₂, hV₂, ρ, hρ, hcoord⟩ :=
    exists_chartFiberCoord_mem_of_metricInner_lt (I := I) g p hW
  let V : Set M := V₁ ∩ V₂
  have hV : V ∈ 𝓝 p := Filter.inter_mem hV₁ hV₂
  let ε : ℝ := Real.sqrt ρ
  have hε : 0 < ε := Real.sqrt_pos.2 hρ
  have hεsq : ε ^ 2 = ρ := by
    simpa [ε] using Real.sq_sqrt hρ.le
  refine ⟨V, hV, ε, hε, W, hW, c, ?_, ?_⟩
  · intro q hq v hv
    let w : E := Geodesic.chartFiberCoord (E := E) (I := I) p
      (⟨q, v⟩ : TangentBundle I M)
    have hw : w ∈ W := hcoord q hq.2 v (by
      rw [← hεsq]
      exact hv)
    have hmain := hc q hq.1 w hw
    have hcurve : Geodesic.IsGeodesicCurveOn (I := I) g (c q w) (Ioo (-2) 2) :=
      hmain.1.isGeodesicCurveOn isOpen_Ioo
    refine ⟨hw, hcurve, hmain.2.1, hmain.2.2, ?_⟩
    intro γ hγ hγ0 hγv
    have h0 : (0 : ℝ) ∈ Ioo (-2) 2 := by norm_num
    have heq0 : γ 0 = c q w 0 := hγ0.trans hmain.2.1.symm
    have hβ : γ 0 ∈ (chartAt H p).source := by
      rw [hγ0, ← hmain.2.1]
      exact hmain.1.1 0 h0
    have hvγ : deriv (Geodesic.chartReading (I := I) p γ) 0 = w := by
      change deriv (fun s => extChartAt I p (γ s)) 0 = w
      exact hγv.deriv
    have hvc : deriv (Geodesic.chartReading (I := I) p (c q w)) 0 = w := by
      change deriv (fun s => extChartAt I p (c q w s)) 0 = w
      exact hmain.2.2.deriv
    exact Geodesic.IsGeodesicOn.eqOn_of_deriv_chartReading_eq
      isOpen_Ioo isPreconnected_Ioo hγ.2 hcurve.2 hγ.1 hcurve.1 h0 heq0 hβ
      (hvγ.trans hvc.symm)
  · apply hcsmooth.mono
    exact Set.prod_mono
      (Set.prod_mono (Set.image_mono inter_subset_left) subset_rfl)
      subset_rfl

end GeodesicLocal
end Riemannian
