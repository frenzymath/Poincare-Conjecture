import OpenGALib.Riemannian.Geodesic.EquationTransfer
import OpenGALib.Riemannian.Geodesic.HopfRinow.ConstantSpeed
import OpenGALib.Riemannian.Exponential.GaussLemma

set_option linter.unusedSectionVars false

/-!
# Local comparison of coordinate and Riemannian norms

Near a point `p₀ : M`, the chart-Gram inner product `chartMetricInner g p₀`
dominates a positive multiple of the coordinate norm: there are `c > 0` and a
neighbourhood `V` of the chart image of `p₀` with

`‖w‖² ≤ c · ⟨w, w⟩_{G(y)}` for all `y ∈ V`, `w : E`.

This is the finite-dimensional lower-semicontinuity of a positive-definite
quadratic form: at `y₀ = φ(p₀)` the Gram form is the intrinsic inner product
`g.metricInner p₀` (readbacks are the identity over the pole,
`trivializationAt_symm_self`), hence positive definite (`g.pos`); the form is
continuous in `(y, w)` (`chartGramOnE_contDiffOn`), so positivity on the
compact unit sphere at `y₀` spreads to a neighbourhood by the tube lemma.

We also record the pole-generalised bridge from the intrinsic squared speed
to the chart-Gram reading (`HasGeodesicEquationAt.speedSq_eq_chartMetricInner`
of `ConstantSpeed.lean` is anchored at a foot of the curve; here the chart
basepoint is arbitrary).

Together these convert the conserved intrinsic speed of a geodesic into a
uniform bound on its coordinate velocity near `p₀` — the estimate that puts
the endpoint data of a Cauchy geodesic inside the uniform-flow ball of
`exists_uniform_geodesic_flow` (do Carmo Ch. 7, Theorem 2.8, c) ⟹ d)).
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** **Local coordinate-norm bound by the chart-Gram form.** Near the
chart image of `p₀`, the positive-definite Gram form dominates a fixed
positive multiple of the squared coordinate norm. -/
theorem exists_sq_norm_le_chartMetricInner (g : RiemannianMetric I M) (p₀ : M) :
    ∃ (c : ℝ) (V : Set E), 0 < c ∧ V ∈ 𝓝 (extChartAt I p₀ p₀) ∧
      V ⊆ (extChartAt I p₀).target ∧
      ∀ y ∈ V, ∀ w : E, ‖w‖ ^ 2 ≤ c * chartMetricInner (I := I) g p₀ y w w := by
  classical
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  set y₀ : E := extChartAt I p₀ p₀ with hy₀_def
  have hy₀ : y₀ ∈ (extChartAt I p₀).target := mem_extChartAt_target p₀
  have htgt_open : IsOpen (extChartAt I p₀).target := isOpen_extChartAt_target p₀
  -- At the pole, the Gram form is the intrinsic inner product, hence positive definite.
  have hpole : ∀ w : E, chartMetricInner (I := I) g p₀ y₀ w w = g.metricInner p₀ w w := by
    intro w
    rw [hy₀_def]
    have hb := chartMetricInner_extChartAt_eq_metricInner (I := I) g p₀
      (mem_chart_source H p₀) w w
    rwa [trivializationAt_symm_self (I := I) p₀ w] at hb
  have hpos : ∀ w : E, w ≠ 0 → 0 < chartMetricInner (I := I) g p₀ y₀ w w := by
    intro w hw
    rw [hpole w]
    exact g.metricInner_self_pos p₀ w hw
  -- Joint continuity of the Gram quadratic form on `target ×ˢ univ`.
  have hQ : ContinuousOn (fun z : E × E => chartMetricInner (I := I) g p₀ z.1 z.2 z.2)
      ((extChartAt I p₀).target ×ˢ (univ : Set E)) := by
    have hfun : (fun z : E × E => chartMetricInner (I := I) g p₀ z.1 z.2 z.2)
        = fun z : E × E => ∑ i, ∑ j, chartGramOnE (I := I) g p₀ i j z.1
            * Geodesic.chartCoord (E := E) i z.2 * Geodesic.chartCoord (E := E) j z.2 := by
      funext z
      simp only [chartMetricInner_def]
    rw [hfun]
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    have hG : ContinuousOn (fun z : E × E => chartGramOnE (I := I) g p₀ i j z.1)
        ((extChartAt I p₀).target ×ˢ (univ : Set E)) :=
      (chartGramOnE_contDiffOn (I := I) g p₀ i j).continuousOn.comp
        continuous_fst.continuousOn fun _ hz => hz.1
    have hci : Continuous fun z : E × E => Geodesic.chartCoord (E := E) i z.2 := by
      have h : Continuous fun z : E × E => Geodesic.chartCoordFunctional (E := E) i z.2 :=
        (Geodesic.chartCoordFunctional (E := E) i).continuous.comp continuous_snd
      simpa only [Geodesic.chartCoordFunctional_apply] using h
    have hcj : Continuous fun z : E × E => Geodesic.chartCoord (E := E) j z.2 := by
      have h : Continuous fun z : E × E => Geodesic.chartCoordFunctional (E := E) j z.2 :=
        (Geodesic.chartCoordFunctional (E := E) j).continuous.comp continuous_snd
      simpa only [Geodesic.chartCoordFunctional_apply] using h
    exact (hG.mul hci.continuousOn).mul hcj.continuousOn
  -- The pole form attains a positive minimum `m` on the compact unit sphere.
  have hScpt : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hSne : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hcont₀ : Continuous fun w : E => chartMetricInner (I := I) g p₀ y₀ w w := by
    have hfun : (fun w : E => chartMetricInner (I := I) g p₀ y₀ w w)
        = fun w : E => ∑ i, ∑ j, chartGramOnE (I := I) g p₀ i j y₀
            * Geodesic.chartCoord (E := E) i w * Geodesic.chartCoord (E := E) j w := by
      funext w
      simp only [chartMetricInner_def]
    rw [hfun]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    have hci : Continuous fun w : E => Geodesic.chartCoord (E := E) i w := by
      have h : Continuous fun w : E => Geodesic.chartCoordFunctional (E := E) i w :=
        (Geodesic.chartCoordFunctional (E := E) i).continuous
      simpa only [Geodesic.chartCoordFunctional_apply] using h
    have hcj : Continuous fun w : E => Geodesic.chartCoord (E := E) j w := by
      have h : Continuous fun w : E => Geodesic.chartCoordFunctional (E := E) j w :=
        (Geodesic.chartCoordFunctional (E := E) j).continuous
      simpa only [Geodesic.chartCoordFunctional_apply] using h
    exact (continuous_const.mul hci).mul hcj
  obtain ⟨w₀, hw₀S, hw₀min⟩ := hScpt.exists_isMinOn hSne hcont₀.continuousOn
  set m : ℝ := chartMetricInner (I := I) g p₀ y₀ w₀ w₀ with hm_def
  have hw₀ne : w₀ ≠ 0 := by
    intro h
    rw [mem_sphere_iff_norm, sub_zero, h, norm_zero] at hw₀S
    norm_num at hw₀S
  have hm : 0 < m := hpos w₀ hw₀ne
  -- Spread the sphere bound `m/2 < Q` to a product neighbourhood via the tube lemma.
  have hUopen : IsOpen (((extChartAt I p₀).target ×ˢ (univ : Set E)) ∩
      (fun z : E × E => chartMetricInner (I := I) g p₀ z.1 z.2 z.2) ⁻¹' Ioi (m / 2)) :=
    hQ.isOpen_inter_preimage (htgt_open.prod isOpen_univ) isOpen_Ioi
  have hsub : ({y₀} : Set E) ×ˢ Metric.sphere (0 : E) 1 ⊆
      ((extChartAt I p₀).target ×ˢ (univ : Set E)) ∩
        (fun z : E × E => chartMetricInner (I := I) g p₀ z.1 z.2 z.2) ⁻¹' Ioi (m / 2) := by
    rintro ⟨y, w⟩ ⟨hy, hwS⟩
    rw [mem_singleton_iff] at hy
    subst hy
    refine ⟨⟨hy₀, mem_univ _⟩, ?_⟩
    have hwne : w ≠ 0 := by
      intro h
      rw [mem_sphere_iff_norm, sub_zero, h, norm_zero] at hwS
      norm_num at hwS
    have hmin : m ≤ chartMetricInner (I := I) g p₀ y₀ w w := hw₀min hwS
    have : m / 2 < chartMetricInner (I := I) g p₀ y₀ w w := by linarith
    exact this
  obtain ⟨u, v, huo, hvo, hyu, hSv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hScpt hUopen hsub
  refine ⟨2 / m, u ∩ (extChartAt I p₀).target, div_pos two_pos hm,
    Filter.inter_mem (huo.mem_nhds (hyu (mem_singleton y₀))) (htgt_open.mem_nhds hy₀),
    inter_subset_right, ?_⟩
  intro y hy w
  rcases eq_or_ne w 0 with rfl | hw
  · rw [chartMetricInner_zero_left (I := I)]
    simp
  -- Normalise `w` onto the sphere and scale the bound back up.
  have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hnwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hŵS : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw]
  have hmem : ((y, ‖w‖⁻¹ • w) : E × E) ∈ u ×ˢ v := ⟨hy.1, hSv hŵS⟩
  have hgt : m / 2 < chartMetricInner (I := I) g p₀ y (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) :=
    (huv hmem).2
  have hexp : chartMetricInner (I := I) g p₀ y (‖w‖⁻¹ • w) (‖w‖⁻¹ • w)
      = ‖w‖⁻¹ * (‖w‖⁻¹ * chartMetricInner (I := I) g p₀ y w w) := by
    rw [chartMetricInner_smul_left, chartMetricInner_smul_right]
  rw [hexp] at hgt
  have hkey : ‖w‖ ^ 2 * (m / 2) < chartMetricInner (I := I) g p₀ y w w := by
    have h2 := mul_lt_mul_of_pos_left hgt (pow_pos hnwpos 2)
    calc ‖w‖ ^ 2 * (m / 2)
        < ‖w‖ ^ 2 * (‖w‖⁻¹ * (‖w‖⁻¹ * chartMetricInner (I := I) g p₀ y w w)) := h2
      _ = (‖w‖ * ‖w‖⁻¹) * ((‖w‖ * ‖w‖⁻¹) * chartMetricInner (I := I) g p₀ y w w) := by
          ring
      _ = chartMetricInner (I := I) g p₀ y w w := by
          rw [mul_inv_cancel₀ hnw, one_mul, one_mul]
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  linarith [hkey]

/-- **Math.** Pole-generalised speed bridge: the intrinsic squared speed of a
geodesic at a time `σ` equals the chart-Gram reading in the chart at *any*
basepoint `β` whose source contains the foot `γ σ`. (The `ConstantSpeed.lean`
version `HasGeodesicEquationAt.speedSq_eq_chartMetricInner` requires the
basepoint to be a point `γ t` of the curve; the proof is identical.) -/
theorem HasGeodesicEquationAt.speedSq_eq_chartMetricInner_of_mem_source
    {g : RiemannianMetric I M} {γ : ℝ → M} {σ : ℝ}
    (h : HasGeodesicEquationAt (I := I) g γ σ) (hcont : ContinuousAt γ σ)
    {β : M} (hsrc : γ σ ∈ (chartAt H β).source) :
    speedSq (I := I) g γ σ = chartMetricInner (I := I) g β
      (chartReading (I := I) β γ σ)
      (deriv (chartReading (I := I) β γ) σ)
      (deriv (chartReading (I := I) β γ) σ) := by
  have hder : deriv (chartReading (I := I) β γ) σ
      = tangentCoordChange I (γ σ) β (γ σ)
          (deriv (chartLocalCurve (I := I) γ σ) σ) :=
    h.deriv_extChartAt_eq hcont hsrc
  have hbridge := chartMetricInner_extChartAt_eq_metricInner (I := I) g β hsrc
    (deriv (chartReading (I := I) β γ) σ) (deriv (chartReading (I := I) β γ) σ)
  have hread : (trivializationAt E (TangentSpace I) β).symm (γ σ)
      (deriv (chartReading (I := I) β γ) σ)
      = deriv (chartLocalCurve (I := I) γ σ) σ := by
    rw [trivializationAt_symm_eq_tangentCoordChange (I := I) β hsrc, hder,
      tangentCoordChange_comp (I := I)
        ⟨⟨mem_extChartAt_source (γ σ), by rw [extChartAt_source]; exact hsrc⟩,
          mem_extChartAt_source (γ σ)⟩,
      tangentCoordChange_self (I := I) (mem_extChartAt_source (γ σ))]
  show g.metricInner (γ σ) (mfderiv 𝓘(ℝ, ℝ) I γ σ 1) (mfderiv 𝓘(ℝ, ℝ) I γ σ 1) = _
  rw [h.mfderiv_apply_one hcont]
  show _ = chartMetricInner (I := I) g β (extChartAt I β (γ σ))
    (deriv (chartReading (I := I) β γ) σ) (deriv (chartReading (I := I) β γ) σ)
  rw [hbridge, hread]

end Geodesic
end Riemannian

end
