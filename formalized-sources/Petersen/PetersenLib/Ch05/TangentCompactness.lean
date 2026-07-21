import PetersenLib.Ch05.ChartTransition

/-!
# Petersen Ch. 5, §5.2 — compactness of bounded-velocity sets in `TM`

For a compact set `K ⊆ M` and a level `c`, the set of tangent vectors based in
`K` of squared metric length at most `c`,
`{x ∈ TM | x.proj ∈ K, g(ẋ, ẋ) ≤ c}`, is compact
(`isCompact_tangentSublevel`).  This is the compactness input to Petersen's
§5.2 extendability arguments (`prop:pet-ch5-leaves-compact-set`,
Cor. 5.2.5): by constancy of speed, the velocity curve of a geodesic
returning to a compact set lives in such a set.

The proof is chart-by-chart.  Over a compact set `C` inside a single chart
source, the chart Gram pairing admits a uniform positive lower eigenvalue
bound `λ` (`exists_forall_le_chartMetricInner`: minimise the continuous Gram
pairing over the compact set `φ_α(C) × S^{n-1}`), so `g(ẋ, ẋ) ≤ c` pins the
trivialization fibre coordinate into the closed ball of radius `√(c/λ)`; the
bounded-velocity set over `C` is then the homeomorphic image under the
inverse trivialization of a closed subset of `C × closedBall`
(`isCompact_tangentSublevel_of_isCompact_subset_chartSource`).  Finitely many
such chart pieces cover a compact base (local compactness of `M`).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The chart Gram pairing scales quadratically:
`⟨r·a, r·b⟩_α^y = r² ⟨a, b⟩_α^y`. -/
theorem chartMetricInner_smul_smul (g : RiemannianMetric I M) (α : M) (y : E)
    (r : ℝ) (a b : E) :
    chartMetricInner (I := I) g α y (r • a) (r • b)
      = r ^ 2 * chartMetricInner (I := I) g α y a b := by
  simp only [chartMetricInner_def, Geodesic.chartCoord_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Math.** The intrinsic squared metric length of a tangent vector based in
the chart source at `α` is the chart-`α` Gram pairing of its trivialization
fibre coordinate: `g_x(ẋ, ẋ) = ⟨u, u⟩_α^{φ_α(x)}` for `u` the chart-`α` fibre
coordinate of `ẋ`. -/
theorem inner_self_eq_chartMetricInner_trivializationAt (g : RiemannianMetric I M)
    {α : M} {x : TangentBundle I M} (hx : x.proj ∈ (chartAt H α).source) :
    g.inner x.proj x.2 x.2
      = chartMetricInner (I := I) g α (extChartAt I α x.proj)
          ((trivializationAt E (TangentSpace I) α x).2)
          ((trivializationAt E (TangentSpace I) α x).2) := by
  obtain ⟨q, w⟩ := x
  have hq : q ∈ (extChartAt I α).source := by rwa [extChartAt_source I]
  have hq' : q ∈ (extChartAt I q).source := mem_extChartAt_source (I := I) q
  have hfib : (trivializationAt E (TangentSpace I) α ⟨q, w⟩).2
      = tangentCoordChange I q α q w := rfl
  rw [hfib, chartMetricInner_eq_inner (I := I) g hq,
    tangentCoordChange_comp (I := I) ⟨⟨hq', hq⟩, hq'⟩,
    tangentCoordChange_self (I := I) hq']

/-- **Math.** Joint continuity of the diagonal chart Gram pairing
`(y, u) ↦ ⟨u, u⟩_α^y` on `target × E`. -/
theorem continuousOn_chartMetricInner_diag (g : RiemannianMetric I M) (α : M) :
    ContinuousOn (fun q : E × E => chartMetricInner (I := I) g α q.1 q.2 q.2)
      ((extChartAt I α).target ×ˢ (univ : Set E)) := by
  have hcoord : ∀ i, Continuous fun q : E × E => Geodesic.chartCoord (E := E) i q.2 := by
    intro i
    have h := (Geodesic.chartCoordFunctional (E := E) i).continuous.comp
      (continuous_snd : Continuous fun q : E × E => q.2)
    simpa only [Function.comp_def, Geodesic.chartCoordFunctional_apply] using h
  simp only [chartMetricInner_def]
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
  refine ContinuousOn.mul (ContinuousOn.mul ?_ (hcoord i).continuousOn)
    (hcoord j).continuousOn
  exact (chartGramOnE_contDiffOn (I := I) g α i j).continuousOn.comp
    continuous_fst.continuousOn fun q hq => hq.1

/-- **Math.** **Uniform Gram eigenvalue lower bound on a compact set**: over a
compact set `C` inside a single chart source, the chart Gram pairing dominates
a positive multiple of the coordinate norm, `⟨u, u⟩_α^{φ_α q} ≥ λ ‖u‖²` for
all `q ∈ C`.  (Minimise the continuous pairing over `φ_α(C) × S^{n-1}`;
positive definiteness of `g` makes the minimum positive.) -/
theorem exists_forall_le_chartMetricInner (g : RiemannianMetric I M)
    {α : M} {C : Set M} (hC : IsCompact C) (hCsub : C ⊆ (chartAt H α).source) :
    ∃ lam > (0 : ℝ), ∀ q ∈ C, ∀ u : E,
      lam * ‖u‖ ^ 2 ≤ chartMetricInner (I := I) g α (extChartAt I α q) u u := by
  classical
  haveI hnontriv : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact ⟨1, one_pos, by simp⟩
  have hCsub' : C ⊆ (extChartAt I α).source := by rwa [extChartAt_source I]
  set T : Set (E × E) := ((extChartAt I α) '' C) ×ˢ Metric.sphere (0 : E) 1 with hT_def
  have hTcomp : IsCompact T :=
    (hC.image_of_continuousOn ((continuousOn_extChartAt α).mono hCsub')).prod
      (isCompact_sphere 0 1)
  have hTne : T.Nonempty :=
    (hCne.image _).prod (NormedSpace.sphere_nonempty.mpr zero_le_one)
  have hTsub : T ⊆ (extChartAt I α).target ×ˢ (univ : Set E) :=
    Set.prod_mono ((Set.image_mono hCsub').trans
      (extChartAt I α).image_source_eq_target.subset) (subset_univ _)
  obtain ⟨⟨y₀, u₀⟩, hmem, hmin⟩ := hTcomp.exists_isMinOn hTne
    ((continuousOn_chartMetricInner_diag (I := I) g α).mono hTsub)
  obtain ⟨⟨q₀, hq₀C, rfl⟩, hu₀⟩ := hmem
  have hq₀src : q₀ ∈ (extChartAt I α).source := hCsub' hq₀C
  have hu₀ne : u₀ ≠ 0 := by
    intro h
    rw [h] at hu₀
    simp at hu₀
  have hDne : tangentCoordChange I α q₀ q₀ u₀ ≠ 0 := by
    intro h
    have hq₀' : q₀ ∈ (extChartAt I q₀).source := mem_extChartAt_source (I := I) q₀
    have hcongr := congrArg (tangentCoordChange I q₀ α q₀) h
    rw [tangentCoordChange_comp (I := I) ⟨⟨hq₀src, hq₀'⟩, hq₀src⟩,
      tangentCoordChange_self (I := I) hq₀src, map_zero] at hcongr
    exact hu₀ne hcongr
  set lam : ℝ := chartMetricInner (I := I) g α (extChartAt I α q₀) u₀ u₀ with hlam_def
  have hlam_pos : 0 < lam := by
    rw [hlam_def, chartMetricInner_eq_inner (I := I) g hq₀src]
    exact g.metricInner_self_pos q₀ _ hDne
  refine ⟨lam, hlam_pos, fun q hq u => ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp [chartMetricInner_def, Geodesic.chartCoord_zero]
  · have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    set w : E := ‖u‖⁻¹ • u with hw_def
    have hw_sphere : w ∈ Metric.sphere (0 : E) 1 := by
      simp only [hw_def, mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ hnorm
    have himg : extChartAt I α q ∈ (extChartAt I α) '' C :=
      Set.mem_image_of_mem _ hq
    have hmemT : ((extChartAt I α q, w) : E × E) ∈ T := ⟨himg, hw_sphere⟩
    have hmin'' := hmin hmemT
    have hmin' : lam ≤ chartMetricInner (I := I) g α (extChartAt I α q) w w :=
      hmin''
    have hu_eq : u = ‖u‖ • w := by
      rw [hw_def, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
    have hscale : chartMetricInner (I := I) g α (extChartAt I α q) u u
        = ‖u‖ ^ 2 * chartMetricInner (I := I) g α (extChartAt I α q) w w := by
      conv_lhs => rw [hu_eq]
      rw [chartMetricInner_smul_smul]
    rw [hscale, mul_comm lam (‖u‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left hmin' (sq_nonneg _)

/-- **Math.** **Uniform Gram eigenvalue upper bound on a compact set**: over a
compact set `C` inside a single chart source, the chart Gram pairing is
dominated by a positive multiple of the coordinate norm,
`⟨u, u⟩_α^{φ_α q} ≤ μ ‖u‖²` for all `q ∈ C`.  (Maximise the continuous pairing
over `φ_α(C) × S^{n-1}`.)  Together with the lower bound
`exists_forall_le_chartMetricInner` this is the two-sided comparison
`λ ‖·‖² ≤ g ≤ μ ‖·‖²` between the metric and the flat chart norm on a compact
set, Petersen's `λ(x)|v|_{g_0} ≤ |v|_g ≤ μ(x)|v|_{g_0}` in the proof of
Thm. 5.3.8 (`thm:pet-ch5-metric-topology`). -/
theorem exists_forall_chartMetricInner_le (g : RiemannianMetric I M)
    {α : M} {C : Set M} (hC : IsCompact C) (hCsub : C ⊆ (chartAt H α).source) :
    ∃ mu > (0 : ℝ), ∀ q ∈ C, ∀ u : E,
      chartMetricInner (I := I) g α (extChartAt I α q) u u ≤ mu * ‖u‖ ^ 2 := by
  classical
  haveI hnontriv : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact ⟨1, one_pos, by simp⟩
  have hCsub' : C ⊆ (extChartAt I α).source := by rwa [extChartAt_source I]
  set T : Set (E × E) := ((extChartAt I α) '' C) ×ˢ Metric.sphere (0 : E) 1 with hT_def
  have hTcomp : IsCompact T :=
    (hC.image_of_continuousOn ((continuousOn_extChartAt α).mono hCsub')).prod
      (isCompact_sphere 0 1)
  have hTne : T.Nonempty :=
    (hCne.image _).prod (NormedSpace.sphere_nonempty.mpr zero_le_one)
  have hTsub : T ⊆ (extChartAt I α).target ×ˢ (univ : Set E) :=
    Set.prod_mono ((Set.image_mono hCsub').trans
      (extChartAt I α).image_source_eq_target.subset) (subset_univ _)
  obtain ⟨⟨y₀, u₀⟩, hmem, hmax⟩ := hTcomp.exists_isMaxOn hTne
    ((continuousOn_chartMetricInner_diag (I := I) g α).mono hTsub)
  obtain ⟨⟨q₀, hq₀C, rfl⟩, hu₀⟩ := hmem
  have hq₀src : q₀ ∈ (extChartAt I α).source := hCsub' hq₀C
  have hu₀ne : u₀ ≠ 0 := by
    intro h
    rw [h] at hu₀
    simp at hu₀
  have hDne : tangentCoordChange I α q₀ q₀ u₀ ≠ 0 := by
    intro h
    have hq₀' : q₀ ∈ (extChartAt I q₀).source := mem_extChartAt_source (I := I) q₀
    have hcongr := congrArg (tangentCoordChange I q₀ α q₀) h
    rw [tangentCoordChange_comp (I := I) ⟨⟨hq₀src, hq₀'⟩, hq₀src⟩,
      tangentCoordChange_self (I := I) hq₀src, map_zero] at hcongr
    exact hu₀ne hcongr
  set mu : ℝ := chartMetricInner (I := I) g α (extChartAt I α q₀) u₀ u₀ with hmu_def
  have hmu_pos : 0 < mu := by
    rw [hmu_def, chartMetricInner_eq_inner (I := I) g hq₀src]
    exact g.metricInner_self_pos q₀ _ hDne
  refine ⟨mu, hmu_pos, fun q hq u => ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp [chartMetricInner_def, Geodesic.chartCoord_zero]
  · have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    set w : E := ‖u‖⁻¹ • u with hw_def
    have hw_sphere : w ∈ Metric.sphere (0 : E) 1 := by
      simp only [hw_def, mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ hnorm
    have himg : extChartAt I α q ∈ (extChartAt I α) '' C :=
      Set.mem_image_of_mem _ hq
    have hmemT : ((extChartAt I α q, w) : E × E) ∈ T := ⟨himg, hw_sphere⟩
    have hmax'' := hmax hmemT
    have hmax' : chartMetricInner (I := I) g α (extChartAt I α q) w w ≤ mu :=
      hmax''
    have hu_eq : u = ‖u‖ • w := by
      rw [hw_def, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
    have hscale : chartMetricInner (I := I) g α (extChartAt I α q) u u
        = ‖u‖ ^ 2 * chartMetricInner (I := I) g α (extChartAt I α q) w w := by
      conv_lhs => rw [hu_eq]
      rw [chartMetricInner_smul_smul]
    rw [hscale, mul_comm mu (‖u‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left hmax' (sq_nonneg _)

/-- **Math.** **Chart-local compactness of bounded-velocity sets**: for a
compact set `C` inside a single chart source and any level `c`, the set of
tangent vectors based in `C` of squared metric length at most `c` is compact —
it is the image under the (continuous) inverse tangent-bundle trivialization
of a closed subset of `C × closedBall(0, √(c/λ))`, with `λ` the uniform Gram
lower bound of `exists_forall_le_chartMetricInner`. -/
theorem isCompact_tangentSublevel_of_isCompact_subset_chartSource
    (g : RiemannianMetric I M) [T2Space M] {α : M} {C : Set M}
    (hC : IsCompact C) (hCsub : C ⊆ (chartAt H α).source) (c : ℝ) :
    IsCompact {x : TangentBundle I M | x.proj ∈ C ∧ g.inner x.proj x.2 x.2 ≤ c} := by
  classical
  obtain ⟨lam, hlam, hbound⟩ := exists_forall_le_chartMetricInner (I := I) g hC hCsub
  set R : ℝ := Real.sqrt (max c 0 / lam) with hR_def
  set e := trivializationAt E (TangentSpace I) α with he_def
  have hbase : e.baseSet = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet α
  set F : M × E → ℝ :=
    fun q => chartMetricInner (I := I) g α (extChartAt I α q.1) q.2 q.2 with hF_def
  have hFcont : ContinuousOn F ((extChartAt I α).source ×ˢ (univ : Set E)) := by
    have hφ : ContinuousOn (fun q : M × E => (extChartAt I α q.1, q.2))
        ((extChartAt I α).source ×ˢ (univ : Set E)) :=
      ((continuousOn_extChartAt α).comp continuous_fst.continuousOn
        fun q hq => hq.1).prodMk continuous_snd.continuousOn
    have hmaps : Set.MapsTo (fun q : M × E => (extChartAt I α q.1, q.2))
        ((extChartAt I α).source ×ˢ (univ : Set E))
        ((extChartAt I α).target ×ˢ (univ : Set E)) := fun q hq =>
      ⟨(extChartAt I α).map_source hq.1, mem_univ _⟩
    simpa only [hF_def, Function.comp_def] using
      (continuousOn_chartMetricInner_diag (I := I) g α).comp hφ hmaps
  set D : Set (M × E) :=
    (C ×ˢ Metric.closedBall (0 : E) R) ∩ F ⁻¹' (Set.Iic c) with hD_def
  have hCsub' : C ⊆ (extChartAt I α).source := by rwa [extChartAt_source I]
  have hprodsub : C ×ˢ Metric.closedBall (0 : E) R
      ⊆ (extChartAt I α).source ×ˢ (univ : Set E) :=
    Set.prod_mono hCsub' (subset_univ _)
  have hCcball : IsCompact (C ×ˢ Metric.closedBall (0 : E) R) :=
    hC.prod (isCompact_closedBall _ _)
  have hD_closed : IsClosed D :=
    (hFcont.mono hprodsub).preimage_isClosed_of_isClosed
      (hC.isClosed.prod Metric.isClosed_closedBall) isClosed_Iic
  have hD_compact : IsCompact D :=
    hCcball.of_isClosed_subset hD_closed inter_subset_left
  -- the bounded-velocity set is the inverse-trivialization image of `D`
  have hkey : {x : TangentBundle I M | x.proj ∈ C ∧ g.inner x.proj x.2 x.2 ≤ c}
      = e.toOpenPartialHomeomorph.symm '' D := by
    ext x
    constructor
    · rintro ⟨hxC, hxg⟩
      have hxbase : x.proj ∈ e.baseSet := by rw [hbase]; exact hCsub hxC
      have hxsrc : x ∈ e.source := e.mem_source.mpr hxbase
      have hbridge : g.inner x.proj x.2 x.2
          = chartMetricInner (I := I) g α (extChartAt I α x.proj) (e x).2 (e x).2 :=
        inner_self_eq_chartMetricInner_trivializationAt (I := I) g (hCsub hxC)
      have hfst : (e x).1 = x.proj := e.coe_fst' hxbase
      have hnormle : ‖(e x).2‖ ≤ R := by
        have hb := hbound x.proj hxC (e x).2
        rw [← hbridge] at hb
        have h1 : lam * ‖(e x).2‖ ^ 2 ≤ max c 0 := le_max_of_le_left (hb.trans hxg)
        have h2 : ‖(e x).2‖ ^ 2 ≤ max c 0 / lam := (le_div_iff₀' hlam).mpr h1
        rw [hR_def, show ‖(e x).2‖ = Real.sqrt (‖(e x).2‖ ^ 2) from
          (Real.sqrt_sq (norm_nonneg _)).symm]
        exact Real.sqrt_le_sqrt h2
      refine ⟨e x, ⟨?_, ?_⟩, e.symm_apply_apply hxsrc⟩
      · exact ⟨by rw [hfst]; exact hxC, Metric.mem_closedBall.mpr
          (by rw [dist_zero_right]; exact hnormle)⟩
      · show F (e x) ∈ Set.Iic c
        have hFval : F (e x) = g.inner x.proj x.2 x.2 := by
          simp only [hF_def]
          rw [hfst, ← hbridge]
        rw [Set.mem_Iic, hFval]
        exact hxg
    · rintro ⟨⟨q, u⟩, ⟨⟨hqC, -⟩, hFle⟩, rfl⟩
      have hqbase : q ∈ e.baseSet := by rw [hbase]; exact hCsub hqC
      have htarget : ((q, u) : M × E) ∈ e.target := by
        rw [e.target_eq]
        exact ⟨hqbase, mem_univ _⟩
      have hproj : (e.toOpenPartialHomeomorph.symm (q, u)).proj = q :=
        e.proj_symm_apply htarget
      have hre : e (e.toOpenPartialHomeomorph.symm (q, u)) = (q, u) :=
        e.apply_symm_apply htarget
      have hqC' : (e.toOpenPartialHomeomorph.symm (q, u)).proj ∈ C := by
        rw [hproj]; exact hqC
      refine ⟨hqC', ?_⟩
      have hbridge := inner_self_eq_chartMetricInner_trivializationAt (I := I) g
        (x := e.toOpenPartialHomeomorph.symm (q, u)) (hCsub hqC')
      have hsnd : (e (e.toOpenPartialHomeomorph.symm (q, u))).2 = u := by rw [hre]
      rw [hbridge, hsnd, hproj]
      have hFle' : F (q, u) ≤ c := hFle
      simpa only [hF_def] using hFle'
  rw [hkey]
  have hDsub : D ⊆ e.target := fun q hq => by
    rw [e.target_eq]
    exact ⟨by rw [hbase]; exact hCsub hq.1.1, mem_univ _⟩
  exact hD_compact.image_of_continuousOn
    (e.toOpenPartialHomeomorph.continuousOn_symm.mono hDsub)

/-- **Math.** Petersen Ch. 5, §5.2 (compactness input to
`prop:pet-ch5-leaves-compact-set`): **bounded-velocity sets over a compact
base are compact** — for `K ⊆ M` compact and any `c`, the set
`{x ∈ TM | x.proj ∈ K, g(ẋ, ẋ) ≤ c}` is compact.  Cover `K` by finitely many
compact chart pieces (local compactness) and apply the chart-local case. -/
theorem isCompact_tangentSublevel (g : RiemannianMetric I M) [T2Space M]
    {K : Set M} (hK : IsCompact K) (c : ℝ) :
    IsCompact {x : TangentBundle I M | x.proj ∈ K ∧ g.inner x.proj x.2 x.2 ≤ c} := by
  classical
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hnbhd : ∀ p : M, ∃ C : Set M,
      C ∈ 𝓝 p ∧ C ⊆ (chartAt H p).source ∧ IsCompact C := fun p =>
    local_compact_nhds ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
  choose Cp hCp_mem hCp_sub hCp_comp using hnbhd
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover Cp fun p _ => hCp_mem p
  have hunion : {x : TangentBundle I M | x.proj ∈ K ∧ g.inner x.proj x.2 x.2 ≤ c}
      = ⋃ p ∈ t, {x : TangentBundle I M |
          x.proj ∈ K ∩ Cp p ∧ g.inner x.proj x.2 x.2 ≤ c} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, exists_prop, mem_inter_iff]
    constructor
    · rintro ⟨hxK, hxg⟩
      obtain ⟨p, hpt, hxp⟩ := mem_iUnion₂.mp (hcover hxK)
      exact ⟨p, hpt, ⟨hxK, hxp⟩, hxg⟩
    · rintro ⟨p, hpt, ⟨hxK, -⟩, hxg⟩
      exact ⟨hxK, hxg⟩
  rw [hunion]
  refine t.finite_toSet.isCompact_biUnion fun p hpt => ?_
  exact isCompact_tangentSublevel_of_isCompact_subset_chartSource (I := I) g
    (hK.inter_right (hCp_comp p).isClosed)
    (inter_subset_right.trans (hCp_sub p)) c

end PetersenLib
