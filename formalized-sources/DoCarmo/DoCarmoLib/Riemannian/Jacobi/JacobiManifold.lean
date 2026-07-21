import DoCarmoLib.Riemannian.Jacobi.PairJacobiField
import DoCarmoLib.Riemannian.Jacobi.Geodesics
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.ConstantSpeed
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge

/-!
# Jacobi fields along a geodesic (manifold form) — split-ported core

Ported into DoCarmoLib from the Morgan–Tian / Poincaré Ch.1, §1.4 development
(toward `cor:dc-ch5-2-5`), keeping only the **definition + chart-reading +
Grönwall-uniqueness core** needed for the exp-differential ↔ Jacobi-field
bridge. The manifold *Sturm-comparison / conjugate-point* material of the
original (`IsConjugatePointAt`, `sqrt_metricInner_comparison`,
`ne_zero_of_sectionalCurvatureAt_le`, `not_isConjugatePointAt_of_sectionalCurvatureAt_le`
and their scalar-derivative helpers) is deliberately dropped here — it is not
used anywhere on the `cor:dc-ch5-2-5` critical path and pulls in the whole
Sturm/comparison cone.

Manifold-level Jacobi fields along a curve `γ : ℝ → M`, on top of the
chart-level Jacobi pair system (`Riemannian.Jacobi.IsJacobiFieldOn`,
`PairJacobiField`).

A tangent vector at `γ τ` is carried in the coordinates of the chart at its own
foot (`TangentSpace I (γ τ) = E`), so a *field along `γ`* is a plain map
`J : ℝ → E`. Its reading in the chart at a fixed basepoint `α` is
`chartVectorRep γ α J := τ ↦ tangentCoordChange I (γ τ) α (γ τ) (J τ)`.

* `IsJacobiFieldAlongOn g γ J DJ a b` — `(J, DJ)` is a Jacobi field along `γ`
  on `[a, b]`: near every time, in the chart at some basepoint containing the
  nearby piece of `γ`, the chart readings satisfy the chart Jacobi pair system
  `IsJacobiFieldOn`. Chart-local, so it survives geodesics leaving any chart.
* `IsJacobiFieldAlongOn.eqOn_zero` — a Jacobi field along a geodesic vanishing
  together with its covariant derivative at the left endpoint vanishes
  identically (chart-local Grönwall uniqueness, propagated by a connectedness
  walk).

Blueprint: `cor:dc-ch5-2-5`, `lem:jacobi-field-coordinates`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Chart readings of tangent vectors carried at their own foot -/

/-- **Math.** Reading back the chart-`α` coordinates of a tangent vector at
`x` through the fibre trivialization recovers the vector: the inverse
trivialization at `α` over `x` undoes the tangent coordinate change
`T_x M → E` into the chart at `α`. -/
theorem trivializationAt_symm_tangentCoordChange {α x : M}
    (hx : x ∈ (chartAt H α).source) (v : E) :
    (trivializationAt E (TangentSpace I) α).symm x
        (tangentCoordChange I x α x v) = v := by
  rw [trivializationAt_symm_eq_tangentCoordChange (I := I) α hx,
    tangentCoordChange_comp (I := I)
      ⟨⟨mem_extChartAt_source (I := I) x,
        by rw [extChartAt_source]; exact hx⟩, mem_extChartAt_source (I := I) x⟩,
    tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) x)]

/-- **Math.** The chart-`α` reading of a tangent vector at `x` vanishes iff
the vector does: the tangent coordinate change is a linear isomorphism. -/
theorem tangentCoordChange_eq_zero_iff {α x : M}
    (hx : x ∈ (chartAt H α).source) {v : E} :
    tangentCoordChange I x α x v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h2 := congrArg ((trivializationAt E (TangentSpace I) α).symm x) h
    rw [trivializationAt_symm_tangentCoordChange (I := I) hx,
      trivializationAt_symm_eq_tangentCoordChange (I := I) α hx] at h2
    simpa using h2
  · rintro rfl
    exact (tangentCoordChange I x α x).map_zero

/-- **Math.** The chart Gram pairing of the chart-`α` readings of two tangent
vectors at `x` is their intrinsic metric pairing: the chart-independence of
`⟨·, ·⟩_g` along a curve, pointwise form. -/
theorem chartMetricInner_tangentCoordChange (g : RiemannianMetric I M)
    {α x : M} (hx : x ∈ (chartAt H α).source) (v w : TangentSpace I x) :
    chartMetricInner (I := I) g α (extChartAt I α x)
        (tangentCoordChange I x α x v) (tangentCoordChange I x α x w)
      = g.metricInner x v w := by
  rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g α hx,
    trivializationAt_symm_tangentCoordChange (I := I) hx,
    trivializationAt_symm_tangentCoordChange (I := I) hx]

/-! ### Manifold-level Jacobi fields along a curve -/

/-- **Math.** The reading, in the chart at the fixed basepoint `α`, of a
field of tangent vectors along `γ` carried at their own feet: at time `τ`
the vector `J τ ∈ T_{γ τ} M` is pushed into the chart at `α` by the tangent
coordinate change. -/
def chartVectorRep (γ : ℝ → M) (α : M) (J : ℝ → E) : ℝ → E :=
  fun τ => tangentCoordChange I (γ τ) α (γ τ) (J τ)

@[simp] theorem chartVectorRep_apply (γ : ℝ → M) (α : M) (J : ℝ → E) (τ : ℝ) :
    chartVectorRep (I := I) γ α J τ
      = tangentCoordChange I (γ τ) α (γ τ) (J τ) := rfl

/-- **Math.** **Jacobi field along a curve, manifold form** (Morgan–Tian
§1.4). A pair of fields `J, DJ : ℝ → E` along `γ` (each `J τ` read as an
element of `T_{γ τ} M`) is a *Jacobi field with covariant derivative `DJ` on
`[a, b]`* if near every time `t₀ ∈ [a, b]` there are a chart basepoint `α`
and a subinterval `[a', b'] ∋ t₀`, a neighbourhood of `t₀` in `[a, b]` whose
`γ`-image lies in the chart at `α`, on which the chart readings of `(J, DJ)`
satisfy the chart Jacobi pair system `∇J = DJ`,
`∇DJ = −ℛ(J, u̇)u̇` (`IsJacobiFieldOn`). The notion is chart-local, so it is
meaningful for curves that leave any single chart.

Blueprint: `cor:dc-ch5-2-5`, `lem:jacobi-field-coordinates`. -/
def IsJacobiFieldAlongOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (J DJ : ℝ → E) (a b : ℝ) : Prop :=
  ∀ t₀ ∈ Icc a b, ∃ (α : M) (a' b' : ℝ), a' < b' ∧ t₀ ∈ Icc a' b' ∧
    Icc a' b' ⊆ Icc a b ∧ Icc a' b' ∈ 𝓝[Icc a b] t₀ ∧
    (∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H α).source) ∧
    IsJacobiFieldOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (chartVectorRep (I := I) γ α J) (chartVectorRep (I := I) γ α DJ) a' b'

/-! ### The fixed-chart geodesic package

Along a geodesic, in any chart whose source contains the relevant piece of
`γ`, the chart curve `u = φ_α ∘ γ` is `C¹` and its velocity has the intrinsic
squared speed as chart Gram norm — first-order chart-change transfer only,
no Christoffel transformation law. -/

section GeodesicPackage

variable [I.Boundaryless]

/-- **Math.** Along a geodesic, the fixed-chart curve `u = φ_α ∘ γ` is
(two-sidedly) differentiable at every time whose foot lies in the chart. -/
theorem IsGeodesicOn.differentiableAt_extChartAt {g : RiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} (hgeo : IsGeodesicOn (I := I) g γ s)
    {α : M} {τ : ℝ} (hτ : τ ∈ s) (hc : ContinuousAt γ τ)
    (hsrc : γ τ ∈ (chartAt H α).source) :
    DifferentiableAt ℝ (fun t => extChartAt I α (γ t)) τ :=
  (((hgeo τ hτ).eventually_hasDerivAt_extChartAt hc hsrc).self_of_nhds).differentiableAt

/-- **Math.** Along a geodesic, the fixed-chart velocity `u̇` is continuous
at every time whose foot lies in the chart. -/
theorem IsGeodesicOn.continuousAt_deriv_extChartAt {g : RiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} (hgeo : IsGeodesicOn (I := I) g γ s)
    {α : M} {τ : ℝ} (hτ : τ ∈ s) (hc : ContinuousAt γ τ)
    (hsrc : γ τ ∈ (chartAt H α).source) :
    ContinuousAt (deriv (fun t => extChartAt I α (γ t))) τ :=
  (hgeo τ hτ).continuousAt_deriv_extChartAt hc hsrc

/-- **Math.** The chart Gram norm of the fixed-chart velocity of a geodesic
is the intrinsic squared speed: `⟨u̇, u̇⟩_{G(u)} = |γ̇|²_g`, in any chart
containing the foot. -/
theorem chartMetricInner_deriv_extChartAt {g : RiemannianMetric I M}
    {γ : ℝ → M} {τ : ℝ}
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ τ)
    (hc : ContinuousAt γ τ) {α : M} (hsrc : γ τ ∈ (chartAt H α).source) :
    chartMetricInner (I := I) g α (extChartAt I α (γ τ))
        (deriv (fun t => extChartAt I α (γ t)) τ)
        (deriv (fun t => extChartAt I α (γ t)) τ)
      = Geodesic.speedSq (I := I) g γ τ := by
  rw [h.deriv_extChartAt_eq hc hsrc,
    chartMetricInner_tangentCoordChange (I := I) g hsrc,
    Geodesic.speedSq_def, h.mfderiv_apply_one hc]

/-- **Math.** Differentiability of the chart Gram coefficients at points of
the chart target. -/
theorem differentiableAt_chartGramOnE (g : RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y :=
  ((chartGramOnE_contDiffOn (I := I) g α i j).contDiffAt
    (extChartAt_target_mem_nhds' (I := I) hy)).differentiableAt (by norm_num)

end GeodesicPackage

/-! ### Chart-independent scalars along a Jacobi field

`F = ⟨J, J⟩`, `G = ⟨DJ, J⟩`, `Hh = ⟨DJ, DJ⟩` are intrinsic metric pairings;
in any chart containing the foot they are computed by the chart Gram pairing
of the chart readings. -/

section Scalars

variable [I.Boundaryless]

/-- **Math.** The intrinsic pairing `⟨V, W⟩_g` along `γ` equals the chart
Gram pairing of the chart readings, in any chart containing the foot. -/
theorem metricInner_eq_chartMetricInner_rep (g : RiemannianMetric I M)
    {γ : ℝ → M} {α : M} {τ : ℝ} (hsrc : γ τ ∈ (chartAt H α).source)
    (V W : ℝ → E) :
    g.metricInner (γ τ) (V τ : TangentSpace I (γ τ)) (W τ)
      = chartMetricInner (I := I) g α (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α V τ) (chartVectorRep (I := I) γ α W τ) :=
  (chartMetricInner_tangentCoordChange (I := I) g hsrc (V τ) (W τ)).symm

/-- **Math.** Continuity, within a chart interval, of the chart Gram pairing
of two continuous coordinate fields along a continuous chart curve. -/
theorem continuousOn_chartMetricInner_pairing (g : RiemannianMetric I M)
    (α : M) {u V W : ℝ → E} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b))
    (hmem : ∀ τ ∈ Icc a b, u τ ∈ (extChartAt I α).target)
    (hV : ContinuousOn V (Icc a b)) (hW : ContinuousOn W (Icc a b)) :
    ContinuousOn (fun τ => chartMetricInner (I := I) g α (u τ) (V τ) (W τ))
      (Icc a b) := by
  simp only [chartMetricInner_def]
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · intro τ hτ
    exact ((differentiableAt_chartGramOnE (I := I) g α (hmem τ hτ) i j).continuousAt.comp_continuousWithinAt
      (hu τ hτ))
  · exact ((Geodesic.chartCoordFunctional (E := E) i).continuous.comp_continuousOn hV).congr
      fun τ _ => rfl
  · exact ((Geodesic.chartCoordFunctional (E := E) j).continuous.comp_continuousOn hW).congr
      fun τ _ => rfl

/-- **Math.** At its own basepoint chart, the chart Gram pairing is the
intrinsic pairing on the nose. -/
theorem chartMetricInner_self_chart (g : RiemannianMetric I M) (x : M) (a c : E) :
    chartMetricInner (I := I) g x (extChartAt I x x) a c
      = g.metricInner x (a : TangentSpace I x) c := by
  rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g x (mem_chart_source H x),
    trivializationAt_symm_self, trivializationAt_symm_self]

/-- **Math.** The readback of the chart image of a foot in the chart source
lies in the trivialization base set. -/
theorem symm_extChartAt_mem_baseSet {α x : M} (hx : x ∈ (chartAt H α).source) :
    (extChartAt I α).symm (extChartAt I α x)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  rw [(extChartAt I α).left_inv (by rw [extChartAt_source]; exact hx)]
  exact hx

end Scalars

/-! ### Restriction of the chart Jacobi pair system -/

/-- **Math.** Restriction of the chart Jacobi pair system to a subinterval. -/
theorem _root_.Riemannian.Jacobi.IsJacobiFieldOn.mono
    {g : RiemannianMetric I M} {α : M} {u J DJ : ℝ → E} {a b a' b' : ℝ}
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    (ha : a ≤ a') (hb : b' ≤ b) :
    IsJacobiFieldOn (I := I) g α u J DJ a' b' where
  hasDerivWithinAt_fst := fun t ht =>
    (h.hasDerivWithinAt_fst t (Icc_subset_Icc ha hb ht)).mono (Icc_subset_Icc ha hb)
  hasDerivWithinAt_snd := fun t ht =>
    (h.hasDerivWithinAt_snd t (Icc_subset_Icc ha hb ht)).mono (Icc_subset_Icc ha hb)

/-! ### Grönwall uniqueness along the geodesic -/

section Main

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **Grönwall uniqueness along the geodesic**: a Jacobi field
along a geodesic vanishing together with its covariant derivative at the
left endpoint vanishes identically on the interval — chart-local uniqueness
of the Jacobi pair system, propagated by a connectedness walk (the set of
times up to which the pair vanishes is closed by continuity and open by
chart-local uniqueness). -/
theorem IsJacobiFieldAlongOn.eqOn_zero
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ}
    (hab : a ≤ b)
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hJa : J a = 0) (hDJa : DJ a = 0) :
    ∀ t ∈ Icc a b, J t = 0 ∧ DJ t = 0 := by
  classical
  -- the set of times up to which the pair vanishes
  set S : Set ℝ := {s | s ∈ Icc a b ∧ ∀ τ ∈ Icc a s, J τ = 0 ∧ DJ τ = 0} with hS
  have haS : a ∈ S := ⟨left_mem_Icc.2 hab, fun τ hτ => by
    obtain rfl : τ = a := le_antisymm hτ.2 hτ.1
    exact ⟨hJa, hDJa⟩⟩
  have hSb : ∀ s ∈ S, s ≤ b := fun s hs => hs.1.2
  have hbdd : BddAbove S := ⟨b, fun s hs => hSb s hs⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  set c := sSup S with hcdef
  have hac : a ≤ c := le_csSup hbdd haS
  have hcb : c ≤ b := csSup_le hSne hSb
  -- everything strictly below the supremum vanishes
  have hbelow : ∀ τ ∈ Ico a c, J τ = 0 ∧ DJ τ = 0 := by
    intro τ hτ
    obtain ⟨s, hsS, hτs⟩ := exists_lt_of_lt_csSup hSne hτ.2
    exact hsS.2 τ ⟨hτ.1, hτs.le⟩
  -- chart data at the supremum
  obtain ⟨α, a', b', hab', hc', hsub', hnbhd', hsrc', hJF'⟩ := hJac c ⟨hac, hcb⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hnbhd'
  -- the pair vanishes at the supremum itself
  have hcz : J c = 0 ∧ DJ c = 0 := by
    rcases eq_or_lt_of_le hac with heq | hlt
    · rw [← heq]; exact ⟨hJa, hDJa⟩
    · -- a < c: the chart readings vanish on a left approach interval and are
      -- continuous within the chart interval, hence vanish at c
      have ha'c : a' < c := by
        have hτmem : max a (c - ε / 2) ∈ Metric.ball c ε ∩ Icc a b := by
          constructor
          · rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by
              simp only [sub_nonpos]; exact max_le hlt.le (by linarith)), neg_sub]
            have : c - ε / 2 ≤ max a (c - ε / 2) := le_max_right _ _
            linarith
          · exact ⟨le_max_left _ _, le_trans (max_le hlt.le (by linarith)) hcb⟩
        have := hball hτmem
        exact lt_of_le_of_lt this.1 (max_lt hlt (by linarith))
      set m := max a' (max a (c - ε / 2)) with hm_def
      have hmc : m < c := max_lt ha'c (max_lt hlt (by linarith))
      have hLsub : Ioo m c ⊆ Icc a' b' := fun τ hτ =>
        ⟨le_trans (le_max_left _ _) hτ.1.le, le_trans hτ.2.le hc'.2⟩
      have hLbelow : Ioo m c ⊆ Ico a c := fun τ hτ =>
        ⟨le_trans (le_trans (le_max_left _ _) (le_max_right a' _)) hτ.1.le, hτ.2⟩
      have hcclosure : c ∈ closure (Ioo m c) := by
        rw [closure_Ioo hmc.ne]; exact ⟨hmc.le, le_rfl⟩
      have hNeBot : (𝓝[Ioo m c] c).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.1 hcclosure
      constructor
      · refine (tangentCoordChange_eq_zero_iff (I := I) (hsrc' c hc')).1 ?_
        refine tendsto_nhds_unique (f := chartVectorRep (I := I) γ α J)
          (l := 𝓝[Ioo m c] c)
          (((hJF'.continuousOn_fst c hc').mono hLsub) : Tendsto _ _ _) ?_
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        have hJτ : J τ = 0 := (hbelow τ (hLbelow hτ)).1
        simp [chartVectorRep_apply, hJτ]
      · refine (tangentCoordChange_eq_zero_iff (I := I) (hsrc' c hc')).1 ?_
        refine tendsto_nhds_unique (f := chartVectorRep (I := I) γ α DJ)
          (l := 𝓝[Ioo m c] c)
          (((hJF'.continuousOn_snd c hc').mono hLsub) : Tendsto _ _ _) ?_
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        have hDJτ : DJ τ = 0 := (hbelow τ (hLbelow hτ)).2
        simp [chartVectorRep_apply, hDJτ]
  -- the supremum is b: otherwise chart-local uniqueness pushes past it
  have hcb' : c = b := by
    by_contra hne
    have hclt : c < b := lt_of_le_of_ne hcb hne
    -- the chart interval extends strictly past c
    have hcb'2 : c < b' := by
      have hτmem : min b (c + ε / 2) ∈ Metric.ball c ε ∩ Icc a b := by
        constructor
        · rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by
            simp only [sub_nonneg]; exact le_min hclt.le (by linarith))]
          have : min b (c + ε / 2) ≤ c + ε / 2 := min_le_right _ _
          linarith
        · exact ⟨le_trans hac (le_min hclt.le (by linarith)), min_le_left _ _⟩
      have := hball hτmem
      exact lt_of_lt_of_le (lt_min hclt (by linarith)) this.2
    set b'' := min b' (min b (c + ε / 2)) with hb''_def
    have hcb'' : c < b'' := lt_min hcb'2 (lt_min hclt (by linarith))
    have hb''sub : Icc c b'' ⊆ Icc a' b' := fun τ hτ =>
      ⟨le_trans hc'.1 hτ.1, le_trans hτ.2 (min_le_left _ _)⟩
    have hb''ab : Icc c b'' ⊆ Icc a b := fun τ hτ =>
      ⟨le_trans hac hτ.1, le_trans hτ.2 (le_trans (min_le_right _ _)
        (min_le_left _ _))⟩
    -- geodesic package on [c, b'']
    have hu_diff : ∀ τ ∈ Icc c b'',
        DifferentiableAt ℝ (fun s => extChartAt I α (γ s)) τ := fun τ hτ =>
      hgeo.differentiableAt_extChartAt (hb''ab hτ) (hγc τ (hb''ab hτ))
        (hsrc' τ (hb''sub hτ))
    have hu_cont : ContinuousOn (fun s => extChartAt I α (γ s)) (Icc c b'') :=
      fun τ hτ => (hu_diff τ hτ).continuousAt.continuousWithinAt
    have hu'_cont : ContinuousOn (deriv (fun s => extChartAt I α (γ s)))
        (Icc c b'') := fun τ hτ =>
      (hgeo.continuousAt_deriv_extChartAt (hb''ab hτ) (hγc τ (hb''ab hτ))
        (hsrc' τ (hb''sub hτ))).continuousWithinAt
    have hmem : ∀ τ ∈ Icc c b'',
        extChartAt I α (γ τ) ∈ interior (extChartAt I α).target := fun τ hτ => by
      rw [(isOpen_extChartAt_target α).interior_eq]
      exact (extChartAt I α).map_source
        (by rw [extChartAt_source]; exact hsrc' τ (hb''sub hτ))
    obtain ⟨Kb, hKb⟩ := exists_nnnorm_jacobiPairCoeffCoord_le (I := I) g α
      hu_cont hu'_cont hmem
    -- chart-local uniqueness from c
    have hb''b' : b'' ≤ b' := by rw [hb''_def]; exact min_le_left _ _
    have hmono := hJF'.mono hc'.1 hb''b'
    have hJc0 : chartVectorRep (I := I) γ α J c = 0 := by
      simp [chartVectorRep_apply, hcz.1]
    have hDJc0 : chartVectorRep (I := I) γ α DJ c = 0 := by
      simp [chartVectorRep_apply, hcz.2]
    have hz := hmono.eqOn_zero hKb hJc0 hDJc0
    -- b'' belongs to S, contradicting the supremum
    have hb''S : b'' ∈ S := by
      refine ⟨⟨le_trans hac hcb''.le, le_trans (min_le_right _ _)
        (min_le_left _ _)⟩, fun τ hτ => ?_⟩
      rcases lt_or_ge τ c with hτc | hτc
      · exact hbelow τ ⟨hτ.1, hτc⟩
      · rcases eq_or_lt_of_le hτc with heq | hτc'
        · rw [← heq]; exact hcz
        · have hτmem : τ ∈ Icc c b'' := ⟨hτc, hτ.2⟩
          constructor
          · exact (tangentCoordChange_eq_zero_iff (I := I)
              (hsrc' τ (hb''sub hτmem))).1 (hz.1 hτmem)
          · exact (tangentCoordChange_eq_zero_iff (I := I)
              (hsrc' τ (hb''sub hτmem))).1 (hz.2 hτmem)
    exact absurd (le_csSup hbdd hb''S) (not_le.2 hcb'')
  -- conclude
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · rw [heq, ← hcb']; exact hcz
  · exact hbelow t ⟨ht.1, hcb' ▸ hlt⟩

end Main

end Riemannian.Jacobi

end
