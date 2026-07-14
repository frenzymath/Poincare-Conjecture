import PetersenLib.Ch05.MetricStructure

/-!
# Petersen Ch. 5, §5.3 — Thm. 5.3.8: the metric topology is the manifold topology

Petersen's Theorem 5.3.8 (`thm:pet-ch5-metric-topology`): on a connected
Riemannian manifold the Riemannian distance `|pq|` (`riemannianDistance`) is a
genuine metric whose topology coincides with the manifold topology, together
with Corollary 5.3.9 (`cor:pet-ch5-compact-complete-metric`): compact
manifolds are metrically complete.

Following Petersen's proof, everything reduces to a two-sided comparison of
`riemannianDistance` with the flat chart distance near each point `p`, via the
uniform Gram eigenvalue bounds `λ ‖u‖² ≤ ⟨u, u⟩_p^y ≤ μ ‖u‖²` of
`TangentCompactness.lean` on a compact chart piece:

* `curveSpeedSq_eq_chartMetricInner_of_hasDerivAt` — the moving-chart speed of
  a curve equals the fixed-chart Gram pairing of the fixed-chart velocity.
* `sqrt_mul_norm_sub_le_curveLength` — **chart-displacement estimate**: a
  piecewise smooth curve travelling in a chart piece carrying the lower Gram
  bound `λ` has `L(γ)|_a^c ≥ √λ ‖x(γ c) − x(γ a)‖` (per smooth piece: the
  fundamental theorem of calculus plus `‖∫ ẋ‖ ≤ ∫ ‖ẋ‖`).
* `sqrt_mul_le_curveLength_of_exit` — **first-exit estimate**: a curve from
  `p` that leaves the chart ball of radius `ε` has length at least `√λ ε`.
* `riemannianDistance_le_sqrt_mul` (packaged in
  `exists_riemannianDistance_le_sqrt_mul`) — **chart-line estimate**: the
  straight chart segment from `p` to a nearby `q` has `g`-length at most
  `√μ ‖x_q − x_p‖`, so `|pq| ≤ √μ ‖x_q − x_p‖`.
* `exists_isPiecewiseSmoothCurve_connecting` — on a connected manifold any two
  points are joined by a piecewise smooth curve (chart lines glue by openness
  of the both-way-reachable set), so `Ω_{p,q} ≠ ∅` and the triangle inequality
  `riemannianDistance_triangle_of_connected` holds unconditionally.
* `isOpen_iff_riemannianDistance`, `eq_of_riemannianDistance_eq_zero` — the
  two comparison estimates give exactly the metric-topology characterisation
  of open sets and the positivity `p ≠ q → |pq| > 0`.
* `riemannianMetricSpace` — the resulting `MetricSpace M` structure, built by
  `MetricSpace.ofDistTopology` so that its topology is **definitionally** the
  manifold topology; `riemannianDistance_inducesManifoldTopology` (Petersen
  Thm. 5.3.8) is then literally `rfl`.
* `compactManifold_metricallyComplete` (Petersen Cor. 5.3.9) — a compact
  manifold is complete in this metric: the metric topology is the compact
  manifold topology, and compact uniform spaces are complete.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open scoped Manifold Topology ContDiff

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Chart-ball images under the inverse chart -/

/-- **Eng.** The inverse-chart image of an open subset of the chart target is
open: it equals `source ∩ φ⁻¹(s)`, and `φ` is continuous on the open source. -/
theorem isOpen_extChartAt_symm_image {z : M} {s : Set E} (hs : IsOpen s)
    (hsub : s ⊆ (extChartAt I z).target) :
    IsOpen ((extChartAt I z).symm '' s) := by
  rw [(extChartAt I z).symm_image_eq_source_inter_preimage hsub]
  exact (continuousOn_extChartAt (I := I) z).isOpen_inter_preimage
    (isOpen_extChartAt_source z) hs

/-- **Eng.** The centre belongs to the inverse-chart image of any chart ball of
positive radius around its chart image. -/
theorem mem_extChartAt_symm_image_ball_self (z : M) {r : ℝ} (hr : 0 < r) :
    z ∈ (extChartAt I z).symm '' Metric.ball (extChartAt I z z) r :=
  ⟨extChartAt I z z, Metric.mem_ball_self hr,
    (extChartAt I z).left_inv (mem_extChartAt_source (I := I) z)⟩

/-- **Eng.** A curve that is `C^∞` on `[a, b]` is piecewise `C^∞` on `[a, b]`:
take the trivial one-piece partition. -/
theorem ContMDiffOn.isPiecewiseSmoothCurve {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b)) :
    IsPiecewiseSmoothCurve (I := I) γ a b := by
  refine ⟨hγ.continuousOn, 1, ![a, b], ?_, ?_, ?_, ?_⟩
  · exact Fin.monotone_iff_le_succ.2 (fun i => by fin_cases i; simpa using hab)
  · simp
  · simp
  · intro i
    fin_cases i
    simpa using hγ

section Boundaryless

variable [I.Boundaryless]

/-! ## Transfer of the moving-chart speed to a fixed chart -/

/-- **Math.** **Fixed-chart reading of the squared speed**: if a curve `γ`
stays in the chart source at `α` near time `t` and its fixed-chart reading
`s ↦ φ_α (γ s)` has derivative `v` at `t`, then the (moving-chart) squared
speed at `t` is the chart-`α` Gram pairing `⟨v, v⟩_α^{φ_α (γ t)}`.  The
moving-chart velocity is the coordinate change of `v` (chain rule through the
chart transition), and the Gram identity `chartMetricInner_eq_inner` matches
the two pairings. -/
theorem curveSpeedSq_eq_chartMetricInner_of_hasDerivAt (g : RiemannianMetric I M)
    {γ : ℝ → M} {α : M} {t : ℝ} {v : E}
    (hsrc : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I α).source)
    (hx : HasDerivAt (fun s => extChartAt I α (γ s)) v t) :
    curveSpeedSq (I := I) g γ t
      = chartMetricInner (I := I) g α (extChartAt I α (γ t)) v v := by
  have hsrc_t : γ t ∈ (extChartAt I α).source := hsrc.self_of_nhds
  have hev : Geodesic.chartLocalCurve (I := I) γ t
      =ᶠ[𝓝 t] (chartTransition (M := M) I α (γ t) ∘ fun s => extChartAt I α (γ s)) := by
    filter_upwards [hsrc] with r hr
    exact (chartTransition_extChartAt (M := M) (I := I) (β := γ t) hr).symm
  have htrans : HasFDerivAt (chartTransition (M := M) I α (γ t))
      (tangentCoordChange I α (γ t) (γ t)) (extChartAt I α (γ t)) :=
    hasFDerivAt_chartTransition (I := I) hsrc_t (mem_extChartAt_source (I := I) (γ t))
  have hvel : deriv (Geodesic.chartLocalCurve (I := I) γ t) t
      = tangentCoordChange I α (γ t) (γ t) v := by
    have hcomp := htrans.comp_hasDerivAt t hx
    exact (hcomp.congr_of_eventuallyEq hev).deriv
  rw [curveSpeedSq_def, hvel]
  exact (chartMetricInner_eq_inner (I := I) g hsrc_t v v).symm

/-! ## The chart-displacement lower bound for the length -/

/-- **Math.** **Chart-displacement estimate, smooth piece**: if `γ` is `C^∞`
on `[c, d]` with values in a set `C` inside the chart source at `α` on which
the chart Gram pairing is bounded below by `λ ‖·‖²`, then
`√λ ‖x(γ d) − x(γ c)‖ ≤ L(γ)|_c^d` where `x = φ_α`.  Indeed
`x(γ d) − x(γ c) = ∫ ẋ` (fundamental theorem of calculus), `‖∫ ẋ‖ ≤ ∫ ‖ẋ‖`,
and pointwise `√λ ‖ẋ‖ ≤ √(⟨ẋ, ẋ⟩_α) = |γ̇|_g`. -/
theorem sqrt_mul_norm_sub_le_curveLength_of_contMDiffOn (g : RiemannianMetric I M)
    {α : M} {C : Set M} (hCsub : C ⊆ (chartAt H α).source) {lam : ℝ} (hlam : 0 < lam)
    (hbound : ∀ q ∈ C, ∀ u : E,
      lam * ‖u‖ ^ 2 ≤ chartMetricInner (I := I) g α (extChartAt I α q) u u)
    {γ : ℝ → M} {c d : ℝ} (hcd : c ≤ d)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc c d)) (hmem : ∀ s ∈ Icc c d, γ s ∈ C) :
    Real.sqrt lam * ‖extChartAt I α (γ d) - extChartAt I α (γ c)‖
      ≤ curveLength (I := I) g γ c d := by
  rcases hcd.eq_or_lt with rfl | hlt
  · simp
  have hsrc : ∀ s ∈ Icc c d, γ s ∈ (extChartAt I α).source := by
    intro s hs
    rw [extChartAt_source I]
    exact hCsub (hmem s hs)
  set x : ℝ → E := fun s => extChartAt I α (γ s) with hx_def
  have hxsmooth : ContDiffOn ℝ ∞ x (Icc c d) := contDiffOn_extChartAt_comp hγ hsrc
  have hUD : UniqueDiffOn ℝ (Icc c d) := uniqueDiffOn_Icc hlt
  set D : ℝ → E := derivWithin x (Icc c d) with hD_def
  have hDcont : ContinuousOn D (Icc c d) :=
    hxsmooth.continuousOn_derivWithin hUD (by norm_num)
  have hD_deriv : ∀ s ∈ Ioo c d, HasDerivAt x (D s) s := by
    intro s hs
    have hnhds : Icc c d ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hdiff : DifferentiableAt ℝ x s :=
      ((hxsmooth.differentiableOn (by norm_num)) s (Ioo_subset_Icc_self hs)).differentiableAt
        hnhds
    have hDs : D s = deriv x s := derivWithin_of_mem_nhds hnhds
    rw [hDs]
    exact hdiff.hasDerivAt
  have hDint : IntervalIntegrable D volume c d := hDcont.intervalIntegrable_of_Icc hlt.le
  have hFTC : (∫ s in c..d, D s) = x d - x c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlt.le hxsmooth.continuousOn
      hD_deriv hDint
  -- pointwise comparison of `√λ ‖ẋ‖` with the speed at interior times
  have hpt : ∀ s ∈ Ioo c d,
      Real.sqrt lam * ‖D s‖ ≤ Real.sqrt (curveSpeedSq (I := I) g γ s) := by
    intro s hs
    have hsIcc : s ∈ Icc c d := Ioo_subset_Icc_self hs
    have hsrc_ev : ∀ᶠ r in 𝓝 s, γ r ∈ (extChartAt I α).source := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
      exact hsrc r hr
    have hspeed : curveSpeedSq (I := I) g γ s
        = chartMetricInner (I := I) g α (extChartAt I α (γ s)) (D s) (D s) :=
      curveSpeedSq_eq_chartMetricInner_of_hasDerivAt (I := I) g hsrc_ev (hD_deriv s hs)
    have hb : lam * ‖D s‖ ^ 2 ≤ curveSpeedSq (I := I) g γ s := by
      rw [hspeed]
      exact hbound (γ s) (hmem s hsIcc) (D s)
    have h1 : Real.sqrt lam * ‖D s‖ = Real.sqrt (lam * ‖D s‖ ^ 2) := by
      rw [Real.sqrt_mul hlam.le, Real.sqrt_sq (norm_nonneg _)]
    rw [h1]
    exact Real.sqrt_le_sqrt hb
  have hInt1 : IntervalIntegrable (fun s => Real.sqrt lam * ‖D s‖) volume c d :=
    (continuousOn_const.mul hDcont.norm).intervalIntegrable_of_Icc hlt.le
  have hInt2 : IntervalIntegrable (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s))
      volume c d :=
    ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (I := I) g hlt.le hγ
  calc Real.sqrt lam * ‖x d - x c‖
      = Real.sqrt lam * ‖∫ s in c..d, D s‖ := by rw [hFTC]
    _ ≤ Real.sqrt lam * ∫ s in c..d, ‖D s‖ :=
        mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hlt.le)
          (Real.sqrt_nonneg lam)
    _ = ∫ s in c..d, Real.sqrt lam * ‖D s‖ :=
        (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ s in c..d, Real.sqrt (curveSpeedSq (I := I) g γ s) :=
        intervalIntegral.integral_mono_on_of_le_Ioo hlt.le hInt1 hInt2 hpt
    _ = curveLength (I := I) g γ c d := rfl

/-- **Math.** **Chart-displacement estimate, piecewise version**: if `γ` is
piecewise `C^∞` on `[a, b]` and stays, on the subinterval `[a, c]`, inside a
set `C` in the chart source at `α` carrying the lower Gram bound `λ ‖·‖²`,
then `√λ ‖x(γ c) − x(γ a)‖ ≤ L(γ)|_a^c`.  Clamp the partition at `c`, apply
the smooth-piece estimate to each clamped piece and chain with the triangle
inequality for the chart displacement and additivity of the length. -/
theorem sqrt_mul_norm_sub_le_curveLength (g : RiemannianMetric I M)
    {α : M} {C : Set M} (hCsub : C ⊆ (chartAt H α).source) {lam : ℝ} (hlam : 0 < lam)
    (hbound : ∀ q ∈ C, ∀ u : E,
      lam * ‖u‖ ^ 2 ≤ chartMetricInner (I := I) g α (extChartAt I α q) u u)
    {γ : ℝ → M} {a b c : ℝ} (hγ : IsPiecewiseSmoothCurve (I := I) γ a b)
    (hc : c ∈ Icc a b) (hmem : ∀ s ∈ Icc a c, γ s ∈ C) :
    Real.sqrt lam * ‖extChartAt I α (γ c) - extChartAt I α (γ a)‖
      ≤ curveLength (I := I) g γ a c := by
  have hInt := hγ.intervalIntegrable_sqrt_curveSpeedSq (I := I) g
  obtain ⟨hcont, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  have hu_mem : ∀ i : Fin (n + 1), u i ∈ Icc a b := fun i =>
    ⟨hu0 ▸ hmono (Fin.zero_le i), hun ▸ hmono (Fin.le_last i)⟩
  -- clamped partition points stay in `[a, b]`
  have hw_mem : ∀ i : Fin (n + 1), min (u i) c ∈ Icc a b := fun i =>
    ⟨le_min (hu_mem i).1 hc.1, (min_le_left _ _).trans (hu_mem i).2⟩
  have key : ∀ k : ℕ, ∀ hk : k < n + 1,
      Real.sqrt lam * ‖extChartAt I α (γ (min (u ⟨k, hk⟩) c)) - extChartAt I α (γ a)‖
        ≤ curveLength (I := I) g γ a (min (u ⟨k, hk⟩) c) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : min (u ⟨0, hk⟩) c = a := by
        have : u ⟨0, hk⟩ = a := hu0
        rw [this, min_eq_left hc.1]
      rw [h0]
      simp
    | succ k ih =>
      intro hk
      have hkn : k < n + 1 := by omega
      have hkn' : k < n := by omega
      set wk := min (u ⟨k, hkn⟩) c with hwk_def
      set wk1 := min (u ⟨k + 1, hk⟩) c with hwk1_def
      have hcast : (⟨k, hkn⟩ : Fin (n + 1)) = (⟨k, hkn'⟩ : Fin n).castSucc := rfl
      have hsuccc : (⟨k + 1, hk⟩ : Fin (n + 1)) = (⟨k, hkn'⟩ : Fin n).succ := rfl
      have huk_le : u ⟨k, hkn⟩ ≤ u ⟨k + 1, hk⟩ := by
        rw [hcast, hsuccc]
        exact hmono Fin.castSucc_lt_succ.le
      have hw_le : wk ≤ wk1 := min_le_min huk_le le_rfl
      have hwk_a : a ≤ wk := (hw_mem ⟨k, hkn⟩).1
      have hwk1_c : wk1 ≤ c := min_le_right _ _
      -- piece estimate on `[wk, wk1]`
      have hpiece : Real.sqrt lam
          * ‖extChartAt I α (γ wk1) - extChartAt I α (γ wk)‖
            ≤ curveLength (I := I) g γ wk wk1 := by
        rcases hw_le.eq_or_lt with heq | hltw
        · rw [heq]
          simp
        · have hwk_lt_c : wk < c := lt_of_lt_of_le hltw hwk1_c
          have hwk_eq : wk = u ⟨k, hkn⟩ := by
            rcases min_cases (u ⟨k, hkn⟩) c with ⟨h1, -⟩ | ⟨h1, h2⟩
            · rw [hwk_def, h1]
            · exfalso
              rw [hwk_def] at hwk_lt_c
              rw [h1] at hwk_lt_c
              exact lt_irrefl c hwk_lt_c
          have hsub : Icc wk wk1 ⊆ Icc (u ⟨k, hkn⟩) (u ⟨k + 1, hk⟩) := by
            apply Icc_subset_Icc
            · rw [hwk_eq]
            · exact min_le_left _ _
          have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc wk wk1) := by
            refine (hsmooth ⟨k, hkn'⟩).mono ?_
            rwa [← hcast, ← hsuccc]
          have hmem' : ∀ s ∈ Icc wk wk1, γ s ∈ C := fun s hs =>
            hmem s ⟨hwk_a.trans hs.1, hs.2.trans hwk1_c⟩
          exact sqrt_mul_norm_sub_le_curveLength_of_contMDiffOn (I := I) g hCsub hlam
            hbound hw_le hsm hmem'
      -- additivity of the length at `wk`
      have hadd : curveLength (I := I) g γ a wk1 =
          curveLength (I := I) g γ a wk + curveLength (I := I) g γ wk wk1 := by
        refine curveLength_additive (I := I) g γ (hInt.mono_set ?_) (hInt.mono_set ?_)
        · rw [uIcc_of_le hwk_a, uIcc_of_le (hc.1.trans hc.2)]
          exact Icc_subset_Icc le_rfl ((hw_mem ⟨k, hkn⟩).2)
        · rw [uIcc_of_le hw_le, uIcc_of_le (hc.1.trans hc.2)]
          exact Icc_subset_Icc hwk_a ((hw_mem ⟨k + 1, hk⟩).2)
      -- chart-displacement triangle inequality
      have htri : ‖extChartAt I α (γ wk1) - extChartAt I α (γ a)‖
          ≤ ‖extChartAt I α (γ wk1) - extChartAt I α (γ wk)‖
            + ‖extChartAt I α (γ wk) - extChartAt I α (γ a)‖ := by
        have := dist_triangle (extChartAt I α (γ wk1)) (extChartAt I α (γ wk))
          (extChartAt I α (γ a))
        simpa [dist_eq_norm] using this
      have hmul := mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg lam)
      have hih := ih hkn
      rw [mul_add] at hmul
      rw [hadd]
      calc Real.sqrt lam * ‖extChartAt I α (γ wk1) - extChartAt I α (γ a)‖
          ≤ Real.sqrt lam * ‖extChartAt I α (γ wk1) - extChartAt I α (γ wk)‖
            + Real.sqrt lam * ‖extChartAt I α (γ wk) - extChartAt I α (γ a)‖ := hmul
        _ ≤ curveLength (I := I) g γ wk wk1 + curveLength (I := I) g γ a wk := by
            gcongr
        _ = curveLength (I := I) g γ a wk + curveLength (I := I) g γ wk wk1 := by ring
  have hfinal := key n n.lt_succ_self
  have hlast : (⟨n, n.lt_succ_self⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hlast, hun, min_eq_right hc.2] at hfinal
  exact hfinal

/-! ## The first-exit estimate -/

/-- **Math.** **First-exit estimate**: let `γ` be a piecewise smooth curve on
`[0, 1]` starting at `p`, and suppose the closed chart ball of radius
`ε₀ ≥ ε > 0` at `p` lies in the chart target and carries the lower Gram bound
`λ ‖·‖²`.  If `γ` meets the complement of the (inverse-chart image of the)
open chart `ε`-ball, then `L(γ) ≥ √λ ε`: up to the first exit time `t₀` the
curve stays in the closed chart ball, so the chart-displacement estimate gives
`L(γ)|_0^{t₀} ≥ √λ ‖x(γ t₀) − x_p‖ ≥ √λ ε`. -/
theorem sqrt_mul_le_curveLength_of_exit [T2Space M] (g : RiemannianMetric I M)
    {p : M} {ε ε₀ : ℝ} (hε : 0 < ε) (hεε₀ : ε ≤ ε₀)
    (htgt : Metric.closedBall (extChartAt I p p) ε₀ ⊆ (extChartAt I p).target)
    {lam : ℝ} (hlam : 0 < lam)
    (hbound : ∀ q ∈ (extChartAt I p).symm '' Metric.closedBall (extChartAt I p p) ε₀,
      ∀ u : E, lam * ‖u‖ ^ 2 ≤ chartMetricInner (I := I) g p (extChartAt I p q) u u)
    {γ : ℝ → M} (hγ : IsPiecewiseSmoothCurve (I := I) γ 0 1) (hγ0 : γ 0 = p)
    (hexit : ∃ t ∈ Icc (0 : ℝ) 1,
      γ t ∉ (extChartAt I p).symm '' Metric.ball (extChartAt I p p) ε) :
    Real.sqrt lam * ε ≤ curveLength (I := I) g γ 0 1 := by
  have hcball_tgt : Metric.closedBall (extChartAt I p p) ε ⊆ (extChartAt I p).target :=
    (Metric.closedBall_subset_closedBall hεε₀).trans htgt
  have hball_tgt : Metric.ball (extChartAt I p p) ε ⊆ (extChartAt I p).target :=
    Metric.ball_subset_closedBall.trans hcball_tgt
  set U := (extChartAt I p).symm '' Metric.ball (extChartAt I p p) ε with hU_def
  set Cε := (extChartAt I p).symm '' Metric.closedBall (extChartAt I p p) ε with hCε_def
  have hUopen : IsOpen U := isOpen_extChartAt_symm_image (I := I) Metric.isOpen_ball hball_tgt
  have hCcomp : IsCompact Cε :=
    (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm p).mono hcball_tgt)
  have hCclosed : IsClosed Cε := hCcomp.isClosed
  have hUsubC : U ⊆ Cε := image_mono Metric.ball_subset_closedBall
  have hCsub_src : Cε ⊆ (chartAt H p).source := by
    rintro q ⟨y, hy, rfl⟩
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target (hcball_tgt hy)
  have hbound' : ∀ q ∈ Cε, ∀ u : E,
      lam * ‖u‖ ^ 2 ≤ chartMetricInner (I := I) g p (extChartAt I p q) u u := fun q hq u =>
    hbound q (image_mono (Metric.closedBall_subset_closedBall hεε₀) hq) u
  -- the set of times at which the curve is outside `U`, and its infimum
  set A := Icc (0 : ℝ) 1 ∩ γ ⁻¹' Uᶜ with hA_def
  have hAclosed : IsClosed A :=
    hγ.1.preimage_isClosed_of_isClosed isClosed_Icc hUopen.isClosed_compl
  have hAne : A.Nonempty := by
    obtain ⟨t, ht, hnot⟩ := hexit
    exact ⟨t, ht, hnot⟩
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set t₀ := sInf A with ht₀_def
  have ht₀A : t₀ ∈ A := hAclosed.csInf_mem hAne hAbdd
  have ht₀_mem : t₀ ∈ Icc (0 : ℝ) 1 := ht₀A.1
  have hp_mem_U : p ∈ U := mem_extChartAt_symm_image_ball_self (I := I) p hε
  have ht₀_pos : 0 < t₀ := by
    rcases ht₀_mem.1.lt_or_eq with h | h
    · exact h
    · exfalso
      apply ht₀A.2
      show γ t₀ ∈ U
      rw [← h, hγ0]
      exact hp_mem_U
  have hbefore : ∀ t ∈ Ico (0 : ℝ) t₀, γ t ∈ U := by
    intro t ht
    by_contra hnot
    have htA : t ∈ A := ⟨⟨ht.1, ht.2.le.trans ht₀_mem.2⟩, hnot⟩
    exact absurd (csInf_le hAbdd htA) (not_le.mpr ht.2)
  -- the curve stays in the closed chart ball on `[0, t₀]`
  have ht₀C : γ t₀ ∈ Cε := by
    have hcwa : ContinuousWithinAt γ (Ico 0 t₀) t₀ :=
      (hγ.1.continuousWithinAt ⟨ht₀_mem.1, ht₀_mem.2⟩).mono
        (fun r hr => ⟨hr.1, hr.2.le.trans ht₀_mem.2⟩)
    have hscl : t₀ ∈ closure (Ico 0 t₀) := by
      rw [closure_Ico ht₀_pos.ne]
      exact ⟨ht₀_mem.1, le_rfl⟩
    have himg : γ '' Ico 0 t₀ ⊆ Cε := by
      rintro w ⟨r, hr, rfl⟩
      exact hUsubC (hbefore r hr)
    exact closure_minimal himg hCclosed (hcwa.mem_closure_image hscl)
  have hmemC : ∀ s ∈ Icc (0 : ℝ) t₀, γ s ∈ Cε := by
    intro s hs
    rcases hs.2.lt_or_eq with hlt | heq
    · exact hUsubC (hbefore s ⟨hs.1, hlt⟩)
    · rw [heq]
      exact ht₀C
  -- displacement estimate up to the exit time
  have hdisp := sqrt_mul_norm_sub_le_curveLength (I := I) g hCsub_src hlam hbound' hγ
    ht₀_mem hmemC
  -- the exit displacement is at least `ε`
  obtain ⟨y, hy_cball, hy_eq⟩ := hmemC t₀ ⟨ht₀_mem.1, le_rfl⟩
  have hxy : extChartAt I p (γ t₀) = y := by
    rw [← hy_eq]
    exact (extChartAt I p).right_inv (hcball_tgt hy_cball)
  have hnorm_ge : ε ≤ ‖extChartAt I p (γ t₀) - extChartAt I p (γ 0)‖ := by
    rw [hγ0, hxy]
    by_contra hlt
    rw [not_le] at hlt
    apply ht₀A.2
    show γ t₀ ∈ U
    exact ⟨y, Metric.mem_ball.mpr (by rwa [dist_eq_norm]), hy_eq⟩
  have hsplit := IsPiecewiseSmoothCurve.curveLength_add (I := I) hγ g ht₀_mem.1 ht₀_mem.2
  have htail : 0 ≤ curveLength (I := I) g γ t₀ 1 :=
    curveLength_nonneg (I := I) g γ ht₀_mem.2
  have hmul := mul_le_mul_of_nonneg_left hnorm_ge (Real.sqrt_nonneg lam)
  linarith

/-! ## The chart-line curve and the upper estimate -/

/-- **Math.** **Chart-line curve**: for `w` in the inverse-chart image of an
open chart ball at `z` contained in the chart target, the straight chart
segment from `φ_z(z)` to `φ_z(w)`, read back through the inverse chart, is a
smooth curve from `z` to `w` inside the chart ball, whose fixed-chart reading
has constant velocity `φ_z(w) − φ_z(z)`. -/
theorem exists_chartLine_curve {z : M} {ε : ℝ}
    (htgt : Metric.ball (extChartAt I z z) ε ⊆ (extChartAt I z).target)
    {w : M} (hw : w ∈ (extChartAt I z).symm '' Metric.ball (extChartAt I z z) ε) :
    ∃ γ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc 0 1) ∧ γ 0 = z ∧ γ 1 = w ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        γ s ∈ (extChartAt I z).symm '' Metric.ball (extChartAt I z z) ε) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun r => extChartAt I z (γ r))
          (extChartAt I z w - extChartAt I z z) s) := by
  obtain ⟨y, hy_ball, rfl⟩ := hw
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hy_ball)
  have hy_tgt : y ∈ (extChartAt I z).target := htgt hy_ball
  have hxw : extChartAt I z ((extChartAt I z).symm y) = y :=
    (extChartAt I z).right_inv hy_tgt
  set x₀ : E := extChartAt I z z with hx₀_def
  set ℓ : ℝ → E := fun s => x₀ + s • (y - x₀) with hℓ_def
  have hℓ_mem : ∀ s ∈ Icc (0 : ℝ) 1, ℓ s ∈ Metric.ball x₀ ε := by
    intro s hs
    have h1 : ‖ℓ s - x₀‖ = s * ‖y - x₀‖ := by
      rw [hℓ_def]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    have h2 : ‖y - x₀‖ < ε := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hy_ball
    rw [Metric.mem_ball, dist_eq_norm, h1]
    calc s * ‖y - x₀‖ ≤ 1 * ‖y - x₀‖ :=
          mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ = ‖y - x₀‖ := one_mul _
      _ < ε := h2
  set γ : ℝ → M := fun s => (extChartAt I z).symm (ℓ s) with hγ_def
  have hγ_mem : ∀ s ∈ Icc (0 : ℝ) 1,
      γ s ∈ (extChartAt I z).symm '' Metric.ball x₀ ε := fun s hs =>
    ⟨ℓ s, hℓ_mem s hs, rfl⟩
  have hℓ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ℓ (Icc 0 1) := by
    have : ContDiff ℝ ∞ ℓ := by
      rw [hℓ_def]
      exact contDiff_const.add (contDiff_id.smul contDiff_const)
    exact this.contMDiff.contMDiffOn
  have hγ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc 0 1) := by
    refine (contMDiffOn_extChartAt_symm z).comp hℓ_smooth ?_
    intro s hs
    exact htgt (hℓ_mem s hs)
  have hγ0 : γ 0 = z := by
    have hℓ0 : ℓ 0 = x₀ := by rw [hℓ_def]; simp
    rw [hγ_def]
    simp only [hℓ0]
    exact (extChartAt I z).left_inv (mem_extChartAt_source (I := I) z)
  have hγ1 : γ 1 = (extChartAt I z).symm y := by
    have hℓ1 : ℓ 1 = y := by rw [hℓ_def]; simp
    show (extChartAt I z).symm (ℓ 1) = (extChartAt I z).symm y
    rw [hℓ1]
  refine ⟨γ, hγ_smooth, hγ0, hγ1, ?_, ?_⟩
  · intro s hs
    exact hγ_mem s hs
  · intro s hs
    have hℓ_deriv : HasDerivAt ℓ (y - x₀) s := by
      have h : HasDerivAt (fun r : ℝ => x₀ + r • (y - x₀)) ((1 : ℝ) • (y - x₀)) s :=
        ((hasDerivAt_id s).smul_const (y - x₀)).const_add x₀
      rw [one_smul] at h
      rw [hℓ_def]
      exact h
    have hxγ : (fun r => extChartAt I z (γ r)) =ᶠ[𝓝 s] ℓ := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
      show extChartAt I z (γ r) = ℓ r
      exact (extChartAt I z).right_inv (htgt (hℓ_mem r hr))
    have hval : extChartAt I z ((extChartAt I z).symm y) - extChartAt I z z = y - x₀ := by
      rw [hxw, hx₀_def]
    rw [hval]
    exact hℓ_deriv.congr_of_eventuallyEq hxγ

/-- **Math.** **Chart-line upper estimate for the distance** (packaged): around
every `p` there is a chart-ball radius `ε > 0` with the closed chart `ε`-ball
inside the chart target, and a Gram upper bound `μ > 0` on the corresponding
compact chart piece, such that every `q` in the inverse-chart image of the
open `ε`-ball satisfies `|pq| ≤ √μ ‖φ_p(q) − φ_p(p)‖`: the straight chart
segment from `p` to `q` has speed `⟨v, v⟩_p ≤ μ ‖v‖²` for the constant
chart velocity `v = φ_p(q) − φ_p(p)`. -/
theorem exists_riemannianDistance_le_sqrt_mul [T2Space M] (g : RiemannianMetric I M)
    (p : M) :
    ∃ ε > (0 : ℝ), Metric.closedBall (extChartAt I p p) ε ⊆ (extChartAt I p).target ∧
      ∃ mu > (0 : ℝ), ∀ q ∈ (extChartAt I p).symm '' Metric.ball (extChartAt I p p) ε,
        riemannianDistance (I := I) g p q
          ≤ Real.sqrt mu * ‖extChartAt I p q - extChartAt I p p‖ := by
  obtain ⟨ε, hε, htgt⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (extChartAt_target_mem_nhds (I := I) p)
  have hball_tgt : Metric.ball (extChartAt I p p) ε ⊆ (extChartAt I p).target :=
    Metric.ball_subset_closedBall.trans htgt
  set C := (extChartAt I p).symm '' Metric.closedBall (extChartAt I p p) ε with hC_def
  have hCcomp : IsCompact C :=
    (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm p).mono htgt)
  have hCsub : C ⊆ (chartAt H p).source := by
    rintro q ⟨y, hy, rfl⟩
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target (htgt hy)
  obtain ⟨mu, hmu, hbound⟩ := exists_forall_chartMetricInner_le (I := I) g hCcomp hCsub
  refine ⟨ε, hε, htgt, mu, hmu, ?_⟩
  intro q hq
  obtain ⟨γ, hγ_smooth, hγ0, hγ1, hγ_mem, hγ_deriv⟩ :=
    exists_chartLine_curve (I := I) hball_tgt hq
  set v : E := extChartAt I p q - extChartAt I p p with hv_def
  -- the speed of the chart line is bounded by `μ ‖v‖²`
  have hspeed_le : ∀ s ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (curveSpeedSq (I := I) g γ s) ≤ Real.sqrt (mu * ‖v‖ ^ 2) := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
    have hγsC : γ s ∈ C := image_mono Metric.ball_subset_closedBall (hγ_mem s hsIcc)
    have hsrc_ev : ∀ᶠ r in 𝓝 s, γ r ∈ (extChartAt I p).source := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
      obtain ⟨y, hy, hyq⟩ := hγ_mem r hr
      rw [← hyq]
      exact (extChartAt I p).map_target (hball_tgt hy)
    have hspeed : curveSpeedSq (I := I) g γ s
        = chartMetricInner (I := I) g p (extChartAt I p (γ s)) v v :=
      curveSpeedSq_eq_chartMetricInner_of_hasDerivAt (I := I) g hsrc_ev (hγ_deriv s hs)
    refine Real.sqrt_le_sqrt ?_
    rw [hspeed]
    exact hbound (γ s) hγsC v
  -- integrate the speed bound
  have hlen_le : curveLength (I := I) g γ 0 1 ≤ Real.sqrt (mu * ‖v‖ ^ 2) := by
    have hInt1 : IntervalIntegrable (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s))
        volume 0 1 :=
      ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (I := I) g zero_le_one hγ_smooth
    have hInt2 : IntervalIntegrable (fun _ : ℝ => Real.sqrt (mu * ‖v‖ ^ 2)) volume 0 1 :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hInt1 hInt2
      hspeed_le
    have hconst : (∫ _ in (0 : ℝ)..1, Real.sqrt (mu * ‖v‖ ^ 2))
        = Real.sqrt (mu * ‖v‖ ^ 2) := by simp
    calc curveLength (I := I) g γ 0 1
        = ∫ s in (0 : ℝ)..1, Real.sqrt (curveSpeedSq (I := I) g γ s) := rfl
      _ ≤ ∫ _ in (0 : ℝ)..1, Real.sqrt (mu * ‖v‖ ^ 2) := hmono
      _ = Real.sqrt (mu * ‖v‖ ^ 2) := hconst
  have hd_le : riemannianDistance (I := I) g p q ≤ curveLength (I := I) g γ 0 1 :=
    riemannianDistance_le_curveLength (I := I) g
      (ContMDiffOn.isPiecewiseSmoothCurve (I := I) zero_le_one hγ_smooth) hγ0 hγ1
  have hsq : Real.sqrt (mu * ‖v‖ ^ 2) = Real.sqrt mu * ‖v‖ := by
    rw [Real.sqrt_mul hmu.le, Real.sqrt_sq (norm_nonneg _)]
  calc riemannianDistance (I := I) g p q
      ≤ curveLength (I := I) g γ 0 1 := hd_le
    _ ≤ Real.sqrt (mu * ‖v‖ ^ 2) := hlen_le
    _ = Real.sqrt mu * ‖v‖ := hsq

/-! ## Smooth path-connectivity of a connected manifold -/

/-- **Math.** Around every point of a boundaryless manifold there is an open
neighbourhood (an inverse-chart ball) all of whose points are joined to the
centre by a piecewise smooth curve — the straight chart line. -/
theorem exists_nhds_isPiecewiseSmoothCurve (z : M) :
    ∃ V : Set M, IsOpen V ∧ z ∈ V ∧ ∀ w ∈ V,
      ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧ γ 0 = z ∧ γ 1 = w := by
  obtain ⟨ε, hε, htgt⟩ := Metric.mem_nhds_iff.mp (extChartAt_target_mem_nhds (I := I) z)
  refine ⟨(extChartAt I z).symm '' Metric.ball (extChartAt I z z) ε,
    isOpen_extChartAt_symm_image (I := I) Metric.isOpen_ball htgt,
    mem_extChartAt_symm_image_ball_self (I := I) z hε, ?_⟩
  intro w hw
  obtain ⟨γ, hγ_smooth, hγ0, hγ1, -, -⟩ := exists_chartLine_curve (I := I) htgt hw
  exact ⟨γ, ContMDiffOn.isPiecewiseSmoothCurve (I := I) zero_le_one hγ_smooth, hγ0, hγ1⟩

/-- **Math.** **Piecewise smooth connectivity** (implicit in Petersen §5.3): on
a connected manifold, any two points are joined by a piecewise smooth curve —
so Petersen's curve space `Ω_{p,q}` is never empty and `riemannianDistance` is
a genuine infimum.  The set of points reachable from `p` is open (chart lines
concatenate) and closed (a point whose chart ball meets the reachable set is
reachable through it, reversing the chart line), hence everything by
connectedness. -/
theorem exists_isPiecewiseSmoothCurve_connecting [ConnectedSpace M] (p q : M) :
    ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧ γ 0 = p ∧ γ 1 = q := by
  set S := {w : M | ∃ γ : ℝ → M,
    IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧ γ 0 = p ∧ γ 1 = w} with hS_def
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro w₀ ⟨γ₁, hγ₁, hγ₁0, hγ₁1⟩
    obtain ⟨V, hVopen, hVmem, hVcurve⟩ := exists_nhds_isPiecewiseSmoothCurve (I := I) w₀
    refine mem_of_superset (hVopen.mem_nhds hVmem) ?_
    intro w hw
    obtain ⟨γ₂, hγ₂, hγ₂0, hγ₂1⟩ := hVcurve w hw
    have hglue : γ₁ 1 = γ₂ 0 := by rw [hγ₁1, hγ₂0]
    exact ⟨curveConcat γ₁ γ₂,
      isPiecewiseSmoothCurve_curveConcat (I := I) hγ₁ hγ₂ hglue,
      by rw [curveConcat_zero]; exact hγ₁0,
      by rw [curveConcat_one]; exact hγ₂1⟩
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro w₀ hw₀
    obtain ⟨V, hVopen, hVmem, hVcurve⟩ := exists_nhds_isPiecewiseSmoothCurve (I := I) w₀
    refine mem_of_superset (hVopen.mem_nhds hVmem) ?_
    intro w hw hwS
    apply hw₀
    obtain ⟨γ₁, hγ₁, hγ₁0, hγ₁1⟩ := hwS
    obtain ⟨γ₂, hγ₂, hγ₂0, hγ₂1⟩ := hVcurve w hw
    -- reverse the chart line from `w₀` to `w`
    set γ₂' : ℝ → M := fun s => γ₂ (0 + 1 - s) with hγ₂'_def
    have hγ₂' : IsPiecewiseSmoothCurve (I := I) γ₂' 0 1 :=
      isPiecewiseSmoothCurve_comp_const_sub (I := I) hγ₂
    have hγ₂'0 : γ₂' 0 = w := by
      show γ₂ (0 + 1 - 0) = w
      norm_num
      exact hγ₂1
    have hγ₂'1 : γ₂' 1 = w₀ := by
      show γ₂ (0 + 1 - 1) = w₀
      norm_num
      exact hγ₂0
    have hglue : γ₁ 1 = γ₂' 0 := by rw [hγ₁1, hγ₂'0]
    exact ⟨curveConcat γ₁ γ₂',
      isPiecewiseSmoothCurve_curveConcat (I := I) hγ₁ hγ₂' hglue,
      by rw [curveConcat_zero]; exact hγ₁0,
      by rw [curveConcat_one]; exact hγ₂'1⟩
  have hSne : S.Nonempty :=
    ⟨p, fun _ => p, isPiecewiseSmoothCurve_const (I := I) p zero_le_one, rfl, rfl⟩
  have hSuniv : S = univ := (IsClopen.eq_univ ⟨hSclosed, hSopen⟩) hSne
  have : q ∈ S := hSuniv ▸ mem_univ q
  exact this

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-distance`, triangle-inequality
clause, connected case): on a connected manifold the triangle inequality
`|pr| ≤ |pq| + |qr|` holds unconditionally, since any two points are joined by
a piecewise smooth curve. -/
theorem riemannianDistance_triangle_of_connected [ConnectedSpace M]
    (g : RiemannianMetric I M) (p q r : M) :
    riemannianDistance (I := I) g p r ≤
      riemannianDistance (I := I) g p q + riemannianDistance (I := I) g q r :=
  riemannianDistance_triangle (I := I) g p q r
    (exists_isPiecewiseSmoothCurve_connecting (I := I) p q)
    (exists_isPiecewiseSmoothCurve_connecting (I := I) q r)

/-! ## The lower estimate for the distance -/

/-- **Math.** **Chart-ball lower estimate for the distance** (packaged): around
every `p` there are `ε₀ > 0` (with the closed chart `ε₀`-ball inside the chart
target) and a Gram lower bound `λ > 0` on the corresponding compact chart
piece such that for every radius `0 < ε ≤ ε₀`, any point outside the
inverse-chart image of the open chart `ε`-ball is at distance at least
`√λ ε` from `p`: every connecting curve first exits the chart ball
(`sqrt_mul_le_curveLength_of_exit`). -/
theorem exists_sqrt_mul_le_riemannianDistance [T2Space M] [ConnectedSpace M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ ε₀ > (0 : ℝ), Metric.closedBall (extChartAt I p p) ε₀ ⊆ (extChartAt I p).target ∧
      ∃ lam > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ q : M,
        q ∉ (extChartAt I p).symm '' Metric.ball (extChartAt I p p) ε →
        Real.sqrt lam * ε ≤ riemannianDistance (I := I) g p q := by
  obtain ⟨ε₀, hε₀, htgt⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (extChartAt_target_mem_nhds (I := I) p)
  set C := (extChartAt I p).symm '' Metric.closedBall (extChartAt I p p) ε₀ with hC_def
  have hCcomp : IsCompact C :=
    (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm p).mono htgt)
  have hCsub : C ⊆ (chartAt H p).source := by
    rintro q ⟨y, hy, rfl⟩
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I p).map_target (htgt hy)
  obtain ⟨lam, hlam, hbound⟩ := exists_forall_le_chartMetricInner (I := I) g hCcomp hCsub
  refine ⟨ε₀, hε₀, htgt, lam, hlam, ?_⟩
  intro ε hε hεε₀ q hq
  have hne : {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
      γ 0 = p ∧ γ 1 = q ∧ L = curveLength (I := I) g γ 0 1}.Nonempty := by
    obtain ⟨γ, hγ, h0, h1⟩ := exists_isPiecewiseSmoothCurve_connecting (I := I) p q
    exact ⟨curveLength (I := I) g γ 0 1, γ, hγ, h0, h1, rfl⟩
  refine le_csInf hne ?_
  rintro L ⟨γ, hγ, h0, h1, rfl⟩
  refine sqrt_mul_le_curveLength_of_exit (I := I) g hε hεε₀ htgt hlam hbound hγ h0 ?_
  exact ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [h1]; exact hq⟩

/-! ## Petersen Thm. 5.3.8 — the metric topology is the manifold topology -/

variable [T2Space M] [ConnectedSpace M]

/-- **Math.** Petersen Thm. 5.3.8 (`thm:pet-ch5-metric-topology`), positivity
clause: `|pq| = 0` forces `p = q`.  If `q ≠ p` then either `q` lies outside
the comparison chart ball at `p` — and then `|pq| ≥ √λ ε₀ > 0` — or it lies
inside, at chart displacement `δ > 0`, and then `|pq| ≥ √λ δ > 0`. -/
theorem eq_of_riemannianDistance_eq_zero (g : RiemannianMetric I M) {p q : M}
    (h : riemannianDistance (I := I) g p q = 0) : p = q := by
  by_contra hne
  obtain ⟨ε₀, hε₀, htgt, lam, hlam, hLB⟩ :=
    exists_sqrt_mul_le_riemannianDistance (I := I) g p
  have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  by_cases hq : q ∈ (extChartAt I p).symm '' Metric.ball (extChartAt I p p) ε₀
  · obtain ⟨y, hy_ball, hy_eq⟩ := hq
    have hy_tgt : y ∈ (extChartAt I p).target :=
      (Metric.ball_subset_closedBall.trans htgt) hy_ball
    have hy_ne : y ≠ extChartAt I p p := by
      rintro rfl
      apply hne
      rw [← hy_eq]
      exact ((extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)).symm
    set δ := ‖y - extChartAt I p p‖ with hδ_def
    have hδ_pos : 0 < δ := by
      rw [hδ_def, norm_pos_iff]
      exact sub_ne_zero_of_ne hy_ne
    have hδ_le : δ ≤ ε₀ := by
      have := Metric.mem_ball.mp hy_ball
      rw [dist_eq_norm] at this
      exact this.le
    have hnot : q ∉ (extChartAt I p).symm '' Metric.ball (extChartAt I p p) δ := by
      rintro ⟨y', hy'_ball, hy'_eq⟩
      have hy'_tgt : y' ∈ (extChartAt I p).target :=
        (Metric.ball_subset_ball hδ_le |>.trans
          (Metric.ball_subset_closedBall.trans htgt)) hy'_ball
      have hinj : y' = y := by
        have h1 : (extChartAt I p).symm y' = (extChartAt I p).symm y := by
          rw [hy'_eq, hy_eq]
        have h2 := congrArg (extChartAt I p) h1
        rwa [(extChartAt I p).right_inv hy'_tgt, (extChartAt I p).right_inv hy_tgt] at h2
      rw [hinj] at hy'_ball
      have := Metric.mem_ball.mp hy'_ball
      rw [dist_eq_norm] at this
      exact absurd this (lt_irrefl δ)
    have hge := hLB δ hδ_pos hδ_le q hnot
    rw [h] at hge
    exact absurd hge (not_le.mpr (by positivity))
  · have hge := hLB ε₀ hε₀ le_rfl q hq
    rw [h] at hge
    exact absurd hge (not_le.mpr (by positivity))

/-- **Math.** Petersen Thm. 5.3.8 (`thm:pet-ch5-metric-topology`), topology
clause: a set is open in the manifold topology exactly when around each of its
points it contains a `riemannianDistance`-ball.  Forward: the first-exit lower
estimate confines small metric balls to inverse-chart balls; backward: the
chart-line upper estimate places an inverse-chart ball inside any metric
ball. -/
theorem isOpen_iff_riemannianDistance (g : RiemannianMetric I M) (s : Set M) :
    IsOpen s ↔ ∀ p ∈ s, ∃ ε > (0 : ℝ), ∀ q : M,
      riemannianDistance (I := I) g p q < ε → q ∈ s := by
  constructor
  · intro hs p hp
    obtain ⟨ε₀, hε₀, htgt, lam, hlam, hLB⟩ :=
      exists_sqrt_mul_le_riemannianDistance (I := I) g p
    -- shrink the chart ball into `s`
    have hs' : s ∩ (extChartAt I p).source ∈ 𝓝 p :=
      inter_mem (hs.mem_nhds hp) (extChartAt_source_mem_nhds (I := I) p)
    have himg : extChartAt I p '' (s ∩ (extChartAt I p).source)
        ∈ 𝓝 (extChartAt I p p) :=
      extChartAt_image_nhds_mem_nhds_of_boundaryless hs'
    obtain ⟨δ', hδ', hball⟩ := Metric.mem_nhds_iff.mp himg
    set δ := min δ' ε₀ with hδ_def
    have hδ_pos : 0 < δ := lt_min hδ' hε₀
    refine ⟨Real.sqrt lam * δ, by positivity, ?_⟩
    intro q hq
    by_contra hqs
    have hnot : q ∉ (extChartAt I p).symm '' Metric.ball (extChartAt I p p) δ := by
      rintro ⟨y, hy_ball, hy_eq⟩
      have hy_img : y ∈ extChartAt I p '' (s ∩ (extChartAt I p).source) :=
        hball ((Metric.ball_subset_ball (min_le_left _ _)) hy_ball)
      obtain ⟨a, ⟨has, ha_src⟩, ha_eq⟩ := hy_img
      have : q = a := by
        rw [← hy_eq, ← ha_eq]
        exact (extChartAt I p).left_inv ha_src
      exact hqs (this ▸ has)
    exact absurd (hLB δ hδ_pos (min_le_right _ _) q hnot) (not_le.mpr hq)
  · intro hs
    rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨ε, hε, hball⟩ := hs p hp
    obtain ⟨ε₁, hε₁, htgt, mu, hmu, hUB⟩ :=
      exists_riemannianDistance_le_sqrt_mul (I := I) g p
    have hsqmu_pos : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
    set ρ := min ε₁ (ε / (Real.sqrt mu + 1)) with hρ_def
    have hρ_pos : 0 < ρ := lt_min hε₁ (by positivity)
    have hkey : Real.sqrt mu * ρ < ε := by
      have h1 : Real.sqrt mu * ρ ≤ Real.sqrt mu * (ε / (Real.sqrt mu + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.sqrt_nonneg mu)
      have h2 : Real.sqrt mu * (ε / (Real.sqrt mu + 1)) < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [hsqmu_pos, hε]
      linarith
    have hVsub : (extChartAt I p).symm '' Metric.ball (extChartAt I p p) ρ ⊆ s := by
      rintro q ⟨y, hy_ball, hy_eq⟩
      have hq_mem : q ∈ (extChartAt I p).symm '' Metric.ball (extChartAt I p p) ε₁ :=
        ⟨y, (Metric.ball_subset_ball (min_le_left _ _)) hy_ball, hy_eq⟩
      have hy_tgt : y ∈ (extChartAt I p).target :=
        (Metric.ball_subset_closedBall.trans htgt)
          ((Metric.ball_subset_ball (min_le_left _ _)) hy_ball)
      have hxq : extChartAt I p q = y := by
        rw [← hy_eq]
        exact (extChartAt I p).right_inv hy_tgt
      have hnorm_lt : ‖extChartAt I p q - extChartAt I p p‖ < ρ := by
        rw [hxq, ← dist_eq_norm]
        exact Metric.mem_ball.mp hy_ball
      have hd_lt : riemannianDistance (I := I) g p q < ε := by
        calc riemannianDistance (I := I) g p q
            ≤ Real.sqrt mu * ‖extChartAt I p q - extChartAt I p p‖ := hUB q hq_mem
          _ < Real.sqrt mu * ρ := by
              exact mul_lt_mul_of_pos_left hnorm_lt hsqmu_pos
          _ < ε := hkey
      exact hball q hd_lt
    have hball_tgt : Metric.ball (extChartAt I p p) ρ ⊆ (extChartAt I p).target :=
      (Metric.ball_subset_ball (min_le_left _ _)).trans
        (Metric.ball_subset_closedBall.trans htgt)
    exact mem_of_superset
      ((isOpen_extChartAt_symm_image (I := I) Metric.isOpen_ball hball_tgt).mem_nhds
        (mem_extChartAt_symm_image_ball_self (I := I) p hρ_pos))
      hVsub

/-- **Math.** Petersen Thm. 5.3.8 (`thm:pet-ch5-metric-topology`), packaged:
on a connected manifold the Riemannian distance is a genuine metric — it is
symmetric, satisfies the triangle inequality, separates points, and the open
sets it defines are exactly the manifold-topology open sets.  The `MetricSpace`
structure is built by `MetricSpace.ofDistTopology`, so its topology is
**definitionally** the manifold topology. -/
@[reducible]
def riemannianMetricSpace (g : RiemannianMetric I M) : MetricSpace M :=
  MetricSpace.ofDistTopology (riemannianDistance (I := I) g)
    (riemannianDistance_self (I := I) g)
    (riemannianDistance_comm (I := I) g)
    (riemannianDistance_triangle_of_connected (I := I) g)
    (isOpen_iff_riemannianDistance (I := I) g)
    (fun _ _ h => eq_of_riemannianDistance_eq_zero (I := I) g h)

/-- **Math.** Petersen Thm. 5.3.8 (`thm:pet-ch5-metric-topology`): **the metric
topology induced by the Riemannian distance coincides with the manifold
topology** — by construction of `riemannianMetricSpace` through
`MetricSpace.ofDistTopology`, the equality holds definitionally. -/
theorem riemannianDistance_inducesManifoldTopology (g : RiemannianMetric I M) :
    (riemannianMetricSpace (I := I) g).toUniformSpace.toTopologicalSpace
      = ‹TopologicalSpace M› := rfl

/-- **Math.** Petersen Cor. 5.3.9 (`cor:pet-ch5-compact-complete-metric`):
**a compact manifold is metrically complete** — the metric topology is the
manifold topology, which is compact, and a compact uniform space is
complete. -/
theorem compactManifold_metricallyComplete [CompactSpace M] (g : RiemannianMetric I M) :
    @CompleteSpace M (riemannianMetricSpace (I := I) g).toUniformSpace :=
  @complete_of_compact M (riemannianMetricSpace (I := I) g).toUniformSpace
    ‹CompactSpace M›

end Boundaryless

end PetersenLib
