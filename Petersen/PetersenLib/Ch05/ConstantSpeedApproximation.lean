import PetersenLib.Ch05.PiecewiseArclength

/-!
# Petersen Ch. 5, §5.3 — approximation by constant-speed curves (Cor. 5.3.10)

Petersen's Corollary 5.3.10 (`cor:pet-ch5-regular-curve-approx`): for a
piecewise smooth curve `c ∈ Ω_{p,q}` and `ε > 0` there is a constant-speed
curve `c̄ ∈ Ω_{p,q}` with `L(c̄) ≤ (1+ε) L(c)`.

Following Petersen (p. 198), the proof replaces `c` by a **chart polygon**: on
a chart ball around each point the Gram pairing is squeezed between
`(1−η)⟨·,·⟩₀` and `(1+η)⟨·,·⟩₀`, where `⟨·,·⟩₀` is the (constant) Gram pairing
at the centre; straight chart segments between consecutive sample points of
`c` are then regular curves whose `g`-length exceeds the corresponding piece
of `c` by a factor at most `√((1+η)/(1−η)) ≤ 1+ε`.  The polygon is a
piecewise regular curve, so the arclength reparametrization
(`prop:pet-ch5-arclength-reparametrization`,
`piecewiseRegularCurve_arclengthReparametrization`) makes it unit-speed, and
an affine rescaling to `[0,1]` makes it constant-speed.

Main pieces:

* `metricInner_sq_le_mul` — Cauchy–Schwarz for `g_x`.
* `exists_chartBall_gram_comparison` — the sharp two-sided comparison of the
  chart Gram pairing with the centre pairing on a small chart ball.
* `sqrt_gram_lower_bound_of_contMDiffOn` / `sqrt_gram_lower_bound_piecewise`
  — the centre-norm displacement lower bound for the length (the straight
  line is shortest for the constant centre metric, by Cauchy–Schwarz and the
  fundamental theorem of calculus).
* `exists_regular_chartLine` — the straight chart segment between two points
  of the ball: a regular smooth curve with the matching upper length bound.
* `approximateByConstantSpeedCurve` — Corollary 5.3.10.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open scoped Manifold Topology ContDiff Interval

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Cauchy–Schwarz for the metric inner product -/

/-- **Math.** **Cauchy–Schwarz** for the Riemannian inner product:
`g_x(V, W)² ≤ g_x(V, V) g_x(W, W)`, by the discriminant of the nonnegative
quadratic `t ↦ g_x(V + tW, V + tW)`. -/
theorem metricInner_sq_le_mul (g : RiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) :
    g.metricInner x V W ^ 2 ≤ g.metricInner x V V * g.metricInner x W W := by
  have key : ∀ t : ℝ, 0 ≤ g.metricInner x W W * (t * t)
      + 2 * g.metricInner x V W * t + g.metricInner x V V := by
    intro t
    have h := g.metricInner_self_nonneg x (V + t • W)
    have expand : g.metricInner x (V + t • W) (V + t • W)
        = g.metricInner x W W * (t * t) + 2 * g.metricInner x V W * t
          + g.metricInner x V V := by
      simp only [RiemannianMetric.metricInner_add_left,
        RiemannianMetric.metricInner_add_right, RiemannianMetric.metricInner_smul_left,
        RiemannianMetric.metricInner_smul_right]
      rw [g.metricInner_comm x W V]
      ring
    rw [expand] at h
    exact h
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-! ## The chart Gram pairing at points of the chart target -/

/-- **Math.** At a point of the chart target the chart Gram pairing is
nonnegative on the diagonal (it is the metric of the pulled-back tangent
vectors). -/
theorem chartMetricInner_self_nonneg_of_mem_target (g : RiemannianMetric I M)
    {α : M} {y : E} (hy : y ∈ (extChartAt I α).target) (a : E) :
    0 ≤ chartMetricInner (I := I) g α y a a := by
  have hx : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  have hxy : extChartAt I α ((extChartAt I α).symm y) = y :=
    (extChartAt I α).right_inv hy
  rw [← hxy, chartMetricInner_eq_inner (I := I) g hx]
  exact g.metricInner_self_nonneg _ _

/-- **Math.** **Cauchy–Schwarz for the chart Gram pairing** at a point of the
chart target: `⟨a, b⟩_y² ≤ ⟨a, a⟩_y ⟨b, b⟩_y`. -/
theorem chartMetricInner_sq_le_mul_of_mem_target (g : RiemannianMetric I M)
    {α : M} {y : E} (hy : y ∈ (extChartAt I α).target) (a b : E) :
    chartMetricInner (I := I) g α y a b ^ 2
      ≤ chartMetricInner (I := I) g α y a a * chartMetricInner (I := I) g α y b b := by
  have hx : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  have hxy : extChartAt I α ((extChartAt I α).symm y) = y :=
    (extChartAt I α).right_inv hy
  rw [← hxy, chartMetricInner_eq_inner (I := I) g hx,
    chartMetricInner_eq_inner (I := I) g hx, chartMetricInner_eq_inner (I := I) g hx]
  exact metricInner_sq_le_mul (I := I) g _ _ _

/-- **Math.** Cauchy–Schwarz, product form: `⟨a, b⟩_y ≤ √⟨a, a⟩_y √⟨b, b⟩_y`
at a point of the chart target. -/
theorem chartMetricInner_le_sqrt_mul_sqrt_of_mem_target (g : RiemannianMetric I M)
    {α : M} {y : E} (hy : y ∈ (extChartAt I α).target) (a b : E) :
    chartMetricInner (I := I) g α y a b
      ≤ Real.sqrt (chartMetricInner (I := I) g α y a a)
        * Real.sqrt (chartMetricInner (I := I) g α y b b) := by
  have h1 : chartMetricInner (I := I) g α y a b
      ≤ |chartMetricInner (I := I) g α y a b| := le_abs_self _
  have h2 : |chartMetricInner (I := I) g α y a b|
      = Real.sqrt (chartMetricInner (I := I) g α y a b ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [h2] at h1
  refine h1.trans ?_
  rw [← Real.sqrt_mul (chartMetricInner_self_nonneg_of_mem_target (I := I) g hy a)]
  exact Real.sqrt_le_sqrt (chartMetricInner_sq_le_mul_of_mem_target (I := I) g hy a b)

/-- **Math.** The chart Gram pairing of the zero vector vanishes. -/
theorem chartMetricInner_zero_right (g : RiemannianMetric I M) (α : M) (y a : E) :
    chartMetricInner (I := I) g α y a 0 = 0 := by
  simp [chartMetricInner_def, Geodesic.chartCoord_zero]

/-- **Math.** The chart Gram pairing of the zero vector vanishes. -/
theorem chartMetricInner_zero_self (g : RiemannianMetric I M) (α : M) (y : E) :
    chartMetricInner (I := I) g α y 0 0 = 0 :=
  chartMetricInner_zero_right (I := I) g α y 0

/-- **Math.** **Minkowski inequality** for the chart Gram pairing at a point
of the chart target: `√⟨a+b, a+b⟩_y ≤ √⟨a, a⟩_y + √⟨b, b⟩_y`. -/
theorem sqrt_chartMetricInner_add_le_of_mem_target (g : RiemannianMetric I M)
    {α : M} {y : E} (hy : y ∈ (extChartAt I α).target) (a b : E) :
    Real.sqrt (chartMetricInner (I := I) g α y (a + b) (a + b))
      ≤ Real.sqrt (chartMetricInner (I := I) g α y a a)
        + Real.sqrt (chartMetricInner (I := I) g α y b b) := by
  set Qa := chartMetricInner (I := I) g α y a a with hQa
  set Qb := chartMetricInner (I := I) g α y b b with hQb
  have hQa0 : 0 ≤ Qa := chartMetricInner_self_nonneg_of_mem_target (I := I) g hy a
  have hQb0 : 0 ≤ Qb := chartMetricInner_self_nonneg_of_mem_target (I := I) g hy b
  have hexpand : chartMetricInner (I := I) g α y (a + b) (a + b)
      = Qa + chartMetricInner (I := I) g α y a b + chartMetricInner (I := I) g α y b a
        + Qb := by
    rw [chartMetricInner_add_left, chartMetricInner_add_right, chartMetricInner_add_right]
    ring
  have hba : chartMetricInner (I := I) g α y b a
      ≤ Real.sqrt Qa * Real.sqrt Qb := by
    have := chartMetricInner_le_sqrt_mul_sqrt_of_mem_target (I := I) g hy b a
    rw [← hQa, ← hQb] at this
    linarith [this]
  have hab : chartMetricInner (I := I) g α y a b
      ≤ Real.sqrt Qa * Real.sqrt Qb := by
    have := chartMetricInner_le_sqrt_mul_sqrt_of_mem_target (I := I) g hy a b
    rw [← hQa, ← hQb] at this
    linarith [this]
  have hle : chartMetricInner (I := I) g α y (a + b) (a + b)
      ≤ (Real.sqrt Qa + Real.sqrt Qb) ^ 2 := by
    rw [hexpand]
    have hsqa : Real.sqrt Qa ^ 2 = Qa := Real.sq_sqrt hQa0
    have hsqb : Real.sqrt Qb ^ 2 = Qb := Real.sq_sqrt hQb0
    nlinarith [hab, hba]
  calc Real.sqrt (chartMetricInner (I := I) g α y (a + b) (a + b))
      ≤ Real.sqrt ((Real.sqrt Qa + Real.sqrt Qb) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt Qa + Real.sqrt Qb :=
        Real.sqrt_sq (by positivity)

section Boundaryless

variable [I.Boundaryless]

/-! ## The sharp two-sided Gram comparison on a small chart ball -/

/-- **Math.** **Sharp two-sided Gram comparison** (Petersen p. 197–198, the
`λ₀, μ₀` of the proofs of Thm. 5.3.8 and Cor. 5.3.10, sharpened so that the
ratio tends to `1`): for every `α ∈ M` and `η > 0` there is a chart ball
around `φ_α(α)` inside the chart target on which the chart Gram pairing is
squeezed between `(1−η)` and `(1+η)` times the **centre** pairing
`⟨·,·⟩_{φ_α(α)}`.  The Gram entries are continuous at the centre, and the
centre pairing dominates a multiple of the Euclidean norm. -/
theorem exists_chartBall_gram_comparison (g : RiemannianMetric I M) (α : M)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε > (0 : ℝ),
      Metric.closedBall (extChartAt I α α) ε ⊆ (extChartAt I α).target ∧
      ∀ y ∈ Metric.closedBall (extChartAt I α α) ε, ∀ u : E,
        (1 - η) * chartMetricInner (I := I) g α (extChartAt I α α) u u
            ≤ chartMetricInner (I := I) g α y u u ∧
          chartMetricInner (I := I) g α y u u
            ≤ (1 + η) * chartMetricInner (I := I) g α (extChartAt I α α) u u := by
  classical
  set x₀ : E := extChartAt I α α with hx₀_def
  have hx₀tgt : x₀ ∈ (extChartAt I α).target := mem_extChartAt_target (I := I) α
  -- the centre pairing dominates a multiple of the Euclidean norm
  obtain ⟨lam, hlam, hlow⟩ := exists_forall_le_chartMetricInner (I := I) g
    (isCompact_singleton (x := α)) (by
      rw [Set.singleton_subset_iff]; exact mem_chart_source H α)
  have hlow₀ : ∀ u : E, lam * ‖u‖ ^ 2
      ≤ chartMetricInner (I := I) g α x₀ u u := fun u =>
    hlow α (Set.mem_singleton α) u
  -- the summed Gram-entry deviation, weighted by the coordinate norms
  set S : E → ℝ := fun y => ∑ i, ∑ j,
    |chartGramOnE (I := I) g α i j y - chartGramOnE (I := I) g α i j x₀|
      * (‖Geodesic.chartCoordFunctional (E := E) i‖
          * ‖Geodesic.chartCoordFunctional (E := E) j‖) with hS_def
  have hScont : ContinuousAt S x₀ := by
    simp only [hS_def]
    refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => ?_
    have hGij : ContinuousAt (chartGramOnE (I := I) g α i j) x₀ :=
      ((chartGramOnE_contDiffOn (I := I) g α i j).contDiffAt
        (extChartAt_target_mem_nhds' (I := I) hx₀tgt)).continuousAt
    exact (((hGij.sub continuousAt_const).abs).mul continuousAt_const)
  have hS0 : S x₀ = 0 := by
    simp [hS_def]
  -- a closed ball on which `S < η λ` and which sits inside the target
  have hev : {y : E | S y < η * lam} ∩ (extChartAt I α).target ∈ 𝓝 x₀ := by
    refine Filter.inter_mem ?_ (extChartAt_target_mem_nhds' (I := I) hx₀tgt)
    have : S ⁻¹' Iio (η * lam) ∈ 𝓝 x₀ := by
      refine hScont.preimage_mem_nhds (Iio_mem_nhds ?_)
      rw [hS0]
      positivity
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hev
  refine ⟨ε, hε, fun y hy => (hball hy).2, ?_⟩
  intro y hy u
  have hSy : S y < η * lam := (hball hy).1
  -- the deviation estimate `|⟨u,u⟩_y − ⟨u,u⟩_{x₀}| ≤ S y ‖u‖²`
  have hcoord : ∀ i : Fin (Module.finrank ℝ E), |Geodesic.chartCoord (E := E) i u|
      ≤ ‖Geodesic.chartCoordFunctional (E := E) i‖ * ‖u‖ := by
    intro i
    rw [← Geodesic.chartCoordFunctional_apply (E := E) i u, ← Real.norm_eq_abs]
    exact (Geodesic.chartCoordFunctional (E := E) i).le_opNorm u
  have hdev : |chartMetricInner (I := I) g α y u u
      - chartMetricInner (I := I) g α x₀ u u| ≤ S y * ‖u‖ ^ 2 := by
    have hsub : chartMetricInner (I := I) g α y u u
        - chartMetricInner (I := I) g α x₀ u u
        = ∑ i, ∑ j, (chartGramOnE (I := I) g α i j y - chartGramOnE (I := I) g α i j x₀)
            * Geodesic.chartCoord (E := E) i u * Geodesic.chartCoord (E := E) j u := by
      rw [chartMetricInner_def, chartMetricInner_def, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsub]
    calc |∑ i, ∑ j, (chartGramOnE (I := I) g α i j y - chartGramOnE (I := I) g α i j x₀)
            * Geodesic.chartCoord (E := E) i u * Geodesic.chartCoord (E := E) j u|
        ≤ ∑ i, |∑ j, (chartGramOnE (I := I) g α i j y - chartGramOnE (I := I) g α i j x₀)
            * Geodesic.chartCoord (E := E) i u * Geodesic.chartCoord (E := E) j u| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(chartGramOnE (I := I) g α i j y - chartGramOnE (I := I) g α i j x₀)
            * Geodesic.chartCoord (E := E) i u * Geodesic.chartCoord (E := E) j u| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |chartGramOnE (I := I) g α i j y - chartGramOnE (I := I) g α i j x₀|
            * (‖Geodesic.chartCoordFunctional (E := E) i‖
                * ‖Geodesic.chartCoordFunctional (E := E) j‖) * ‖u‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          have hi := hcoord i
          have hj := hcoord j
          have habs : |chartGramOnE (I := I) g α i j y
              - chartGramOnE (I := I) g α i j x₀| ≥ 0 := abs_nonneg _
          calc |chartGramOnE (I := I) g α i j y - chartGramOnE (I := I) g α i j x₀|
                * |Geodesic.chartCoord (E := E) i u| * |Geodesic.chartCoord (E := E) j u|
              ≤ |chartGramOnE (I := I) g α i j y - chartGramOnE (I := I) g α i j x₀|
                * (‖Geodesic.chartCoordFunctional (E := E) i‖ * ‖u‖)
                * (‖Geodesic.chartCoordFunctional (E := E) j‖ * ‖u‖) := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left hi (abs_nonneg _)) hj
                  (abs_nonneg _) ?_
                exact mul_nonneg (abs_nonneg _)
                  (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            _ = |chartGramOnE (I := I) g α i j y - chartGramOnE (I := I) g α i j x₀|
                * (‖Geodesic.chartCoordFunctional (E := E) i‖
                    * ‖Geodesic.chartCoordFunctional (E := E) j‖) * ‖u‖ ^ 2 := by
                ring
      _ = S y * ‖u‖ ^ 2 := by
          simp only [hS_def]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
  have hηlam : S y * ‖u‖ ^ 2 ≤ η * (lam * ‖u‖ ^ 2) := by
    have : S y * ‖u‖ ^ 2 ≤ (η * lam) * ‖u‖ ^ 2 := by
      have h2 : (0:ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right hSy.le h2
    linarith [this]
  have hkey : |chartMetricInner (I := I) g α y u u
      - chartMetricInner (I := I) g α x₀ u u|
      ≤ η * chartMetricInner (I := I) g α x₀ u u := by
    refine hdev.trans (hηlam.trans ?_)
    exact mul_le_mul_of_nonneg_left (hlow₀ u) hη.le
  obtain ⟨h1, h2⟩ := abs_le.mp hkey
  constructor
  · nlinarith [h1]
  · nlinarith [h2]

/-! ## The centre-norm displacement lower bound -/

/-- **Math.** **Centre-norm displacement bound, smooth piece** (Petersen
p. 198): if `γ` is `C^∞` on `[c, d]` with values in the inverse-chart image
of a closed ball carrying the lower Gram bound `(1−η)⟨·,·⟩₀`, then
`√((1−η)⟨Δx, Δx⟩₀) ≤ L(γ)|_c^d` for the chart displacement
`Δx = φ(γ d) − φ(γ c)`.  For the constant centre metric the straight line is
shortest: pair the displacement against the constant functional
`⟨Δx, ·⟩₀` and use Cauchy–Schwarz plus the fundamental theorem of
calculus. -/
theorem sqrt_gram_lower_bound_of_contMDiffOn (g : RiemannianMetric I M)
    {α : M} {η ε : ℝ} (hη1 : η < 1)
    (hball : Metric.closedBall (extChartAt I α α) ε ⊆ (extChartAt I α).target)
    (hlow : ∀ y ∈ Metric.closedBall (extChartAt I α α) ε, ∀ u : E,
      (1 - η) * chartMetricInner (I := I) g α (extChartAt I α α) u u
        ≤ chartMetricInner (I := I) g α y u u)
    {γ : ℝ → M} {c d : ℝ} (hcd : c ≤ d)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc c d))
    (hmem : ∀ s ∈ Icc c d,
      γ s ∈ (extChartAt I α).symm '' Metric.closedBall (extChartAt I α α) ε) :
    Real.sqrt ((1 - η) * chartMetricInner (I := I) g α (extChartAt I α α)
        (extChartAt I α (γ d) - extChartAt I α (γ c))
        (extChartAt I α (γ d) - extChartAt I α (γ c)))
      ≤ curveLength (I := I) g γ c d := by
  classical
  set x₀ : E := extChartAt I α α with hx₀_def
  have hx₀tgt : x₀ ∈ (extChartAt I α).target := mem_extChartAt_target (I := I) α
  have hη' : (0:ℝ) < 1 - η := by linarith
  rcases hcd.eq_or_lt with rfl | hlt
  · rw [sub_self, chartMetricInner_zero_self, mul_zero, Real.sqrt_zero, curveLength_self]
  -- chart membership facts
  have hchart : ∀ s ∈ Icc c d,
      extChartAt I α (γ s) ∈ Metric.closedBall x₀ ε := by
    intro s hs
    obtain ⟨y, hy, hyγ⟩ := hmem s hs
    rw [← hyγ, (extChartAt I α).right_inv (hball hy)]
    exact hy
  have hsrc : ∀ s ∈ Icc c d, γ s ∈ (extChartAt I α).source := by
    intro s hs
    obtain ⟨y, hy, hyγ⟩ := hmem s hs
    rw [← hyγ]
    exact (extChartAt I α).map_target (hball hy)
  -- the fixed-chart reading and its derivative
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
      ((hxsmooth.differentiableOn (by norm_num)) s
        (Ioo_subset_Icc_self hs)).differentiableAt hnhds
    have hDs : D s = deriv x s := derivWithin_of_mem_nhds hnhds
    rw [hDs]
    exact hdiff.hasDerivAt
  have hDint : IntervalIntegrable D volume c d := hDcont.intervalIntegrable_of_Icc hlt.le
  have hFTC : (∫ s in c..d, D s) = x d - x c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlt.le hxsmooth.continuousOn
      hD_deriv hDint
  -- the displacement and its centre pairing
  set w : E := x d - x c with hw_def
  set Q : ℝ := chartMetricInner (I := I) g α x₀ w w with hQ_def
  have hQ0 : 0 ≤ Q := chartMetricInner_self_nonneg_of_mem_target (I := I) g hx₀tgt w
  rcases hQ0.eq_or_lt with hQzero | hQpos
  · -- degenerate displacement: the bound is trivial
    rw [← hQzero, mul_zero, Real.sqrt_zero]
    exact curveLength_nonneg (I := I) g γ hlt.le
  -- the constant functional `⟨w, ·⟩₀` as a continuous linear map
  set Φ : E →L[ℝ] ℝ := ∑ i, ∑ j,
    (chartGramOnE (I := I) g α i j x₀ * Geodesic.chartCoord (E := E) i w) •
      Geodesic.chartCoordFunctional (E := E) j with hΦ_def
  have hΦ_apply : ∀ u : E, Φ u = chartMetricInner (I := I) g α x₀ w u := by
    intro u
    rw [hΦ_def, chartMetricInner_def]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.smul_apply, Geodesic.chartCoordFunctional_apply]
    simp only [smul_eq_mul]
  -- pointwise bound: `Φ(D s) ≤ √Q · √(speed) / √(1−η)`
  have hpt : ∀ s ∈ Ioo c d, Φ (D s)
      ≤ (Real.sqrt Q / Real.sqrt (1 - η))
        * Real.sqrt (curveSpeedSq (I := I) g γ s) := by
    intro s hs
    have hsIcc : s ∈ Icc c d := Ioo_subset_Icc_self hs
    have hsrc_ev : ∀ᶠ r in 𝓝 s, γ r ∈ (extChartAt I α).source := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
      exact hsrc r hr
    have hspeed : curveSpeedSq (I := I) g γ s
        = chartMetricInner (I := I) g α (x s) (D s) (D s) :=
      curveSpeedSq_eq_chartMetricInner_of_hasDerivAt (I := I) g hsrc_ev (hD_deriv s hs)
    -- Cauchy–Schwarz at the centre
    have hCS : Φ (D s) ≤ Real.sqrt Q
        * Real.sqrt (chartMetricInner (I := I) g α x₀ (D s) (D s)) := by
      rw [hΦ_apply (D s)]
      exact chartMetricInner_le_sqrt_mul_sqrt_of_mem_target (I := I) g hx₀tgt w (D s)
    -- centre pairing dominated by the moving pairing
    have hdom : chartMetricInner (I := I) g α x₀ (D s) (D s)
        ≤ curveSpeedSq (I := I) g γ s / (1 - η) := by
      rw [hspeed, le_div_iff₀ hη']
      have := hlow (x s) (hchart s hsIcc) (D s)
      linarith [this]
    have hsq0 : 0 ≤ chartMetricInner (I := I) g α x₀ (D s) (D s) :=
      chartMetricInner_self_nonneg_of_mem_target (I := I) g hx₀tgt (D s)
    have hmono : Real.sqrt (chartMetricInner (I := I) g α x₀ (D s) (D s))
        ≤ Real.sqrt (curveSpeedSq (I := I) g γ s) / Real.sqrt (1 - η) := by
      have h1 := Real.sqrt_le_sqrt hdom
      rwa [Real.sqrt_div (curveSpeedSq_nonneg (I := I) g γ s)] at h1
    calc Φ (D s) ≤ Real.sqrt Q
          * Real.sqrt (chartMetricInner (I := I) g α x₀ (D s) (D s)) := hCS
      _ ≤ Real.sqrt Q * (Real.sqrt (curveSpeedSq (I := I) g γ s) / Real.sqrt (1 - η)) :=
          mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg Q)
      _ = (Real.sqrt Q / Real.sqrt (1 - η)) * Real.sqrt (curveSpeedSq (I := I) g γ s) := by
          ring
  -- FTC for the paired reading
  have hΦFTC : (∫ s in c..d, Φ (D s)) = Q := by
    have hderiv : ∀ s ∈ Ioo c d, HasDerivAt (fun r => Φ (x r)) (Φ (D s)) s := fun s hs =>
      (Φ.hasFDerivAt.comp_hasDerivAt s (hD_deriv s hs))
    have hcont : ContinuousOn (fun r => Φ (x r)) (Icc c d) :=
      Φ.continuous.comp_continuousOn hxsmooth.continuousOn
    have hint : IntervalIntegrable (fun s => Φ (D s)) volume c d :=
      (Φ.continuous.comp_continuousOn hDcont).intervalIntegrable_of_Icc hlt.le
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlt.le hcont hderiv hint
    rw [this, ← Φ.map_sub, hΦ_apply]
  -- integrate the pointwise bound
  have hIntSpeed : IntervalIntegrable
      (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s)) volume c d :=
    ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (I := I) g hlt.le hγ
  have hint1 : IntervalIntegrable (fun s => Φ (D s)) volume c d :=
    (Φ.continuous.comp_continuousOn hDcont).intervalIntegrable_of_Icc hlt.le
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hlt.le hint1
    (hIntSpeed.const_mul (Real.sqrt Q / Real.sqrt (1 - η))) hpt
  rw [hΦFTC, intervalIntegral.integral_const_mul] at hmono
  -- conclude by dividing by `√Q`
  have hQsqrt_pos : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have h1η_pos : 0 < Real.sqrt (1 - η) := Real.sqrt_pos.mpr hη'
  have hstep : Q * Real.sqrt (1 - η)
      ≤ Real.sqrt Q * ∫ s in c..d, Real.sqrt (curveSpeedSq (I := I) g γ s) := by
    have h := mul_le_mul_of_nonneg_right hmono h1η_pos.le
    calc Q * Real.sqrt (1 - η)
        ≤ Real.sqrt Q / Real.sqrt (1 - η)
          * (∫ s in c..d, Real.sqrt (curveSpeedSq (I := I) g γ s))
          * Real.sqrt (1 - η) := h
      _ = Real.sqrt Q * ∫ s in c..d, Real.sqrt (curveSpeedSq (I := I) g γ s) := by
          field_simp
  have hfinal : Real.sqrt (1 - η) * Real.sqrt Q
      ≤ ∫ s in c..d, Real.sqrt (curveSpeedSq (I := I) g γ s) := by
    nlinarith [hstep, Real.mul_self_sqrt hQ0, hQsqrt_pos, h1η_pos]
  rw [Real.sqrt_mul hη'.le]
  exact hfinal

/-- **Math.** **Centre-norm displacement bound, piecewise clamped version**:
for a piecewise smooth curve `γ` on `[a, b]` and a subinterval
`[a', b'] ⊆ [a, b]` on which `γ` stays in the inverse-chart image of the
comparison ball, `√((1−η)⟨Δx, Δx⟩₀) ≤ L(γ)|_{a'}^{b'}` for the chart
displacement `Δx = φ(γ b') − φ(γ a')`.  Clamp the partition to `[a', b']`,
apply the smooth-piece estimate on each clamped piece, and chain with the
Minkowski inequality of the centre pairing and additivity of the length. -/
theorem sqrt_gram_lower_bound_piecewise (g : RiemannianMetric I M)
    {α : M} {η ε : ℝ} (hη1 : η < 1)
    (hball : Metric.closedBall (extChartAt I α α) ε ⊆ (extChartAt I α).target)
    (hlow : ∀ y ∈ Metric.closedBall (extChartAt I α α) ε, ∀ u : E,
      (1 - η) * chartMetricInner (I := I) g α (extChartAt I α α) u u
        ≤ chartMetricInner (I := I) g α y u u)
    {γ : ℝ → M} {a b a' b' : ℝ} (hγ : IsPiecewiseSmoothCurve (I := I) γ a b)
    (ha' : a' ∈ Icc a b) (hb' : b' ∈ Icc a b) (ha'b' : a' ≤ b')
    (hmem : ∀ s ∈ Icc a' b',
      γ s ∈ (extChartAt I α).symm '' Metric.closedBall (extChartAt I α α) ε) :
    Real.sqrt ((1 - η) * chartMetricInner (I := I) g α (extChartAt I α α)
        (extChartAt I α (γ b') - extChartAt I α (γ a'))
        (extChartAt I α (γ b') - extChartAt I α (γ a')))
      ≤ curveLength (I := I) g γ a' b' := by
  classical
  have hη' : (0:ℝ) < 1 - η := by linarith
  have hx₀tgt : extChartAt I α α ∈ (extChartAt I α).target :=
    mem_extChartAt_target (I := I) α
  have hab : a ≤ b := ha'.1.trans ha'.2
  have hInt := hγ.intervalIntegrable_sqrt_curveSpeedSq (I := I) g
  have hIntsub : ∀ s t : ℝ, s ∈ Icc a b → t ∈ Icc a b →
      IntervalIntegrable (fun τ => Real.sqrt (curveSpeedSq (I := I) g γ τ))
        volume s t := by
    intro s t hs ht
    refine hInt.mono_set (uIcc_subset_uIcc ?_ ?_)
    · rwa [uIcc_of_le hab]
    · rwa [uIcc_of_le hab]
  -- Minkowski for the centre seminorm
  have htri : ∀ x y z : E,
      Real.sqrt ((1 - η) * chartMetricInner (I := I) g α (extChartAt I α α)
          (z - x) (z - x))
        ≤ Real.sqrt ((1 - η) * chartMetricInner (I := I) g α (extChartAt I α α)
            (z - y) (z - y))
          + Real.sqrt ((1 - η) * chartMetricInner (I := I) g α (extChartAt I α α)
              (y - x) (y - x)) := by
    intro x y z
    have hzx : z - x = (z - y) + (y - x) := by abel
    rw [hzx, Real.sqrt_mul hη'.le, Real.sqrt_mul hη'.le, Real.sqrt_mul hη'.le,
      ← mul_add]
    exact mul_le_mul_of_nonneg_left
      (sqrt_chartMetricInner_add_le_of_mem_target (I := I) g hx₀tgt (z - y) (y - x))
      (Real.sqrt_nonneg _)
  obtain ⟨hcont, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  -- the clamped partition
  set w : Fin (n + 1) → ℝ := fun i => min (max (u i) a') b' with hw_def
  have hw_mem : ∀ i, w i ∈ Icc a' b' := fun i =>
    ⟨le_min (le_max_right _ _) ha'b', min_le_right _ _⟩
  have hw_ab : ∀ i, w i ∈ Icc a b := fun i =>
    ⟨ha'.1.trans (hw_mem i).1, (hw_mem i).2.trans hb'.2⟩
  have key : ∀ k : ℕ, ∀ hk : k < n + 1,
      Real.sqrt ((1 - η) * chartMetricInner (I := I) g α (extChartAt I α α)
          (extChartAt I α (γ (w ⟨k, hk⟩)) - extChartAt I α (γ a'))
          (extChartAt I α (γ (w ⟨k, hk⟩)) - extChartAt I α (γ a')))
        ≤ curveLength (I := I) g γ a' (w ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hw0 : w ⟨0, hk⟩ = a' := by
        have h0 : u ⟨0, hk⟩ = a := hu0
        simp only [hw_def, h0]
        rw [max_eq_right ha'.1, min_eq_left ha'b']
      rw [hw0, sub_self, chartMetricInner_zero_self, mul_zero, Real.sqrt_zero,
        curveLength_self]
    | succ k ih =>
      intro hk
      have hkn : k < n + 1 := by omega
      have hkn' : k < n := by omega
      have hcast : (⟨k, hkn⟩ : Fin (n + 1)) = (⟨k, hkn'⟩ : Fin n).castSucc := rfl
      have hsuccc : (⟨k + 1, hk⟩ : Fin (n + 1)) = (⟨k, hkn'⟩ : Fin n).succ := rfl
      have hw_le : w ⟨k, hkn⟩ ≤ w ⟨k + 1, hk⟩ := by
        refine min_le_min (max_le_max ?_ le_rfl) le_rfl
        rw [hcast, hsuccc]
        exact hmono Fin.castSucc_lt_succ.le
      -- the piece estimate on the clamped piece
      have hpiece : Real.sqrt ((1 - η) * chartMetricInner (I := I) g α (extChartAt I α α)
          (extChartAt I α (γ (w ⟨k + 1, hk⟩)) - extChartAt I α (γ (w ⟨k, hkn⟩)))
          (extChartAt I α (γ (w ⟨k + 1, hk⟩)) - extChartAt I α (γ (w ⟨k, hkn⟩))))
          ≤ curveLength (I := I) g γ (w ⟨k, hkn⟩) (w ⟨k + 1, hk⟩) := by
        rcases hw_le.eq_or_lt with heq | hltw
        · rw [heq, sub_self, chartMetricInner_zero_self, mul_zero, Real.sqrt_zero,
            curveLength_self]
        · have hwk_lt_b' : w ⟨k, hkn⟩ < b' :=
            lt_of_lt_of_le hltw (hw_mem ⟨k + 1, hk⟩).2
          have hwk_eq : w ⟨k, hkn⟩ = max (u ⟨k, hkn⟩) a' := by
            rcases le_or_gt (max (u ⟨k, hkn⟩) a') b' with h | h
            · exact min_eq_left h
            · exfalso
              have : w ⟨k, hkn⟩ = b' := min_eq_right h.le
              rw [this] at hwk_lt_b'
              exact lt_irrefl b' hwk_lt_b'
          have hwk1_gt_a' : a' < w ⟨k + 1, hk⟩ :=
            lt_of_le_of_lt (hw_mem ⟨k, hkn⟩).1 hltw
          have hwk1_eq : w ⟨k + 1, hk⟩ = min (u ⟨k + 1, hk⟩) b' := by
            rcases le_or_gt a' (u ⟨k + 1, hk⟩) with h | h
            · simp only [hw_def]
              rw [max_eq_left h]
            · exfalso
              have hmax : max (u ⟨k + 1, hk⟩) a' = a' := max_eq_right h.le
              have : w ⟨k + 1, hk⟩ = a' := by
                simp only [hw_def]
                rw [hmax]
                exact min_eq_left ha'b'
              rw [this] at hwk1_gt_a'
              exact lt_irrefl a' hwk1_gt_a'
          have hsub_piece : Icc (w ⟨k, hkn⟩) (w ⟨k + 1, hk⟩)
              ⊆ Icc (u ⟨k, hkn⟩) (u ⟨k + 1, hk⟩) := by
            apply Icc_subset_Icc
            · rw [hwk_eq]
              exact le_max_left _ _
            · rw [hwk1_eq]
              exact min_le_left _ _
          have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (w ⟨k, hkn⟩) (w ⟨k + 1, hk⟩)) := by
            refine (hsmooth ⟨k, hkn'⟩).mono ?_
            rwa [← hcast, ← hsuccc]
          have hmem' : ∀ s ∈ Icc (w ⟨k, hkn⟩) (w ⟨k + 1, hk⟩),
              γ s ∈ (extChartAt I α).symm ''
                Metric.closedBall (extChartAt I α α) ε := fun s hs =>
            hmem s ⟨(hw_mem ⟨k, hkn⟩).1.trans hs.1, hs.2.trans (hw_mem ⟨k + 1, hk⟩).2⟩
          exact sqrt_gram_lower_bound_of_contMDiffOn (I := I) g hη1 hball hlow
            hw_le hsm hmem'
      -- additivity of the length at the clamp point
      have hadd : curveLength (I := I) g γ a' (w ⟨k + 1, hk⟩)
          = curveLength (I := I) g γ a' (w ⟨k, hkn⟩)
            + curveLength (I := I) g γ (w ⟨k, hkn⟩) (w ⟨k + 1, hk⟩) :=
        curveLength_additive (I := I) g γ
          (hIntsub a' (w ⟨k, hkn⟩) ⟨ha'.1, ha'.2⟩ (hw_ab _))
          (hIntsub (w ⟨k, hkn⟩) (w ⟨k + 1, hk⟩) (hw_ab _) (hw_ab _))
      have hih := ih hkn
      have htri' := htri (extChartAt I α (γ a')) (extChartAt I α (γ (w ⟨k, hkn⟩)))
        (extChartAt I α (γ (w ⟨k + 1, hk⟩)))
      rw [hadd]
      calc Real.sqrt ((1 - η) * chartMetricInner (I := I) g α (extChartAt I α α)
              (extChartAt I α (γ (w ⟨k + 1, hk⟩)) - extChartAt I α (γ a'))
              (extChartAt I α (γ (w ⟨k + 1, hk⟩)) - extChartAt I α (γ a')))
          ≤ Real.sqrt ((1 - η) * chartMetricInner (I := I) g α (extChartAt I α α)
              (extChartAt I α (γ (w ⟨k + 1, hk⟩)) - extChartAt I α (γ (w ⟨k, hkn⟩)))
              (extChartAt I α (γ (w ⟨k + 1, hk⟩)) - extChartAt I α (γ (w ⟨k, hkn⟩))))
            + Real.sqrt ((1 - η) * chartMetricInner (I := I) g α (extChartAt I α α)
                (extChartAt I α (γ (w ⟨k, hkn⟩)) - extChartAt I α (γ a'))
                (extChartAt I α (γ (w ⟨k, hkn⟩)) - extChartAt I α (γ a'))) := htri'
        _ ≤ curveLength (I := I) g γ (w ⟨k, hkn⟩) (w ⟨k + 1, hk⟩)
            + curveLength (I := I) g γ a' (w ⟨k, hkn⟩) := add_le_add hpiece hih
        _ = curveLength (I := I) g γ a' (w ⟨k, hkn⟩)
            + curveLength (I := I) g γ (w ⟨k, hkn⟩) (w ⟨k + 1, hk⟩) := by ring
  have hfinal := key n n.lt_succ_self
  have hlast : (⟨n, n.lt_succ_self⟩ : Fin (n + 1)) = Fin.last n := rfl
  have hwlast : w (Fin.last n) = b' := by
    simp only [hw_def, hun]
    rw [max_eq_left (ha'b'.trans hb'.2), min_eq_right hb'.2]
  rw [hlast, hwlast] at hfinal
  exact hfinal

/-- **Math.** **The straight chart segment between two points of a comparison
ball** (Petersen p. 198): given the two-sided Gram comparison on the closed
`ε`-ball at `α` and two distinct points `p ≠ q` of the inverse-chart image of
the open ball, the chart segment from `p` to `q` is a smooth **regular**
curve (on an open window around `[0,1]`) from `p` to `q` with
`L(σ) ≤ √((1+η)⟨Δx, Δx⟩₀)` for the chart displacement
`Δx = φ(q) − φ(p)`. -/
theorem exists_regular_chartLine (g : RiemannianMetric I M)
    {α : M} {η ε : ℝ} (hη1 : η < 1)
    (hball : Metric.closedBall (extChartAt I α α) ε ⊆ (extChartAt I α).target)
    (hcomp : ∀ y ∈ Metric.closedBall (extChartAt I α α) ε, ∀ u : E,
        (1 - η) * chartMetricInner (I := I) g α (extChartAt I α α) u u
            ≤ chartMetricInner (I := I) g α y u u ∧
          chartMetricInner (I := I) g α y u u
            ≤ (1 + η) * chartMetricInner (I := I) g α (extChartAt I α α) u u)
    {p q : M} (hp : p ∈ (extChartAt I α).symm '' Metric.ball (extChartAt I α α) ε)
    (hq : q ∈ (extChartAt I α).symm '' Metric.ball (extChartAt I α α) ε)
    (hpq : p ≠ q) :
    ∃ (σ : ℝ → M) (Jσ : Set ℝ), IsOpen Jσ ∧ Icc (0:ℝ) 1 ⊆ Jσ ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ Jσ ∧ σ 0 = p ∧ σ 1 = q ∧
      (∀ t ∈ Icc (0:ℝ) 1, curveSpeedSq (I := I) g σ t ≠ 0) ∧
      curveLength (I := I) g σ 0 1
        ≤ Real.sqrt ((1 + η) * chartMetricInner (I := I) g α (extChartAt I α α)
            (extChartAt I α q - extChartAt I α p)
            (extChartAt I α q - extChartAt I α p)) := by
  classical
  have hη' : (0:ℝ) < 1 - η := by linarith
  set x₀ : E := extChartAt I α α with hx₀_def
  obtain ⟨yp, hyp, hpeq⟩ := hp
  obtain ⟨yq, hyq, hqeq⟩ := hq
  have hyp_tgt : yp ∈ (extChartAt I α).target :=
    hball (Metric.ball_subset_closedBall hyp)
  have hyq_tgt : yq ∈ (extChartAt I α).target :=
    hball (Metric.ball_subset_closedBall hyq)
  have hxp : extChartAt I α p = yp := by
    rw [← hpeq]
    exact (extChartAt I α).right_inv hyp_tgt
  have hxq : extChartAt I α q = yq := by
    rw [← hqeq]
    exact (extChartAt I α).right_inv hyq_tgt
  set v : E := yq - yp with hv_def
  have hv_ne : v ≠ 0 := by
    intro h
    apply hpq
    have : yp = yq := by
      rw [hv_def, sub_eq_zero] at h
      exact h.symm
    rw [← hpeq, ← hqeq, this]
  -- the chart line and its window
  set ℓl : ℝ → E := fun s => yp + s • v with hℓl_def
  have hℓl_cont : Continuous ℓl := by
    rw [hℓl_def]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hconv : ∀ s ∈ Icc (0:ℝ) 1, ℓl s ∈ Metric.ball x₀ ε := by
    intro s hs
    have hcvx := convex_ball x₀ ε hyp hyq (by linarith [hs.2] : (0:ℝ) ≤ 1 - s) hs.1
      (by ring)
    have hform : (1 - s) • yp + s • yq = ℓl s := by
      rw [hℓl_def, hv_def]
      module
    rwa [hform] at hcvx
  set Jσ : Set ℝ := ℓl ⁻¹' Metric.ball x₀ ε with hJσ_def
  have hJσ_open : IsOpen Jσ := Metric.isOpen_ball.preimage hℓl_cont
  have hIccJσ : Icc (0:ℝ) 1 ⊆ Jσ := fun s hs => hconv s hs
  have hℓl_ball : ∀ t ∈ Jσ, ℓl t ∈ Metric.ball x₀ ε := fun t ht => ht
  set σ : ℝ → M := fun s => (extChartAt I α).symm (ℓl s) with hσ_def
  have hℓl_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ℓl Jσ := by
    have : ContDiff ℝ ∞ ℓl := by
      rw [hℓl_def]
      exact contDiff_const.add (contDiff_id.smul contDiff_const)
    exact this.contMDiff.contMDiffOn
  have hσ_smooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ Jσ := by
    refine (contMDiffOn_extChartAt_symm α).comp hℓl_smooth ?_
    intro s hs
    exact hball (Metric.ball_subset_closedBall (hℓl_ball s hs))
  have hσ0 : σ 0 = p := by
    have hℓl0 : ℓl 0 = yp := by
      rw [hℓl_def]
      simp
    rw [hσ_def]
    simp only [hℓl0]
    exact hpeq
  have hσ1 : σ 1 = q := by
    have hℓl1 : ℓl 1 = yq := by
      rw [hℓl_def, hv_def]
      simp
    rw [hσ_def]
    simp only [hℓl1]
    exact hqeq
  -- the fixed-chart reading of `σ` has constant velocity `v`
  have hspeed : ∀ t ∈ Jσ, curveSpeedSq (I := I) g σ t
      = chartMetricInner (I := I) g α (ℓl t) v v := by
    intro t ht
    have hℓl_deriv : HasDerivAt ℓl v t := by
      have h : HasDerivAt (fun r : ℝ => yp + r • v) ((1 : ℝ) • v) t :=
        ((hasDerivAt_id t).smul_const v).const_add yp
      rw [one_smul] at h
      rw [hℓl_def]
      exact h
    have hsrc_ev : ∀ᶠ r in 𝓝 t, σ r ∈ (extChartAt I α).source := by
      filter_upwards [hJσ_open.mem_nhds ht] with r hr
      exact (extChartAt I α).map_target
        (hball (Metric.ball_subset_closedBall (hℓl_ball r hr)))
    have hread : (fun r => extChartAt I α (σ r)) =ᶠ[𝓝 t] ℓl := by
      filter_upwards [hJσ_open.mem_nhds ht] with r hr
      show extChartAt I α (σ r) = ℓl r
      exact (extChartAt I α).right_inv
        (hball (Metric.ball_subset_closedBall (hℓl_ball r hr)))
    have hx_deriv : HasDerivAt (fun r => extChartAt I α (σ r)) v t :=
      hℓl_deriv.congr_of_eventuallyEq hread
    have hkey := curveSpeedSq_eq_chartMetricInner_of_hasDerivAt (I := I) g hsrc_ev hx_deriv
    have harg : extChartAt I α (σ t) = ℓl t :=
      (extChartAt I α).right_inv
        (hball (Metric.ball_subset_closedBall (hℓl_ball t ht)))
    rw [hkey, harg]
  -- positivity of the centre pairing of `v`
  obtain ⟨lam, hlam, hlow0⟩ := exists_forall_le_chartMetricInner (I := I) g
    (isCompact_singleton (x := α)) (by
      rw [Set.singleton_subset_iff]; exact mem_chart_source H α)
  have hQv_pos : 0 < chartMetricInner (I := I) g α x₀ v v := by
    have h1 := hlow0 α (Set.mem_singleton α) v
    have h2 : (0:ℝ) < lam * ‖v‖ ^ 2 := by
      have : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv_ne
      positivity
    exact lt_of_lt_of_le h2 h1
  -- regularity on `[0, 1]`
  have hreg : ∀ t ∈ Icc (0:ℝ) 1, curveSpeedSq (I := I) g σ t ≠ 0 := by
    intro t ht
    have htJ : t ∈ Jσ := hIccJσ ht
    rw [hspeed t htJ]
    have hlower := (hcomp (ℓl t) (Metric.ball_subset_closedBall (hℓl_ball t htJ)) v).1
    have : (0:ℝ) < (1 - η) * chartMetricInner (I := I) g α x₀ v v := by positivity
    exact (lt_of_lt_of_le this hlower).ne'
  -- the length bound
  have hlen : curveLength (I := I) g σ 0 1
      ≤ Real.sqrt ((1 + η) * chartMetricInner (I := I) g α x₀ v v) := by
    have hσIcc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ (Icc 0 1) := hσ_smooth.mono hIccJσ
    have hInt1 : IntervalIntegrable
        (fun s => Real.sqrt (curveSpeedSq (I := I) g σ s)) volume 0 1 :=
      ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (I := I) g zero_le_one hσIcc
    have hptw : ∀ s ∈ Ioo (0:ℝ) 1, Real.sqrt (curveSpeedSq (I := I) g σ s)
        ≤ Real.sqrt ((1 + η) * chartMetricInner (I := I) g α x₀ v v) := by
      intro s hs
      have hsJ : s ∈ Jσ := hIccJσ (Ioo_subset_Icc_self hs)
      rw [hspeed s hsJ]
      refine Real.sqrt_le_sqrt ?_
      exact (hcomp (ℓl s) (Metric.ball_subset_closedBall (hℓl_ball s hsJ)) v).2
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hInt1
      intervalIntegrable_const hptw
    have hconst : (∫ _ in (0:ℝ)..1,
        Real.sqrt ((1 + η) * chartMetricInner (I := I) g α x₀ v v))
        = Real.sqrt ((1 + η) * chartMetricInner (I := I) g α x₀ v v) := by
      simp
    calc curveLength (I := I) g σ 0 1
        = ∫ s in (0:ℝ)..1, Real.sqrt (curveSpeedSq (I := I) g σ s) := rfl
      _ ≤ ∫ _ in (0:ℝ)..1,
            Real.sqrt ((1 + η) * chartMetricInner (I := I) g α x₀ v v) := hmono
      _ = Real.sqrt ((1 + η) * chartMetricInner (I := I) g α x₀ v v) := hconst
  refine ⟨σ, Jσ, hJσ_open, hIccJσ, hσ_smooth, hσ0, hσ1, hreg, ?_⟩
  rw [hxp, hxq]
  exact hlen

/-! ## The chained per-piece estimate -/

/-- **Math.** On a comparison ball the straight chart segment between the
endpoints of a curve piece is a regular curve whose length exceeds the
piece's length by a factor at most `√((1+η)/(1−η))`: the upper bound
`L(σ) ≤ √((1+η)⟨Δx,Δx⟩₀)` of `exists_regular_chartLine` chains with the
lower bound `√((1−η)⟨Δx,Δx⟩₀) ≤ L(γ)|_{a'}^{b'}` of
`sqrt_gram_lower_bound_piecewise`. -/
private theorem exists_regular_chartLine_length_le (g : RiemannianMetric I M)
    {α : M} {η δ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hball : Metric.closedBall (extChartAt I α α) δ ⊆ (extChartAt I α).target)
    (hcomp : ∀ y ∈ Metric.closedBall (extChartAt I α α) δ, ∀ u : E,
        (1 - η) * chartMetricInner (I := I) g α (extChartAt I α α) u u
            ≤ chartMetricInner (I := I) g α y u u ∧
          chartMetricInner (I := I) g α y u u
            ≤ (1 + η) * chartMetricInner (I := I) g α (extChartAt I α α) u u)
    {γ : ℝ → M} {a b a' b' : ℝ} (hγ : IsPiecewiseSmoothCurve (I := I) γ a b)
    (ha' : a' ∈ Icc a b) (hb' : b' ∈ Icc a b) (ha'b' : a' ≤ b')
    (hmem : ∀ s ∈ Icc a' b',
      γ s ∈ (extChartAt I α).symm '' Metric.ball (extChartAt I α α) δ)
    (hne : γ a' ≠ γ b') :
    ∃ (σ : ℝ → M) (Jσ : Set ℝ), IsOpen Jσ ∧ Icc (0:ℝ) 1 ⊆ Jσ ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ Jσ ∧ σ 0 = γ a' ∧ σ 1 = γ b' ∧
      (∀ s ∈ Icc (0:ℝ) 1, curveSpeedSq (I := I) g σ s ≠ 0) ∧
      curveLength (I := I) g σ 0 1
        ≤ Real.sqrt ((1 + η) / (1 - η)) * curveLength (I := I) g γ a' b' := by
  have h1η : (0:ℝ) < 1 - η := by linarith
  have hpa := hmem a' ⟨le_refl a', ha'b'⟩
  have hpb := hmem b' ⟨ha'b', le_refl b'⟩
  obtain ⟨σ, Jσ, hJσ, hJsub, hσ, hσ0, hσ1, hσreg, hσlen⟩ :=
    exists_regular_chartLine (I := I) g hη1 hball hcomp hpa hpb hne
  refine ⟨σ, Jσ, hJσ, hJsub, hσ, hσ0, hσ1, hσreg, ?_⟩
  have hlow := sqrt_gram_lower_bound_piecewise (I := I) g hη1 hball
    (fun y hy u => (hcomp y hy u).1) hγ ha' hb' ha'b'
    (fun s hs => Set.image_mono Metric.ball_subset_closedBall (hmem s hs))
  set Q : ℝ := chartMetricInner (I := I) g α (extChartAt I α α)
      (extChartAt I α (γ b') - extChartAt I α (γ a'))
      (extChartAt I α (γ b') - extChartAt I α (γ a')) with hQ_def
  have hfactor : (1 + η) / (1 - η) * ((1 - η) * Q) = (1 + η) * Q := by
    field_simp
  calc curveLength (I := I) g σ 0 1
      ≤ Real.sqrt ((1 + η) * Q) := hσlen
    _ = Real.sqrt ((1 + η) / (1 - η)) * Real.sqrt ((1 - η) * Q) := by
        rw [← hfactor, Real.sqrt_mul (div_nonneg (by linarith) h1η.le)]
    _ ≤ Real.sqrt ((1 + η) / (1 - η)) * curveLength (I := I) g γ a' b' :=
        mul_le_mul_of_nonneg_left hlow (Real.sqrt_nonneg _)

/-! ## The chart polygon -/

/-- The polygon invariant for the constant-speed approximation: on each unit
interval `[j, j+1]`, `j ≤ m`, the curve `P` agrees with a reference curve
that is smooth on an open window around the interval and has nonvanishing
speed there.  This is `IsPiecewiseRegularCurve` with the canonical
integer partition of `[0, m+1]`. -/
private def IsChartPolygon (g : RiemannianMetric I M) (P : ℝ → M) (m : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ m → ∃ (σ : ℝ → M) (J : Set ℝ), IsOpen J ∧
    Icc (j : ℝ) ((j : ℝ) + 1) ⊆ J ∧ ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ J ∧
    EqOn P σ (Icc (j : ℝ) ((j : ℝ) + 1)) ∧
    ∀ s ∈ Icc (j : ℝ) ((j : ℝ) + 1), curveSpeedSq (I := I) g σ s ≠ 0

/-- A chart polygon with `m + 1` unit segments is a piecewise regular curve
on `[0, m + 1]`. -/
private theorem IsChartPolygon.isPiecewiseRegularCurve {g : RiemannianMetric I M}
    {P : ℝ → M} {m : ℕ} (hP : IsChartPolygon (I := I) g P m) :
    IsPiecewiseRegularCurve (I := I) g P 0 ((m : ℝ) + 1) := by
  refine ⟨m + 1, fun i => ((i : ℕ) : ℝ), fun i j hij => Nat.cast_le.mpr hij, by simp, ?_, ?_⟩
  · show ((Fin.last (m + 1) : ℕ) : ℝ) = (m : ℝ) + 1
    rw [Fin.val_last]
    push_cast
    ring
  · intro i
    obtain ⟨σ, J, hJ, hsub, hσ, heq, hreg⟩ := hP i (Nat.lt_succ_iff.mp i.isLt)
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    exact ⟨σ, J, hJ, hsub, hσ, heq, hreg⟩

/-- **Math.** The inductive engine for Cor. 5.3.10: given a partition
`t 0 ≤ t 1 ≤ ⋯ ≤ t N` of a parameter interval such that on each piece the
curve either does not move between the endpoints or admits a regular chart
segment between them with length at most `C` times the piece's length, the
chart segments glue to a chart polygon from `γ (t 0)` to `γ (t k)` of length
at most `C L(γ)|_{t 0}^{t k}` — unless the curve does not move at all. -/
private theorem exists_chartPolygon_glue (g : RiemannianMetric I M) {C : ℝ} (hC : 0 ≤ C)
    {γ : ℝ → M} {t : ℕ → ℝ} {N : ℕ}
    (hmono : ∀ i, i < N → t i ≤ t (i + 1))
    (hγ : IsPiecewiseSmoothCurve (I := I) γ (t 0) (t N))
    (hpieces : ∀ i, i < N →
      γ (t i) = γ (t (i + 1)) ∨
      ∃ (σ : ℝ → M) (Jσ : Set ℝ), IsOpen Jσ ∧ Icc (0:ℝ) 1 ⊆ Jσ ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ Jσ ∧ σ 0 = γ (t i) ∧ σ 1 = γ (t (i + 1)) ∧
        (∀ s ∈ Icc (0:ℝ) 1, curveSpeedSq (I := I) g σ s ≠ 0) ∧
        curveLength (I := I) g σ 0 1 ≤ C * curveLength (I := I) g γ (t i) (t (i + 1))) :
    ∀ k, k ≤ N →
      γ (t 0) = γ (t k) ∨
      ∃ (m : ℕ) (P : ℝ → M), IsChartPolygon (I := I) g P m ∧
        P 0 = γ (t 0) ∧ P ((m : ℝ) + 1) = γ (t k) ∧
        curveLength (I := I) g P 0 ((m : ℝ) + 1)
          ≤ C * curveLength (I := I) g γ (t 0) (t k) := by
  classical
  -- monotonicity chain and integrability of the speed on subintervals
  have htle : ∀ j, j ≤ N → ∀ i, i ≤ j → t i ≤ t j := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      obtain rfl : i = 0 := Nat.le_zero.mp hi
      exact le_rfl
    | succ j ih =>
      intro hjN i hi
      by_cases hij : i ≤ j
      · exact (ih (Nat.le_of_succ_le hjN) i hij).trans (hmono j (Nat.lt_of_succ_le hjN))
      · obtain rfl : i = j + 1 := by omega
        exact le_rfl
  have hInt := hγ.intervalIntegrable_sqrt_curveSpeedSq (I := I) g
  have htmemN : ∀ i, i ≤ N → t i ∈ Set.uIcc (t 0) (t N) := by
    intro i hi
    rw [Set.uIcc_of_le (htle N le_rfl 0 (Nat.zero_le N))]
    exact ⟨htle i hi 0 (Nat.zero_le i), htle N le_rfl i hi⟩
  have hIntsub : ∀ i, i ≤ N → ∀ j, j ≤ N → IntervalIntegrable
      (fun τ => Real.sqrt (curveSpeedSq (I := I) g γ τ))
        MeasureTheory.volume (t i) (t j) :=
    fun i hi j hj => hInt.mono_set (Set.uIcc_subset_uIcc (htmemN i hi) (htmemN j hj))
  have hLnonneg : ∀ i, i ≤ N → ∀ j, j ≤ N → i ≤ j →
      0 ≤ curveLength (I := I) g γ (t i) (t j) :=
    fun i _ j hj hij => curveLength_nonneg (I := I) g γ (htle j hj i hij)
  have hLsplit : ∀ k, k < N →
      curveLength (I := I) g γ (t 0) (t (k + 1)) =
        curveLength (I := I) g γ (t 0) (t k)
          + curveLength (I := I) g γ (t k) (t (k + 1)) :=
    fun k hk => curveLength_additive (I := I) g γ
      (hIntsub 0 (Nat.zero_le N) k hk.le) (hIntsub k hk.le (k + 1) hk)
  intro k
  induction k with
  | zero => intro _; exact Or.inl rfl
  | succ k ih =>
    intro hk1
    have hkN : k < N := Nat.lt_of_succ_le hk1
    rcases hpieces k hkN with hdeg | ⟨σ, Jσ, hJσ, hJsub, hσ, hσ0, hσ1, hσreg, hσlen⟩
    · -- degenerate piece: the polygon (or the equality) carries over
      rcases ih hkN.le with heq | ⟨m, P, hPP, hP0, hPend, hPlen⟩
      · exact Or.inl (heq.trans hdeg)
      · refine Or.inr ⟨m, P, hPP, hP0, hPend.trans hdeg, hPlen.trans ?_⟩
        rw [hLsplit k hkN]
        nlinarith [mul_nonneg hC (hLnonneg k hkN.le (k + 1) hk1 (Nat.le_succ k))]
    · rcases ih hkN.le with heq | ⟨m, P, hPP, hP0, hPend, hPlen⟩
      · -- the curve has not moved yet: start a fresh polygon with `σ` alone
        refine Or.inr ⟨0, σ, ?_, ?_, ?_, ?_⟩
        · intro j hj
          obtain rfl : j = 0 := Nat.le_zero.mp hj
          refine ⟨σ, Jσ, hJσ, ?_, hσ, fun s _ => rfl, ?_⟩
          · simpa using hJsub
          · intro s hs
            refine hσreg s ?_
            simpa using hs
        · rw [hσ0]; exact heq.symm
        · simp only [Nat.cast_zero, zero_add]
          exact hσ1
        · simp only [Nat.cast_zero, zero_add]
          refine hσlen.trans ?_
          rw [hLsplit k hkN]
          nlinarith [mul_nonneg hC (hLnonneg 0 (Nat.zero_le N) k hkN.le (Nat.zero_le k))]
      · -- extend the polygon by the chart segment
        have hglue2 : σ 0 = P ((m : ℝ) + 1) := by rw [hσ0]; exact hPend.symm
        set P' : ℝ → M :=
          fun s => if s ≤ (m : ℝ) + 1 then P s else σ (1 * s + -((m : ℝ) + 1))
          with hP'_def
        have hP'eqP : EqOn P' P (Icc (0:ℝ) ((m : ℝ) + 1)) := by
          intro s hs
          simp only [hP'_def]
          rw [if_pos hs.2]
        have hP'eqσ : EqOn P' (fun r => σ (1 * r + -((m : ℝ) + 1)))
            (Icc ((m : ℝ) + 1) ((m : ℝ) + 2)) := by
          intro s hs
          simp only [hP'_def]
          rcases lt_or_eq_of_le hs.1 with hlt | heqs
          · rw [if_neg (not_le.mpr hlt)]
          · rw [← heqs, if_pos le_rfl, ← hglue2]
            exact congrArg σ (by ring)
        have hPP' : IsChartPolygon (I := I) g P' (m + 1) := by
          intro j hj
          by_cases hjm : j ≤ m
          · obtain ⟨σj, Jj, hJj, hsubj, hσj, heqj, hregj⟩ := hPP j hjm
            refine ⟨σj, Jj, hJj, hsubj, hσj, ?_, hregj⟩
            intro s hs
            have hjR : ((j : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hjm
            exact (hP'eqP ⟨(Nat.cast_nonneg j).trans hs.1,
              hs.2.trans (by linarith)⟩).trans (heqj hs)
          · obtain rfl : j = m + 1 := by omega
            refine ⟨fun r => σ (1 * r + -((m : ℝ) + 1)),
              (fun r : ℝ => 1 * r + -((m : ℝ) + 1)) ⁻¹' Jσ,
              hJσ.preimage ((continuous_const.mul continuous_id).add continuous_const),
              ?_, ?_, ?_, ?_⟩
            · intro s hs
              have h1 := hs.1; have h2 := hs.2
              push_cast at h1 h2
              exact Set.mem_preimage.mpr
                (hJsub (mem_Icc.mpr ⟨by linarith, by linarith⟩))
            · exact hσ.comp
                ((((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff).contMDiffOn)
                (fun s hs => hs)
            · intro s hs
              have h1 := hs.1; have h2 := hs.2
              push_cast at h1 h2
              exact hP'eqσ (mem_Icc.mpr ⟨by linarith, by linarith⟩)
            · intro s hs
              have h1 := hs.1; have h2 := hs.2
              push_cast at h1 h2
              rw [curveSpeedSq_comp_mul_add (I := I) g σ 1 (-((m : ℝ) + 1)) s,
                one_pow, one_mul]
              exact hσreg _ (mem_Icc.mpr ⟨by linarith, by linarith⟩)
        refine Or.inr ⟨m + 1, P', hPP', ?_, ?_, ?_⟩
        · exact (hP'eqP (mem_Icc.mpr ⟨le_rfl, by positivity⟩)).trans hP0
        · have hmem2 : (((m + 1 : ℕ) : ℝ)) + 1 ∈ Icc ((m : ℝ) + 1) ((m : ℝ) + 2) := by
            constructor <;> · push_cast; linarith
          calc P' ((((m + 1 : ℕ) : ℝ)) + 1)
              = σ (1 * ((((m + 1 : ℕ) : ℝ)) + 1) + -((m : ℝ) + 1)) := hP'eqσ hmem2
            _ = σ 1 := congrArg σ (by push_cast; ring)
            _ = γ (t (k + 1)) := hσ1
        · have hcast : (((m + 1 : ℕ) : ℝ)) + 1 = ((m : ℝ) + 1) + 1 := by
            push_cast; ring
          rw [hcast]
          have hps : IsPiecewiseSmoothCurve (I := I) P' 0 (((m : ℝ) + 1) + 1) := by
            have h := (IsChartPolygon.isPiecewiseRegularCurve
              (I := I) hPP').isPiecewiseSmoothCurve
            rwa [hcast] at h
          rw [hps.curveLength_add (I := I) g (by positivity : (0:ℝ) ≤ (m : ℝ) + 1)
            (by linarith : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) + 1)]
          have hlen1 : curveLength (I := I) g P' 0 ((m : ℝ) + 1)
              = curveLength (I := I) g P 0 ((m : ℝ) + 1) :=
            curveLength_congr_Icc (I := I) g hP'eqP
              (mem_Icc.mpr ⟨le_rfl, by positivity⟩)
              (mem_Icc.mpr ⟨by positivity, le_rfl⟩)
          have hlen2 : curveLength (I := I) g P' ((m : ℝ) + 1) (((m : ℝ) + 1) + 1)
              = curveLength (I := I) g σ 0 1 := by
            have e1 : curveLength (I := I) g P' ((m : ℝ) + 1) (((m : ℝ) + 1) + 1)
                = curveLength (I := I) g (fun r => σ (1 * r + -((m : ℝ) + 1)))
                    ((m : ℝ) + 1) (((m : ℝ) + 1) + 1) :=
              curveLength_congr_Icc (I := I) g hP'eqσ
                (mem_Icc.mpr ⟨le_rfl, by linarith⟩)
                (mem_Icc.mpr ⟨by linarith, by linarith⟩)
            rw [e1, curveLength_comp_mul_add (I := I) g σ zero_le_one
              (-((m : ℝ) + 1)) ((m : ℝ) + 1) (((m : ℝ) + 1) + 1),
              show (1:ℝ) * ((m : ℝ) + 1) + -((m : ℝ) + 1) = 0 by ring,
              show (1:ℝ) * (((m : ℝ) + 1) + 1) + -((m : ℝ) + 1) = 1 by ring]
          rw [hlen1, hlen2]
          calc curveLength (I := I) g P 0 ((m : ℝ) + 1) + curveLength (I := I) g σ 0 1
              ≤ C * curveLength (I := I) g γ (t 0) (t k)
                + C * curveLength (I := I) g γ (t k) (t (k + 1)) :=
                add_le_add hPlen hσlen
            _ = C * curveLength (I := I) g γ (t 0) (t (k + 1)) := by
                rw [← mul_add, ← hLsplit k hkN]

/-! ## Corollary 5.3.10 -/

/-- **Math.** Petersen Ch. 5, §5.3, **Corollary 5.3.10**
(`cor:pet-ch5-regular-curve-approx`): **approximation by constant-speed
curves**.  For a piecewise smooth curve `γ ∈ Ω_{p,q}` and `ε > 0` there is a
constant-speed piecewise smooth curve `σ ∈ Ω_{p,q}` with
`L(σ) ≤ (1+ε) L(γ)`.

Petersen p. 198: cover the compact image `γ([0,1])` by finitely many chart
balls on which the chart Gram pairing is squeezed between `(1−η)` and
`(1+η)` times the centre pairing, with `(1+η)/(1−η) = 1+ε`; replace `γ` on
each piece of a sufficiently fine partition (via the Lebesgue number of the
cover) by the straight chart segment between the sample points; the segments
glue to a piecewise regular chart polygon whose length exceeds `L(γ)` by a
factor at most `√(1+ε)`; the arclength reparametrization of the polygon,
affinely rescaled to `[0,1]`, is the desired constant-speed curve. -/
theorem approximateByConstantSpeedCurve (g : RiemannianMetric I M)
    {γ : ℝ → M} (hγ : IsPiecewiseSmoothCurve (I := I) γ 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ → M, IsPiecewiseSmoothCurve (I := I) σ 0 1 ∧
      σ 0 = γ 0 ∧ σ 1 = γ 1 ∧ IsConstantSpeedCurve (I := I) g σ 0 1 ∧
      curveLength (I := I) g σ 0 1 ≤ (1 + ε) * curveLength (I := I) g γ 0 1 := by
  classical
  by_cases hpq : γ 0 = γ 1
  · -- the curve does not move between its endpoints: a constant curve works
    refine ⟨fun _ => γ 0, isPiecewiseSmoothCurve_const (I := I) (γ 0) zero_le_one,
      rfl, hpq, ⟨0, le_rfl, ∅, fun s _ => by rw [curveSpeedSq_const]; norm_num⟩, ?_⟩
    rw [curveLength_const]
    exact mul_nonneg (by linarith) (curveLength_nonneg (I := I) g γ zero_le_one)
  · -- the comparison factor
    set η : ℝ := ε / (2 + ε) with hη_def
    have h2ε : (0:ℝ) < 2 + ε := by linarith
    have hη : 0 < η := by rw [hη_def]; exact div_pos hε h2ε
    have hη1 : η < 1 := by rw [hη_def, div_lt_one h2ε]; linarith
    have h1η : (0:ℝ) < 1 - η := by linarith
    have hratio : (1 + η) / (1 - η) = 1 + ε := by
      rw [div_eq_iff h1η.ne', hη_def]
      field_simp
      ring
    have hcont : ContinuousOn γ (Icc 0 1) := hγ.1
    -- the comparison ball at each point of the curve
    have hchart : ∀ τ : Icc (0:ℝ) 1, ∃ d > (0:ℝ),
        Metric.closedBall (extChartAt I (γ τ) (γ τ)) d ⊆ (extChartAt I (γ τ)).target ∧
        ∀ y ∈ Metric.closedBall (extChartAt I (γ τ) (γ τ)) d, ∀ u : E,
          (1 - η) * chartMetricInner (I := I) g (γ τ) (extChartAt I (γ τ) (γ τ)) u u
              ≤ chartMetricInner (I := I) g (γ τ) y u u ∧
            chartMetricInner (I := I) g (γ τ) y u u
              ≤ (1 + η) * chartMetricInner (I := I) g (γ τ) (extChartAt I (γ τ) (γ τ)) u u :=
      fun τ => exists_chartBall_gram_comparison (I := I) g (γ τ) hη
    choose δ hδ hball hcomp using hchart
    -- pull the ball images back to relatively open subsets of `[0, 1]`
    have hW : ∀ τ : Icc (0:ℝ) 1, ∃ u : Set ℝ, IsOpen u ∧
        γ ⁻¹' ((extChartAt I (γ τ)).source ∩
          extChartAt I (γ τ) ⁻¹' Metric.ball (extChartAt I (γ τ) (γ τ)) (δ τ)) ∩ Icc 0 1
          = u ∩ Icc 0 1 :=
      fun τ => continuousOn_iff'.mp hcont _
        ((continuousOn_extChartAt (γ τ)).isOpen_inter_preimage
          (isOpen_extChartAt_source (γ τ)) Metric.isOpen_ball)
    choose W hWopen hWeq using hW
    have hcover : Icc (0:ℝ) 1 ⊆ ⋃ τ : Icc (0:ℝ) 1, W τ := by
      intro x hx
      have hxmem : x ∈ γ ⁻¹' ((extChartAt I (γ (⟨x, hx⟩ : Icc (0:ℝ) 1))).source ∩
          extChartAt I (γ (⟨x, hx⟩ : Icc (0:ℝ) 1)) ⁻¹'
            Metric.ball (extChartAt I (γ (⟨x, hx⟩ : Icc (0:ℝ) 1))
              (γ (⟨x, hx⟩ : Icc (0:ℝ) 1))) (δ ⟨x, hx⟩)) ∩ Icc 0 1 :=
        ⟨⟨mem_extChartAt_source _, Metric.mem_ball_self (hδ ⟨x, hx⟩)⟩, hx⟩
      rw [hWeq ⟨x, hx⟩] at hxmem
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxmem.1⟩
    -- the Lebesgue number of the cover, and a finer uniform partition
    obtain ⟨r, hr, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hWopen hcover
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hr
    set N : ℕ := N₀ + 1 with hN_def
    have hNpos : (0:ℝ) < (N : ℝ) := by
      rw [hN_def]; exact_mod_cast Nat.succ_pos N₀
    have hNr : 1 / (N : ℝ) < r := by
      rw [hN_def]; push_cast; exact hN₀
    set t : ℕ → ℝ := fun i => (i : ℝ) / (N : ℝ) with ht_def
    have ht0 : t 0 = 0 := by simp [ht_def]
    have htN : t N = 1 := by
      simp only [ht_def]; exact div_self hNpos.ne'
    have hmono' : ∀ i, i < N → t i ≤ t (i + 1) := by
      intro i _
      simp only [ht_def, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.le_succ i
    have htmem : ∀ i, i ≤ N → t i ∈ Icc (0:ℝ) 1 := by
      intro i hi
      simp only [ht_def]
      constructor
      · positivity
      · rw [div_le_one hNpos]
        exact_mod_cast hi
    have hwidth : ∀ i : ℕ, t (i + 1) - t i = 1 / (N : ℝ) := by
      intro i
      simp only [ht_def]
      push_cast
      ring
    -- each piece of the partition sits in one comparison ball image
    have hpieceball : ∀ i, i < N → ∃ τ : Icc (0:ℝ) 1, ∀ s ∈ Icc (t i) (t (i + 1)),
        γ s ∈ (extChartAt I (γ τ)).symm ''
          Metric.ball (extChartAt I (γ τ) (γ τ)) (δ τ) := by
      intro i hi
      obtain ⟨τ, hτ⟩ := hleb (t i) (htmem i hi.le)
      refine ⟨τ, fun s hs => ?_⟩
      have hsIcc : s ∈ Icc (0:ℝ) 1 :=
        ⟨(htmem i hi.le).1.trans hs.1, hs.2.trans (htmem (i + 1) hi).2⟩
      have hsball : s ∈ Metric.ball (t i) r := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
        have hw := hwidth i
        linarith [hs.2]
      have hsW : s ∈ W τ ∩ Icc 0 1 := ⟨hτ hsball, hsIcc⟩
      rw [← hWeq τ] at hsW
      obtain ⟨⟨hsrc, hpre⟩, -⟩ := hsW
      exact ⟨extChartAt I (γ τ) (γ s), hpre, (extChartAt I (γ τ)).left_inv hsrc⟩
    -- the per-piece hypothesis of the gluing engine, with `C = √(1+ε)`
    have hγ'' : IsPiecewiseSmoothCurve (I := I) γ (t 0) (t N) := by
      rw [ht0, htN]; exact hγ
    have hpieces' : ∀ i, i < N →
        γ (t i) = γ (t (i + 1)) ∨
        ∃ (σ : ℝ → M) (Jσ : Set ℝ), IsOpen Jσ ∧ Icc (0:ℝ) 1 ⊆ Jσ ∧
          ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ Jσ ∧ σ 0 = γ (t i) ∧ σ 1 = γ (t (i + 1)) ∧
          (∀ s ∈ Icc (0:ℝ) 1, curveSpeedSq (I := I) g σ s ≠ 0) ∧
          curveLength (I := I) g σ 0 1
            ≤ Real.sqrt (1 + ε) * curveLength (I := I) g γ (t i) (t (i + 1)) := by
      intro i hi
      by_cases hne : γ (t i) = γ (t (i + 1))
      · exact Or.inl hne
      · obtain ⟨τ, hτ⟩ := hpieceball i hi
        obtain ⟨σ, Jσ, h1, h2, h3, h4, h5, h6, h7⟩ :=
          exists_regular_chartLine_length_le (I := I) g hη hη1 (hball τ) (hcomp τ)
            hγ (htmem i hi.le) (htmem (i + 1) hi) (hmono' i hi) hτ hne
        rw [hratio] at h7
        exact Or.inr ⟨σ, Jσ, h1, h2, h3, h4, h5, h6, h7⟩
    -- run the gluing engine
    have hglue := exists_chartPolygon_glue (I := I) g (Real.sqrt_nonneg (1 + ε))
      hmono' hγ'' hpieces' N le_rfl
    rw [ht0, htN] at hglue
    rcases hglue with heq | ⟨m, P, hPP, hP0, hPend, hPlen⟩
    · exact absurd heq hpq
    -- reparametrize the polygon by arclength
    obtain ⟨ψ, hψinv, hψmem, hψsmooth, hψ0, hψend, ⟨T, hTunit⟩, hψarc⟩ :=
      piecewiseRegularCurve_arclengthReparametrization (I := I) g
        (IsChartPolygon.isPiecewiseRegularCurve (I := I) hPP)
    set L : ℝ := curveLength (I := I) g P 0 ((m : ℝ) + 1) with hL_def
    have hL0 : 0 ≤ L := by
      rw [hL_def]
      exact curveLength_nonneg (I := I) g P (by positivity)
    have hLpos : 0 < L := by
      rcases hL0.eq_or_lt with h0 | h
      · exfalso
        apply hpq
        calc γ 0 = P 0 := hP0.symm
          _ = (P ∘ ψ) 0 := hψ0.symm
          _ = (P ∘ ψ) L := by rw [← h0]
          _ = P ((m : ℝ) + 1) := hψend
          _ = γ 1 := hPend
      · exact h
    -- rescale the unit-speed curve to `[0, 1]`
    refine ⟨fun s => (P ∘ ψ) (L * s + 0), ?_, ?_, ?_, ?_, ?_⟩
    · apply isPiecewiseSmoothCurve_comp_mul_add (I := I) hLpos
      rw [show L * 0 + 0 = 0 by ring, show L * 1 + 0 = L by ring]
      exact hψsmooth
    · show (P ∘ ψ) (L * 0 + 0) = γ 0
      rw [show L * 0 + 0 = 0 by ring, hψ0, hP0]
    · show (P ∘ ψ) (L * 1 + 0) = γ 1
      rw [show L * 1 + 0 = L by ring, hψend, hPend]
    · refine ⟨L, hL0, T.image (fun x => x / L), ?_⟩
      intro s hs
      obtain ⟨hsI, hsT⟩ := hs
      rw [curveSpeedSq_comp_mul_add (I := I) g (P ∘ ψ) L 0 s]
      have hLs : L * s + 0 ∈ Icc (0:ℝ) L \ (T : Set ℝ) := by
        constructor
        · constructor
          · have := hsI.1; nlinarith
          · have := hsI.2; nlinarith
        · intro hmemT
          apply hsT
          have hdiv : (L * s + 0) / L = s := by
            rw [add_zero]
            exact mul_div_cancel_left₀ s hLpos.ne'
          exact Finset.mem_coe.mpr (Finset.mem_image.mpr
            ⟨L * s + 0, Finset.mem_coe.mp hmemT, hdiv⟩)
      rw [hTunit _ hLs, mul_one]
    · have hlen1 : curveLength (I := I) g (fun s => (P ∘ ψ) (L * s + 0)) 0 1
          = curveLength (I := I) g (P ∘ ψ) (L * 0 + 0) (L * 1 + 0) :=
        curveLength_comp_mul_add (I := I) g (P ∘ ψ) hL0 0 0 1
      rw [hlen1, show L * 0 + 0 = 0 by ring, show L * 1 + 0 = L by ring,
        hψarc L (mem_Icc.mpr ⟨hL0, le_rfl⟩)]
      have hsqrt_le : Real.sqrt (1 + ε) ≤ 1 + ε := by
        have h1 : Real.sqrt (1 + ε) ≤ Real.sqrt ((1 + ε) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
        rwa [Real.sqrt_sq (by linarith)] at h1
      calc L ≤ Real.sqrt (1 + ε) * curveLength (I := I) g γ 0 1 := hPlen
        _ ≤ (1 + ε) * curveLength (I := I) g γ 0 1 :=
            mul_le_mul_of_nonneg_right hsqrt_le
              (curveLength_nonneg (I := I) g γ zero_le_one)

end Boundaryless

end PetersenLib
