import PetersenLib.Ch05.ExponentialMap
import PetersenLib.Riemannian.Geodesic.HopfRinow.GramBound

/-!
# Petersen Ch. 5, §5.5.1 — positivity of the injectivity radius

`injectivityRadius_pos`: for every `p ∈ M`, the injectivity radius is strictly
positive, `0 < inj_p`.  This is the fact that makes `def:pet-ch5-injectivity-radius`
(the largest `ε > 0` on which `exp_p` restricts to a diffeomorphism onto its image)
a genuine positive number rather than a vacuous supremum, and is what underlies the
existence of Riemannian normal coordinates at every point.

The proof turns the **model-space** local-diffeomorphism data of
`expMap_localDiffeomorphism` (a `ρ > 0` with `exp_p` injective on and defined over
the model-norm ball `‖w‖ < ρ`) into a witness for the **`g`-metric** ball used in
the definition of `injectivityRadius`.  The bridge is the fibre coercivity at the
pole `‖v‖ ≤ √c·|v|_g` (`exists_sq_norm_le_chartMetricInner` evaluated at
`extChartAt I p p`, where the chart-Gram form is the intrinsic inner product): taking
`ε = ρ / (√c + 1)` makes `|v|_g < ε` force `‖v‖ ≤ √c·ε < ρ`, so the whole `g`-ball of
radius `ε` sits inside the model-norm ball where `exp_p` is defined and injective.
Hence `ENNReal.ofReal ε` lies in the set whose supremum is `injectivityRadius`, and
`0 < ε` gives the conclusion.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-injectivity-radius`, positivity): the
injectivity radius at any point is strictly positive, `0 < inj_p`.  Equivalently the
set of radii on which `exp_p` restricts to an injective map defined over the whole
`g`-metric ball is nonempty with a positive element, so its supremum is positive.

This is exactly the statement that the "largest `ε > 0` such that `exp_p` is a
diffeomorphism onto its image" of the definition is a genuine positive number, and
in particular that Riemannian normal coordinates exist at every point. -/
theorem injectivityRadius_pos (g : RiemannianMetric I M) (p : M) :
    0 < injectivityRadius (I := I) g p := by
  classical
  -- model-space local-diffeomorphism data: `ρ > 0` with `exp_p` defined and
  -- injective on the model-norm ball `‖w‖ < ρ`.
  obtain ⟨ρ, hρ, hdom, hinj, -, -⟩ := expMap_localDiffeomorphism (I := I) g p
  -- fibre coercivity near the pole, `‖w‖² ≤ c·⟨w,w⟩_{G(y)}`.
  obtain ⟨c, V, hc, hVmem, -, hcoerc⟩ := exists_sq_norm_le_chartMetricInner (I := I) g p
  -- at the pole the chart-Gram form is the intrinsic inner product.
  have hchart : ∀ w : E,
      chartMetricInner (I := I) g p (extChartAt I p p) w w = g.metricInner p w w := by
    intro w
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) w w,
      trivializationAt_symm_self]
  have hy₀V : extChartAt I p p ∈ V := mem_of_mem_nhds hVmem
  -- pole coercivity `‖w‖ ≤ √c · |w|_g`.
  have hcoercPole : ∀ w : E, ‖w‖ ≤ Real.sqrt c * Real.sqrt (g.metricInner p w w) := by
    intro w
    have h1 := hcoerc (extChartAt I p p) hy₀V w
    rw [hchart w] at h1
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ ≤ Real.sqrt (c * g.metricInner p w w) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt c * Real.sqrt (g.metricInner p w w) := Real.sqrt_mul hc.le _
  -- the working real radius.
  set ε := ρ / (Real.sqrt c + 1) with hε_def
  have hden_pos : (0 : ℝ) < Real.sqrt c + 1 := by positivity
  have hε_pos : 0 < ε := div_pos hρ hden_pos
  -- `|v|_g < ε` forces `v` into the model-norm ball where `exp_p` is well-behaved.
  have hkey : ∀ v : E, g.metricInner p v v < ε ^ 2 → ‖v‖ < ρ := by
    intro v hv
    have hsqrt_le : Real.sqrt (g.metricInner p v v) ≤ ε := by
      have h := Real.sqrt_le_sqrt hv.le
      rwa [Real.sqrt_sq hε_pos.le] at h
    calc ‖v‖ ≤ Real.sqrt c * Real.sqrt (g.metricInner p v v) := hcoercPole v
      _ ≤ Real.sqrt c * ε := mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg c)
      _ < (Real.sqrt c + 1) * ε := by nlinarith [Real.sqrt_nonneg c, hε_pos]
      _ = ρ := by rw [hε_def]; field_simp
  -- `ENNReal.ofReal ε` is a witness in the supremum set defining `injectivityRadius`.
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hε_pos) (le_sSup ?_)
  refine ⟨ε, hε_pos, rfl, fun v hv => hdom v (hkey v hv), fun v₁ hv₁ v₂ hv₂ hexp => ?_⟩
  exact hinj (mem_ball_zero_iff.mpr (hkey v₁ hv₁)) (mem_ball_zero_iff.mpr (hkey v₂ hv₂)) hexp

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-injectivity-radius`, usable form): **below
the injectivity radius, `exp_p` is defined on and injective over the whole `g`-metric
ball.**  If `0 ≤ r` and `ENNReal.ofReal r < inj_p`, then every `v ∈ T_pM` with
`|v|_g < r` lies in the exponential domain and `exp_p` is injective on the `g`-ball
`{v | |v|_g < r}`.  This is the consumer-facing consequence of the supremum defining
`injectivityRadius`: any radius strictly below `inj_p` inherits the domain and
injectivity of some witness above it, since both properties are monotone in the ball. -/
theorem expMap_injOn_of_lt_injectivityRadius (g : RiemannianMetric I M) (p : M)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : ENNReal.ofReal r < injectivityRadius (I := I) g p) :
    (∀ v : TangentSpace I p, g.metricInner p v v < r ^ 2 → v ∈ expDomain (I := I) g p) ∧
      Set.InjOn (expMap (I := I) g p)
        {v : TangentSpace I p | g.metricInner p v v < r ^ 2} := by
  obtain ⟨s, hs_mem, hrs⟩ := lt_sSup_iff.mp hr
  obtain ⟨ε, hε_pos, rfl, hdom, hinj⟩ := hs_mem
  have hrε : r < ε := (ENNReal.ofReal_lt_ofReal_iff hε_pos).mp hrs
  have hrr : r ^ 2 ≤ ε ^ 2 := by gcongr
  have hsub : {v : TangentSpace I p | g.metricInner p v v < r ^ 2}
      ⊆ {v : TangentSpace I p | g.metricInner p v v < ε ^ 2} :=
    fun v hv => lt_of_lt_of_le hv hrr
  exact ⟨fun v hv => hdom v (hsub hv), hinj.mono hsub⟩

end PetersenLib

end
