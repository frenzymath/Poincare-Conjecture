/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Exponential/CornerRigidity.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Exponential.SegmentUpperBound

/-!
# Corner rigidity: a broken minimizing curve has no corner

do Carmo, *Riemannian Geometry*, Ch. 3, Corollary 3.9 (the equality case), in
the form consumed by the Hopf–Rinow growth induction (Ch. 7, Theorem 2.8): if
two unit-speed legs leave a point `x` in directions `u₁, u₂ ∈ T_xM` and the
concatenation through `x` realizes the distance between its endpoints — i.e.
`d(exp_x(η u₁), exp_x(η u₂)) = 2η` for all small `η > 0` — then the two legs
leave in exactly opposite directions: `u₂ = -u₁`.

The proof is a strict-triangle-inequality argument in `(T_xM, g_x)` and needs
none of the polar-lift equality analysis: by the chord upper bound
(`exists_edist_expMap_segment_le`), for every `θ > 1` and small `η`

`2η = d(exp_x(η u₁), exp_x(η u₂)) ≤ θ · |η u₂ − η u₁|_x = θ η |u₂ − u₁|_x`,

so `|u₂ − u₁|_x ≥ 2`. For `g_x`-unit vectors,
`|u₂ − u₁|_x² = 2 − 2⟨u₁,u₂⟩_x ≥ 4` forces `⟨u₁,u₂⟩_x ≤ -1`, whence
`|u₁ + u₂|_x² = 2 + 2⟨u₁,u₂⟩_x ≤ 0` and positive definiteness of `g_x` gives
`u₁ + u₂ = 0`.
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

namespace PetersenLib

namespace Exponential

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless] [CompleteSpace E]

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
variable [T2Space (TangentBundle I M')]

/-- **Math.** **Corner rigidity** (do Carmo Ch. 3, Cor. 3.9, equality case, as
used in the Hopf–Rinow growth induction): if `u₁, u₂ ∈ T_xM` are `g_x`-unit
vectors and the broken curve through `x` realizes the distance
`d(exp_x(η u₁), exp_x(η u₂)) = 2η` for all sufficiently small `η > 0`, then
`u₂ = -u₁` — there is no corner. Strict triangle inequality in `(T_xM, g_x)`
against the chord upper bound `exists_edist_expMap_segment_le`. -/
theorem eq_neg_of_forall_edist_expMap_eq (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) (x : M') {u₁ u₂ : E}
    (h₁ : chartMetricInner (I := I) g x (extChartAt I x x) u₁ u₁ = 1)
    (h₂ : chartMetricInner (I := I) g x (extChartAt I x x) u₂ u₂ = 1)
    {η₀ : ℝ} (hη₀ : 0 < η₀)
    (h : ∀ η : ℝ, 0 < η → η < η₀ →
      edist (expMap (I := I) g x ((η • u₁ : E) : TangentSpace I x))
          (expMap (I := I) g x ((η • u₂ : E) : TangentSpace I x))
        = ENNReal.ofReal (2 * η)) :
    u₂ = -u₁ := by
  classical
  -- the Gram lower bound at `x`: positivity of the form
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g x
  have hgram0 : ∀ w : E,
      ‖w‖ ^ 2 ≤ c * chartMetricInner (I := I) g x (extChartAt I x x) w w :=
    fun w => hgramV _ (mem_of_mem_nhds hVc) w
  have hQnonneg : ∀ w : E,
      0 ≤ chartMetricInner (I := I) g x (extChartAt I x x) w w := by
    intro w
    have h1 := hgram0 w
    nlinarith [sq_nonneg ‖w‖, hc]
  -- Step 1: `2 ≤ θ √⟨u₂ − u₁, u₂ − u₁⟩ₓ` for every `θ > 1`
  have hstep1 : ∀ θ : ℝ, 1 < θ → 2 ≤ θ * Real.sqrt
      (chartMetricInner (I := I) g x (extChartAt I x x) (u₂ - u₁) (u₂ - u₁)) := by
    intro θ hθ
    obtain ⟨ρ, hρ, hdom, hsrc, hchord⟩ :=
      exists_edist_expMap_segment_le (I := I) g hg x hθ
    set S : ℝ := ‖u₁‖ + ‖u₂‖ + 1 with hSdef
    have hS : 0 < S := by positivity
    have hu₁S : ‖u₁‖ < S := by
      rw [hSdef]
      linarith [norm_nonneg u₂]
    have hu₂S : ‖u₂‖ < S := by
      rw [hSdef]
      linarith [norm_nonneg u₁]
    set η : ℝ := min (η₀ / 2) (ρ / S) with hηdef
    have hη : 0 < η := lt_min (by linarith) (div_pos hρ hS)
    have hηη₀ : η < η₀ := (min_le_left _ _).trans_lt (by linarith)
    have hηρS : η ≤ ρ / S := min_le_right _ _
    have hnorm : ∀ u : E, ‖u‖ < S → ‖(η • u : E)‖ < ρ := by
      intro u hu
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      calc η * ‖u‖ ≤ (ρ / S) * ‖u‖ :=
            mul_le_mul_of_nonneg_right hηρS (norm_nonneg _)
        _ < ρ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ hS]
            exact mul_lt_mul_of_pos_left hu hρ
    have hedist := h η hη hηη₀
    have hle := hchord (η • u₁) (η • u₂) (hnorm u₁ hu₁S) (hnorm u₂ hu₂S)
    rw [hedist] at hle
    have hsmulsub : (η • u₂ : E) - η • u₁ = η • (u₂ - u₁) := (smul_sub η u₂ u₁).symm
    rw [hsmulsub] at hle
    have hQsmul : chartMetricInner (I := I) g x (extChartAt I x x)
          (η • (u₂ - u₁)) (η • (u₂ - u₁))
        = η ^ 2 * chartMetricInner (I := I) g x (extChartAt I x x)
            (u₂ - u₁) (u₂ - u₁) := by
      rw [chartMetricInner_smul_left, chartMetricInner_smul_right]
      ring
    rw [hQsmul, Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη.le] at hle
    have hreal : 2 * η ≤ θ * (η * Real.sqrt
        (chartMetricInner (I := I) g x (extChartAt I x x) (u₂ - u₁) (u₂ - u₁))) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
    nlinarith [hreal, hη, Real.sqrt_nonneg
      (chartMetricInner (I := I) g x (extChartAt I x x) (u₂ - u₁) (u₂ - u₁))]
  -- Step 2: `⟨u₂ − u₁, u₂ − u₁⟩ₓ ≥ 4`
  have hs2 : 2 ≤ Real.sqrt
      (chartMetricInner (I := I) g x (extChartAt I x x) (u₂ - u₁) (u₂ - u₁)) := by
    by_contra hlt
    push_neg at hlt
    rcases eq_or_lt_of_le (Real.sqrt_nonneg
        (chartMetricInner (I := I) g x (extChartAt I x x) (u₂ - u₁) (u₂ - u₁)))
      with heq | hpos
    · linarith [hstep1 2 one_lt_two, heq.symm ▸ (by norm_num :
        (2 : ℝ) * 0 = 0)]
    · have h2s : 1 < 2 / Real.sqrt
          (chartMetricInner (I := I) g x (extChartAt I x x) (u₂ - u₁) (u₂ - u₁)) :=
        (one_lt_div hpos).mpr hlt
      set s : ℝ := Real.sqrt
        (chartMetricInner (I := I) g x (extChartAt I x x) (u₂ - u₁) (u₂ - u₁))
      have hθ1 : 1 < (1 + 2 / s) / 2 := by linarith
      have hθlt : (1 + 2 / s) / 2 < 2 / s := by linarith
      have hcontra := hstep1 ((1 + 2 / s) / 2) hθ1
      have hprod : (1 + 2 / s) / 2 * s < 2 := by
        calc (1 + 2 / s) / 2 * s < (2 / s) * s :=
              mul_lt_mul_of_pos_right hθlt hpos
          _ = 2 := div_mul_cancel₀ 2 hpos.ne'
      linarith
  have hQ4 : 4 ≤ chartMetricInner (I := I) g x (extChartAt I x x)
      (u₂ - u₁) (u₂ - u₁) := by
    have h4 : (2 : ℝ) ^ 2 ≤ Real.sqrt
        (chartMetricInner (I := I) g x (extChartAt I x x) (u₂ - u₁) (u₂ - u₁)) ^ 2 := by
      nlinarith [hs2]
    rw [Real.sq_sqrt (hQnonneg _)] at h4
    linarith
  -- Step 3: expand and use positive definiteness
  have hexp1 : chartMetricInner (I := I) g x (extChartAt I x x) (u₂ - u₁) (u₂ - u₁)
      = 2 - 2 * chartMetricInner (I := I) g x (extChartAt I x x) u₁ u₂ := by
    have hd : u₂ - u₁ = u₂ + (-1 : ℝ) • u₁ := by module
    rw [hd]
    simp only [chartMetricInner_add_left, chartMetricInner_add_right,
      chartMetricInner_smul_left, chartMetricInner_smul_right]
    rw [chartMetricInner_symm (I := I) g x (extChartAt I x x) u₂ u₁, h₁, h₂]
    ring
  have hexp2 : chartMetricInner (I := I) g x (extChartAt I x x) (u₁ + u₂) (u₁ + u₂)
      = 2 + 2 * chartMetricInner (I := I) g x (extChartAt I x x) u₁ u₂ := by
    simp only [chartMetricInner_add_left, chartMetricInner_add_right]
    rw [chartMetricInner_symm (I := I) g x (extChartAt I x x) u₂ u₁, h₁, h₂]
    ring
  have hB : chartMetricInner (I := I) g x (extChartAt I x x) u₁ u₂ ≤ -1 := by
    rw [hexp1] at hQ4
    linarith
  have hsum : chartMetricInner (I := I) g x (extChartAt I x x)
      (u₁ + u₂) (u₁ + u₂) ≤ 0 := by
    rw [hexp2]
    linarith
  have hzero : u₁ + u₂ = 0 := by
    have hnorm2 := hgram0 (u₁ + u₂)
    have hn0 : ‖u₁ + u₂‖ ^ 2 ≤ 0 := by nlinarith [hc]
    have : ‖u₁ + u₂‖ = 0 := by nlinarith [norm_nonneg (u₁ + u₂)]
    exact norm_eq_zero.mp this
  exact eq_neg_of_add_eq_zero_right hzero

end Exponential

end PetersenLib
