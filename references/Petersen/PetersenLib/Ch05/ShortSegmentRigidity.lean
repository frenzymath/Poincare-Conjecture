import PetersenLib.Ch05.ShortSegmentUniquePiecewise
import PetersenLib.Ch05.PiecewiseArclength

/-!
# Petersen Ch. 5, §5.5.2 — short geodesics are segments: the rigid form

Petersen Theorem 5.5.4 (`thm:pet-ch5-short-geodesics-segments`), sharpened in the
two directions that `ShortSegmentUniquePiecewise.lean` leaves open.  That file
concludes only that a length-minimizing competitor is *some* monotone
reparametrization `σ(t) = exp_p(s(t)·v)` of the radial geodesic, and it measures
the uniqueness radius in the model norm `‖v‖` while measuring the ball clause in
the intrinsic norm `|v|_g`.  Here:

* `shortGeodesicsAreUniqueSegments_eq` pins the reparametrization down to
  `s = id`, i.e. `σ(t) = exp_p(t·v)` on the nose.  The extra input is the
  **length-fraction clause** of the vendored engine
  `PetersenLib.Exponential.exists_gauss_equality_manifold_piecewise` — its
  seventh conclusion component, which `shortGeodesicsAreUniqueSegments`
  discards.  It says `pathELength σ 0 t = s t · |v|_g`; against a competitor
  whose length grows proportionally (`L(σ)|_0^t = |v|_g · t`, which is exactly
  what `IsSegment` supplies) this forces `s t · |v|_g = t · |v|_g`, hence
  `s = id` once `|v|_g > 0`.  The degenerate `v = 0` branch is free.

* `expMap_isSegment_unique` assembles all three clauses of Thm. 5.5.4 with the
  radius measured throughout in the **intrinsic** norm `|v|_g` (matching
  `def:pet-ch5-metric-balls`), and states the uniqueness against every
  `IsSegment` competitor.  The `‖·‖`-to-`|·|_g` conversion is the one-sided
  coercivity `PetersenLib.Geodesic.exists_sq_norm_le_chartMetricInner`,
  evaluated at the pole, exactly as `ExpBallImage.lean` does it.

## What this file does NOT provide

The radius `ε` is **furnished existentially**, not accepted as a hypothesis.
Petersen's Theorem 5.5.4 hypothesises "let `ε` be a radius on which `exp_p` is a
diffeomorphism" and concludes `U = B(p, ε)` and the uniqueness **at that `ε`**;
every statement here supplies its own `ε` instead.  Closing that gap requires
restating the vendored `∃ρ` Gauss/minimizing-equality chain
(`Riemannian/Exponential/GaussLemma.lean`,
`Riemannian/Exponential/MinimizingEqualityPiecewise.lean`) in
hypothesised-`ρ` form, together with the confinement fact that
`B(0,ε) ⊆ expDomain g p` forces `exp_p(B(0,ε)) ⊆ (chartAt H p).source`.  That is
a separate, large piece of work; see the report for `thm:pet-ch5-short-geodesics-segments`.

Consequently this file does **not** earn `\leanok` on
`thm:pet-ch5-short-geodesics-segments` itself; it is an honestly-scoped
normal-ball form of it.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

/-- **Math.** Petersen Ch. 5, Theorem 5.5.4 (`thm:pet-ch5-short-geodesics-segments`),
**uniqueness half, rigid form**: the minimizing competitor is the radial geodesic
*on the nose*, not merely up to reparametrization.

There is `ε > 0` such that the model ball `B_ε(0) ⊂ T_pM` lies in the exponential
domain and, for every `v` with `‖v‖ < ε`, every piecewise-`C^∞` curve
`σ : [0,1] → M` from `p` to `exp_p v` whose length grows **proportionally**,

`L(σ)|_0^t = |v|_g · t` for all `t ∈ [0,1]` ,

satisfies `σ(t) = exp_p(t·v)` for all `t ∈ [0,1]`.

This strengthens `shortGeodesicsAreUniqueSegments`, whose conclusion is only
`σ(t) = exp_p(s(t)·v)` for some monotone `s` with `s 0 = 0`, `s 1 = 1`.  The
proportional-length hypothesis is not an extra assumption in context: it is
literally the proportional-arclength conjunct of `IsSegment` (see
`expMap_isSegment_unique`, which discharges it), and `IsSegment` is a predicate
on a *parametrized* curve, so "the unique segment of speed `|v|`" does mean
`σ(t) = exp_p(t·v)` pointwise.

The proof keeps the engine's length-fraction clause `pathELength σ 0 t = s t · |v|_g`
(discarded by `shortGeodesicsAreUniqueSegments`), converts it to
`L(σ)|_0^t = s t · |v|_g` by the piecewise length bridge on `[0, t]`, and cancels
`|v|_g > 0` against the hypothesis. -/
theorem shortGeodesicsAreUniqueSegments_eq (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      ∀ v : E, ‖v‖ < ε → ∀ σ : ℝ → M,
        IsPiecewiseSmoothCurve (I := I) σ 0 1 →
        σ 0 = p →
        σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
        (∀ t ∈ Icc (0 : ℝ) 1, curveLength (I := I) g σ 0 t
          = Real.sqrt (g.metricInner p v v) * t) →
        ∀ t ∈ Icc (0 : ℝ) 1,
          σ t = expMap (I := I) g p ((t • v : E) : TangentSpace I p) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨ρ, hρ, hdom, -, -, hkey⟩ :=
    Exponential.exists_gauss_equality_manifold_piecewise (I := I) g p
  refine ⟨ρ, hρ, hdom, fun v hv σ hσ hσ0 hσ1 hfrac t ht => ?_⟩
  have hchart : chartMetricInner (I := I) g p (extChartAt I p p) v v = g.metricInner p v v := by
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) v v,
      trivializationAt_symm_self]
  set Q : ℝ := Real.sqrt (g.metricInner p v v) with hQdef
  have hQnn : 0 ≤ Q := Real.sqrt_nonneg _
  have hlen1 : curveLength (I := I) g σ 0 1 = Q := by
    have := hfrac 1 ⟨zero_le_one, le_rfl⟩; rw [this]; ring
  have hpath : Manifold.pathELength I σ 0 1 = ENNReal.ofReal Q := by
    rw [pathELength_eq_ofReal_curveLength_of_isPiecewiseSmoothCurve (I := I) g hσ, hlen1]
  have hlen' : Manifold.pathELength I σ 0 1
      = ENNReal.ofReal (Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p p) v v)) := by
    rw [hpath, hchart]
  obtain ⟨hcont, n, u, hmono, hu0, hun, hsmooth⟩ := hσ
  set τ : ℕ → ℝ := fun i => u ⟨min i n, Nat.lt_succ_of_le (min_le_right i n)⟩ with hτdef
  have hτval : ∀ (i : ℕ) (hi : i ≤ n), τ i = u ⟨i, Nat.lt_succ_of_le hi⟩ := by
    intro i hi
    exact congrArg u (Fin.ext (min_eq_left hi))
  have hτ0 : τ 0 = 0 := by rw [hτval 0 (Nat.zero_le n)]; exact hu0
  have hτn : τ n = 1 := by rw [hτval n le_rfl]; exact hun
  have hτmono : ∀ i < n, τ i ≤ τ (i + 1) := by
    intro i hi
    rw [hτval i hi.le, hτval (i + 1) hi]
    exact hmono (by simp [Fin.le_def])
  have hτsm : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1))) := by
    intro i hi
    rw [hτval i hi.le, hτval (i + 1) hi]
    have hcast : (⟨i, Nat.lt_succ_of_le hi.le⟩ : Fin (n + 1))
        = (⟨i, hi⟩ : Fin n).castSucc := rfl
    have hsucc : (⟨i + 1, Nat.lt_succ_of_le hi⟩ : Fin (n + 1))
        = (⟨i, hi⟩ : Fin n).succ := rfl
    rw [hcast, hsucc]
    exact (hsmooth ⟨i, hi⟩).of_le (by exact_mod_cast le_top)
  obtain ⟨s, hcs, hms, hs0, hs1, hstep, hsfrac, himg⟩ :=
    hkey v hv σ n τ hτ0 hτn hτmono hcont hτsm hσ0 hσ1 hlen'
  -- The length-fraction clause of the engine, on `[0, t]`.
  have hσpw : IsPiecewiseSmoothCurve (I := I) σ 0 1 := ⟨hcont, n, u, hmono, hu0, hun, hsmooth⟩
  have hsub : IsPiecewiseSmoothCurve (I := I) σ 0 t := hσpw.mono le_rfl ht.1 ht.2
  have hst01 : s t ∈ Icc (0 : ℝ) 1 := (hstep t ht).1
  have hbridge : ENNReal.ofReal (curveLength (I := I) g σ 0 t)
      = ENNReal.ofReal (s t * Q) := by
    rw [← pathELength_eq_ofReal_curveLength_of_isPiecewiseSmoothCurve (I := I) g hsub,
      hsfrac t ht, hchart]
  have heq : curveLength (I := I) g σ 0 t = s t * Q := by
    have h1 : (0:ℝ) ≤ curveLength (I := I) g σ 0 t := curveLength_nonneg g σ ht.1
    have h2 : (0:ℝ) ≤ s t * Q := mul_nonneg hst01.1 hQnn
    exact (ENNReal.ofReal_eq_ofReal_iff h1 h2).mp hbridge
  rw [hfrac t ht] at heq
  -- Either `|v|_g = 0`, forcing `v = 0`, or we may cancel it to get `s t = t`.
  rcases eq_or_lt_of_le hQnn with hQ0 | hQpos
  · have hv0 : v = 0 := by
      by_contra hne
      have hpos := g.metricInner_self_pos p v hne
      have hz : Real.sqrt (g.metricInner p v v) = 0 := hQ0.symm
      rw [Real.sqrt_eq_zero'] at hz
      linarith
    rw [(hstep t ht).2, hv0]
    simp
  · have hst : s t = t := by
      have h : s t * Q = t * Q := by linarith [heq]
      exact mul_right_cancel₀ (ne_of_gt hQpos) h
    rw [(hstep t ht).2, hst]
    exact rfl

section BallImage

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M]

/-- **Math.** Petersen Ch. 5, Theorem 5.5.4 (`thm:pet-ch5-short-geodesics-segments`)
**on a normal ball — all clauses, intrinsic radius, `IsSegment` on both sides**,
when the ambient metric-space structure on `M` is the Riemannian distance of `g`
(`hg : g.IsRiemannianDist`).

There is `ε > 0` such that

* `{v | |v|_g < ε} ⊂ T_pM` lies in the exponential domain;
* (**`U = B(p, δ)`**) for every `0 < δ ≤ ε`, `exp_p({v | |v|_g < δ}) = B(p, δ)`;
* (**existence and uniqueness**) for every `v` with `|v|_g < ε`, the radial curve
  `t ↦ exp_p(t·v)` **is** a segment on `[0,1]`, and every segment
  `σ : [0,1] → M` from `p` to `exp_p v` satisfies `σ(t) = exp_p(t·v)` for all
  `t ∈ [0,1]`.

Every radius here is measured in the intrinsic norm `|v|_g = √(g_p(v,v))`,
matching `def:pet-ch5-metric-balls`; the conversion from the model norm `‖v‖`
used by the vendored engine is the one-sided coercivity
`exists_sq_norm_le_chartMetricInner` evaluated at the pole.

The uniqueness clause is in fact *stronger* than the book's: it quantifies over
every `IsSegment` competitor on `[0,1]` — not only those declared to have speed
`|v|` — because `IsSegment` together with `expMap_riemannianDistance_eq` already
forces the speed to be `|v|_g`; and it concludes pointwise equality with the
radial geodesic rather than equality up to reparametrization.

**The one deviation from Thm. 5.5.4**: `ε` is furnished existentially here,
whereas Petersen hypothesises a radius on which `exp_p` is a diffeomorphism and
concludes at that radius.  See the module docstring. -/
theorem expMap_isSegment_unique (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ v : E, Real.sqrt (g.metricInner p v v) < ε →
        (v : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ ε →
        (fun v : E => expMap (I := I) g p (v : TangentSpace I p)) ''
            {v : E | Real.sqrt (g.metricInner p v v) < δ}
          = metricBall (I := I) g p δ) ∧
      (∀ v : E, Real.sqrt (g.metricInner p v v) < ε →
        IsSegment (I := I) g
            (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) 0 1 ∧
        ∀ σ : ℝ → M, IsSegment (I := I) g σ 0 1 → σ 0 = p →
          σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
          ∀ t ∈ Icc (0 : ℝ) 1,
            σ t = expMap (I := I) g p ((t • v : E) : TangentSpace I p)) := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨εB, hεB, hball⟩ := expMap_ballImage (I := I) g hg p
  obtain ⟨εU, hεU, hdom, huniq⟩ := shortGeodesicsAreUniqueSegments_eq (I := I) g p
  obtain ⟨εD, hεD, -, hdist⟩ := expMap_riemannianDistance_eq (I := I) g p
  obtain ⟨εS, hεS, hseg⟩ := exists_expMap_isSegment (I := I) g p
  obtain ⟨c, V, hc, hVmem, -, hcoerc⟩ := exists_sq_norm_le_chartMetricInner (I := I) g p
  have hchart : ∀ w : E,
      chartMetricInner (I := I) g p (extChartAt I p p) w w = g.metricInner p w w := by
    intro w
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) w w,
      trivializationAt_symm_self]
  have hy₀V : extChartAt I p p ∈ V := mem_of_mem_nhds hVmem
  -- One-sided coercivity at the pole: `‖w‖ ≤ √c · |w|_g`.
  have hcoercPole : ∀ w : E, ‖w‖ ≤ Real.sqrt c * Real.sqrt (g.metricInner p w w) := by
    intro w
    have h1 := hcoerc (extChartAt I p p) hy₀V w
    rw [hchart w] at h1
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ ≤ Real.sqrt (c * g.metricInner p w w) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt c * Real.sqrt (g.metricInner p w w) := Real.sqrt_mul hc.le _
  set m : ℝ := min εB (min εU (min εD εS)) with hmdef
  have hm : 0 < m := lt_min hεB (lt_min hεU (lt_min hεD hεS))
  refine ⟨min εB (m / (Real.sqrt c + 1)), lt_min hεB (by positivity), ?_, ?_, ?_⟩
  · intro v hv
    exact hdom v (by
      have h1 : Real.sqrt (g.metricInner p v v) < m / (Real.sqrt c + 1) :=
        hv.trans_le (min_le_right _ _)
      have := hcoercPole v
      rw [lt_div_iff₀ (by positivity)] at h1
      nlinarith [Real.sqrt_nonneg (g.metricInner p v v), Real.sqrt_nonneg c,
        min_le_left εU (min εD εS), min_le_right εB (min εU (min εD εS))])
  · exact fun δ hδ hδe => hball δ hδ (hδe.trans (min_le_left _ _))
  · intro v hv
    have hnorm : ‖v‖ < m := by
      have h1 : Real.sqrt (g.metricInner p v v) < m / (Real.sqrt c + 1) :=
        hv.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at h1
      nlinarith [Real.sqrt_nonneg (g.metricInner p v v), Real.sqrt_nonneg c, hcoercPole v]
    have hvU : ‖v‖ < εU := hnorm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hvD : ‖v‖ < εD :=
      hnorm.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hvS : ‖v‖ < εS :=
      hnorm.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨hseg v hvS, fun σ hσseg hσ0 hσ1 => ?_⟩
    obtain ⟨hpw, hlen, k, hk0, hkfrac⟩ := hσseg
    -- `IsSegment` forces the speed constant `k` to be `|v|_g`.
    have hd : riemannianDistance (I := I) g (σ 0) (σ 1) = Real.sqrt (g.metricInner p v v) := by
      rw [hσ0, hσ1]; exact hdist v hvD
    have hk : k = Real.sqrt (g.metricInner p v v) := by
      have := hkfrac 1 ⟨zero_le_one, le_rfl⟩
      rw [hlen, hd] at this
      simpa using this.symm
    refine huniq v hvU σ hpw hσ0 hσ1 (fun t ht => ?_)
    rw [hkfrac t ht, hk]; ring

end BallImage

end PetersenLib

end
