import PetersenLib.Ch05.PiecewiseLengthBridge
import PetersenLib.Ch05.RadialSmooth
import PetersenLib.Ch05.ExpBallImage
import PetersenLib.Riemannian.Exponential.MinimizingEqualityPiecewise

/-!
# Petersen Ch. 5, §5.5.2 — short geodesics are unique segments (piecewise competitors)

Petersen Theorem 5.5.4 (`thm:pet-ch5-short-geodesics-segments`), **uniqueness
half, in Petersen's own regularity class**: the competitors are the
piecewise-`C^∞` curves (`IsPiecewiseSmoothCurve`), i.e. exactly the curves that
`IsSegment` and the Petersen distance infimum range over.

`ShortSegmentUnique.lean` proves the same statement for globally-`C^∞`
competitors.  This file removes that restriction, by feeding the Petersen
partition data into the vendored piecewise do Carmo minimizing-equality engine
`PetersenLib.Exponential.exists_gauss_equality_manifold_piecewise` (do Carmo
Ch. 3, Prop. 3.6, equality clause, piecewise-`C¹` case, escape handled).  Two
pieces of glue:

* the piecewise length bridge
  `pathELength_eq_ofReal_curveLength_of_isPiecewiseSmoothCurve`
  (`PiecewiseLengthBridge.lean`) turns the Petersen length hypothesis
  `L(σ) = |v|_g` into the engine's `pathELength` hypothesis;
* the index bridge `Fin (n+1) → ℝ` (Petersen's partition type) to `ℕ → ℝ` (the
  engine's), by `i ↦ u ⟨min i n, _⟩`.

The regularity direction is free: `IsPiecewiseSmoothCurve` gives `C^∞` pieces and
the engine only asks for `C¹` pieces.

The **existence** half — the radial geodesic is a segment realizing
`d(p, exp_p v) = |v|_g` — is `exists_expMap_isSegment` / `expMap_riemannianDistance_eq`
(`RadialSmooth.lean`); the `U = B(p, ε)` clause is `expMap_ballImage`
(`ExpBallImage.lean`).
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
**uniqueness half, for genuine piecewise-`C^∞` competitors**.  There is `ε > 0`
such that the model ball `B_ε(0) ⊂ T_pM` lies in the exponential domain and, for
every `v` with `‖v‖ < ε`, every **piecewise-`C^∞`** curve `σ : [0,1] → M` from `p`
to `exp_p v` whose Petersen length equals the radial length,

`L(σ)|_0^1 = |v|_g = √(g_p(v, v))` ,

is a **monotone reparametrization of the radial geodesic**: there is a continuous
nondecreasing `s : [0,1] → [0,1]` with `s(0) = 0`, `s(1) = 1` and
`σ(t) = exp_p(s(t)·v)` for all `t ∈ [0,1]`; in particular `σ` traces exactly the
radial geodesic's image, `σ([0,1]) = exp_p([0,1]·v)`.

Hence, up to reparametrization, the radial geodesic `t ↦ exp_p(tv)` is the unique
segment of speed `|v|_g` from `p` to `exp_p v` among the curves Petersen's §5.3
metric layer admits (`IsPiecewiseSmoothCurve`, the regularity class of
`IsSegment`). -/
theorem shortGeodesicsAreUniqueSegments (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      ∀ v : E, ‖v‖ < ε → ∀ σ : ℝ → M,
        IsPiecewiseSmoothCurve (I := I) σ 0 1 →
        σ 0 = p →
        σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
        curveLength (I := I) g σ 0 1 = Real.sqrt (g.metricInner p v v) →
        ∃ s : ℝ → ℝ, ContinuousOn s (Icc 0 1) ∧ MonotoneOn s (Icc 0 1) ∧
          s 0 = 0 ∧ s 1 = 1 ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            σ t = expMap (I := I) g p ((s t • v : E) : TangentSpace I p)) ∧
          σ '' Icc 0 1
            = (fun r : ℝ => expMap (I := I) g p ((r • v : E) : TangentSpace I p)) ''
                Icc 0 1 := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨ρ, hρ, hdom, -, -, hkey⟩ :=
    Exponential.exists_gauss_equality_manifold_piecewise (I := I) g p
  refine ⟨ρ, hρ, hdom, fun v hv σ hσ hσ0 hσ1 hlen => ?_⟩
  -- at the chart origin the chart-Gram radial length is the intrinsic one `|v|_g`
  have hchart : chartMetricInner (I := I) g p (extChartAt I p p) v v = g.metricInner p v v := by
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) v v,
      trivializationAt_symm_self]
  -- the piecewise length bridge turns the Petersen length hypothesis into the
  -- `pathELength` hypothesis of the vendored equality engine
  have hpath : Manifold.pathELength I σ 0 1
      = ENNReal.ofReal (curveLength (I := I) g σ 0 1) :=
    pathELength_eq_ofReal_curveLength_of_isPiecewiseSmoothCurve (I := I) g hσ
  have hlen' : Manifold.pathELength I σ 0 1
      = ENNReal.ofReal (Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p p) v v)) := by
    rw [hpath, hlen, hchart]
  -- unpack the Petersen partition and re-index it `Fin (n+1) → ℝ  ↝  ℕ → ℝ`
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
  obtain ⟨s, hcs, hms, hs0, hs1, hstep, -, himg⟩ :=
    hkey v hv σ n τ hτ0 hτn hτmono hcont hτsm hσ0 hσ1 hlen'
  exact ⟨s, hcs, hms, hs0, hs1, fun t ht => (hstep t ht).2, himg⟩

section BallImage

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M]

/-- **Math.** Petersen Ch. 5, Theorem 5.5.4 (`thm:pet-ch5-short-geodesics-segments`),
**both clauses**, when the ambient metric-space structure on `M` is the Riemannian
distance of `g` (`hg : g.IsRiemannianDist`).  There is `ε > 0` such that

* `B_ε(0) ⊂ T_pM` lies in the exponential domain;
* (**`U = B(p, δ)`**, Cor. 5.5.6) for every `0 < δ ≤ ε`,
  `exp_p({v | |v|_g < δ}) = B(p, δ)`;
* (**uniqueness**) for every `v` with `‖v‖ < ε`, every piecewise-`C^∞` curve
  `σ : [0,1] → M` from `p` to `exp_p v` with `L(σ) = |v|_g` is a monotone
  reparametrization `σ(t) = exp_p(s(t)·v)` of the radial geodesic, and
  `σ([0,1]) = exp_p([0,1]·v)`.

The ball clause is `expMap_ballImage`, the uniqueness clause is
`shortGeodesicsAreUniqueSegments`; `ε` is the minimum of the two radii.  Note the
two clauses measure the radius differently — the ball clause in the intrinsic
norm `|v|_g`, the uniqueness clause in the model norm `‖v‖` — each as supplied by
its source. -/
theorem shortGeodesicsAreUniqueSegments_of_isRiemannianDist
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ ε →
        (fun v : E => expMap (I := I) g p (v : TangentSpace I p)) ''
            {v : E | Real.sqrt (g.metricInner p v v) < δ}
          = metricBall (I := I) g p δ) ∧
      ∀ v : E, ‖v‖ < ε → ∀ σ : ℝ → M,
        IsPiecewiseSmoothCurve (I := I) σ 0 1 →
        σ 0 = p →
        σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
        curveLength (I := I) g σ 0 1 = Real.sqrt (g.metricInner p v v) →
        ∃ s : ℝ → ℝ, ContinuousOn s (Icc 0 1) ∧ MonotoneOn s (Icc 0 1) ∧
          s 0 = 0 ∧ s 1 = 1 ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            σ t = expMap (I := I) g p ((s t • v : E) : TangentSpace I p)) ∧
          σ '' Icc 0 1
            = (fun r : ℝ => expMap (I := I) g p ((r • v : E) : TangentSpace I p)) ''
                Icc 0 1 := by
  obtain ⟨ε₁, hε₁, hball⟩ := expMap_ballImage (I := I) g hg p
  obtain ⟨ε₂, hε₂, hdom, huniq⟩ := shortGeodesicsAreUniqueSegments (I := I) g p
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun w hw => hdom w (hw.trans_le (min_le_right _ _)),
    fun δ hδ hδe => hball δ hδ (hδe.trans (min_le_left _ _)),
    fun v hv => huniq v (hv.trans_le (min_le_right _ _))⟩

end BallImage

end PetersenLib

end
