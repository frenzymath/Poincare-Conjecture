import PetersenLib.Ch05.RadialSmooth
import PetersenLib.Riemannian.Exponential.MinimizingEqualityManifold

/-!
# Petersen Ch. 5, §5.5.2 — short geodesics are segments (the uniqueness half)

Toward Petersen Theorem 5.5.4 (`thm:pet-ch5-short-geodesics-segments`).  The
**existence** half — the radial geodesic `t ↦ exp_p(tv)` is a segment realizing
`d(p, exp_p v) = |v|_g` — is `exists_expMap_isSegment` /
`expMap_riemannianDistance_eq` (`RadialSmooth.lean`).  This file lands the
**uniqueness** half, for smooth competitors:

  near `p`, any `C^∞` curve `σ : [0,1] → M` from `p` to `exp_p v` whose Petersen
  length `L(σ)` equals the radial length `|v|_g` is a **monotone reparametrization
  of the radial geodesic** — there is a continuous nondecreasing
  `s : [0,1] → [0,1]`, `s(0) = 0`, `s(1) = 1`, with `σ(t) = exp_p(s(t)·v)`.

So the short radial geodesic is, up to reparametrization, the **unique** smooth
segment from `p` to `exp_p v` of speed `|v|_g` — Petersen's uniqueness clause of
Thm 5.5.4, restricted from piecewise-`C^∞` to globally-`C^∞` competitors (the
regularity at which the do Carmo minimizing-equality engine is stated).

The whole content is the vendored do Carmo minimizing-geodesic **equality** engine
`PetersenLib.Exponential.exists_gauss_equality_manifold` (do Carmo Ch. 3, Prop. 3.6
equality clause, escape case handled): every `C¹` competitor realizing the radial
`pathELength` is a monotone reparametrization of the radial geodesic.  The only
Petersen-side glue is the length bridge `pathELength_eq_ofReal_curveLength`
(`DistanceEDistBridge.lean`) turning `L(σ)` into `pathELength`, plus the chart-origin
identity `chartMetricInner_extChartAt_eq_metricInner` identifying the chart-Gram
radial length with `|v|_g`.

No ambient metric-space structure and no distance-`edist` bridge is needed: the
competitor's length is supplied as a hypothesis, not inferred from a distance
infimum.
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
**uniqueness half** (smooth competitors).  There is `ε > 0` such that the model
ball `B_ε(0) ⊂ T_pM` lies in the exponential domain and, for every `v` with
`‖v‖ < ε`, every `C^∞` curve `σ : [0,1] → M` from `p` to `exp_p v` whose Petersen
length equals the radial length,

`L(σ)|_0^1 = |v|_g = √(g_p(v, v))` ,

is a **monotone reparametrization of the radial geodesic**: there is a continuous
nondecreasing `s : [0,1] → [0,1]` with `s(0) = 0`, `s(1) = 1` and
`σ(t) = exp_p(s(t)·v)` for all `t ∈ [0,1]`.

Hence, up to reparametrization, the radial geodesic `t ↦ exp_p(tv)` is the unique
smooth segment of speed `|v|_g` from `p` to `exp_p v` — the uniqueness clause of
Thm 5.5.4 (restricted to globally-`C^∞` competitors, the regularity at which the
vendored do Carmo minimizing-equality engine `exists_gauss_equality_manifold` is
stated). -/
theorem exists_expMap_smoothSegment_unique (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      ∀ v : E, ‖v‖ < ε → ∀ σ : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ (Icc 0 1) →
        σ 0 = p →
        σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
        curveLength (I := I) g σ 0 1 = Real.sqrt (g.metricInner p v v) →
        ∃ s : ℝ → ℝ, ContinuousOn s (Icc 0 1) ∧ MonotoneOn s (Icc 0 1) ∧
          s 0 = 0 ∧ s 1 = 1 ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            σ t = expMap (I := I) g p ((s t • v : E) : TangentSpace I p) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨ρ, hρ, hdom, -, -, hkey⟩ :=
    Exponential.exists_gauss_equality_manifold (I := I) g p
  refine ⟨ρ, hρ, hdom, fun v hv σ hσ hσ0 hσ1 hlen => ?_⟩
  -- the smooth competitor is in particular `C¹`
  have hσC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) := hσ.of_le (by exact_mod_cast le_top)
  -- at the chart origin the chart-Gram radial length is the intrinsic one `|v|_g`
  have hchart : chartMetricInner (I := I) g p (extChartAt I p p) v v = g.metricInner p v v := by
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) v v,
      trivializationAt_symm_self]
  -- the length bridge turns the Petersen length hypothesis into the `pathELength`
  -- hypothesis of the vendored equality engine
  have hpath : Manifold.pathELength I σ 0 1
      = ENNReal.ofReal (curveLength (I := I) g σ 0 1) :=
    pathELength_eq_ofReal_curveLength (I := I) g zero_le_one hσ
  have hlen' : Manifold.pathELength I σ 0 1
      = ENNReal.ofReal (Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p p) v v)) := by
    rw [hpath, hlen, hchart]
  obtain ⟨s, hcont, hmono, hs0, hs1, hstep, -, -⟩ :=
    hkey v hv σ hσC1 hσ0 hσ1 hlen'
  exact ⟨s, hcont, hmono, hs0, hs1, fun t ht => (hstep t ht).2⟩

end PetersenLib

end
