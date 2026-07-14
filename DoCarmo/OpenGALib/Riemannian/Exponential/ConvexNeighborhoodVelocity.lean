import OpenGALib.Riemannian.Exponential.TotallyNormalDiffeo

set_option linter.unusedSectionVars false

/-!
# Uniform smallness of the joining velocity (do Carmo Ch. 3, §4)

The convex-neighborhood proof (`prop:dc-ch3-4-2`) feeds the interior deduction
`exists_forall_geodesic_dist_lt_of_admissible` a joining geodesic whose
chart-velocity data must be *small* — small enough for the base to read into the
`nomax` neighborhood `V` and for the rescaled velocity to sit in the flow's ball
of initial conditions. do Carmo controls this by shrinking the ball: as the two
endpoints `q₁, q₂` collapse onto `p`, the joining velocity `v` (do Carmo's
`exp_{q₁}⁻¹ q₂`) tends to `0`.

In the chart at `p`, the joining velocity is the second component of the inverse
pair map, `w = (Ginv(φ_p(q₁), φ_p(q₂)))₂` (`thm:dc-ch3-3-7`). The inverse pair
map fixes the center diagonal — `Ginv(φ_p(p), φ_p(p)) = (φ_p(p), 0)` (do Carmo's
`exp_p⁻¹ p = 0`), now exposed by `exists_totallyNormal_c1_diffeo` — and `Ginv` is
`C¹`, hence continuous, on the open diffeomorphism image. So `w` is a continuous
function of `(φ_p(q₁), φ_p(q₂))` vanishing at the center diagonal, and it is
uniformly small on a small enough geodesic ball.

This file isolates that smallness as reusable infrastructure:

* `exists_closedBall_forall_pair_norm_lt` — **a chart-pair functional vanishing
  at the center diagonal is uniformly small on a small closed ball**: for any
  `Ψ : E × E → F` continuous at `(φ_p(p), φ_p(p))` with
  `Ψ(φ_p(p), φ_p(p)) = 0`, and any `r > 0`, there is `β > 0` with
  `closedBall p β` inside the chart source and
  `‖Ψ(φ_p(q₁), φ_p(q₂))‖ < r` for all `q₁, q₂ ∈ closedBall p β`. Pure
  continuity/charts: eventual smallness of `Ψ` near the diagonal center, pulled
  back through the chart's continuity at `p`.
* `exists_closedBall_forall_ginvSnd_norm_lt` — **the joining velocity is
  uniformly small on a small ball**: specializing to
  `Ψ = fun x => (Ginv x).2`, whose continuity comes from `C¹`-ness of `Ginv` on
  the open image and whose diagonal value is `0` (the center fixed point). This
  is the velocity half of the convex-neighborhood admissibility, uniform over
  the ball — do Carmo's "`v → 0` as `q₁, q₂ → p`".
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M')]

/-- **Math.** **A chart-pair functional vanishing at the center diagonal is
uniformly small on a small closed ball** (do Carmo Ch. 3, §4). Let `Ψ` be a map
of chart-coordinate pairs `E × E → F`, continuous at the diagonal center
`(φ_p(p), φ_p(p))` and vanishing there. Then for every tolerance `r > 0` there is
a radius `β > 0` such that the closed geodesic ball `closedBall p β` lies inside
the chart source at `p` and every pair of points `q₁, q₂ ∈ closedBall p β` reads
to a small value: `‖Ψ(φ_p(q₁), φ_p(q₂))‖ < r`.

This is the pure continuity/charts skeleton of do Carmo's "the joining velocity
tends to `0` as the endpoints collapse onto `p`": `Ψ` is eventually within `r`
of `0` near the diagonal center (its continuity there), and the chart's
continuity at `p` pulls that neighborhood back to a closed geodesic ball. -/
theorem exists_closedBall_forall_pair_norm_lt {F : Type*} [NormedAddCommGroup F]
    (p : M') (Ψ : E × E → F)
    (hΨcont : ContinuousAt Ψ ((extChartAt I p p, extChartAt I p p) : E × E))
    (hΨ0 : Ψ ((extChartAt I p p, extChartAt I p p) : E × E) = 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ β : ℝ, 0 < β ∧ closedBall p β ⊆ (chartAt H p).source ∧
      ∀ q₁ ∈ closedBall p β, ∀ q₂ ∈ closedBall p β,
        ‖Ψ ((extChartAt I p q₁, extChartAt I p q₂) : E × E)‖ < r := by
  set y₀ : E := extChartAt I p p with hy₀
  -- `Ψ` is eventually within `r` of `0` near the diagonal center
  have hev : ∀ᶠ x in 𝓝 ((y₀, y₀) : E × E), ‖Ψ x‖ < r := by
    have hcont : ContinuousAt (fun x : E × E => ‖Ψ x‖) ((y₀, y₀) : E × E) := hΨcont.norm
    refine hcont.eventually_lt continuousAt_const ?_
    simp only [hΨ0, norm_zero]
    exact hr
  -- turn this into a product-ball radius `ρ`
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hev
  -- the chart pulls a `ρ`-ball around `y₀` back to a neighborhood of `p`
  have hpre : extChartAt I p ⁻¹' ball y₀ ρ ∈ 𝓝 p :=
    (continuousAt_extChartAt p).preimage_mem_nhds
      (isOpen_ball.mem_nhds (mem_ball_self hρ))
  have hsrc : (chartAt H p).source ∈ 𝓝 p :=
    (chartAt H p).open_source.mem_nhds (mem_chart_source H p)
  obtain ⟨β, hβ, hβsub⟩ :=
    (Metric.nhds_basis_closedBall.mem_iff).mp (inter_mem hpre hsrc)
  refine ⟨β, hβ, fun q hq => (hβsub hq).2, ?_⟩
  intro q₁ hq₁ q₂ hq₂
  have h1 : extChartAt I p q₁ ∈ ball y₀ ρ := (hβsub hq₁).1
  have h2 : extChartAt I p q₂ ∈ ball y₀ ρ := (hβsub hq₂).1
  have hpair : ((extChartAt I p q₁, extChartAt I p q₂) : E × E) ∈ ball ((y₀, y₀) : E × E) ρ := by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (mem_ball.mp h1) (mem_ball.mp h2)
  exact hρsub hpair

/-- **Math.** **The joining velocity is uniformly small on a small ball** (do Carmo
Ch. 3, §4, the velocity half of the convex-neighborhood admissibility). Let
`Ginv` be the inverse pair map of `thm:dc-ch3-3-7`, `C¹` — hence continuous — on
the open diffeomorphism image `U`, with the center diagonal fixed:
`Ginv(φ_p(p), φ_p(p)) = (φ_p(p), 0)` (do Carmo's `exp_p⁻¹ p = 0`). Then for every
`r > 0` there is `β > 0` with `closedBall p β` inside the chart source and, for
all `q₁, q₂ ∈ closedBall p β`, the joining chart velocity
`w = (Ginv(φ_p(q₁), φ_p(q₂)))₂` obeys `‖w‖ < r`.

This is do Carmo's "`v → 0` as the endpoints collapse onto `p`", made uniform:
`(Ginv ·)₂` is continuous at the diagonal center (`Ginv` continuous on the open
`U ∋ (φ_p(p), φ_p(p))`) and vanishes there (the fixed diagonal), so
`exists_closedBall_forall_pair_norm_lt` applies. -/
theorem exists_closedBall_forall_ginvSnd_norm_lt
    (p : M') {Ginv : E × E → E × E} {U : Set (E × E)}
    (hUopen : IsOpen U)
    (hmem : ((extChartAt I p p, extChartAt I p p) : E × E) ∈ U)
    (hcont : ContinuousOn Ginv U)
    (hdiag : Ginv ((extChartAt I p p, extChartAt I p p) : E × E)
      = ((extChartAt I p p, (0 : E)) : E × E))
    {r : ℝ} (hr : 0 < r) :
    ∃ β : ℝ, 0 < β ∧ closedBall p β ⊆ (chartAt H p).source ∧
      ∀ q₁ ∈ closedBall p β, ∀ q₂ ∈ closedBall p β,
        ‖(Ginv ((extChartAt I p q₁, extChartAt I p q₂) : E × E)).2‖ < r := by
  refine exists_closedBall_forall_pair_norm_lt p (fun x => (Ginv x).2) ?_ ?_ hr
  · exact (hcont.continuousAt (hUopen.mem_nhds hmem)).snd
  · show (Ginv ((extChartAt I p p, extChartAt I p p) : E × E)).2 = 0
    rw [hdiag]

end Exponential

end Riemannian
