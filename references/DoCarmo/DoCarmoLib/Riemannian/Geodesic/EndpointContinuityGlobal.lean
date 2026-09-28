import DoCarmoLib.Riemannian.Geodesic.EndpointContinuity
import DoCarmoLib.Riemannian.Exponential.ProperAssembly

/-!
# Endpoint continuity of geodesics: clopen globalization

do Carmo, *Riemannian Geometry*, Ch. 7, proof of Theorem 2.8, f) ⟹ b), the
final analytic input of Hopf–Rinow: if global geodesics `γₙ` start at `p`
with chart velocities `vₙ → v`, and `γ` is a global geodesic through
`(p, v)`, then `γₙ (tₙ) → γ t₀` whenever `tₙ → t₀`
(`tendsto_geodesic_eval_of_tendsto_initialData`).

The local ingredient is the flow-box step of `EndpointContinuity.lean`
(`exists_conv_step_eval`): around every base time `t✶` there is a radius
`ρ > 0` on which the convergence invariant `ConvAt` — positions and
chart-at-the-limit-point velocities of the `γₙ` converge to those of `γ` —
propagates between any two times of the `ρ`-interval, including evaluation
at converging times. This file globalizes the step by a clopen argument:
the set `S = {t | ConvAt g γ γs t}` is

* **open** — for `t ∈ S`, the step radius `ρ` at `t✶ = t` propagates the
  invariant from `t` to the whole ball `B(t, ρ)`;
* **closed** — for `t ∈ closure S`, the ball `B(t, ρ)` around `t✶ = t` meets
  `S` at some `t'`, and the step propagates the invariant from `t'` back
  to `t`;
* **nonempty** — `0 ∈ S`: all the curves start at `p`, and their chart
  velocities at `0` converge by hypothesis.

Since `ℝ` is connected, `S = ℝ`; the moving-time part of the step at
`t✶ = t₀` then upgrades `ConvAt t₀` to `γₙ (tₙ) → γ t₀`. The statement is
shaped to instantiate the endpoint-continuity hypothesis `hend` of
`Riemannian.Exponential.completeSpace_of_forall_geodesic` directly.
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff


namespace Riemannian

namespace Geodesic

open Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
variable [T2Space (TangentBundle I M')]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Endpoint continuity of geodesics in their initial data**
(do Carmo Ch. 7, proof of Theorem 2.8, f) ⟹ b)): if the global geodesics
`γₙ` and `γ` all start at `p`, the initial chart velocities converge
(`vₙ → v`), and `tₙ → t₀`, then `γₙ (tₙ) → γ t₀`. The set of times where the
convergence invariant `ConvAt` holds contains `0` and is clopen by the
flow-box step (`exists_conv_step`), hence is all of the connected line `ℝ`;
the moving-time flow-box estimate (`exists_conv_step_eval`) at `t₀` finishes.
The statement instantiates the endpoint-continuity hypothesis `hend` of
`Riemannian.Exponential.completeSpace_of_forall_geodesic`. -/
theorem tendsto_geodesic_eval_of_tendsto_initialData (g : RiemannianMetric I M') (p : M')
    {γ : ℝ → M'} {γs : ℕ → ℝ → M'} {v : E} {vs : ℕ → E} {ts : ℕ → ℝ} {t₀ : ℝ}
    (hγgeo : IsGeodesic (I := I) g γ) (hγc : Continuous γ) (hγ0 : γ 0 = p)
    (hgeo : ∀ n, IsGeodesic (I := I) g (γs n)) (hc : ∀ n, Continuous (γs n))
    (h0 : ∀ n, γs n 0 = p)
    (hγv : HasDerivAt (fun τ => extChartAt I p (γ τ)) v 0)
    (hv : ∀ n, HasDerivAt (fun τ => extChartAt I p (γs n τ)) (vs n) 0)
    (hvs : Filter.Tendsto vs Filter.atTop (𝓝 v))
    (hts : Filter.Tendsto ts Filter.atTop (𝓝 t₀)) :
    Filter.Tendsto (fun n => γs n (ts n)) Filter.atTop (𝓝 (γ t₀)) := by
  subst hγ0
  -- base case: the invariant holds at time `0` — positions are constantly
  -- `γ 0`, and the chart velocities at `0` converge by hypothesis
  have hbase : ConvAt (I := I) γ γs 0 := by
    constructor
    · simp only [h0]
      exact tendsto_const_nhds
    · have hseq : (fun n => deriv (fun τ => extChartAt I (γ 0) (γs n τ)) 0) = vs :=
        funext fun n => (hv n).deriv
      rw [hseq, hγv.deriv]
      exact hvs
  -- clopen globalization: the invariant holds at every time
  have hall : ∀ t : ℝ, ConvAt (I := I) γ γs t := by
    have hopen : IsOpen {t : ℝ | ConvAt (I := I) γ γs t} := by
      rw [Metric.isOpen_iff]
      intro t ht
      obtain ⟨ρ, hρ, hstep⟩ := exists_conv_step (I := I) g hγgeo hγc hgeo hc t
      refine ⟨ρ, hρ, fun u hu => ?_⟩
      rw [Metric.mem_ball, Real.dist_eq] at hu
      exact hstep t u (by simpa using hρ.le) hu.le ht
    have hclosed : IsClosed {t : ℝ | ConvAt (I := I) γ γs t} := by
      refine isClosed_of_closure_subset fun t ht => ?_
      obtain ⟨ρ, hρ, hstep⟩ := exists_conv_step (I := I) g hγgeo hγc hgeo hc t
      obtain ⟨t', ht'S, ht'd⟩ := Metric.mem_closure_iff.mp ht ρ hρ
      rw [Real.dist_eq, abs_sub_comm] at ht'd
      exact hstep t' t ht'd.le (by simpa using hρ.le) ht'S
    have huniv : {t : ℝ | ConvAt (I := I) γ γs t} = Set.univ :=
      IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, hbase⟩
    exact fun t => Set.eq_univ_iff_forall.mp huniv t
  -- moving-time finish: the flow-box estimate at `t₀` evaluates the tail
  -- at the converging times `ts n`
  obtain ⟨ρ, hρ, hstep⟩ := exists_conv_step_eval (I := I) g hγgeo hγc hgeo hc t₀
  have hself : |t₀ - t₀| ≤ ρ := by simpa using hρ.le
  have hev : ∀ᶠ n in Filter.atTop, |ts n - t₀| ≤ ρ := by
    filter_upwards [hts (Metric.closedBall_mem_nhds t₀ hρ)] with n hn
    simpa [Real.dist_eq] using hn
  exact (hstep t₀ hself (hall t₀) ts t₀ hself hev hts).1

end Geodesic

end Riemannian
