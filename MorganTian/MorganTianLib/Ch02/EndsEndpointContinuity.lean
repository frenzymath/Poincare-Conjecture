import MorganTianLib.Ch02.EndsExist
import OpenGALib.Riemannian.Geodesic.EndpointContinuity
import OpenGALib.Riemannian.Geodesic.HopfRinow.ConstantSpeed
import OpenGALib.Riemannian.Exponential.ConvexNeighborhoodContinuity

/-!
# Morgan–Tian Ch. 2 — endpoint continuity from the flow-box step

The properness argument for `lem:ends-exist` (`EndsExist.lean`) rests on the
**endpoint continuity** `GeodesicEndpointContinuity g p`: global geodesics from
`p` with chart velocities `vₙ → v` satisfy `γₙ(tₙ) → γ(t₀)` whenever
`tₙ → t₀`.

This file reduces that continuity to a single **flow-box step**
`ConvStepProperty g` — the universally quantified form of do Carmo's
`exists_conv_step` (`OpenGALib`'s `Geodesic/EndpointContinuity.lean`): around
every base time there is a radius on which the convergence invariant
`Riemannian.Geodesic.ConvAt` (positions *and* chart-at-the-limit velocities
converge) propagates.  Granting that step, the argument is elementary:

* the invariant holds at `t = 0` (both curves start at `p` with the given
  velocities);
* the set of times where it holds is **clopen** in `ℝ` (the step propagates it
  both into and out of each base interval), hence — `ℝ` being connected — all of
  `ℝ`, giving position convergence `γₙ(t) → γ(t)` at every fixed `t`;
* a uniform Lipschitz estimate `d(γₙ s, γₙ t) ≤ √speedSqₙ · |s − t|`
  (`IsGeodesicOn.dist_le`, with `speedSqₙ = ⟨vₙ, vₙ⟩_p` bounded because
  `vₙ → v`) upgrades fixed times to converging times `tₙ → t₀`.

Discharging `ConvStepProperty g` unconditionally closes `lem:ends-exist`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7, Theorem 2.8, f) ⟹ b).
-/

open Set Filter Riemannian Riemannian.Geodesic Riemannian.Exponential
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- **Math.** **The flow-box convergence step** (universally quantified form of
do Carmo's `exists_conv_step`): for any limit geodesic `γ` and sequence of
geodesics `γs`, around every base time `tstar` there is a radius `ρ > 0` such
that the convergence invariant `Riemannian.Geodesic.ConvAt g γ γs`
propagates from any time to any other time within `ρ` of `tstar`. -/
def ConvStepProperty (g : RiemannianMetric I M) : Prop :=
  ∀ (γ : ℝ → M) (γs : ℕ → ℝ → M),
    IsGeodesic (I := I) g γ → Continuous γ →
    (∀ n, IsGeodesic (I := I) g (γs n)) → (∀ n, Continuous (γs n)) →
    ∀ tstar : ℝ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ t u : ℝ, |t - tstar| ≤ ρ → |u - tstar| ≤ ρ →
      ConvAt (I := I) g γ γs t → ConvAt (I := I) g γ γs u

/-- **Math.** **Endpoint continuity from the flow-box step.** Granting the
convergence step `ConvStepProperty g`, geodesics emanating from `p` depend
continuously on their initial velocity, uniformly in time along the limit
geodesic: `GeodesicEndpointContinuity g p`. -/
theorem geodesicEndpointContinuity_of_convStep (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) (p : M) (hstep : ConvStepProperty g) :
    GeodesicEndpointContinuity g p := by
  intro γ γs v vs ts t₀ hγgeo hγc hγ0 hγsgeo hγsc hγs0 hγv hγsv hvs hts
  -- The set of times where the convergence invariant holds.
  set S : Set ℝ := {t | ConvAt (I := I) g γ γs t} with hSdef
  -- Base case: the invariant holds at `t = 0`.
  have hbase : (0 : ℝ) ∈ S := by
    refine ⟨?_, ?_⟩
    · have hcurve : (fun n => γs n 0) = fun _ => γ 0 := by
        funext n; rw [hγs0 n, hγ0]
      rw [hcurve]; exact tendsto_const_nhds
    · have hchartγ : deriv (fun τ => extChartAt I (γ 0) (γ τ)) 0 = v := by
        rw [hγ0]; exact hγv.deriv
      have hchart : ∀ n, deriv (fun τ => extChartAt I (γ 0) (γs n τ)) 0 = vs n := by
        intro n; rw [hγ0]; exact (hγsv n).deriv
      rw [hchartγ]
      simp only [hchart]
      exact hvs
  -- The step, specialized to our data.
  have hstep' := hstep γ γs hγgeo hγc hγsgeo hγsc
  -- `S` is open.
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨ρ, hρ, hprop⟩ := hstep' t
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hρ) ?_
    intro u hu
    have hut : |u - t| ≤ ρ := by
      rw [Metric.mem_ball, Real.dist_eq] at hu; exact hu.le
    exact hprop t u (by simp [abs_zero, hρ.le]) hut ht
  -- `Sᶜ` is open, i.e. `S` is closed.
  have hScompl : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨ρ, hρ, hprop⟩ := hstep' t
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hρ) ?_
    intro u hu huS
    have hut : |u - t| ≤ ρ := by
      rw [Metric.mem_ball, Real.dist_eq] at hu; exact hu.le
    exact ht (hprop u t hut (by simp [abs_zero, hρ.le]) huS)
  -- `S` is clopen and nonempty, hence all of `ℝ`.
  have hSclopen : IsClopen S := ⟨isOpen_compl_iff.mp hScompl, hSopen⟩
  have hSuniv : S = Set.univ := hSclopen.eq_univ ⟨0, hbase⟩
  have hSall : ∀ t : ℝ, ConvAt (I := I) g γ γs t := by
    intro t
    have : t ∈ S := by rw [hSuniv]; exact Set.mem_univ t
    exact this
  -- Position convergence at every fixed time.
  have hpos : ∀ t : ℝ, Tendsto (fun n => γs n t) atTop (𝓝 (γ t)) := fun t => (hSall t).1
  -- The squared speed of each `γs n` in terms of the chart velocity `vs n`.
  have hspeed : ∀ n, speedSq (I := I) g (γs n) 0 =
      chartMetricInner (I := I) g p (extChartAt I p p) (vs n) (vs n) := by
    intro n
    have hp0 : (γs n) 0 = p := hγs0 n
    have hge : HasGeodesicEquationAt (I := I) g (γs n) 0 :=
      (hγsgeo n).hasGeodesicEquationAt 0
    have hcont : ContinuousAt (γs n) 0 := (hγsc n).continuousAt
    have hsrc : (γs n) 0 ∈ (chartAt H ((γs n) 0)).source := by
      rw [hp0]; exact mem_chart_source H p
    have h := hge.speedSq_eq_chartMetricInner (t := 0) hcont hsrc
    have e1 : chartLocalCurve (I := I) (γs n) 0 0 = extChartAt I p p := by
      simp only [chartLocalCurve_def, hp0]
    have e2 : deriv (chartLocalCurve (I := I) (γs n) 0) 0 = vs n := by
      have hfun : chartLocalCurve (I := I) (γs n) 0
          = fun τ => extChartAt I p (γs n τ) := by
        funext τ; simp only [chartLocalCurve_def, hp0]
      rw [hfun]; exact (hγsv n).deriv
    rw [h, e1, e2, hp0]
  -- The squared speeds are bounded above: they converge, being the chart Gram
  -- form `Q` of the convergent sequence `vs n → v`.  `Q` is kept opaque (`set`)
  -- so its heavy `chartMetricInner`/`extChartAt` unfolding never enters defeq.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ n, speedSq (I := I) g (γs n) 0 ≤ C := by
    set Q : E × E → ℝ :=
      fun z => chartMetricInner (I := I) g p (extChartAt I p p) z.1 z.2 with hQ
    have hpair : Continuous Q := continuous_chartMetricInner_pair (I := I) g p (extChartAt I p p)
    have hd : Tendsto (fun n => (vs n, vs n)) atTop (𝓝 ((v, v) : E × E)) :=
      hvs.prodMk_nhds hvs
    have hcomp : Tendsto (fun n => Q (vs n, vs n)) atTop (𝓝 (Q (v, v))) :=
      (hpair.tendsto (v, v)).comp hd
    obtain ⟨C, hCub⟩ := hcomp.bddAbove_range
    refine ⟨C, fun n => ?_⟩
    have hspeedQ : speedSq (I := I) g (γs n) 0 = Q (vs n, vs n) := by
      simp only [hQ, hspeed n]
    rw [hspeedQ]
    exact hCub ⟨n, rfl⟩
  -- A uniform Lipschitz constant for the geodesics `γs n`.
  have hLip : ∀ (n : ℕ) (s t : ℝ), dist (γs n s) (γs n t) ≤ Real.sqrt C * |s - t| := by
    intro n s t
    have hgon : IsGeodesicOn (I := I) g (γs n) Set.univ := (hγsgeo n).isGeodesicOn _
    have hconton : ContinuousOn (γs n) Set.univ := (hγsc n).continuousOn
    -- reduce to `a ≤ b`
    have hkey : ∀ a b : ℝ, a ≤ b →
        dist (γs n a) (γs n b) ≤ Real.sqrt C * (b - a) := by
      intro a b hab
      have hd := hgon.dist_le g hg isOpen_univ isPreconnected_univ hconton
        (Set.mem_univ a) (Set.mem_univ b) hab
      have hspeed_ab : speedSq (I := I) g (γs n) a = speedSq (I := I) g (γs n) 0 :=
        hgon.speedSq_eq isOpen_univ isPreconnected_univ hconton
          (Set.mem_univ a) (Set.mem_univ 0)
      rw [hspeed_ab] at hd
      have hle : Real.sqrt (speedSq (I := I) g (γs n) 0) ≤ Real.sqrt C :=
        Real.sqrt_le_sqrt (hC n)
      calc dist (γs n a) (γs n b)
          ≤ Real.sqrt (speedSq (I := I) g (γs n) 0) * (b - a) := hd
        _ ≤ Real.sqrt C * (b - a) := by
            apply mul_le_mul_of_nonneg_right hle (by linarith)
    rcases le_total s t with hst | hst
    · have := hkey s t hst
      rwa [abs_of_nonpos (by linarith : s - t ≤ 0), neg_sub]
    · have := hkey t s hst
      rw [dist_comm]
      rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)]
  -- Converging times: `γs n (ts n) → γ t₀`.
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ n, dist (γs n (ts n)) (γ t₀) ≤
      Real.sqrt C * |ts n - t₀| + dist (γs n t₀) (γ t₀) := by
    intro n
    calc dist (γs n (ts n)) (γ t₀)
        ≤ dist (γs n (ts n)) (γs n t₀) + dist (γs n t₀) (γ t₀) := dist_triangle _ _ _
      _ ≤ Real.sqrt C * |ts n - t₀| + dist (γs n t₀) (γ t₀) := by
          gcongr
          exact hLip n (ts n) t₀
  -- both terms of the bound tend to `0`
  have hterm1 : Tendsto (fun n => Real.sqrt C * |ts n - t₀|) atTop (𝓝 0) := by
    have : Tendsto (fun n => |ts n - t₀|) atTop (𝓝 0) := by
      have := (hts.sub_const t₀).abs
      simpa using this
    simpa using this.const_mul (Real.sqrt C)
  have hterm2 : Tendsto (fun n => dist (γs n t₀) (γ t₀)) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero.mp (hpos t₀))
  have hsum : Tendsto (fun n => Real.sqrt C * |ts n - t₀| + dist (γs n t₀) (γ t₀))
      atTop (𝓝 0) := by simpa using hterm1.add hterm2
  refine squeeze_zero (fun n => dist_nonneg) hbound hsum

end MorganTianLib

end
