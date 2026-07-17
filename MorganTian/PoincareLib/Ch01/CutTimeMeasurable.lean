import PoincareLib.Ch01.CutLocus

/-!
# Morgan–Tian Ch. 1, §1.5 — the cut time is measurable, and the sup is attained

Two facts about the cut time `c(v)` of `Ch01/CutLocus.lean`, both consequences of one observation:

  **the minimizing condition is a closed condition.**

`γ_v` is minimizing up to `t` iff `d(p, γ_v(t)) = t·|v|_g`, an equality between two functions that
are continuous in `t` (the geodesic is continuous) and continuous in `v` (`exp_p` is continuous, and
the metric `g_p` is a *continuous* bilinear form on `T_pM`). From the `t`-side we get that the set
`T_v` of minimizing times is closed, hence the supremum defining `c(v)` is **attained**:

  `le_cutTime_iff` : `0 ≤ t → (ENNReal.ofReal t ≤ c(v) ↔ γ_v is minimizing up to t)`.

From the `v`-side we then get that every superlevel set `{v | ofReal t ≤ c(v)}` is *closed*, hence

  `measurable_cutTime` : `Measurable (cutTime g hg p)`.

**Why this matters.** `c` is famously only *upper* semicontinuous in general — lower semicontinuity
(equivalently: openness of the segment domain `U_p`) is the hard half, and needs the Klingenberg
dichotomy. Measurability is all the volume theory ever uses, and it is cheap: it follows from
upper semicontinuity alone. This is what lets `Ch01/CutLocusNull.lean` prove `μ_g(C_p) = 0` without
first proving `U_p` open.

`cutTime_smul_eq_one` records the rescaling fact in the exact form the cut-vector set needs:
if `u` is a `g`-unit vector with finite cut time `c`, then `c·u` has cut time exactly `1`.
-/

open MeasureTheory Set Filter Riemannian Riemannian.Geodesic
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]

/-! ## The radial geodesic as the exponential of a rescaled vector -/

/-- **Math.** `γ_v(t) = exp_p(t·v)`: the radial geodesic evaluated at time `t` is the exponential of
the rescaled vector. This is `globalGeodesic_smul` read at `s = 1`, and it is what converts every
statement about `t ↦ γ_v(t)` into a statement about the *continuous* map `exp_p`. -/
theorem globalGeodesic_eq_expMapGlobal_smul (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    globalGeodesic (I := I) g hg p v t
      = expMapGlobal (I := I) g hg p ((t • v : TangentSpace I p)) := by
  simp [expMapGlobal_def, globalGeodesic_smul g hg p v t]

/-! ## The metric is a continuous quadratic form on the tangent space -/

/-- **Math.** `v ↦ |v|²_g = g_p(v,v)` is continuous on `T_pM`.

Note this cannot be read off `g.inner p` being a *continuous* linear map: mathlib's `TangentSpace`
carries only a topological-module structure (it derives `TopologicalSpace, AddCommGroup, Module`,
no norm), so `ContinuousLinearMap.continuous₂` — which lives in the normed setting — does not
apply to the fibre. Instead we go through the chart: at the pole of its own chart the Gram form
*is* `g_p` (`chartMetricInner_extChartAt_eq_metricInner`), and the chart Gram form is a finite sum
of products of continuous coordinate functionals (`continuous_chartMetricInner_pair`). -/
theorem continuous_metricInner_self (g : RiemannianMetric I M) (p : M) :
    Continuous (fun v : E => g.metricInner p (v : TangentSpace I p) (v : TangentSpace I p)) := by
  have hpole : ∀ w : E,
      chartMetricInner (I := I) g p (extChartAt I p p) w w
        = g.metricInner p (w : TangentSpace I p) (w : TangentSpace I p) := by
    intro w
    have hb := chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) w w
    rwa [trivializationAt_symm_self (I := I) p w] at hb
  -- the chart Gram quadratic form: a finite sum of products of continuous coordinate functionals
  have hcont : Continuous fun v : E =>
      chartMetricInner (I := I) g p (extChartAt I p p) v v := by
    simp only [chartMetricInner_def]
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_const.mul (Geodesic.continuous_chartCoord (E := E) i)).mul
        (Geodesic.continuous_chartCoord (E := E) j)
  exact hcont.congr hpole

/-- **Math.** `v ↦ |v|_g` is continuous on `T_pM`. -/
theorem continuous_metricNorm (g : RiemannianMetric I M) (p : M) :
    Continuous (fun v : E =>
      Real.sqrt (g.metricInner p (v : TangentSpace I p) (v : TangentSpace I p))) :=
  Real.continuous_sqrt.comp (continuous_metricInner_self (I := I) g p)

/-! ## The minimizing times form a closed set -/

/-- **Math.** `T_v = {t ≥ 0 : γ_v minimizes up to t}` is **closed**. Both sides of the defining
equality `d(p, γ_v(t)) = t·|v|_g` are continuous in `t`, so `T_v` is the intersection of `[0,∞)`
with the zero set of a continuous function. -/
theorem isClosed_minimizingTimes (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) : IsClosed (minimizingTimes (I := I) g hg p v) := by
  have hcont : Continuous fun t : ℝ =>
      dist p (globalGeodesic (I := I) g hg p v t) - Real.sqrt (g.metricInner p v v) * t :=
    ((continuous_const.dist (continuous_globalGeodesic (I := I) g hg p v)).sub
      (continuous_const.mul continuous_id))
  have hset : minimizingTimes (I := I) g hg p v
      = {t : ℝ | 0 ≤ t} ∩ (fun t : ℝ =>
          dist p (globalGeodesic (I := I) g hg p v t)
            - Real.sqrt (g.metricInner p v v) * t) ⁻¹' {0} := by
    ext t
    simp only [minimizingTimes, IsMinimizingUpTo, mem_setOf_eq, mem_inter_iff, mem_preimage,
      mem_singleton_iff, sub_eq_zero]
  rw [hset]
  exact isClosed_Ici.inter (IsClosed.preimage hcont isClosed_singleton)

/-! ## The supremum defining the cut time is attained -/

/-- **Math.** **The cut time dominates `t` exactly when `γ_v` minimizes up to `t`.**

The `←` direction is the definition of a supremum. The `→` direction is the content: it says the
supremum is *attained*, i.e. `γ_v` is still minimizing at the cut time itself. It holds because
`T_v` is closed (`isClosed_minimizingTimes`) and downward closed
(`IsMinimizingUpTo.mono`): if `c(v) ≥ t` then either some minimizing time already exceeds `t`
(and monotonicity gives `t ∈ T_v`), or `t` is a limit of minimizing times from below (and
closedness gives `t ∈ T_v`). -/
theorem le_cutTime_iff (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal t ≤ cutTime (I := I) g hg p v ↔ IsMinimizingUpTo (I := I) g hg p v t := by
  refine ⟨fun hle => ?_, fun h => le_cutTime (I := I) g hg p v ⟨ht, h⟩⟩
  rcases eq_or_lt_of_le ht with rfl | htpos
  · exact isMinimizingUpTo_zero (I := I) g hg p v
  -- Either some minimizing time reaches `t` …
  by_cases hreach : ∃ s ∈ minimizingTimes (I := I) g hg p v, t ≤ s
  · obtain ⟨s, hs, hts⟩ := hreach
    exact IsMinimizingUpTo.mono (I := I) g hg p v hs.2 ht hts
  -- … or `t` is a limit of minimizing times from below, and `T_v` is closed.
  push_neg at hreach
  have hmem : t ∈ closure (minimizingTimes (I := I) g hg p v) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    -- if no minimizing time exceeded `t - ε`, the supremum would be `≤ ofReal (t - ε) < ofReal t`
    by_contra hcon
    push_neg at hcon
    have hbound : ∀ s ∈ minimizingTimes (I := I) g hg p v, s ≤ t - ε := by
      intro s hs
      have hst : s < t := hreach s hs
      have := hcon s hs
      rw [Real.dist_eq, abs_of_pos (by linarith)] at this
      linarith
    have hsup : cutTime (I := I) g hg p v ≤ ENNReal.ofReal (t - ε) := by
      refine iSup₂_le fun s hs => ?_
      exact ENNReal.ofReal_le_ofReal (hbound s hs)
    have hlt : ENNReal.ofReal (t - ε) < ENNReal.ofReal t :=
      ENNReal.ofReal_lt_ofReal_iff htpos |>.2 (by linarith)
    exact absurd (hle.trans hsup) (not_le.2 hlt)
  have := (isClosed_minimizingTimes (I := I) g hg p v).closure_eq ▸ hmem
  exact this.2

/-! ## Measurability of the cut time -/

variable [MeasurableSpace E] [BorelSpace E]

/-- **Math.** For fixed `t ≥ 0`, the set of directions along which the radial geodesic minimizes up
to time `t` is **closed** in `T_pM`. The defining equality `d(p, exp_p(t·v)) = t·|v|_g` has both
sides continuous in `v`: the left by continuity of `exp_p` (`continuous_expMapGlobal`), the right
because `g_p` is a continuous bilinear form. -/
theorem isClosed_setOf_isMinimizingUpTo (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) (t : ℝ) :
    IsClosed {v : E | IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) t} := by
  have hL : Continuous fun v : E =>
      dist p (expMapGlobal (I := I) g hg p ((t • v : E) : TangentSpace I p)) :=
    continuous_const.dist
      ((continuous_expMapGlobal (I := I) g hg p).comp
        ((continuous_id (X := E)).const_smul t))
  have hR : Continuous fun v : E =>
      Real.sqrt (g.metricInner p (v : TangentSpace I p) (v : TangentSpace I p)) * t :=
    (continuous_metricNorm (I := I) g p).mul continuous_const
  have hset : {v : E | IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) t}
      = {v : E |
          dist p (expMapGlobal (I := I) g hg p ((t • v : E) : TangentSpace I p))
            = Real.sqrt (g.metricInner p (v : TangentSpace I p) (v : TangentSpace I p)) * t} := by
    ext v
    simp only [IsMinimizingUpTo, mem_setOf_eq,
      globalGeodesic_eq_expMapGlobal_smul (I := I) g hg p (v : TangentSpace I p) t]
  rw [hset]
  exact isClosed_eq hL hR

/-- **Math.** **The cut time is measurable.**

Its superlevel sets are closed: `{v | ofReal t ≤ c(v)} = {v | γ_v minimizes up to t}` by
`le_cutTime_iff`, and that set is closed by `isClosed_setOf_isMinimizingUpTo`. A function into
`ℝ≥0∞` with measurable `Ici`-preimages is measurable. -/
theorem measurable_cutTime (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    Measurable (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) := by
  refine measurable_of_Ici fun c => ?_
  rcases eq_or_ne c 0 with rfl | hc0
  · have hu : (Ici (0 : ℝ≥0∞)) = univ := by ext x; simp
    rw [hu, preimage_univ]
    exact MeasurableSet.univ
  rcases eq_top_or_lt_top c with rfl | hctop
  · -- `{v | c(v) = ∞} = ⋂ n, {v | ofReal n ≤ c(v)}`, a countable intersection of closed sets
    have hEq : (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) ⁻¹' Ici ⊤
        = ⋂ n : ℕ, {v : E | IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) (n : ℝ)} := by
      ext v
      simp only [mem_preimage, mem_Ici, top_le_iff, mem_iInter, mem_setOf_eq]
      constructor
      · intro htop n
        refine (le_cutTime_iff (I := I) g hg p (v : TangentSpace I p)
          (Nat.cast_nonneg n)).1 ?_
        rw [htop]; exact le_top
      · intro hall
        refine eq_top_iff.2 (le_of_forall_lt fun b hb => ?_)
        obtain ⟨n, hn⟩ := exists_nat_gt b.toReal
        refine lt_of_lt_of_le ?_
          ((le_cutTime_iff (I := I) g hg p (v : TangentSpace I p)
            (Nat.cast_nonneg n)).2 (hall n))
        calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb.ne_top).symm
          _ < ENNReal.ofReal (n : ℝ) :=
              ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hn) |>.2 hn
    rw [hEq]
    exact MeasurableSet.iInter fun n =>
      (isClosed_setOf_isMinimizingUpTo (I := I) g hg p (n : ℝ)).measurableSet
  · -- `c` is finite and nonzero: `{v | c ≤ c(v)} = {v | γ_v minimizes up to c.toReal}`
    have hcr : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hctop.ne
    have hEq : (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) ⁻¹' Ici c
        = {v : E | IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) c.toReal} := by
      ext v
      simp only [mem_preimage, mem_Ici, mem_setOf_eq]
      refine ⟨fun h => (le_cutTime_iff (I := I) g hg p (v : TangentSpace I p)
        ENNReal.toReal_nonneg).1 (by rwa [hcr]), fun h => ?_⟩
      rw [← hcr]
      exact (le_cutTime_iff (I := I) g hg p (v : TangentSpace I p) ENNReal.toReal_nonneg).2 h
    rw [hEq]
    exact (isClosed_setOf_isMinimizingUpTo (I := I) g hg p c.toReal).measurableSet

/-! ## Rescaling to cut time one -/

/-- **Math.** **The cut time rescales inversely with the vector**: `c(λ·v) = c(v)/λ`.

If the radial geodesic of `v` stops minimizing at the finite time `b`, then that of `λ·v` — which
traverses the same curve `λ` times faster — stops minimizing at `b/λ`.

Both inequalities are the reparameterisation `isMinimizingUpTo_smul`. The `≥` half additionally
needs the supremum to be *attained* (`le_cutTime_iff`): one has to know `γ_v` still minimizes *at*
its own cut time, not merely before it. -/
theorem cutTime_smul (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b)
    (hcut : cutTime (I := I) g hg p v = ENNReal.ofReal b) :
    cutTime (I := I) g hg p ((c • v : TangentSpace I p)) = ENNReal.ofReal (b / c) := by
  refine le_antisymm ?_ ?_
  · -- `≤` : a minimizing time `t > b/c` for `c·v` would give the minimizing time `c·t > b` for `v`
    by_contra hcon
    rw [not_le, cutTime, lt_iSup_iff] at hcon
    obtain ⟨t, hlt⟩ := hcon
    rw [lt_iSup_iff] at hlt
    obtain ⟨ht, hbt⟩ := hlt
    have htb : b / c < t := by
      by_contra hle
      rw [not_lt] at hle
      exact absurd hbt (not_lt.mpr (ENNReal.ofReal_le_ofReal hle))
    -- `c·v` minimizing up to `t` means `v` minimizing up to `c·t`
    have hv : IsMinimizingUpTo (I := I) g hg p v (c * t) :=
      (isMinimizingUpTo_smul (I := I) g hg p v hc t).1 ht.2
    have hle : ENNReal.ofReal (c * t) ≤ ENNReal.ofReal b := by
      rw [← hcut]
      exact le_cutTime (I := I) g hg p v ⟨mul_nonneg hc.le ht.1, hv⟩
    rw [ENNReal.ofReal_le_ofReal_iff hb] at hle
    rw [div_lt_iff₀ hc] at htb
    nlinarith
  · -- `≥` : `v` minimizes up to its own cut time `b`, so `c·v` minimizes up to `b/c`
    have hv : IsMinimizingUpTo (I := I) g hg p v b :=
      (le_cutTime_iff (I := I) g hg p v hb).1 (by rw [hcut])
    have hcv : IsMinimizingUpTo (I := I) g hg p ((c • v : TangentSpace I p)) (b / c) := by
      rw [isMinimizingUpTo_smul (I := I) g hg p v hc, mul_div_cancel₀ b (ne_of_gt hc)]
      exact hv
    exact le_cutTime (I := I) g hg p ((c • v : TangentSpace I p))
      ⟨div_nonneg hb hc.le, hcv⟩

/-- **Math.** **The cut vector of a unit direction has cut time `1`.** If `u` is a `g`-unit vector
whose radial geodesic stops minimizing at the finite time `c > 0`, then the vector `c·u` — the point
of `T_pM` that `exp_p` sends to the cut point — has cut time exactly `1`.

This is the equation that makes the set of cut vectors a *level set* of the (measurable) cut time,
and hence measurable. -/
theorem cutTime_smul_eq_one (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {u : TangentSpace I p} {c : ℝ} (hc : 0 < c)
    (hcut : cutTime (I := I) g hg p u = ENNReal.ofReal c) :
    cutTime (I := I) g hg p ((c • u : TangentSpace I p)) = 1 := by
  rw [cutTime_smul (I := I) g hg p u hc hc.le hcut, div_self (ne_of_gt hc), ENNReal.ofReal_one]

end PoincareLib

end
