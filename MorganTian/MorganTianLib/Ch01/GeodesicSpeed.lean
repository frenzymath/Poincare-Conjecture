import MorganTianLib.Ch01.BrokenEnergy
import MorganTianLib.Ch01.Geodesics
import OpenGALib.Riemannian.Geodesic.HopfRinow.ConstantSpeed

/-!
# Poincaré Ch. 1 — constant speed of a geodesic, and the energy of a minimizing geodesic

Half 2 of `prop:minimal-geodesic-no-conjugate` needs the hypothesis "`γ` is minimal"
turned into an **energy** statement: `2 E(γ) = d(γ 0, γ 1)²`, in exactly the
normalisation of `MorganTianLib.sq_dist_le_sum_chart_energy` (whose right-hand side
`∑ᵢ ∫ᵢ ⟨u′, u′⟩` *is* `2 E`).  That needs minimality **together with constant speed**.

## Constant speed

The intrinsic squared speed `speedSq g γ t = g_{γ t}(γ′ t, γ′ t)` and its constancy
along a geodesic already exist in OpenGALib
(`Riemannian.Geodesic.speedSq`, `Riemannian.Geodesic.IsGeodesicOn.speedSq_eq`, do Carmo
Ch. 3 §2: `d/dt⟨γ′,γ′⟩ = 2⟨Dγ′/dt, γ′⟩ = 0`).  We restate it here in Morgan–Tian's
notation (`isGeodesicOn_metricInner_velocity_eq`) and — this is the new content — read
it in a **fixed chart**:

* `speedSq_eq_chartMetricInner_of_mem_source` — the intrinsic squared speed of a
  geodesic equals its chart-Gram expression in *any* chart containing the foot
  (OpenGALib only has the version whose chart is anchored at a point *of the curve*);
* `chartEnergyDensity_eq_speedSq` — hence the **chart energy density** of
  `BrokenEnergy.lean` (the integrand of `sq_dist_le_sum_chart_energy`, written with
  `derivWithin` over the piece) is constant along a geodesic.

## Energy of a minimizing geodesic

* `sum_chart_energy_eq_speedSq` — for a geodesic cut at any partition of `[0, 1]` and
  read in any chart on each piece, `∑ᵢ ∫ᵢ ⟨u′, u′⟩ = ⟨γ′, γ′⟩` (the pieces' widths sum
  to `1`).  This is `2 E(γ) = c²` with `c` the (constant) speed.
  The minimality hypothesis of the two theorems below is `√⟨γ′, γ′⟩ ≤ d(γ 0, γ 1)`, i.e.
  literally "the length of `γ` is at most the distance between its endpoints": the length
  of a *unit-time* geodesic **is** its speed, `ℓ(γ|[a,b]) = √⟨γ′, γ′⟩ · (b - a)`
  (`Riemannian.Geodesic.IsGeodesicOn.pathELength_eq`), so any caller holding do Carmo's
  minimality in the `Manifold.pathELength` API can discharge it.  It is stated with `dist`
  rather than `pathELength` to keep the statement free of the `RiemannianBundle` instance
  (and of the `ContinuousENorm` diamond it drags onto `TangentSpace`).
* `dist_eq_sqrt_speedSq_of_minimizing` — with the converse inequality
  `d ≤ c` (`IsGeodesicOn.dist_le`, geodesics are `c`-Lipschitz), minimality forces
  `d(γ 0, γ 1) = c`.
* `sum_chart_energy_eq_sq_dist_of_minimizing` — **`2 E(γ) = d(γ 0, γ 1)²`**, the
  equality case of `sq_dist_le_sum_chart_energy`.  This is what makes `s = 0` a
  *minimum* of the energy of a variation of a minimizing geodesic.

Blueprint: `prop:minimal-geodesic-no-conjugate`, `claim:second-variation-minimal-geodesic`.
-/

open Set MeasureTheory
open scoped ContDiff Manifold Topology ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-! ## Constant speed -/

section Speed

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** The **squared speed** `⟨γ′(t), γ′(t)⟩_g` of a curve, `γ′(t) = mfderiv γ t 1`
the manifold velocity.  Alias of `Riemannian.Geodesic.speedSq`. -/
abbrev speedSq (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  Riemannian.Geodesic.speedSq (I := I) g γ t

/-- **Math.** **Geodesics have constant speed** (do Carmo Ch. 3, §2, the remark after
Def. 2.1): along a geodesic `γ` the quantity `g_{γ t}(γ′ t, γ′ t)` is independent of `t`.
The computation is `d/dt⟨γ′, γ′⟩ = 2⟨Dγ′/dt, γ′⟩ = 0`: metric compatibility turns the
derivative into the covariant acceleration, which vanishes by the geodesic equation; the
derivative vanishes at *every* time of the (open, preconnected) parameter set, so the
speed is constant there even though `γ` leaves every single chart.

This is `Riemannian.Geodesic.IsGeodesicOn.speedSq_eq`, restated in Morgan–Tian's
notation. -/
theorem isGeodesicOn_metricInner_velocity_eq {g : RiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s)
    (hconn : IsPreconnected s) (hcont : ContinuousOn γ s) {a b : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) :
    g.metricInner (γ a) (mfderiv 𝓘(ℝ, ℝ) I γ a 1) (mfderiv 𝓘(ℝ, ℝ) I γ a 1)
      = g.metricInner (γ b) (mfderiv 𝓘(ℝ, ℝ) I γ b 1) (mfderiv 𝓘(ℝ, ℝ) I γ b 1) :=
  Riemannian.Geodesic.IsGeodesicOn.speedSq_eq (I := I) hγ hs hconn hcont ha hb

/-- **Math.** The squared speed of a geodesic is **nonnegative** (it is a Gram form
evaluated on a single vector). -/
theorem speedSq_nonneg (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    0 ≤ speedSq (I := I) g γ t :=
  g.metricInner_self_nonneg _ _

/-- **Math.** **The squared speed of a geodesic in a fixed chart.**  If `γ` satisfies the
geodesic equation at `σ` and its foot `γ σ` lies in the chart at an *arbitrary* basepoint
`α : M`, then the intrinsic squared speed is the chart-Gram square of the chart velocity
`u′ = (φ_α ∘ γ)′`:

  `⟨γ′(σ), γ′(σ)⟩_g = G^α_{φ_α(γ σ)}(u′(σ), u′(σ))`.

OpenGALib's `HasGeodesicEquationAt.speedSq_eq_chartMetricInner` proves this for a chart
anchored at a point `γ t` *of the curve*; the proof only uses that the foot lies in the
chart source, so it generalises verbatim to any `α`.  The chart velocity is transported to
the foot chart by the tangent coordinate change (first-order calculus only, no Christoffel
transformation law), and the Gram form is the metric read through the trivialisation. -/
theorem speedSq_eq_chartMetricInner_of_mem_source {g : RiemannianMetric I M}
    {γ : ℝ → M} {σ : ℝ} {α : M} (h : HasGeodesicEquationAt (I := I) g γ σ)
    (hcont : ContinuousAt γ σ) (hsrc : γ σ ∈ (chartAt H α).source) :
    speedSq (I := I) g γ σ = chartMetricInner (I := I) g α (extChartAt I α (γ σ))
      (deriv (fun r => extChartAt I α (γ r)) σ)
      (deriv (fun r => extChartAt I α (γ r)) σ) := by
  have hder : deriv (fun r => extChartAt I α (γ r)) σ
      = tangentCoordChange I (γ σ) α (γ σ)
          (deriv (chartLocalCurve (I := I) γ σ) σ) :=
    h.deriv_extChartAt_eq hcont hsrc
  have hbridge := chartMetricInner_extChartAt_eq_metricInner (I := I) g α hsrc
    (deriv (fun r => extChartAt I α (γ r)) σ) (deriv (fun r => extChartAt I α (γ r)) σ)
  have hread : (trivializationAt E (TangentSpace I) α).symm (γ σ)
      (deriv (fun r => extChartAt I α (γ r)) σ)
      = deriv (chartLocalCurve (I := I) γ σ) σ := by
    rw [trivializationAt_symm_eq_tangentCoordChange (I := I) α hsrc, hder,
      tangentCoordChange_comp (I := I)
        ⟨⟨mem_extChartAt_source (γ σ), by rw [extChartAt_source]; exact hsrc⟩,
          mem_extChartAt_source (γ σ)⟩,
      tangentCoordChange_self (I := I) (mem_extChartAt_source (γ σ))]
  show g.metricInner (γ σ) (mfderiv 𝓘(ℝ, ℝ) I γ σ 1) (mfderiv 𝓘(ℝ, ℝ) I γ σ 1) = _
  rw [h.mfderiv_apply_one hcont, hbridge, hread]

/-- **Math.** **The chart energy density of a geodesic is its squared speed.**  On a
nondegenerate piece `[a, b]` of times along which the geodesic `γ` stays in the chart at
`α`, the integrand of `sq_dist_le_sum_chart_energy` — the chart Gram square of the
`derivWithin`-velocity of the chart reading — equals `⟨γ′(t), γ′(t)⟩_g` at every
`t ∈ [a, b]`.  (Over a nondegenerate `Icc` the `derivWithin` is the honest `deriv`, since
the chart reading of a geodesic is differentiable and `Icc a b` has the unique-derivative
property.) -/
theorem chartEnergyDensity_eq_speedSq {g : RiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s) (hcont : ContinuousOn γ s)
    {α : M} {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ s)
    (hsrc : ∀ r ∈ Icc a b, γ r ∈ (chartAt H α).source) {t : ℝ} (ht : t ∈ Icc a b) :
    chartMetricInner (I := I) g α (extChartAt I α (γ t))
        (derivWithin (fun r => extChartAt I α (γ r)) (Icc a b) t)
        (derivWithin (fun r => extChartAt I α (γ r)) (Icc a b) t)
      = speedSq (I := I) g γ t := by
  have hts : t ∈ s := hsub ht
  have hct : ContinuousAt γ t := (hcont t hts).continuousAt (hs.mem_nhds hts)
  have hgeo : HasGeodesicEquationAt (I := I) g γ t := hγ t hts
  have hD : HasDerivAt (fun r => extChartAt I α (γ r))
      (tangentCoordChange I (γ t) α (γ t) (deriv (chartLocalCurve (I := I) γ t) t)) t :=
    (hgeo.eventually_hasDerivAt_extChartAt hct (hsrc t ht)).self_of_nhds
  have hdw : derivWithin (fun r => extChartAt I α (γ r)) (Icc a b) t
      = deriv (fun r => extChartAt I α (γ r)) t := by
    rw [hD.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht), hD.deriv]
  rw [hdw, ← speedSq_eq_chartMetricInner_of_mem_source hgeo hct (hsrc t ht)]

end Speed

/-! ## The energy of a minimizing geodesic -/

section Energy

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** A partition `τ 0 = 0 ≤ τ 1 ≤ ⋯ ≤ τ n = 1` is monotone: `τ i ≤ τ j` for
`i ≤ j ≤ n`.  (Bookkeeping for the pieces of a broken chart reading.) -/
theorem partition_monotone {n : ℕ} {τ : ℕ → ℝ} (hτ : ∀ i < n, τ i ≤ τ (i + 1)) :
    ∀ j ≤ n, ∀ i ≤ j, τ i ≤ τ j := by
  intro j
  induction j with
  | zero => intro _ i hi; simp [Nat.le_zero.mp hi]
  | succ k ih =>
      intro hk i hi
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact (ih (Nat.le_of_succ_le hk) i (Nat.lt_succ_iff.mp h)).trans
          (hτ k (Nat.lt_of_succ_le hk))
      · rw [Nat.le_antisymm hi h]

/-- **Math.** Each piece of a partition of `[0, 1]` lies in `[0, 1]`. -/
theorem partition_piece_subset {n : ℕ} {τ : ℕ → ℝ} (hτ : ∀ i < n, τ i ≤ τ (i + 1))
    (hτ0 : τ 0 = 0) (hτn : τ n = 1) {i : ℕ} (hi : i < n) :
    Icc (τ i) (τ (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
  have hlo : (0 : ℝ) ≤ τ i := by
    rw [← hτ0]; exact partition_monotone hτ i (le_of_lt hi) 0 (Nat.zero_le _)
  have hhi : τ (i + 1) ≤ 1 := by
    rw [← hτn]; exact partition_monotone hτ n le_rfl (i + 1) hi
  exact Icc_subset_Icc hlo hhi

/-- **Math.** **The energy of a geodesic is its squared speed.**  Let `γ` be a geodesic on
an open preconnected set of times containing `[0, 1]`, cut at a partition
`τ 0 = 0 ≤ ⋯ ≤ τ n = 1` and read in a chart at `β i` on the `i`-th piece.  Then, in the
normalisation of `sq_dist_le_sum_chart_energy` (whose right-hand side is *twice* the
energy),

  `2 E(γ) = ∑ᵢ ∫_{τ i}^{τ (i+1)} ⟨u′, u′⟩ = ⟨γ′, γ′⟩_g = c²`,

because the integrand is the constant `c²` on each piece
(`chartEnergyDensity_eq_speedSq` and constancy of the speed) and the widths of the pieces
sum to `τ n - τ 0 = 1`.  Degenerate pieces `τ i = τ (i+1)` are harmless: both sides of the
piecewise identity vanish. -/
theorem sum_chart_energy_eq_speedSq (g : RiemannianMetric I M)
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s)
    (hconn : IsPreconnected s) (hcont : ContinuousOn γ s) (hIcc : Icc (0 : ℝ) 1 ⊆ s)
    {n : ℕ} {τ : ℕ → ℝ} {β : ℕ → M}
    (hτ : ∀ i < n, τ i ≤ τ (i + 1)) (hτ0 : τ 0 = 0) (hτn : τ n = 1)
    (hsrc : ∀ i < n, ∀ t ∈ Icc (τ i) (τ (i + 1)), γ t ∈ (chartAt H (β i)).source) :
    ∑ i ∈ Finset.range n,
        ∫ t in (τ i)..(τ (i + 1)),
          chartMetricInner (I := I) g (β i) (extChartAt I (β i) (γ t))
            (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
            (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
      = speedSq (I := I) g γ 0 := by
  have h0s : (0 : ℝ) ∈ s := hIcc ⟨le_rfl, zero_le_one⟩
  -- each piece integrates the constant `c = ⟨γ′, γ′⟩` over its width
  have hpiece : ∀ i ∈ Finset.range n,
      (∫ t in (τ i)..(τ (i + 1)),
          chartMetricInner (I := I) g (β i) (extChartAt I (β i) (γ t))
            (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
            (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t))
        = (τ (i + 1) - τ i) * speedSq (I := I) g γ 0 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rcases eq_or_lt_of_le (hτ i hi') with heq | hlt
    · rw [← heq]
      simp
    · have hsub : Icc (τ i) (τ (i + 1)) ⊆ s :=
        (partition_piece_subset hτ hτ0 hτn hi').trans hIcc
      have hcongr : ∀ t ∈ uIcc (τ i) (τ (i + 1)),
          chartMetricInner (I := I) g (β i) (extChartAt I (β i) (γ t))
              (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
              (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
            = speedSq (I := I) g γ 0 := by
        intro t ht
        rw [uIcc_of_le (hτ i hi')] at ht
        rw [chartEnergyDensity_eq_speedSq hγ hs hcont hlt hsub (hsrc i hi') ht]
        exact Riemannian.Geodesic.IsGeodesicOn.speedSq_eq (I := I) hγ hs hconn hcont
          (hsub ht) h0s
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const,
        smul_eq_mul]
  rw [Finset.sum_congr rfl hpiece, ← Finset.sum_mul, Finset.sum_range_sub τ n, hτ0, hτn,
    sub_zero, one_mul]

/-- **Math.** **Minimality, unpacked.**  do Carmo's minimality hypothesis for a curve on
`[0, 1]` — "the length of `γ` is at most the distance between its endpoints", i.e.
`ℓ(γ|[0,1]) ≤ d(γ 0, γ 1)` — says exactly `√⟨γ′, γ′⟩ ≤ d(γ 0, γ 1)`, because the length of
a *unit-time* geodesic **is** its speed: `ℓ(γ|[a,b]) = √⟨γ′, γ′⟩ · (b - a)` by
`Riemannian.Geodesic.IsGeodesicOn.pathELength_eq`.  That is the shape in which the
minimality hypothesis `hmin` of the theorems below is to be discharged; it is stated here
as a `dist` inequality (no `Manifold.pathELength`, hence no `RiemannianBundle` instance) so
that it is instance-diamond free.

**Math.** **A minimizing geodesic on `[0, 1]` has speed `d(γ 0, γ 1)`.**  One
inequality is minimality (`√⟨γ′, γ′⟩ ≤ d`, the hypothesis); the other is that a geodesic is
Lipschitz with constant its speed (`IsGeodesicOn.dist_le`:
`d(γ 0, γ 1) ≤ √⟨γ′, γ′⟩ · (1 - 0)`). -/
theorem dist_eq_sqrt_speedSq_of_minimizing (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hcont : ContinuousOn γ s) (hIcc : Icc (0 : ℝ) 1 ⊆ s)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1)) :
    dist (γ 0) (γ 1) = Real.sqrt (speedSq (I := I) g γ 0) := by
  have h0s : (0 : ℝ) ∈ s := hIcc ⟨le_rfl, zero_le_one⟩
  have h1s : (1 : ℝ) ∈ s := hIcc ⟨zero_le_one, le_rfl⟩
  have hlip := Riemannian.Geodesic.IsGeodesicOn.dist_le (I := I) g hg hγ hs hconn hcont
    h0s h1s zero_le_one
  rw [sub_zero, mul_one] at hlip
  exact le_antisymm hlip hmin

/-- **Math.** **`2 E(γ) = d(γ 0, γ 1)²` for a minimizing geodesic** — the equality case of
`sq_dist_le_sum_chart_energy`, and the missing input (H2) of half 2 of
`prop:minimal-geodesic-no-conjugate`.

Let `γ` be a geodesic on an open preconnected set of times containing `[0, 1]`, cut at a
partition `τ 0 = 0 ≤ ⋯ ≤ τ n = 1` and read in a chart at `β i` on the `i`-th piece, and
suppose `γ` is **minimizing**: its length `√⟨γ′, γ′⟩` is at most `d(γ 0, γ 1)`
(discharge this from the `Manifold.pathELength` API through
`Riemannian.Geodesic.IsGeodesicOn.pathELength_eq`, the length of a unit-time geodesic
being its speed).
Then, in the exact normalisation of `sq_dist_le_sum_chart_energy`,

  `∑ᵢ ∫_{τ i}^{τ (i+1)} ⟨u′, u′⟩ = d(γ 0, γ 1)²`,

i.e. `2 E(γ) = d²`, i.e. `E(γ) = d²/2`.  Proof: the energy is the squared speed `c²`
(`sum_chart_energy_eq_speedSq`, by constant speed), and minimality forces `c = d`
(`dist_eq_sqrt_speedSq_of_minimizing`). -/
theorem sum_chart_energy_eq_sq_dist_of_minimizing (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hcont : ContinuousOn γ s) (hIcc : Icc (0 : ℝ) 1 ⊆ s)
    {n : ℕ} {τ : ℕ → ℝ} {β : ℕ → M}
    (hτ : ∀ i < n, τ i ≤ τ (i + 1)) (hτ0 : τ 0 = 0) (hτn : τ n = 1)
    (hsrc : ∀ i < n, ∀ t ∈ Icc (τ i) (τ (i + 1)), γ t ∈ (chartAt H (β i)).source)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1)) :
    ∑ i ∈ Finset.range n,
        ∫ t in (τ i)..(τ (i + 1)),
          chartMetricInner (I := I) g (β i) (extChartAt I (β i) (γ t))
            (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
            (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
      = dist (γ 0) (γ 1) ^ 2 := by
  rw [sum_chart_energy_eq_speedSq g hγ hs hconn hcont hIcc hτ hτ0 hτn hsrc,
    dist_eq_sqrt_speedSq_of_minimizing g hg hγ hs hconn hcont hIcc hmin,
    Real.sq_sqrt (speedSq_nonneg (I := I) g γ 0)]

/-- **Math.** The same statement in the `E = d²/2` normalisation: the energy
`E(γ) = ½ ∑ᵢ ∫ᵢ ⟨u′, u′⟩` of a minimizing geodesic on `[0, 1]` is `d(γ 0, γ 1)² / 2`. -/
theorem chart_energy_eq_sq_dist_div_two_of_minimizing (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hcont : ContinuousOn γ s) (hIcc : Icc (0 : ℝ) 1 ⊆ s)
    {n : ℕ} {τ : ℕ → ℝ} {β : ℕ → M}
    (hτ : ∀ i < n, τ i ≤ τ (i + 1)) (hτ0 : τ 0 = 0) (hτn : τ n = 1)
    (hsrc : ∀ i < n, ∀ t ∈ Icc (τ i) (τ (i + 1)), γ t ∈ (chartAt H (β i)).source)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1)) :
    (1 / 2 : ℝ) * ∑ i ∈ Finset.range n,
        ∫ t in (τ i)..(τ (i + 1)),
          chartMetricInner (I := I) g (β i) (extChartAt I (β i) (γ t))
            (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
            (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
      = dist (γ 0) (γ 1) ^ 2 / 2 := by
  rw [sum_chart_energy_eq_sq_dist_of_minimizing g hg hγ hs hconn hcont hIcc hτ hτ0 hτn
    hsrc hmin]
  ring

end Energy

end MorganTianLib

end

#print axioms MorganTianLib.isGeodesicOn_metricInner_velocity_eq
#print axioms MorganTianLib.speedSq_eq_chartMetricInner_of_mem_source
#print axioms MorganTianLib.chartEnergyDensity_eq_speedSq
#print axioms MorganTianLib.sum_chart_energy_eq_speedSq
#print axioms MorganTianLib.dist_eq_sqrt_speedSq_of_minimizing
#print axioms MorganTianLib.sum_chart_energy_eq_sq_dist_of_minimizing
#print axioms MorganTianLib.chart_energy_eq_sq_dist_div_two_of_minimizing
