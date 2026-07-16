import OpenGALib.Riemannian.Exponential.MinimizingGeodesic
import OpenGALib.Riemannian.Exponential.MinimizingPathPiecewise
import OpenGALib.Riemannian.Geodesic.HopfRinow.CurveReadback

/-!
# Poincaré Ch. 1 — the energy of a broken chart variation dominates the squared distance

This file proves the analytic half of Morgan–Tian's second-variation argument for
`prop:minimal-geodesic-no-conjugate`: for a *piecewise*-`C¹` curve `σ` joining `p = σ 0`
to `q = σ 1`, read in a chart on each piece,

  `d(p, q)² ≤ L(σ)² ≤ 2 E(σ)`,

where `L` is the length and `E = ½ ∑ᵢ ∫ᵢ ⟨σ′, σ′⟩` the energy.  In the normalisation used
below the right-hand side is literally `∑ᵢ ∫ᵢ ⟨σ′, σ′⟩` (twice the energy).

The proof is in three independent steps.

* `sq_intervalIntegral_le_mul_intervalIntegral_sq` — Cauchy–Schwarz on one interval,
  `(∫ f)² ≤ (b - a) ∫ f²`, by the discriminant trick.
* `sq_sum_le_sum_of_sq_le_mul` — the finite Cauchy–Schwarz recombination of the pieces.
  It is division-free, so degenerate pieces `τ i = τ (i+1)` are harmless.
* `dist_le_sum_chart_length` / `sq_dist_le_sum_chart_energy` — the manifold chain: the
  metric distance between the endpoints is bounded by the sum of the chart lengths of the
  pieces (`edist_le_pathELength_piecewise_partition`, `pathELength_sum_partition`,
  `pathELength_eq_ofReal_integral_chartMetricInner`), and then the two Cauchy–Schwarz
  steps upgrade `d ≤ ∑ Lᵢ` to `d² ≤ ∑ ∫ᵢ ⟨σ′, σ′⟩` because the piece widths `τ(i+1) - τ i`
  sum to `1`.

Blueprint: `claim:second-variation-minimal-geodesic`, `prop:minimal-geodesic-no-conjugate`.
-/

open Set MeasureTheory
open scoped ContDiff Manifold Topology ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

/-! ## Step 0 — a triviality about degenerate pieces -/

/-- **Math.** Any function is continuous on a set with at most one point: the neighbourhood
filter within a singleton is the pure filter.  This is what makes a *degenerate* piece
`τ i = τ (i+1)` of a partition harmless below. -/
theorem continuousOn_of_subsingleton {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set X} (hs : s.Subsingleton) : ContinuousOn f s := by
  intro x hx
  have hsub : s ⊆ {x} := fun y hy => hs hy hx
  have hle : 𝓝[s] x ≤ pure x := by
    calc 𝓝[s] x ≤ 𝓝[{x}] x := nhdsWithin_mono _ hsub
      _ = pure x := nhdsWithin_singleton x
  exact (tendsto_pure_nhds f x).mono_left hle

/-! ## Step 1 — Cauchy–Schwarz on one interval -/

/-- **Math.** **Cauchy–Schwarz for an interval integral.**  For a continuous `f` on `[a, b]`,
`(∫ₐᵇ f)² ≤ (b - a) · ∫ₐᵇ f²`.  Proof by the discriminant trick: for every `c`,
`0 ≤ ∫ (f - c)² = ∫ f² - 2c ∫ f + c²(b - a)`; taking `c = (∫ f)/(b - a)` when `a < b` and
rearranging gives the claim, while for `a = b` both sides vanish.

Applied with `f = |σ′|` this is the classical `L² ≤ (b - a) · 2E` bound. -/
theorem sq_intervalIntegral_le_mul_intervalIntegral_sq
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  have hf2 : ContinuousOn (fun t => (f t) ^ 2) (Set.Icc a b) := hf.pow 2
  have hf2i : IntervalIntegrable (fun t => (f t) ^ 2) volume a b :=
    hf2.intervalIntegrable_of_Icc hab
  set S : ℝ := ∫ t in a..b, f t with hS
  set Q : ℝ := ∫ t in a..b, (f t) ^ 2 with hQ
  have key : ∀ c : ℝ, 0 ≤ Q - 2 * c * S + c ^ 2 * (b - a) := by
    intro c
    have h0 : 0 ≤ ∫ t in a..b, (f t - c) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
    have hexp : (∫ t in a..b, (f t - c) ^ 2) = Q - 2 * c * S + c ^ 2 * (b - a) := by
      have hpt : ∀ t : ℝ, (f t - c) ^ 2 = ((f t) ^ 2 - (2 * c) * f t) + c ^ 2 := by
        intro t; ring
      simp_rw [hpt]
      rw [intervalIntegral.integral_add (hf2i.sub (hfi.const_mul (2 * c)))
          intervalIntegrable_const,
        intervalIntegral.integral_sub hf2i (hfi.const_mul (2 * c)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hexp] at h0
    exact h0
  have hba : 0 < b - a := by linarith
  have h := key (S / (b - a))
  have hne : (b - a) ≠ 0 := ne_of_gt hba
  have h' : 0 ≤ (Q - 2 * (S / (b - a)) * S + (S / (b - a)) ^ 2 * (b - a)) * (b - a) :=
    mul_nonneg h (le_of_lt hba)
  field_simp at h'
  nlinarith [h', hba, sq_nonneg S]

/-! ## Step 2 — the finite Cauchy–Schwarz recombination -/

/-- **Math.** **Recombining the pieces.**  If the piece lengths `A i` are nonnegative and
satisfy the Cauchy–Schwarz bound `(A i)² ≤ Δ i · B i` against the piece widths `Δ i` and the
piece energies `B i`, and the widths sum to `1`, then `(∑ A i)² ≤ ∑ B i`.

The proof is the finite Cauchy–Schwarz inequality applied to `√(Δ i)` and `√(B i)`; it uses
no division, so degenerate pieces (`Δ i = 0`) cause no trouble. -/
theorem sq_sum_le_sum_of_sq_le_mul
    {n : ℕ} {A Δ B : ℕ → ℝ}
    (hA : ∀ i ∈ Finset.range n, 0 ≤ A i)
    (hΔ : ∀ i ∈ Finset.range n, 0 ≤ Δ i)
    (hB : ∀ i ∈ Finset.range n, 0 ≤ B i)
    (hCS : ∀ i ∈ Finset.range n, (A i) ^ 2 ≤ Δ i * B i)
    (hsum : ∑ i ∈ Finset.range n, Δ i = 1) :
    (∑ i ∈ Finset.range n, A i) ^ 2 ≤ ∑ i ∈ Finset.range n, B i := by
  classical
  set r : ℕ → ℝ := fun i => Real.sqrt (Δ i * B i) with hr
  -- `A i ≤ r i` piecewise
  have hAr : ∀ i ∈ Finset.range n, A i ≤ r i := by
    intro i hi
    have h1 : A i = Real.sqrt ((A i) ^ 2) := (Real.sqrt_sq (hA i hi)).symm
    rw [h1, hr]
    exact Real.sqrt_le_sqrt (hCS i hi)
  have hsumAr : ∑ i ∈ Finset.range n, A i ≤ ∑ i ∈ Finset.range n, r i :=
    Finset.sum_le_sum hAr
  -- the Cauchy–Schwarz bound on `∑ r i`
  have hCS2 : (∑ i ∈ Finset.range n, r i) ^ 2
      ≤ (∑ i ∈ Finset.range n, Δ i) * ∑ i ∈ Finset.range n, B i := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ hΔ hB ?_
    intro i hi
    exact Real.sq_sqrt (mul_nonneg (hΔ i hi) (hB i hi))
  rw [hsum, one_mul] at hCS2
  have hAnn : 0 ≤ ∑ i ∈ Finset.range n, A i := Finset.sum_nonneg hA
  calc (∑ i ∈ Finset.range n, A i) ^ 2 ≤ (∑ i ∈ Finset.range n, r i) ^ 2 :=
        pow_le_pow_left₀ hAnn hsumAr 2
    _ ≤ ∑ i ∈ Finset.range n, B i := hCS2

/-! ## Step 3 — the manifold chain -/

section Manifold

open Riemannian Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** On a piece `[a, b]` along which a `C¹` curve `σ` stays in the chart at `α`, the
*chart energy density* `t ↦ g_{φ(σ t)}(u′ t, u′ t)` of the chart reading `u = φ_α ∘ σ` is
continuous.  Indeed `u` is `C¹` (`contDiffOn_extChartAt_comp`), so `u′ = derivWithin u` is
continuous, and the chart Gram form depends continuously on the base point and the two
vectors (`continuousOn_chartMetricInner_along`). -/
theorem continuousOn_chartEnergyDensity (g : RiemannianMetric I M) {σ : ℝ → M} {a b : ℝ}
    {α : M} (hab : a ≤ b) (hσ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc a b))
    (hsrc : ∀ t ∈ Icc a b, σ t ∈ (chartAt H α).source) :
    ContinuousOn (fun t => chartMetricInner (I := I) g α (extChartAt I α (σ t))
        (derivWithin (fun s => extChartAt I α (σ s)) (Icc a b) t)
        (derivWithin (fun s => extChartAt I α (σ s)) (Icc a b) t)) (Icc a b) := by
  set u : ℝ → E := fun s => extChartAt I α (σ s) with hu
  set u' : ℝ → E := derivWithin u (Icc a b) with hu'
  have huC1 : ContDiffOn ℝ 1 u (Icc a b) := contDiffOn_extChartAt_comp hσ hsrc
  have hu'cont : ContinuousOn u' (Icc a b) := by
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact continuousOn_of_subsingleton (by simp)
    · exact huC1.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
  have htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I α).target := fun t ht =>
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  exact continuousOn_chartMetricInner_along (I := I) g α huC1.continuousOn hu'cont hu'cont htgt

/-- **Math.** The chart energy density of a `C¹` curve is nonnegative: it is the Gram form of
the Riemannian metric evaluated on a single vector, read at a point of the chart target
(`chartMetricInner_self_nonneg_of_mem_target`). -/
theorem chartEnergyDensity_nonneg (g : RiemannianMetric I M) {σ : ℝ → M} {a b : ℝ}
    {α : M} (hsrc : ∀ t ∈ Icc a b, σ t ∈ (chartAt H α).source) {t : ℝ} (ht : t ∈ Icc a b) :
    0 ≤ chartMetricInner (I := I) g α (extChartAt I α (σ t))
        (derivWithin (fun s => extChartAt I α (σ s)) (Icc a b) t)
        (derivWithin (fun s => extChartAt I α (σ s)) (Icc a b) t) := by
  have htgt : extChartAt I α (σ t) ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  exact chartMetricInner_self_nonneg_of_mem_target (I := I) g α htgt _

/-- **Math.** **Cauchy–Schwarz on one piece.**  On a piece `[a, b]` along which the `C¹` curve
`σ` stays in the chart at `α`, the square of the chart *length* of the piece is at most the
width `b - a` times the chart *energy* (twice the energy) of the piece:

  `(∫ₐᵇ √⟨u′, u′⟩)² ≤ (b - a) · ∫ₐᵇ ⟨u′, u′⟩`.

This is `sq_intervalIntegral_le_mul_intervalIntegral_sq` applied to `f = √⟨u′, u′⟩`, whose
square is `⟨u′, u′⟩` because the chart Gram form is nonnegative on the chart target. -/
theorem sq_chartLength_le_mul_chartEnergy (g : RiemannianMetric I M) {σ : ℝ → M} {a b : ℝ}
    {α : M} (hab : a ≤ b) (hσ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc a b))
    (hsrc : ∀ t ∈ Icc a b, σ t ∈ (chartAt H α).source) :
    (∫ t in a..b, Real.sqrt (chartMetricInner (I := I) g α (extChartAt I α (σ t))
        (derivWithin (fun s => extChartAt I α (σ s)) (Icc a b) t)
        (derivWithin (fun s => extChartAt I α (σ s)) (Icc a b) t))) ^ 2
      ≤ (b - a) * ∫ t in a..b, chartMetricInner (I := I) g α (extChartAt I α (σ t))
        (derivWithin (fun s => extChartAt I α (σ s)) (Icc a b) t)
        (derivWithin (fun s => extChartAt I α (σ s)) (Icc a b) t) := by
  set q : ℝ → ℝ := fun t => chartMetricInner (I := I) g α (extChartAt I α (σ t))
      (derivWithin (fun s => extChartAt I α (σ s)) (Icc a b) t)
      (derivWithin (fun s => extChartAt I α (σ s)) (Icc a b) t) with hq
  have hqcont : ContinuousOn q (Icc a b) := continuousOn_chartEnergyDensity g hab hσ hsrc
  have hqnn : ∀ t ∈ Icc a b, 0 ≤ q t := fun t ht => chartEnergyDensity_nonneg g hsrc ht
  have hsq : ContinuousOn (fun t => Real.sqrt (q t)) (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn hqcont
  have hmain := sq_intervalIntegral_le_mul_intervalIntegral_sq hab hsq
  have hcongr : (∫ t in a..b, (Real.sqrt (q t)) ^ 2) = ∫ t in a..b, q t := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact Real.sq_sqrt (hqnn t ht)
  rw [hcongr] at hmain
  exact hmain

/-- **Math.** **The length half.**  For a piecewise-`C¹` curve `σ` on `[0, 1]`, cut at the
partition `τ 0 = 0 ≤ τ 1 ≤ ⋯ ≤ τ n = 1` and read in a chart at `β i` on the `i`-th piece, the
metric distance between the endpoints is at most the sum of the chart lengths of the pieces.

This is the triangle inequality plus the fact that the Riemannian distance is bounded by the
length of any competing curve (`edist_le_pathELength_piecewise_partition`), combined with the
additivity of the path length over a partition (`pathELength_sum_partition`) and the chart
readback of the length of a single `C¹` piece
(`pathELength_eq_ofReal_integral_chartMetricInner`). -/
theorem dist_le_sum_chartLength
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {σ : ℝ → M} {n : ℕ} {τ : ℕ → ℝ} {β : ℕ → M}
    (hτ : ∀ i < n, τ i ≤ τ (i + 1)) (hτ0 : τ 0 = 0) (hτn : τ n = 1)
    (hσ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1))))
    (hsrc : ∀ i < n, ∀ t ∈ Icc (τ i) (τ (i + 1)), σ t ∈ (chartAt H (β i)).source) :
    dist (σ 0) (σ 1)
      ≤ ∑ i ∈ Finset.range n,
          ∫ t in (τ i)..(τ (i + 1)),
            Real.sqrt (chartMetricInner (I := I) g (β i) (extChartAt I (β i) (σ t))
              (derivWithin (fun s => extChartAt I (β i) (σ s)) (Icc (τ i) (τ (i + 1))) t)
              (derivWithin (fun s => extChartAt I (β i) (σ s)) (Icc (τ i) (τ (i + 1))) t)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  set A : ℕ → ℝ := fun i =>
    ∫ t in (τ i)..(τ (i + 1)),
      Real.sqrt (chartMetricInner (I := I) g (β i) (extChartAt I (β i) (σ t))
        (derivWithin (fun s => extChartAt I (β i) (σ s)) (Icc (τ i) (τ (i + 1))) t)
        (derivWithin (fun s => extChartAt I (β i) (σ s)) (Icc (τ i) (τ (i + 1))) t)) with hA
  have hAnn : ∀ i ∈ Finset.range n, 0 ≤ A i := by
    intro i hi
    exact intervalIntegral.integral_nonneg (hτ i (Finset.mem_range.mp hi))
      fun t _ => Real.sqrt_nonneg _
  -- distance is bounded by the path length (instance paths are taken from the lemmas
  -- themselves: stating them by hand picks a different route to the tangent `ENorm`)
  have hedist := edist_le_pathELength_piecewise_partition g hg hτ hσ (le_of_eq hτ0) zero_le_one
    (le_of_eq hτn.symm)
  -- the path length is the sum of the piece lengths
  have hpart := pathELength_sum_partition (σ := σ) g hτ
  rw [hτ0, hτn] at hpart
  have hle : edist (σ 0) (σ 1) ≤ ENNReal.ofReal (∑ i ∈ Finset.range n, A i) := by
    rw [ENNReal.ofReal_sum_of_nonneg hAnn]
    refine hedist.trans ?_
    rw [← hpart]
    refine le_of_eq (Finset.sum_congr rfl ?_)
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact pathELength_eq_ofReal_integral_chartMetricInner g (hτ i hi') (hσ i hi') (hsrc i hi')
  rw [dist_edist]
  exact ENNReal.toReal_le_of_le_ofReal (Finset.sum_nonneg hAnn) hle

/-- **Math.** **`d(p, q)² ≤ 2 E(σ)`** (Morgan–Tian, Ch. 1, the elementary half of the second
variation argument for `prop:minimal-geodesic-no-conjugate`).  For a piecewise-`C¹` curve `σ`
on `[0, 1]`, cut at `τ 0 = 0 ≤ ⋯ ≤ τ n = 1` and read in a chart at `β i` on the `i`-th piece,

  `d(σ 0, σ 1)² ≤ ∑ᵢ ∫_{τ i}^{τ (i+1)} ⟨σ′, σ′⟩ = 2 E(σ)`.

Proof: `d ≤ ∑ᵢ Lᵢ` (`dist_le_sum_chartLength`); each piece satisfies the Cauchy–Schwarz bound
`Lᵢ² ≤ (τ(i+1) - τ i) · Eᵢ` (`sq_chartLength_le_mul_chartEnergy`); the widths telescope to
`τ n - τ 0 = 1`; so the finite Cauchy–Schwarz recombination `sq_sum_le_sum_of_sq_le_mul` gives
`(∑ᵢ Lᵢ)² ≤ ∑ᵢ Eᵢ`.

This is the inequality that makes `s = 0` a *minimum* of the energy of a variation of a
minimizing geodesic, hence `E″(0) ≥ 0`, hence `I(V, V) ≥ 0` for the index form. -/
theorem sq_dist_le_sum_chart_energy
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {σ : ℝ → M} {n : ℕ} {τ : ℕ → ℝ} {β : ℕ → M}
    (hτ : ∀ i < n, τ i ≤ τ (i + 1)) (hτ0 : τ 0 = 0) (hτn : τ n = 1)
    (hσ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1))))
    (hsrc : ∀ i < n, ∀ t ∈ Icc (τ i) (τ (i + 1)), σ t ∈ (chartAt H (β i)).source) :
    dist (σ 0) (σ 1) ^ 2
      ≤ ∑ i ∈ Finset.range n,
          ∫ t in (τ i)..(τ (i + 1)),
            chartMetricInner (I := I) g (β i) (extChartAt I (β i) (σ t))
              (derivWithin (fun s => extChartAt I (β i) (σ s)) (Icc (τ i) (τ (i + 1))) t)
              (derivWithin (fun s => extChartAt I (β i) (σ s)) (Icc (τ i) (τ (i + 1))) t) := by
  set A : ℕ → ℝ := fun i =>
    ∫ t in (τ i)..(τ (i + 1)),
      Real.sqrt (chartMetricInner (I := I) g (β i) (extChartAt I (β i) (σ t))
        (derivWithin (fun s => extChartAt I (β i) (σ s)) (Icc (τ i) (τ (i + 1))) t)
        (derivWithin (fun s => extChartAt I (β i) (σ s)) (Icc (τ i) (τ (i + 1))) t)) with hA
  set B : ℕ → ℝ := fun i =>
    ∫ t in (τ i)..(τ (i + 1)),
      chartMetricInner (I := I) g (β i) (extChartAt I (β i) (σ t))
        (derivWithin (fun s => extChartAt I (β i) (σ s)) (Icc (τ i) (τ (i + 1))) t)
        (derivWithin (fun s => extChartAt I (β i) (σ s)) (Icc (τ i) (τ (i + 1))) t) with hB
  set Δ : ℕ → ℝ := fun i => τ (i + 1) - τ i with hΔ
  have hAnn : ∀ i ∈ Finset.range n, 0 ≤ A i := fun i hi =>
    intervalIntegral.integral_nonneg (hτ i (Finset.mem_range.mp hi))
      fun t _ => Real.sqrt_nonneg _
  have hΔnn : ∀ i ∈ Finset.range n, 0 ≤ Δ i := fun i hi => by
    have := hτ i (Finset.mem_range.mp hi); simp only [hΔ]; linarith
  have hBnn : ∀ i ∈ Finset.range n, 0 ≤ B i := fun i hi =>
    intervalIntegral.integral_nonneg (hτ i (Finset.mem_range.mp hi))
      fun t ht => chartEnergyDensity_nonneg g (hsrc i (Finset.mem_range.mp hi)) ht
  have hCS : ∀ i ∈ Finset.range n, (A i) ^ 2 ≤ Δ i * B i := fun i hi => by
    have hi' := Finset.mem_range.mp hi
    exact sq_chartLength_le_mul_chartEnergy g (hτ i hi') (hσ i hi') (hsrc i hi')
  have hΔsum : ∑ i ∈ Finset.range n, Δ i = 1 := by
    simp only [hΔ]
    rw [Finset.sum_range_sub τ n, hτ0, hτn, sub_zero]
  have hlen : dist (σ 0) (σ 1) ≤ ∑ i ∈ Finset.range n, A i :=
    dist_le_sum_chartLength g hg hτ hτ0 hτn hσ hsrc
  calc dist (σ 0) (σ 1) ^ 2 ≤ (∑ i ∈ Finset.range n, A i) ^ 2 :=
        pow_le_pow_left₀ dist_nonneg hlen 2
    _ ≤ ∑ i ∈ Finset.range n, B i := sq_sum_le_sum_of_sq_le_mul hAnn hΔnn hBnn hCS hΔsum

end Manifold

end MorganTianLib

end
