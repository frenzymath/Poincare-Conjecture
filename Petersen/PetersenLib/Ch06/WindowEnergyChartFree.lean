import PetersenLib.Ch05.FirstVariation

/-!
# Petersen Ch. 6 — the chart-free energy of a variation is the `α`-read window energy

Ch. 5 defines the energy `E(γ)|_{t_1}^{t_2} = ½∫⟨γ̇, γ̇⟩` chart-freely
(`energyFunctional`), through `curveSpeedSq`, whose squared speed at time `t` is read in the
chart **centred at the foot point `γ t`** — a chart that *moves with `t`*.  Ch. 6's second
variation engine, by contrast, differentiates a genuine parametric integral: one **fixed**
chart `α` reads the whole slab, and the integrand is the chart Gram pairing
`chartMetricInner g α` of the `α`-reading's `t`-velocity with itself.

This file supplies the single bridge between the two, extracted from the tail of Ch. 5's
`hasDerivAt_windowEnergy`, so that Ch. 6 can consume it as a lemma rather than reprove it
inline.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** **The chart-free window energy is the fixed-chart window integral, near `s = 0`.**
For a smooth variation `f : (-δ, δ) × [t_1, t_2] → M` whose whole slab lies in the source of
the extended chart at a single point `α`,

$$E(f_s)\big|_{t_1}^{t_2}
  \;=\; \int_{t_1}^{t_2} \tfrac12\,
    \big\langle \partial_t (\varphi_\alpha \circ f_s),\, \partial_t (\varphi_\alpha \circ f_s)
    \big\rangle^{\varphi_\alpha(f_s(t))}_\alpha \, dt$$

for all `s` in a neighbourhood of `0`.

*Why the two sides are not definitionally the same.*  The left-hand side is Ch. 5's chart-free
`energyFunctional`, defined through `curveSpeedSq`, which at each time `t` reads the velocity in
the chart centred at the **moving foot point** `f s t`: the chart changes with `t` (and with
`s`).  The right-hand side reads the entire slab in the **one fixed chart `α`**.  The two agree
because the squared speed is a chart-independent quantity: the moving-chart velocity is the
coordinate change (`tangentCoordChange`) of the fixed-chart velocity, and the chart Gram
pairings `chartMetricInner` at the two centres are matched by exactly that coordinate change
(this is `curveSpeedSq_eq_chartMetricInner_of_hasDerivAt`).  So the identity is a change of
coordinates on the integrand, not a computation.

*Why the equality is only eventual in `s`.*  The bridge needs, at each time, the curve `f s ·`
to stay in `α`'s chart source on a whole neighbourhood of `t` — otherwise `φ_α ∘ f s` has no
derivative to read.  That is exactly what `hsrc` grants, but only for `s ∈ (-δ, δ)`; nothing is
known about `f s` for `|s| ≥ δ`, where the right-hand side may be meaningless.  Hence the
conclusion is an `EventuallyEq` at `𝓝 0`, opened by `Ioo (-δ) δ ∈ 𝓝 0`.  This is the shape the
second-variation engine wants anyway: it only ever differentiates in `s` at `s = 0`, and
`HasDerivAt.congr_of_eventuallyEq` consumes precisely an eventual equality.

The two endpoints `{t_1, t_2}` are discarded along the way: `hsrc` gives no interior
neighbourhood there, but they form a `volume`-null set, so `intervalIntegral.integral_congr_ae`
still identifies the integrals. -/
theorem energyFunctional_eventuallyEq_windowEnergy_chart (g : RiemannianMetric I M) (α : M)
    {f : ℝ → ℝ → M} {δ t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ < t₂)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Icc t₁ t₂))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Icc t₁ t₂,
      Function.uncurry f p ∈ (extChartAt I α).source) :
    (fun s => energyFunctional (I := I) g (f s) t₁ t₂) =ᶠ[𝓝 (0 : ℝ)]
      fun s => ∫ t in t₁..t₂, (1 / 2) * chartMetricInner (I := I) g α
        (extChartAt I α (f s t))
        (derivWithin (fun t' => extChartAt I α (f s t')) (Icc t₁ t₂) t)
        (derivWithin (fun t' => extChartAt I α (f s t')) (Icc t₁ t₂) t) := by
  classical
  set S : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Icc t₁ t₂ with hS_def
  -- the chart-`α` reading of the variation
  set c : ℝ × ℝ → E := fun p => extChartAt I α (f p.1 p.2) with hc_def
  have hcd : ContDiffOn ℝ ∞ c S := contDiffOn_extChartAt_comp₂ hf hsrc
  -- the one-sided `t`-slice derivative of the chart reading, on the slab
  have hslice_t : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      HasDerivWithinAt (fun t' => c (s, t'))
        (fderivWithin ℝ c S (s, t) ((0, 1) : ℝ × ℝ)) (Icc t₁ t₂) t := by
    intro s t hs ht
    have hdw : DifferentiableWithinAt ℝ c S (s, t) :=
      (hcd (s, t) ⟨hs, ht⟩).differentiableWithinAt (by norm_num)
    have hline : HasDerivAt (fun t' : ℝ => ((s, t') : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) t := by
      simpa using (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
    exact hdw.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq t
      (hline.hasDerivWithinAt (s := Icc t₁ t₂)) (fun t' ht' => ⟨hs, ht'⟩) rfl
  have hderivWithin_t : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t
        = fderivWithin ℝ c S (s, t) ((0, 1) : ℝ × ℝ) := by
    intro s t hs ht
    exact (hslice_t hs ht).derivWithin (uniqueDiffOn_Icc h12 t ht)
  -- the two window endpoints are a null set, so they may be discarded
  have hnull : volume ({t₁, t₂} : Set ℝ) = 0 := (Set.toFinite _).measure_zero volume
  have hIoc_mem : ∀ {t : ℝ}, t ∈ Ι t₁ t₂ → t ∉ ({t₁, t₂} : Set ℝ) → t ∈ Ioo t₁ t₂ := by
    intro t htI htbad
    rw [Set.uIoc_of_le h12.le, Set.mem_Ioc] at htI
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htbad
    exact ⟨htI.1, lt_of_le_of_ne htI.2 htbad.2⟩
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
  rw [energyFunctional_def, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
  have ht : t ∈ Ioo t₁ t₂ := hIoc_mem htI htbad
  have htIcc : t ∈ Icc t₁ t₂ := Ioo_subset_Icc_self ht
  have hsrc_ev : ∀ᶠ r in 𝓝 t, f s r ∈ (extChartAt I α).source := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact hsrc (s, r) ⟨hs, Ioo_subset_Icc_self hr⟩
  have hx : HasDerivAt (fun r => extChartAt I α (f s r))
      (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t) t := by
    have h1 := (hslice_t hs htIcc).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rw [hderivWithin_t hs htIcc]
    exact h1
  have hspeed := curveSpeedSq_eq_chartMetricInner_of_hasDerivAt (I := I) g hsrc_ev hx
  simp only [hc_def] at hspeed
  rw [hspeed]

end PetersenLib
