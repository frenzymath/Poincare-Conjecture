import PetersenLib.Ch05.FirstVariation

/-!
# Petersen Ch. 5, §5.4 — local minima of energy are geodesics (Theorem 5.4.3)

Petersen's Theorem 5.4.3 (`thm:pet-ch5-energy-minima-geodesics`): a piecewise
smooth curve that is a local minimum of the energy functional among curves
with the same endpoints is a (smooth) geodesic.  The proof is the classical
calculus-of-variations argument, run through the first variation formula
(`firstVariationOfEnergy`, Lemma 5.4.2):

* **Chart bump variations** (`chartBumpVariation`): given a chart at `α`
  containing `γ` on a window `[t₁, t₂] ⊆ [a, b]` and a smooth field
  `w : ℝ → E` with `tsupport w ⊆ (t₁, t₂)`, deform `γ` inside the chart by
  `c̄(s, t) = φ_α⁻¹(φ_α(γ t) + s·w t)` and leave it unchanged elsewhere.  For
  small `s` this is a proper piecewise smooth variation of `γ`, smooth on
  every slab on which `γ` is smooth, with variational field
  `∂ₛc̄(0, t) = Dτ_{α→γ(t)}(w t)`.
* **The fundamental lemma of the calculus of variations**
  (`stationary_curveAcceleration_eq_zero`): at a time `τ` interior to a
  smooth piece, testing with `w = λ · v₀` (a `ContDiffBump` `λ` concentrated
  at `τ` times the constant chart acceleration `v₀ = ü(τ) + Γ_α(u̇, u̇)(u)|_τ`)
  makes the first variation `-∫ λ ⟨v₀, c̈⟩_α dt`, which vanishes only if the
  continuous nonnegative integrand vanishes at `τ`; positive-definiteness of
  the chart Gram pairing then forces `c̈(τ) = 0`.
* **Break-term elimination** (`stationary_velocityJump_eq_zero`): at a break
  `u_i` of the smoothness partition, testing with a bump equal to `1` at
  `u_i` times the constant velocity jump `w₀ = ∂ₜ⁻c̄ − ∂ₜ⁺c̄|_{u_i}` leaves
  only the break term `|w₀|²_g = 0`, so the one-sided velocities agree.
* **C² gluing at breaks**: with matching one-sided velocities, the geodesic
  equation itself matches the one-sided second derivatives (both equal
  `-Γ(v, v)(u)` by continuity of the coordinate ODE up to the break), so the
  foot-chart reading is twice differentiable *across* the break and the
  moving-foot geodesic equation `Geodesic.HasGeodesicEquationAt` holds there.
  (Petersen glues with local uniqueness, Theorem 5.2.2; since the Lean
  geodesic predicate asks for `C²` data at each time, the direct one-sided
  matching suffices and no ODE uniqueness is needed.)

`energyLocalMinimum_isGeodesic` assembles these into Theorem 5.4.3, and
`segment_isGeodesic` derives the corollary that piecewise smooth segments are
geodesics (`cor:pet-ch5-segments-are-geodesics`) via Proposition 5.4.1.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open scoped Manifold Topology ContDiff Interval

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Strict smoothness partitions -/

/-- **Eng.** Every piecewise smooth curve admits a **strictly increasing**
smoothness partition, ℕ-indexed as `firstVariationOfEnergy` consumes it:
drop the degenerate pieces of the monotone `Fin`-partition.  (`n = 0` occurs
exactly when `a = b`.) -/
theorem IsPiecewiseSmoothCurve.exists_strictMono_partition {γ : ℝ → M} {a b : ℝ}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b) :
    ∃ (n : ℕ) (u : ℕ → ℝ), (∀ i < n, u i < u (i + 1)) ∧ u 0 = a ∧ u n = b ∧
      ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (u i) (u (i + 1))) := by
  obtain ⟨-, m, v, hmono, hv0, hvm, hsm⟩ := hγ
  induction m generalizing a with
  | zero =>
    refine ⟨0, fun _ => a, by omega, rfl, ?_, by omega⟩
    rw [← hv0, ← hvm]
    rfl
  | succ m ih =>
    -- the tail partition, from `v 1` to `b`
    obtain ⟨n, u, hstrict, hu0, hun, husm⟩ := ih (a := v 1) (v := fun i => v i.succ)
      (fun i j hij => hmono (Fin.succ_le_succ_iff.mpr hij)) rfl
      (by rw [← hvm]; congr 1)
      (fun i => by
        have h := hsm i.succ
        rwa [← Fin.succ_castSucc] at h)
    rcases eq_or_lt_of_le (hmono (Fin.zero_le 1)) with hcase | hcase
    · -- degenerate first piece: reuse the tail partition
      exact ⟨n, u, hstrict, by rw [hu0, ← hcase, hv0], hun, husm⟩
    · -- prepend the first piece `[a, v 1]`
      refine ⟨n + 1, fun k => match k with | 0 => a | (j + 1) => u j, ?_, rfl, hun, ?_⟩
      · intro i hi
        match i with
        | 0 => simpa [hu0] using hv0 ▸ hcase
        | (j + 1) => exact hstrict j (by omega)
      · intro i hi
        match i with
        | 0 =>
          have h := hsm 0
          simpa [hv0, hu0] using h
        | (j + 1) => exact husm j (by omega)

section Boundaryless

variable [I.Boundaryless]

/-! ## The acceleration through a fixed chart -/

/-- **Math.** The acceleration `c̈(t)` of a curve, read at the foot chart, is
the coordinate change of the Γ-corrected second derivative of any fixed chart
reading `u = φ_α ∘ γ`:
`c̈(t) = Dτ_{α→γ(t)}(ü(t) + Γ_α(u̇(t), u̇(t))(u(t)))` — the inline corollary of
`chartReading_acceleration_transfer` that makes the fundamental lemma of the
calculus of variations a statement about the fixed chart `α`. -/
theorem curveAcceleration_eq_tangentCoordChange (g : RiemannianMetric I M)
    {γ : ℝ → M} {t : ℝ} {α : M}
    (hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I α).source)
    (hu1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I α (γ s'))
      (deriv (fun s' => extChartAt I α (γ s')) s) s)
    (hu2 : DifferentiableAt ℝ (deriv (fun s' => extChartAt I α (γ s'))) t) :
    curveAcceleration (I := I) g γ t
      = tangentCoordChange I α (γ t) (γ t)
          (deriv (deriv (fun s' => extChartAt I α (γ s'))) t
            + Geodesic.chartChristoffelContraction (I := I) g α
              (deriv (fun s' => extChartAt I α (γ s')) t)
              (deriv (fun s' => extChartAt I α (γ s')) t)
              (extChartAt I α (γ t))) := by
  classical
  -- `γ` is continuous at `t`: it is `φ_α⁻¹` of its continuous chart reading
  have hcont : ContinuousAt γ t := by
    have hBcont : ContinuousAt (fun s' => extChartAt I α (γ s')) t :=
      hu1.self_of_nhds.differentiableAt.continuousAt
    have hsymm : ContinuousAt (extChartAt I α).symm (extChartAt I α (γ t)) :=
      continuousAt_extChartAt_symm'' ((extChartAt I α).map_source hev.self_of_nhds)
    have hcomp : ContinuousAt ((extChartAt I α).symm ∘
        fun s' => extChartAt I α (γ s')) t :=
      hsymm.comp (f := fun s' => extChartAt I α (γ s')) (x := t) hBcont
    refine hcomp.congr ?_
    filter_upwards [hev] with s hs
    exact (extChartAt I α).left_inv hs
  have hev' : ∀ᶠ s in 𝓝 t,
      γ s ∈ (extChartAt I α).source ∩ (extChartAt I (γ t)).source := by
    filter_upwards [hev, hcont.eventually_mem
      ((isOpen_extChartAt_source (γ t)).mem_nhds
        (mem_extChartAt_source (I := I) (γ t)))] with s h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨hvel, hacc⟩ := chartReading_acceleration_transfer (I := I) g
    (γ := γ) (α := α) (β := γ t) hev' hu1 hu2.hasDerivAt
  have h1 : deriv (deriv (Geodesic.chartLocalCurve (I := I) γ t)) t
      = tangentCoordChange I α (γ t) (γ t)
          (deriv (deriv (fun s' => extChartAt I α (γ s'))) t
            + Geodesic.chartChristoffelContraction (I := I) g α
              (deriv (fun s' => extChartAt I α (γ s')) t)
              (deriv (fun s' => extChartAt I α (γ s')) t)
              (extChartAt I α (γ t)))
        - Geodesic.chartChristoffelContraction (I := I) g (γ t)
            (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
            (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
            (extChartAt I (γ t) (γ t)) := hacc.deriv
  rw [curveAcceleration_def]
  show (deriv (deriv (Geodesic.chartLocalCurve (I := I) γ t)) t +
      Geodesic.chartChristoffelContraction (I := I) g (γ t)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
        (extChartAt I (γ t) (γ t)) : E)
    = tangentCoordChange I α (γ t) (γ t)
        (deriv (deriv (fun s' => extChartAt I α (γ s'))) t
          + Geodesic.chartChristoffelContraction (I := I) g α
            (deriv (fun s' => extChartAt I α (γ s')) t)
            (deriv (fun s' => extChartAt I α (γ s')) t)
            (extChartAt I α (γ t)))
  rw [h1]
  abel

/-! ## Chart bump variations -/

/-- **Math.** The **chart bump variation** of a curve: inside the window
`(t₁, t₂)` deform `γ` in the chart at `α` along the field `w`,
`c̄(s, t) = φ_α⁻¹(φ_α(γ t) + s · w t)`; outside the window leave `γ`
untouched.  With `w` supported inside the window the two regimes agree near
the window ends, so the variation is as smooth as `γ` and `w` are. -/
def chartBumpVariation (α : M) (γ : ℝ → M) (w : ℝ → E) (t₁ t₂ : ℝ) (s t : ℝ) : M :=
  if t ∈ Ioo t₁ t₂ then (extChartAt I α).symm (extChartAt I α (γ t) + s • w t) else γ t

theorem chartBumpVariation_of_notMem {α : M} {γ : ℝ → M} {w : ℝ → E} {t₁ t₂ s t : ℝ}
    (ht : t ∉ Ioo t₁ t₂) :
    chartBumpVariation (I := I) α γ w t₁ t₂ s t = γ t := if_neg ht

theorem chartBumpVariation_of_eq_zero {α : M} {γ : ℝ → M} {w : ℝ → E} {t₁ t₂ s t : ℝ}
    (hsrc : ∀ t' ∈ Ioo t₁ t₂, γ t' ∈ (extChartAt I α).source) (hw : w t = 0) :
    chartBumpVariation (I := I) α γ w t₁ t₂ s t = γ t := by
  rw [chartBumpVariation]
  split_ifs with ht
  · rw [hw, smul_zero, add_zero, (extChartAt I α).left_inv (hsrc t ht)]
  · rfl

theorem chartBumpVariation_zero {α : M} {γ : ℝ → M} {w : ℝ → E} {t₁ t₂ t : ℝ}
    (hsrc : ∀ t' ∈ Ioo t₁ t₂, γ t' ∈ (extChartAt I α).source) :
    chartBumpVariation (I := I) α γ w t₁ t₂ 0 t = γ t := by
  rw [chartBumpVariation]
  split_ifs with ht
  · rw [zero_smul, add_zero, (extChartAt I α).left_inv (hsrc t ht)]
  · rfl

theorem chartBumpVariation_zero_eq {α : M} {γ : ℝ → M} {w : ℝ → E} {t₁ t₂ : ℝ}
    (hsrc : ∀ t' ∈ Ioo t₁ t₂, γ t' ∈ (extChartAt I α).source) :
    chartBumpVariation (I := I) α γ w t₁ t₂ 0 = γ :=
  funext fun _ => chartBumpVariation_zero hsrc

/-- **Eng.** A uniform variation half-width: for `|s|` small the deformed
chart points stay in the chart target.  Compactness of the window image plus
openness of the target (boundaryless model) give a uniform thickening
radius. -/
theorem exists_chartBumpVariation_width {α : M} {γ : ℝ → M} {w : ℝ → E} {t₁ t₂ : ℝ}
    (h12 : t₁ ≤ t₂) (hγc : ContinuousOn γ (Icc t₁ t₂)) (hw : Continuous w)
    (hsrc : ∀ t ∈ Icc t₁ t₂, γ t ∈ (extChartAt I α).source) :
    ∃ ε > 0, ∀ s : ℝ, |s| < ε → ∀ t ∈ Icc t₁ t₂,
      extChartAt I α (γ t) + s • w t ∈ (extChartAt I α).target := by
  have hKc : IsCompact ((fun t => extChartAt I α (γ t)) '' Icc t₁ t₂) := by
    refine isCompact_Icc.image_of_continuousOn ?_
    exact (continuousOn_extChartAt α).comp hγc fun t ht => hsrc t ht
  have hKsub : (fun t => extChartAt I α (γ t)) '' Icc t₁ t₂ ⊆ (extChartAt I α).target :=
    image_subset_iff.mpr fun t ht => (extChartAt I α).map_source (hsrc t ht)
  obtain ⟨δ, hδ, hthick⟩ :=
    hKc.exists_thickening_subset_open (isOpen_extChartAt_target α) hKsub
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (w t₁)) (hC t₁ (left_mem_Icc.mpr h12))
  refine ⟨δ / (C + 1), div_pos hδ (by linarith), fun s hs t ht => ?_⟩
  refine hthick ?_
  rw [Metric.mem_thickening_iff]
  refine ⟨extChartAt I α (γ t), mem_image_of_mem _ ht, ?_⟩
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  calc |s| * ‖w t‖ ≤ |s| * C := by
        exact mul_le_mul_of_nonneg_left (hC t ht) (abs_nonneg s)
    _ ≤ |s| * (C + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
    _ < δ / (C + 1) * (C + 1) := by
        exact mul_lt_mul_of_pos_right hs (by linarith)
    _ = δ := by field_simp

/-- **Eng.** The chart bump variation is smooth on every parameter slab over a
time interval on which `γ` is smooth: on the window the chart formula is a
composition of smooth maps, off the support of `w` the variation is constant
in `s` and equals `γ`, and the two regimes agree on the (open) overlap. -/
theorem chartBumpVariation_contMDiffOn_slab {α : M} {γ : ℝ → M} {w : ℝ → E}
    {t₁ t₂ p q ε : ℝ}
    (hγpq : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc p q))
    (hsrc : ∀ t ∈ Icc t₁ t₂, γ t ∈ (extChartAt I α).source)
    (hw : ContDiff ℝ ∞ w) (hwsupp : tsupport w ⊆ Ioo t₁ t₂)
    (htarget : ∀ s : ℝ, |s| < ε → ∀ t ∈ Icc t₁ t₂,
      extChartAt I α (γ t) + s • w t ∈ (extChartAt I α).target) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (Function.uncurry (chartBumpVariation (I := I) α γ w t₁ t₂))
      (Ioo (-ε) ε ×ˢ Icc p q) := by
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  by_cases hmem : t ∈ tsupport w
  · -- chart-formula regime, on the open window
    have htw : t ∈ Ioo t₁ t₂ := hwsupp hmem
    refine ⟨univ ×ˢ Ioo t₁ t₂, isOpen_univ.prod isOpen_Ioo, ⟨mem_univ _, htw⟩, ?_⟩
    have hmid : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => extChartAt I α (γ x.2) + x.1 • w x.2)
        ((Ioo (-ε) ε ×ˢ Icc p q) ∩ univ ×ˢ Ioo t₁ t₂) := by
      have huα : ContDiffOn ℝ ∞ (fun t' => extChartAt I α (γ t'))
          (Icc p q ∩ Icc t₁ t₂) :=
        contDiffOn_extChartAt_comp (hγpq.mono inter_subset_left)
          fun t' ht' => hsrc t' ht'.2
      refine ContDiffOn.add ?_ ?_
      · exact huα.comp contDiff_snd.contDiffOn
          fun x hx => ⟨hx.1.2, Ioo_subset_Icc_self hx.2.2⟩
      · exact (contDiff_fst.smul (hw.comp contDiff_snd)).contDiffOn
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun x : ℝ × ℝ => (extChartAt I α).symm (extChartAt I α (γ x.2) + x.1 • w x.2))
        ((Ioo (-ε) ε ×ˢ Icc p q) ∩ univ ×ˢ Ioo t₁ t₂) := by
      refine (contMDiffOn_extChartAt_symm α).comp
        (contMDiffOn_iff_contDiffOn.mpr hmid) ?_
      intro x hx
      exact htarget x.1 (abs_lt.mpr ⟨hx.1.1.1, hx.1.1.2⟩) x.2 (Ioo_subset_Icc_self hx.2.2)
    refine hcomp.congr fun x hx => ?_
    show chartBumpVariation (I := I) α γ w t₁ t₂ x.1 x.2 = _
    exact if_pos hx.2.2
  · -- constant-in-`s` regime, off the support of `w`
    refine ⟨univ ×ˢ (tsupport w)ᶜ, isOpen_univ.prod (isClosed_tsupport w).isOpen_compl,
      ⟨mem_univ _, hmem⟩, ?_⟩
    have hγs : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun x : ℝ × ℝ => γ x.2)
        ((Ioo (-ε) ε ×ˢ Icc p q) ∩ univ ×ˢ (tsupport w)ᶜ) :=
      hγpq.comp (contDiff_snd.contMDiff.contMDiffOn) fun x hx => hx.1.2
    refine hγs.congr fun x hx => ?_
    show chartBumpVariation (I := I) α γ w t₁ t₂ x.1 x.2 = γ x.2
    exact chartBumpVariation_of_eq_zero
      (fun t' ht' => hsrc t' (Ioo_subset_Icc_self ht'))
      (image_eq_zero_of_notMem_tsupport hx.2.2)

/-- **Eng.** The chart bump variation is continuous on the full parameter
strip over `[a, b]` (where `γ` is merely continuous). -/
theorem chartBumpVariation_continuousOn {α : M} {γ : ℝ → M} {w : ℝ → E}
    {t₁ t₂ a b ε : ℝ}
    (hγc : ContinuousOn γ (Icc a b)) (hwin : Icc t₁ t₂ ⊆ Icc a b)
    (hsrc : ∀ t ∈ Icc t₁ t₂, γ t ∈ (extChartAt I α).source)
    (hw : Continuous w) (hwsupp : tsupport w ⊆ Ioo t₁ t₂)
    (htarget : ∀ s : ℝ, |s| < ε → ∀ t ∈ Icc t₁ t₂,
      extChartAt I α (γ t) + s • w t ∈ (extChartAt I α).target) :
    ContinuousOn (Function.uncurry (chartBumpVariation (I := I) α γ w t₁ t₂))
      (Ioo (-ε) ε ×ˢ Icc a b) := by
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  by_cases hmem : t ∈ tsupport w
  · have htw : t ∈ Ioo t₁ t₂ := hwsupp hmem
    have hU : (univ ×ˢ Ioo t₁ t₂ : Set (ℝ × ℝ)) ∈ 𝓝 (s, t) :=
      (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, htw⟩
    rw [← continuousWithinAt_inter hU]
    have hmid : ContinuousOn (fun x : ℝ × ℝ => extChartAt I α (γ x.2) + x.1 • w x.2)
        ((Ioo (-ε) ε ×ˢ Icc a b) ∩ univ ×ˢ Ioo t₁ t₂) := by
      have huα : ContinuousOn (fun t' => extChartAt I α (γ t')) (Icc t₁ t₂) :=
        (continuousOn_extChartAt α).comp (hγc.mono hwin) fun t' ht' => hsrc t' ht'
      refine ContinuousOn.add ?_ ?_
      · exact huα.comp continuous_snd.continuousOn
          fun x hx => Ioo_subset_Icc_self hx.2.2
      · exact (continuous_fst.smul (hw.comp continuous_snd)).continuousOn
    have hcomp : ContinuousOn
        (fun x : ℝ × ℝ => (extChartAt I α).symm (extChartAt I α (γ x.2) + x.1 • w x.2))
        ((Ioo (-ε) ε ×ˢ Icc a b) ∩ univ ×ˢ Ioo t₁ t₂) := by
      refine (continuousOn_extChartAt_symm α).comp hmid ?_
      intro x hx
      exact htarget x.1 (abs_lt.mpr ⟨hx.1.1.1, hx.1.1.2⟩) x.2 (Ioo_subset_Icc_self hx.2.2)
    refine (hcomp.congr fun x hx => ?_) _ ⟨⟨hs, ht⟩, mem_univ _, htw⟩
    show chartBumpVariation (I := I) α γ w t₁ t₂ x.1 x.2 = _
    exact if_pos hx.2.2
  · have hU : (univ ×ˢ (tsupport w)ᶜ : Set (ℝ × ℝ)) ∈ 𝓝 (s, t) :=
      (isOpen_univ.prod (isClosed_tsupport w).isOpen_compl).mem_nhds ⟨mem_univ _, hmem⟩
    rw [← continuousWithinAt_inter hU]
    have hγs : ContinuousOn (fun x : ℝ × ℝ => γ x.2)
        ((Ioo (-ε) ε ×ˢ Icc a b) ∩ univ ×ˢ (tsupport w)ᶜ) :=
      hγc.comp continuous_snd.continuousOn fun x hx => hx.1.2
    refine (hγs.congr fun x hx => ?_) _ ⟨⟨hs, ht⟩, mem_univ _, hmem⟩
    show chartBumpVariation (I := I) α γ w t₁ t₂ x.1 x.2 = γ x.2
    exact chartBumpVariation_of_eq_zero
      (fun t' ht' => hsrc t' (Ioo_subset_Icc_self ht'))
      (image_eq_zero_of_notMem_tsupport hx.2.2)

/-- **Math.** The **variational field** of a chart bump variation, read in the
foot chart at a window time: `∂ₛc̄(0, t) = Dτ_{α→γ(t)}(w t)`, the coordinate
change of the deformation field. -/
theorem chartBumpVariation_hasDerivAt_field {α : M} {γ : ℝ → M} {w : ℝ → E}
    {t₁ t₂ t ε : ℝ} (hε : 0 < ε) (ht : t ∈ Ioo t₁ t₂)
    (hsrc : ∀ t' ∈ Icc t₁ t₂, γ t' ∈ (extChartAt I α).source)
    (htarget : ∀ s : ℝ, |s| < ε → ∀ t' ∈ Icc t₁ t₂,
      extChartAt I α (γ t') + s • w t' ∈ (extChartAt I α).target) :
    HasDerivAt (fun s => extChartAt I (γ t)
        (chartBumpVariation (I := I) α γ w t₁ t₂ s t))
      (tangentCoordChange I α (γ t) (γ t) (w t)) 0 := by
  have hsrct : γ t ∈ (extChartAt I α).source := hsrc t (Ioo_subset_Icc_self ht)
  have hline : HasDerivAt (fun s : ℝ => extChartAt I α (γ t) + s • w t) (w t) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (w t)).const_add (extChartAt I α (γ t))
  have hτ : HasFDerivAt (chartTransition (M := M) I α (γ t))
      (tangentCoordChange I α (γ t) (γ t)) (extChartAt I α (γ t)) :=
    hasFDerivAt_chartTransition hsrct (mem_extChartAt_source (I := I) (γ t))
  have hcomp : HasDerivAt (fun s : ℝ => chartTransition (M := M) I α (γ t)
      (extChartAt I α (γ t) + s • w t))
      (tangentCoordChange I α (γ t) (γ t) (w t)) 0 := by
    refine hτ.comp_hasDerivAt_of_eq 0 hline ?_
    simp
  refine hcomp.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < ε := by
    have := Metric.ball_mem_nhds (0 : ℝ) hε
    filter_upwards [this] with s hs
    simpa [Real.dist_eq] using hs
  filter_upwards [hev] with s hs
  have hmemT : extChartAt I α (γ t) + s • w t ∈ (extChartAt I α).target :=
    htarget s hs t (Ioo_subset_Icc_self ht)
  have hfs : chartBumpVariation (I := I) α γ w t₁ t₂ s t
      = (extChartAt I α).symm (extChartAt I α (γ t) + s • w t) := if_pos ht
  rw [hfs]
  have hx' : (extChartAt I α).symm (extChartAt I α (γ t) + s • w t)
      ∈ (extChartAt I α).source := (extChartAt I α).map_target hmemT
  have h1 := chartTransition_extChartAt (I := I) (M := M) (α := α) (β := γ t) hx'
  rw [(extChartAt I α).right_inv hmemT] at h1
  exact h1.symm

/-- **Eng.** Off the window, the variation is constant in `s`, so the
variational field vanishes. -/
theorem chartBumpVariation_field_eq_zero {α : M} {γ : ℝ → M} {w : ℝ → E}
    {t₁ t₂ t : ℝ} (ht : t ∉ Ioo t₁ t₂) :
    deriv (fun s => extChartAt I (γ t)
      (chartBumpVariation (I := I) α γ w t₁ t₂ s t)) 0 = 0 := by
  have h : (fun s => extChartAt I (γ t) (chartBumpVariation (I := I) α γ w t₁ t₂ s t))
      = fun _ => extChartAt I (γ t) (γ t) :=
    funext fun s => by rw [chartBumpVariation_of_notMem ht]
  rw [h]
  exact deriv_const 0 _

/-- **Eng.** Assemble a chart bump variation into a **proper piecewise smooth
variation** of `γ` along a strict smoothness partition, ready for the first
variation formula. -/
theorem exists_chartBumpVariation_curveVariation {γ : ℝ → M} {a b t₁ t₂ : ℝ}
    {α : M} {w : ℝ → E}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b)
    {n : ℕ} {u : ℕ → ℝ} (hu0 : u 0 = a) (hun : u n = b)
    (husm : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (u i) (u (i + 1))))
    (humono : ∀ i j, i ≤ j → j ≤ n → u i ≤ u j)
    (hwin : Icc t₁ t₂ ⊆ Icc a b) (h12 : t₁ ≤ t₂)
    (hsrc : ∀ t ∈ Icc t₁ t₂, γ t ∈ (extChartAt I α).source)
    (hw : ContDiff ℝ ∞ w) (hwsupp : tsupport w ⊆ Ioo t₁ t₂) :
    ∃ V : CurveVariation (I := I) γ a b,
      V.toFun = chartBumpVariation (I := I) α γ w t₁ t₂ ∧ IsProperVariation V ∧
      (∀ s : ℝ, |s| < V.width → ∀ t ∈ Icc t₁ t₂,
        extChartAt I α (γ t) + s • w t ∈ (extChartAt I α).target) ∧
      ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry V.toFun)
        (Ioo (-V.width) V.width ×ˢ Icc (u i) (u (i + 1))) := by
  obtain ⟨ε, hε, htarget⟩ :=
    exists_chartBumpVariation_width h12 (hγ.1.mono hwin) hw.continuous hsrc
  have hsrc' : ∀ t' ∈ Ioo t₁ t₂, γ t' ∈ (extChartAt I α).source :=
    fun t' ht' => hsrc t' (Ioo_subset_Icc_self ht')
  have ha_t₁ : a ≤ t₁ := (hwin (left_mem_Icc.mpr h12)).1
  have ht₂_b : t₂ ≤ b := (hwin (right_mem_Icc.mpr h12)).2
  refine ⟨⟨chartBumpVariation (I := I) α γ w t₁ t₂, ε, hε,
    fun t _ => chartBumpVariation_zero hsrc',
    chartBumpVariation_continuousOn hγ.1 hwin hsrc hw.continuous hwsupp htarget,
    ⟨n, fun i => u i, ?_, by simpa using hu0, by simpa using hun, ?_⟩⟩,
    rfl, ?_, htarget, ?_⟩
  · -- monotonicity of the Fin partition
    intro i j hij
    exact humono i j hij (Nat.le_of_lt_succ j.isLt)
  · -- slab smoothness for each piece
    intro i
    have h := chartBumpVariation_contMDiffOn_slab (ε := ε)
      (husm i i.isLt) hsrc hw hwsupp htarget
    simpa using h
  · -- properness: the window excludes the endpoints
    intro s _
    constructor
    · exact chartBumpVariation_of_notMem fun hmem => absurd hmem.1 (not_lt.mpr ha_t₁)
    · exact chartBumpVariation_of_notMem fun hmem => absurd hmem.2 (not_lt.mpr ht₂_b)
  · -- slab smoothness along the strict partition, ℕ-indexed
    intro i hi
    exact chartBumpVariation_contMDiffOn_slab (ε := ε)
      (husm i hi) hsrc hw hwsupp htarget

end Boundaryless

/-! ## The fundamental lemma of the calculus of variations, bump form -/

/-- **Eng.** A strict partition is monotone below its length. -/
theorem strictPartition_mono {n : ℕ} {u : ℕ → ℝ}
    (hstrict : ∀ i < n, u i < u (i + 1)) :
    ∀ i j, i ≤ j → j ≤ n → u i ≤ u j := by
  intro i j hij hjn
  induction j with
  | zero =>
    obtain rfl : i = 0 := Nat.le_zero.mp hij
    exact le_refl _
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact (ih (Nat.lt_succ_iff.mp h) (by omega)).trans (hstrict m (by omega)).le

/-- **Math.** The **fundamental lemma of the calculus of variations**, bump
form: a function continuous on `[t₁, t₂]` that integrates to zero against
every small smooth bump centred at an interior point `τ` is nonpositive
at `τ`.  (Testing against bumps concentrated where `Φ > Φ(τ)/2 > 0` would
otherwise make the integral positive.) -/
theorem nonpos_of_forall_contDiffBump_integral_eq_zero {Φ : ℝ → ℝ} {t₁ t₂ τ : ℝ}
    (hτ : τ ∈ Ioo t₁ t₂) (hΦ : ContinuousOn Φ (Icc t₁ t₂))
    (hint : ∀ lam : ContDiffBump τ, lam.rOut < min (τ - t₁) (t₂ - τ) →
      ∫ t in t₁..t₂, lam t * Φ t = 0) :
    Φ τ ≤ 0 := by
  by_contra hpos
  push Not at hpos
  -- a radius on which `Φ > Φ τ / 2 > 0`
  have hcontAt : ContinuousAt Φ τ := hΦ.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
  have hev : ∀ᶠ x in 𝓝 τ, Φ τ / 2 < Φ x :=
    hcontAt.eventually_const_lt (half_lt_self hpos)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hball⟩ := hev
  set r := min (η / 2) (min (τ - t₁) (t₂ - τ) / 2) with hr_def
  have hminpos : 0 < min (τ - t₁) (t₂ - τ) := by
    rcases hτ with ⟨h1, h2⟩
    exact lt_min (by linarith) (by linarith)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrη : r ≤ η / 2 := min_le_left _ _
  have hrm : r ≤ min (τ - t₁) (t₂ - τ) / 2 := min_le_right _ _
  have hrt₁ : min (τ - t₁) (t₂ - τ) ≤ τ - t₁ := min_le_left _ _
  have hrt₂ : min (τ - t₁) (t₂ - τ) ≤ t₂ - τ := min_le_right _ _
  set lam : ContDiffBump τ := ⟨r / 2, r, by linarith, by linarith⟩
  have hrOut : lam.rOut < min (τ - t₁) (t₂ - τ) := by
    show r < min (τ - t₁) (t₂ - τ)
    linarith
  -- the three continuity/integrability pieces
  have hsub : Icc (τ - r) (τ + r) ⊆ Icc t₁ t₂ := by
    intro x hx
    exact ⟨by rcases hx with ⟨h1, -⟩; linarith, by rcases hx with ⟨-, h2⟩; linarith⟩
  have hcontG : ContinuousOn (fun t => lam t * Φ t) (Icc t₁ t₂) :=
    lam.continuous.continuousOn.mul hΦ
  have hi1 : IntervalIntegrable (fun t => lam t * Φ t) volume t₁ (τ - r) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact hcontG.mono fun x hx => ⟨hx.1, by rcases hx with ⟨-, h2⟩; linarith⟩
  have hi2 : IntervalIntegrable (fun t => lam t * Φ t) volume (τ - r) (τ + r) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact hcontG.mono hsub
  have hi3 : IntervalIntegrable (fun t => lam t * Φ t) volume (τ + r) t₂ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact hcontG.mono fun x hx => ⟨by rcases hx with ⟨h1, -⟩; linarith, hx.2⟩
  -- the middle integral is positive
  have hpos_mid : 0 < ∫ t in (τ - r)..(τ + r), lam t * Φ t := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hi2 ?_ (by linarith)
    intro x hx
    have hxball : x ∈ Metric.ball τ lam.rOut := by
      show x ∈ Metric.ball τ r
      rw [Real.ball_eq_Ioo]
      exact hx
    refine mul_pos (lam.pos_of_mem_ball hxball) ?_
    have hxdist : dist x τ < η := by
      rw [Real.dist_eq, abs_lt]
      rcases hx with ⟨h1, h2⟩
      constructor <;> linarith
    exact lt_trans (by linarith) (hball hxdist)
  -- the outer integrals vanish
  have hzero1 : (∫ t in t₁..(τ - r), lam t * Φ t) = 0 := by
    have heq : EqOn (fun t => lam t * Φ t) (fun _ => (0 : ℝ)) (uIcc t₁ (τ - r)) := by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      have hlam0 : lam x = 0 := by
        refine lam.zero_of_le_dist ?_
        rw [Real.dist_eq]
        show r ≤ |x - τ|
        rw [abs_sub_comm, abs_of_nonneg (by rcases hx with ⟨-, h2⟩; linarith)]
        rcases hx with ⟨-, h2⟩
        linarith
      simp [hlam0]
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
  have hzero3 : (∫ t in (τ + r)..t₂, lam t * Φ t) = 0 := by
    have heq : EqOn (fun t => lam t * Φ t) (fun _ => (0 : ℝ)) (uIcc (τ + r) t₂) := by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      have hlam0 : lam x = 0 := by
        refine lam.zero_of_le_dist ?_
        rw [Real.dist_eq]
        show r ≤ |x - τ|
        rw [abs_of_nonneg (by rcases hx with ⟨h1, -⟩; linarith)]
        rcases hx with ⟨h1, -⟩
        linarith
      simp [hlam0]
    rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
  -- assemble the contradiction
  have hsplit1 : (∫ t in t₁..(τ - r), lam t * Φ t)
      + (∫ t in (τ - r)..(τ + r), lam t * Φ t)
      = ∫ t in t₁..(τ + r), lam t * Φ t :=
    intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hsplit2 : (∫ t in t₁..(τ + r), lam t * Φ t)
      + (∫ t in (τ + r)..t₂, lam t * Φ t)
      = ∫ t in t₁..t₂, lam t * Φ t :=
    intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3
  have htotal := hint lam hrOut
  rw [← hsplit2, ← hsplit1, hzero1, hzero3] at htotal
  linarith

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** Petersen Ch. 5, §5.4, Theorem 5.4.3
(`thm:pet-ch5-energy-minima-geodesics`), **first half**: a piecewise smooth
curve that is a local minimum of energy among proper variations has vanishing
acceleration at every time interior to a smooth piece.  This is the
fundamental lemma of the calculus of variations: test the first variation
formula with chart bump variations `φ⁻¹(φ(γ t) + s λ(t) v₀)` concentrated at
`τ` in the direction of the chart acceleration `v₀`, and let the bump shrink. -/
theorem stationary_curveAcceleration_eq_zero (g : RiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b)
    {n : ℕ} {u : ℕ → ℝ} (hstrict : ∀ i < n, u i < u (i + 1))
    (hu0 : u 0 = a) (hun : u n = b)
    (husm : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (u i) (u (i + 1))))
    (hmin : ∀ V : CurveVariation (I := I) γ a b, IsProperVariation V →
      IsLocalMin (fun s => energyFunctional (I := I) g (V.curve s) a b) 0)
    {i : ℕ} (hi : i < n) {τ : ℝ} (hτ : τ ∈ Ioo (u i) (u (i + 1))) :
    curveAcceleration (I := I) g γ τ = 0 := by
  classical
  have humono := strictPartition_mono hstrict
  -- 1. a window `Icc t₁ t₂ ⊆ S` inside the open piece and the chart source
  have hγcont : ContinuousOn γ (Icc (u i) (u (i + 1))) := (husm i hi).continuousOn
  have hct : ContinuousAt γ τ := hγcont.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
  have hevsrc : ∀ᶠ t in 𝓝 τ, γ t ∈ (extChartAt I (γ τ)).source :=
    hct.eventually_mem ((isOpen_extChartAt_source (γ τ)).mem_nhds
      (mem_extChartAt_source (I := I) (γ τ)))
  have hevIoo : ∀ᶠ t in 𝓝 τ, t ∈ Ioo (u i) (u (i + 1)) := Ioo_mem_nhds hτ.1 hτ.2
  obtain ⟨d, hd, hprop⟩ := Metric.eventually_nhds_iff.mp (hevsrc.and hevIoo)
  set t₁ := τ - d / 4 with ht₁_def
  set t₂ := τ + d / 4 with ht₂_def
  set S := Ioo (τ - d / 2) (τ + d / 2) with hS_def
  have hSprop : ∀ t ∈ S, γ t ∈ (extChartAt I (γ τ)).source ∧
      t ∈ Ioo (u i) (u (i + 1)) := by
    intro t ht
    refine hprop ?_
    rw [Real.dist_eq, abs_lt]
    rcases ht with ⟨h1, h2⟩
    constructor <;> linarith
  have hS_open : IsOpen S := isOpen_Ioo
  have hτS : τ ∈ S := ⟨by linarith, by linarith⟩
  have hIccsub : Icc t₁ t₂ ⊆ S := by
    intro x hx
    rcases hx with ⟨h1, h2⟩
    exact ⟨by simp only [ht₁_def] at h1; linarith, by simp only [ht₂_def] at h2; linarith⟩
  have h12 : t₁ ≤ t₂ := by simp only [ht₁_def, ht₂_def]; linarith
  have hτwin : τ ∈ Ioo t₁ t₂ := ⟨by simp only [ht₁_def]; linarith,
    by simp only [ht₂_def]; linarith⟩
  have hsrcS : ∀ t ∈ S, γ t ∈ (extChartAt I (γ τ)).source := fun t ht => (hSprop t ht).1
  have hsrcIcc : ∀ t ∈ Icc t₁ t₂, γ t ∈ (extChartAt I (γ τ)).source :=
    fun t ht => hsrcS t (hIccsub ht)
  have hSIoo : S ⊆ Ioo (u i) (u (i + 1)) := fun t ht => (hSprop t ht).2
  have hwinIcc : Icc t₁ t₂ ⊆ Icc a b := by
    intro x hx
    have hx' := hSIoo (hIccsub hx)
    constructor
    · calc a = u 0 := hu0.symm
        _ ≤ u i := humono 0 i (Nat.zero_le _) (by omega)
        _ ≤ x := hx'.1.le
    · calc x ≤ u (i + 1) := hx'.2.le
        _ ≤ u n := humono (i + 1) n (by omega) le_rfl
        _ = b := hun
  -- 2. the chart reading and its Γ-corrected second derivative on `S`
  set uc : ℝ → E := fun t => extChartAt I (γ τ) (γ t) with huc_def
  have hγS : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ S :=
    (husm i hi).mono (hSIoo.trans Ioo_subset_Icc_self)
  have huc : ContDiffOn ℝ ∞ uc S := contDiffOn_extChartAt_comp hγS hsrcS
  set u1 : ℝ → E := deriv uc with hu1_def
  have hu1 : ContDiffOn ℝ ∞ u1 S :=
    huc.deriv_of_isOpen hS_open (le_of_eq (by rfl))
  set Acc : ℝ → E := fun t => deriv u1 t
    + Geodesic.chartChristoffelContraction (I := I) g (γ τ) (u1 t) (u1 t) (uc t)
    with hAcc_def
  have hmemT : ∀ t ∈ S, uc t ∈ (extChartAt I (γ τ)).target :=
    fun t ht => (extChartAt I (γ τ)).map_source (hsrcS t ht)
  have huc_cont : ContinuousOn uc S := huc.continuousOn
  have hu1_cont : ContinuousOn u1 S := hu1.continuousOn
  have hdu1_cont : ContinuousOn (deriv u1) S :=
    hu1.continuousOn_deriv_of_isOpen hS_open (by norm_num)
  have hAcc_cont : ContinuousOn Acc S :=
    hdu1_cont.add (continuousOn_chartChristoffelContraction_comp g (γ τ)
      huc_cont hu1_cont hu1_cont hmemT)
  -- 3. the acceleration through the chart at `γ τ`, on the open window
  have hreg : ∀ t ∈ S, (∀ᶠ s' in 𝓝 t, HasDerivAt uc (deriv uc s') s')
      ∧ DifferentiableAt ℝ u1 t := by
    intro t ht
    constructor
    · filter_upwards [hS_open.mem_nhds ht] with s' hs'
      exact ((huc.differentiableOn (by norm_num)).differentiableAt
        (hS_open.mem_nhds hs')).hasDerivAt
    · exact (hu1.differentiableOn (by norm_num)).differentiableAt (hS_open.mem_nhds ht)
  have htransfer : ∀ t ∈ S, curveAcceleration (I := I) g γ t
      = tangentCoordChange I (γ τ) (γ t) (γ t) (Acc t) := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I (γ τ)).source := by
      filter_upwards [hS_open.mem_nhds ht] with s hs
      exact hsrcS s hs
    exact curveAcceleration_eq_tangentCoordChange g hev (hreg t ht).1 (hreg t ht).2
  -- 4. the target pairing `Φ` and its continuity
  set v₀ : E := Acc τ with hv₀_def
  set Φ : ℝ → ℝ := fun t => chartMetricInner (I := I) g (γ τ) (uc t) v₀ (Acc t)
    with hΦ_def
  have hΦS : ContinuousOn Φ S :=
    continuousOn_chartMetricInner_comp g (γ τ) huc_cont continuousOn_const hAcc_cont hmemT
  have hΦτ : Φ τ = g.inner (γ τ) v₀ v₀ := by
    have h1 : Φ τ = g.inner (γ τ)
        (tangentCoordChange I (γ τ) (γ τ) (γ τ) v₀)
        (tangentCoordChange I (γ τ) (γ τ) (γ τ) (Acc τ)) :=
      chartMetricInner_eq_inner g (hsrcS τ hτS) v₀ (Acc τ)
    rw [← hv₀_def] at h1
    simp only [tangentCoordChange_self (I := I)
      (mem_extChartAt_source (I := I) (γ τ))] at h1
    exact h1
  have hΦτ_nonneg : 0 ≤ Φ τ := by
    rw [hΦτ]
    exact g.metricInner_self_nonneg (γ τ) v₀
  -- 5. stationarity: every small bump integrates to zero against `Φ`
  have hbump : ∀ lam : ContDiffBump τ, lam.rOut < min (τ - t₁) (t₂ - τ) →
      ∫ t in t₁..t₂, lam t * Φ t = 0 := by
    intro lam hlam
    have hlam_t₁ : lam.rOut < τ - t₁ := lt_of_lt_of_le hlam (min_le_left _ _)
    have hlam_t₂ : lam.rOut < t₂ - τ := lt_of_lt_of_le hlam (min_le_right _ _)
    set w : ℝ → E := fun t => lam t • v₀ with hw_def
    have hw : ContDiff ℝ ∞ w := lam.contDiff.smul contDiff_const
    have hwsupp : tsupport w ⊆ Ioo t₁ t₂ := by
      refine (tsupport_smul_subset_left (fun t => lam t) fun _ => v₀).trans ?_
      rw [lam.tsupport_eq]
      intro x hx
      rw [Metric.mem_closedBall, Real.dist_eq] at hx
      have hx' := abs_le.mp hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    obtain ⟨V, hVfun, hVproper, hVtarget, hVslab⟩ :=
      exists_chartBumpVariation_curveVariation hγ hu0 hun husm humono hwinIcc h12
        hsrcIcc hw hwsupp
    have hsrc' : ∀ t' ∈ Ioo t₁ t₂, γ t' ∈ (extChartAt I (γ τ)).source :=
      fun t' ht' => hsrcIcc t' (Ioo_subset_Icc_self ht')
    have hV0 : V.toFun 0 = γ := by
      rw [hVfun]
      exact chartBumpVariation_zero_eq hsrc'
    have hcurve0 : V.curve 0 = γ := by
      funext x
      rw [CurveVariation.curve_apply, hV0]
    -- first variation + stationarity
    have hfv := firstVariationOfEnergy (I := I) g V hstrict hu0 hun hVslab
    have hD := (hmin V hVproper).hasDerivAt_eq_zero hfv
    -- all partition points lie outside the window
    have ht₁S : t₁ ∈ S := ⟨by simp only [ht₁_def]; linarith,
      by simp only [ht₁_def]; linarith⟩
    have ht₂S : t₂ ∈ S := ⟨by simp only [ht₂_def]; linarith,
      by simp only [ht₂_def]; linarith⟩
    have hui_t₁ : u i < t₁ := (hSIoo ht₁S).1
    have hui1_t₂ : t₂ < u (i + 1) := (hSIoo ht₂S).2
    have hnotwin : ∀ j, j ≤ n → u j ∉ Ioo t₁ t₂ := by
      intro j hj hmem
      rcases Nat.lt_or_ge j (i + 1) with hji | hji
      · have := humono j i (by omega) (by omega)
        linarith [hmem.1]
      · have := humono (i + 1) j hji hj
        linarith [hmem.2]
    -- the variational field vanishes off the window
    have hinner_zero : ∀ (x : M) (v : TangentSpace I x),
        g.inner x (0 : TangentSpace I x) v = 0 := by
      intro x v
      rw [map_zero]
      simp
    have hfield0 : ∀ x, x ∉ Ioo t₁ t₂ →
        deriv (fun s => extChartAt I (V.toFun 0 x) (V.toFun s x)) 0 = 0 := by
      intro x hx
      have h1 : (fun s => extChartAt I (V.toFun 0 x) (V.toFun s x))
          = fun _ => extChartAt I (γ x) (γ x) := by
        funext s
        rw [hVfun, chartBumpVariation_of_notMem hx, chartBumpVariation_of_notMem hx]
      rw [h1]
      exact deriv_const 0 _
    -- the boundary sum vanishes
    have hsum0 : (∑ j ∈ Finset.range n,
        (g.inner (V.toFun 0 (u (j + 1)))
            ((deriv (fun s => extChartAt I (V.toFun 0 (u (j + 1)))
              (V.toFun s (u (j + 1)))) 0 : E))
            ((derivWithin (fun t => extChartAt I (V.toFun 0 (u (j + 1)))
              (V.toFun 0 t)) (Icc (u j) (u (j + 1))) (u (j + 1)) : E))
          - g.inner (V.toFun 0 (u j))
              ((deriv (fun s => extChartAt I (V.toFun 0 (u j))
                (V.toFun s (u j))) 0 : E))
              ((derivWithin (fun t => extChartAt I (V.toFun 0 (u j))
                (V.toFun 0 t)) (Icc (u j) (u (j + 1))) (u j) : E)))) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      have hA : g.inner (V.toFun 0 (u (j + 1)))
          ((deriv (fun s => extChartAt I (V.toFun 0 (u (j + 1)))
            (V.toFun s (u (j + 1)))) 0 : E))
          ((derivWithin (fun t => extChartAt I (V.toFun 0 (u (j + 1)))
            (V.toFun 0 t)) (Icc (u j) (u (j + 1))) (u (j + 1)) : E)) = 0 := by
        rw [hfield0 (u (j + 1)) (hnotwin (j + 1) (by omega))]
        exact hinner_zero _ _
      have hB : g.inner (V.toFun 0 (u j))
          ((deriv (fun s => extChartAt I (V.toFun 0 (u j))
            (V.toFun s (u j))) 0 : E))
          ((derivWithin (fun t => extChartAt I (V.toFun 0 (u j))
            (V.toFun 0 t)) (Icc (u j) (u (j + 1))) (u j) : E)) = 0 := by
        rw [hfield0 (u j) (hnotwin j (by omega))]
        exact hinner_zero _ _
      rw [hA, hB, sub_zero]
    -- pointwise identification of the integrand with `lam · Φ`
    have hpt : ∀ t : ℝ, g.inner (V.toFun 0 t)
        ((deriv (fun s => extChartAt I (V.toFun 0 t) (V.toFun s t)) 0 : E))
        (curveAcceleration (I := I) g (V.curve 0) t) = lam t * Φ t := by
      intro t
      by_cases ht : t ∈ Ioo t₁ t₂
      · have htS : t ∈ S := hIccsub (Ioo_subset_Icc_self ht)
        have hsrct : γ t ∈ (extChartAt I (γ τ)).source := hsrcS t htS
        have hfieldt : deriv (fun s => extChartAt I (γ t) (V.toFun s t)) 0
            = lam t • tangentCoordChange I (γ τ) (γ t) (γ t) v₀ := by
          have h := (chartBumpVariation_hasDerivAt_field (ε := V.width)
            V.width_pos ht hsrcIcc hVtarget).deriv
          rw [hVfun, h]
          exact (tangentCoordChange I (γ τ) (γ t) (γ t)).map_smul (lam t) v₀
        have hacct : curveAcceleration (I := I) g (V.curve 0) t
            = tangentCoordChange I (γ τ) (γ t) (γ t) (Acc t) := by
          rw [hcurve0]
          exact htransfer t htS
        have hgram : g.inner (γ t)
            (tangentCoordChange I (γ τ) (γ t) (γ t) v₀)
            (tangentCoordChange I (γ τ) (γ t) (γ t) (Acc t)) = Φ t :=
          (chartMetricInner_eq_inner g hsrct v₀ (Acc t)).symm
        rw [hV0, hfieldt, hacct, ← hgram]
        exact g.metricInner_smul_left (γ t) (lam t) _ _
      · rw [hfield0 t ht]
        have hlam0 : lam t = 0 := by
          refine lam.zero_of_le_dist ?_
          rw [Real.dist_eq]
          rcases not_and_or.mp ht with h | h
          · rw [not_lt] at h
            rw [abs_sub_comm, abs_of_nonneg (by linarith [lam.rOut_pos, hlam_t₁])]
            linarith [hlam_t₁]
          · rw [not_lt] at h
            rw [abs_of_nonneg (by linarith [lam.rOut_pos, hlam_t₂])]
            linarith [hlam_t₂]
        rw [hlam0, zero_mul]
        exact hinner_zero _ _
    -- `lam · Φ` is continuous (off the bump support it vanishes near each point)
    have hG : Continuous fun t => lam t * Φ t := by
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hx : x ∈ tsupport fun t => lam t
      · have hxIoo : x ∈ Ioo t₁ t₂ := by
          rw [lam.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hx
          have hx' := abs_le.mp hx
          exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
        have hxS : x ∈ S := hIccsub (Ioo_subset_Icc_self hxIoo)
        exact lam.continuous.continuousAt.mul (hΦS.continuousAt (hS_open.mem_nhds hxS))
      · have hev0 : (fun t => lam t * Φ t) =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
          simp only [hy]
          exact zero_mul _
        exact continuousAt_const.congr hev0.symm
    -- localize the integral to the window
    have ha_t₁ : a ≤ t₁ := (hwinIcc (left_mem_Icc.mpr h12)).1
    have ht₂_b : t₂ ≤ b := (hwinIcc (right_mem_Icc.mpr h12)).2
    have hzero_left : (∫ t in a..t₁, lam t * Φ t) = 0 := by
      have heq : EqOn (fun t => lam t * Φ t) (fun _ => (0 : ℝ)) (uIcc a t₁) := by
        intro x hx
        rw [uIcc_of_le ha_t₁] at hx
        obtain ⟨-, h2⟩ := hx
        have hlam0 : lam x = 0 := by
          refine lam.zero_of_le_dist ?_
          rw [Real.dist_eq, abs_sub_comm,
            abs_of_nonneg (by linarith [lam.rOut_pos, hlam_t₁])]
          linarith [hlam_t₁]
        show lam x * Φ x = 0
        rw [hlam0, zero_mul]
      rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
    have hzero_right : (∫ t in t₂..b, lam t * Φ t) = 0 := by
      have heq : EqOn (fun t => lam t * Φ t) (fun _ => (0 : ℝ)) (uIcc t₂ b) := by
        intro x hx
        rw [uIcc_of_le ht₂_b] at hx
        obtain ⟨h1, -⟩ := hx
        have hlam0 : lam x = 0 := by
          refine lam.zero_of_le_dist ?_
          rw [Real.dist_eq,
            abs_of_nonneg (by linarith [lam.rOut_pos, hlam_t₂])]
          linarith [hlam_t₂]
        show lam x * Φ x = 0
        rw [hlam0, zero_mul]
      rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
    have hsplit1 : (∫ t in a..t₁, lam t * Φ t) + (∫ t in t₁..t₂, lam t * Φ t)
        = ∫ t in a..t₂, lam t * Φ t :=
      intervalIntegral.integral_add_adjacent_intervals
        (hG.intervalIntegrable a t₁) (hG.intervalIntegrable t₁ t₂)
    have hsplit2 : (∫ t in a..t₂, lam t * Φ t) + (∫ t in t₂..b, lam t * Φ t)
        = ∫ t in a..b, lam t * Φ t :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hG.intervalIntegrable a t₁).trans (hG.intervalIntegrable t₁ t₂))
        (hG.intervalIntegrable t₂ b)
    have hIeq : (∫ t in a..b, g.inner (V.toFun 0 t)
        ((deriv (fun s => extChartAt I (V.toFun 0 t) (V.toFun s t)) 0 : E))
        (curveAcceleration (I := I) g (V.curve 0) t)) = ∫ t in a..b, lam t * Φ t :=
      intervalIntegral.integral_congr fun x _ => hpt x
    rw [hsum0, hIeq, ← hsplit2, ← hsplit1, hzero_left, hzero_right] at hD
    linarith
  -- 6. the fundamental lemma forces `Φ τ = 0`, hence `v₀ = 0`
  have hΦτ_le : Φ τ ≤ 0 :=
    nonpos_of_forall_contDiffBump_integral_eq_zero hτwin (hΦS.mono hIccsub) hbump
  have hΦτ0 : g.inner (γ τ) v₀ v₀ = 0 := by
    rw [← hΦτ]
    exact le_antisymm hΦτ_le hΦτ_nonneg
  have hv₀ : v₀ = 0 := by
    by_contra hne
    exact absurd hΦτ0 (ne_of_gt (g.metricInner_self_pos (γ τ) v₀ hne))
  rw [htransfer τ hτS, ← hv₀_def, hv₀, map_zero]

/-- **Math.** Converse transfer: if the acceleration `c̈(t)` vanishes, then the
Γ-corrected second derivative of **any** chart reading vanishes — invert the
coordinate change of `curveAcceleration_eq_tangentCoordChange` through
`tangentCoordChange_comp`/`tangentCoordChange_self`. -/
theorem chartAcceleration_eq_zero_of_curveAcceleration (g : RiemannianMetric I M)
    {γ : ℝ → M} {t : ℝ} {α : M}
    (hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I α).source)
    (hu1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I α (γ s'))
      (deriv (fun s' => extChartAt I α (γ s')) s) s)
    (hu2 : DifferentiableAt ℝ (deriv (fun s' => extChartAt I α (γ s'))) t)
    (hacc : curveAcceleration (I := I) g γ t = 0) :
    deriv (deriv (fun s' => extChartAt I α (γ s'))) t
      + Geodesic.chartChristoffelContraction (I := I) g α
        (deriv (fun s' => extChartAt I α (γ s')) t)
        (deriv (fun s' => extChartAt I α (γ s')) t)
        (extChartAt I α (γ t)) = 0 := by
  have htr := curveAcceleration_eq_tangentCoordChange g hev hu1 hu2
  rw [hacc] at htr
  have hsrct : γ t ∈ (extChartAt I α).source := hev.self_of_nhds
  set A : E := deriv (deriv (fun s' => extChartAt I α (γ s'))) t
    + Geodesic.chartChristoffelContraction (I := I) g α
      (deriv (fun s' => extChartAt I α (γ s')) t)
      (deriv (fun s' => extChartAt I α (γ s')) t)
      (extChartAt I α (γ t)) with hA_def
  have hcomp : tangentCoordChange I (γ t) α (γ t)
      (tangentCoordChange I α (γ t) (γ t) A) = tangentCoordChange I α α (γ t) A :=
    tangentCoordChange_comp (I := I)
      ⟨⟨hsrct, mem_extChartAt_source (I := I) (γ t)⟩, hsrct⟩
  have hself : tangentCoordChange I α α (γ t) A = A :=
    tangentCoordChange_self (I := I) hsrct
  have h0 : tangentCoordChange I α (γ t) (γ t) A = 0 := htr.symm
  rw [h0, map_zero] at hcomp
  rw [← hself, ← hcomp]

/-- **Math.** Petersen Ch. 5, §5.4, Theorem 5.4.3, **second half — break-term
elimination**: at an interior break of the smoothness partition of an
energy-stationary curve, the one-sided velocities agree.  Test the first
variation formula with a bump variation centred at the break in the direction
of the velocity jump: the integral term dies (the acceleration already
vanishes a.e. by the fundamental lemma), only the two break terms survive,
and they sum to `-|jump|²_g`. -/
theorem stationary_velocityJump_eq_zero (g : RiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b)
    {n : ℕ} {u : ℕ → ℝ} (hstrict : ∀ i < n, u i < u (i + 1))
    (hu0 : u 0 = a) (hun : u n = b)
    (husm : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (u i) (u (i + 1))))
    (hmin : ∀ V : CurveVariation (I := I) γ a b, IsProperVariation V →
      IsLocalMin (fun s => energyFunctional (I := I) g (V.curve s) a b) 0)
    {i : ℕ} (hin : i + 1 < n) :
    (derivWithin (fun t => extChartAt I (γ (u (i + 1))) (γ t))
        (Icc (u i) (u (i + 1))) (u (i + 1)) : E)
      = derivWithin (fun t => extChartAt I (γ (u (i + 1))) (γ t))
        (Icc (u (i + 1)) (u (i + 2))) (u (i + 1)) := by
  classical
  have humono := strictPartition_mono hstrict
  set q := u (i + 1) with hq_def
  -- 1. a window `Icc t₁ t₂` around the break inside `(u i, u (i+2))` and the chart
  have hab : a < b := by
    calc a = u 0 := hu0.symm
      _ ≤ u i := humono 0 i (Nat.zero_le _) (by omega)
      _ < u (i + 1) := hstrict i (by omega)
      _ ≤ u n := humono (i + 1) n (by omega) le_rfl
      _ = b := hun
  have haq : a < q := by
    calc a = u 0 := hu0.symm
      _ ≤ u i := humono 0 i (Nat.zero_le _) (by omega)
      _ < q := hstrict i (by omega)
  have hqb : q < b := by
    calc q < u (i + 2) := hstrict (i + 1) (by omega)
      _ ≤ u n := humono (i + 2) n (by omega) le_rfl
      _ = b := hun
  have hct : ContinuousAt γ q := hγ.1.continuousAt (Icc_mem_nhds haq hqb)
  have hevsrc : ∀ᶠ t in 𝓝 q, γ t ∈ (extChartAt I (γ q)).source :=
    hct.eventually_mem ((isOpen_extChartAt_source (γ q)).mem_nhds
      (mem_extChartAt_source (I := I) (γ q)))
  have hevIoo : ∀ᶠ t in 𝓝 q, t ∈ Ioo (u i) (u (i + 2)) :=
    Ioo_mem_nhds (hstrict i (by omega)) (hstrict (i + 1) (by omega))
  obtain ⟨d, hd, hprop⟩ := Metric.eventually_nhds_iff.mp (hevsrc.and hevIoo)
  set t₁ := q - d / 4 with ht₁_def
  set t₂ := q + d / 4 with ht₂_def
  have hwprop : ∀ t ∈ Icc t₁ t₂, γ t ∈ (extChartAt I (γ q)).source ∧
      t ∈ Ioo (u i) (u (i + 2)) := by
    intro t ht
    refine hprop ?_
    rw [Real.dist_eq, abs_lt]
    rcases ht with ⟨h1, h2⟩
    constructor
    · simp only [ht₁_def] at h1; linarith
    · simp only [ht₂_def] at h2; linarith
  have h12 : t₁ ≤ t₂ := by simp only [ht₁_def, ht₂_def]; linarith
  have hqwin : q ∈ Ioo t₁ t₂ := ⟨by simp only [ht₁_def]; linarith,
    by simp only [ht₂_def]; linarith⟩
  have hsrcIcc : ∀ t ∈ Icc t₁ t₂, γ t ∈ (extChartAt I (γ q)).source :=
    fun t ht => (hwprop t ht).1
  have hui_t₁ : u i < t₁ :=
    (hwprop t₁ (left_mem_Icc.mpr h12)).2.1
  have hui2_t₂ : t₂ < u (i + 2) :=
    (hwprop t₂ (right_mem_Icc.mpr h12)).2.2
  have hwinIcc : Icc t₁ t₂ ⊆ Icc a b := by
    intro x hx
    have hx' := (hwprop x hx).2
    constructor
    · calc a = u 0 := hu0.symm
        _ ≤ u i := humono 0 i (Nat.zero_le _) (by omega)
        _ ≤ x := hx'.1.le
    · calc x ≤ u (i + 2) := hx'.2.le
        _ ≤ u n := humono (i + 2) n (by omega) le_rfl
        _ = b := hun
  -- 2. the one-sided velocities and the jump direction
  set vL : E := derivWithin (fun t => extChartAt I (γ q) (γ t))
    (Icc (u i) (u (i + 1))) (u (i + 1)) with hvL_def
  set vR : E := derivWithin (fun t => extChartAt I (γ q) (γ t))
    (Icc (u (i + 1)) (u (i + 2))) (u (i + 1)) with hvR_def
  set w₀ : E := vL - vR with hw₀_def
  -- 3. the bump variation at the break
  set lam : ContDiffBump q := ⟨d / 8, d / 6, by linarith, by linarith⟩ with hlam_def
  have hlam_rOut : lam.rOut = d / 6 := rfl
  set w : ℝ → E := fun t => lam t • w₀ with hw_def
  have hw : ContDiff ℝ ∞ w := lam.contDiff.smul contDiff_const
  have hwsupp : tsupport w ⊆ Ioo t₁ t₂ := by
    refine (tsupport_smul_subset_left (fun t => lam t) fun _ => w₀).trans ?_
    rw [lam.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, hlam_rOut] at hx
    have hx' := abs_le.mp hx
    constructor
    · simp only [ht₁_def]; linarith [hx'.1]
    · simp only [ht₂_def]; linarith [hx'.2]
  obtain ⟨V, hVfun, hVproper, hVtarget, hVslab⟩ :=
    exists_chartBumpVariation_curveVariation hγ hu0 hun husm humono hwinIcc h12
      hsrcIcc hw hwsupp
  have hsrc' : ∀ t' ∈ Ioo t₁ t₂, γ t' ∈ (extChartAt I (γ q)).source :=
    fun t' ht' => hsrcIcc t' (Ioo_subset_Icc_self ht')
  have hV0 : V.toFun 0 = γ := by
    rw [hVfun]
    exact chartBumpVariation_zero_eq hsrc'
  have hcurve0 : V.curve 0 = γ := by
    funext x
    rw [CurveVariation.curve_apply, hV0]
  -- 4. first variation + stationarity
  have hfv := firstVariationOfEnergy (I := I) g V hstrict hu0 hun hVslab
  have hD := (hmin V hVproper).hasDerivAt_eq_zero hfv
  -- 5. partition points other than the break lie outside the window
  have hnotwin : ∀ j, j ≤ n → j ≠ i + 1 → u j ∉ Ioo t₁ t₂ := by
    intro j hj hne hmem
    rcases Nat.lt_or_ge j (i + 1) with hji | hji
    · have := humono j i (by omega) (by omega)
      linarith [hmem.1]
    · have hji2 : i + 2 ≤ j := by omega
      have := humono (i + 2) j hji2 hj
      linarith [hmem.2]
  have hinner_zero : ∀ (x : M) (v : TangentSpace I x),
      g.inner x (0 : TangentSpace I x) v = 0 := by
    intro x v
    rw [map_zero]
    simp
  have hfield0 : ∀ x, x ∉ Ioo t₁ t₂ →
      deriv (fun s => extChartAt I (V.toFun 0 x) (V.toFun s x)) 0 = 0 := by
    intro x hx
    have h1 : (fun s => extChartAt I (V.toFun 0 x) (V.toFun s x))
        = fun _ => extChartAt I (γ x) (γ x) := by
      funext s
      rw [hVfun, chartBumpVariation_of_notMem hx, chartBumpVariation_of_notMem hx]
    rw [h1]
    exact deriv_const 0 _
  -- 6. the variational field at the break is the jump direction
  have hfieldq : deriv (fun s => extChartAt I (γ (u (i + 1)))
      (V.toFun s (u (i + 1)))) 0 = w₀ := by
    have h := (chartBumpVariation_hasDerivAt_field (ε := V.width)
      V.width_pos hqwin hsrcIcc hVtarget).deriv
    rw [hVfun]
    rw [show (fun s => extChartAt I (γ (u (i + 1)))
        (chartBumpVariation (I := I) (γ q) γ w t₁ t₂ s (u (i + 1))))
      = fun s => extChartAt I (γ q) (chartBumpVariation (I := I) (γ q) γ w t₁ t₂ s q)
      from rfl]
    rw [h]
    have hlamq : lam q = 1 :=
      lam.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    show tangentCoordChange I (γ q) (γ q) (γ q) (w q) = w₀
    rw [tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) (γ q))]
    show lam q • w₀ = w₀
    rw [hlamq, one_smul]
  -- 7. the boundary sum collapses to the two break terms
  set F : ℕ → ℝ := fun j =>
    g.inner (V.toFun 0 (u (j + 1)))
        ((deriv (fun s => extChartAt I (V.toFun 0 (u (j + 1)))
          (V.toFun s (u (j + 1)))) 0 : E))
        ((derivWithin (fun t => extChartAt I (V.toFun 0 (u (j + 1)))
          (V.toFun 0 t)) (Icc (u j) (u (j + 1))) (u (j + 1)) : E))
      - g.inner (V.toFun 0 (u j))
          ((deriv (fun s => extChartAt I (V.toFun 0 (u j))
            (V.toFun s (u j))) 0 : E))
          ((derivWithin (fun t => extChartAt I (V.toFun 0 (u j))
            (V.toFun 0 t)) (Icc (u j) (u (j + 1))) (u j) : E)) with hF_def
  have hFzero : ∀ j ∈ Finset.range n, j ∉ ({i, i + 1} : Finset ℕ) → F j = 0 := by
    intro j hj hne
    have hj' := Finset.mem_range.mp hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
    have hA : g.inner (V.toFun 0 (u (j + 1)))
        ((deriv (fun s => extChartAt I (V.toFun 0 (u (j + 1)))
          (V.toFun s (u (j + 1)))) 0 : E))
        ((derivWithin (fun t => extChartAt I (V.toFun 0 (u (j + 1)))
          (V.toFun 0 t)) (Icc (u j) (u (j + 1))) (u (j + 1)) : E)) = 0 := by
      rw [hfield0 (u (j + 1)) (hnotwin (j + 1) (by omega) (by omega))]
      exact hinner_zero _ _
    have hB : g.inner (V.toFun 0 (u j))
        ((deriv (fun s => extChartAt I (V.toFun 0 (u j))
          (V.toFun s (u j))) 0 : E))
        ((derivWithin (fun t => extChartAt I (V.toFun 0 (u j))
          (V.toFun 0 t)) (Icc (u j) (u (j + 1))) (u j) : E)) = 0 := by
      rw [hfield0 (u j) (hnotwin j (by omega) (by omega))]
      exact hinner_zero _ _
    rw [hF_def]
    simp only
    rw [hA, hB, sub_zero]
  have hFi : F i = g.inner (γ q) ((w₀ : E)) ((vL : E)) := by
    have hB : g.inner (V.toFun 0 (u i))
        ((deriv (fun s => extChartAt I (V.toFun 0 (u i))
          (V.toFun s (u i))) 0 : E))
        ((derivWithin (fun t => extChartAt I (V.toFun 0 (u i))
          (V.toFun 0 t)) (Icc (u i) (u (i + 1))) (u i) : E)) = 0 := by
      rw [hfield0 (u i) (hnotwin i (by omega) (by omega))]
      exact hinner_zero _ _
    rw [hF_def]
    simp only
    rw [hB, sub_zero, hV0, hfieldq]
  have hFi1 : F (i + 1) = -(g.inner (γ q) ((w₀ : E)) ((vR : E))) := by
    have hA : g.inner (V.toFun 0 (u (i + 1 + 1)))
        ((deriv (fun s => extChartAt I (V.toFun 0 (u (i + 1 + 1)))
          (V.toFun s (u (i + 1 + 1)))) 0 : E))
        ((derivWithin (fun t => extChartAt I (V.toFun 0 (u (i + 1 + 1)))
          (V.toFun 0 t)) (Icc (u (i + 1)) (u (i + 1 + 1))) (u (i + 1 + 1)) : E)) = 0 := by
      rw [hfield0 (u (i + 1 + 1)) (hnotwin (i + 1 + 1) (by omega) (by omega))]
      exact hinner_zero _ _
    rw [hF_def]
    simp only
    rw [hA, hV0, hfieldq, zero_sub]
  have hsum_eq : (∑ j ∈ Finset.range n, F j)
      = g.inner (γ q) ((w₀ : E)) ((vL : E)) - g.inner (γ q) ((w₀ : E)) ((vR : E)) := by
    have hsub : ({i, i + 1} : Finset ℕ) ⊆ Finset.range n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    rw [← Finset.sum_subset hsub hFzero, Finset.sum_pair (by omega)]
    rw [hFi, hFi1]
    ring
  -- 8. the acceleration integral vanishes a.e.
  have hBfin : (Set.Finite ((fun j => u j) '' (Set.Iic n))) :=
    (Set.finite_Iic n).image _
  have hIzero : (∫ t in a..b, g.inner (V.toFun 0 t)
      ((deriv (fun s => extChartAt I (V.toFun 0 t) (V.toFun s t)) 0 : E))
      (curveAcceleration (I := I) g (V.curve 0) t)) = 0 := by
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (hBfin.measure_zero volume)] with t htB htI
    rw [Set.uIoc_of_le hab.le, Set.mem_Ioc] at htI
    have htne : ∀ j, j ≤ n → t ≠ u j := by
      intro j hj hne
      exact htB ⟨j, Set.mem_Iic.mpr hj, hne.symm⟩
    -- find the smoothness piece containing `t`
    set P : ℕ → Prop := fun k => u k < t with hP_def
    have hP0 : P 0 := by
      show u 0 < t
      rw [hu0]
      exact htI.1
    set j := Nat.findGreatest P n with hj_def
    have hjle : j ≤ n := Nat.findGreatest_le n
    have hPj : P j := Nat.findGreatest_spec (Nat.zero_le n) hP0
    have hjn : j < n := by
      rcases Nat.lt_or_ge j n with h | h
      · exact h
      · exfalso
        have hjeq : j = n := le_antisymm hjle h
        have : u n < t := by rw [← hjeq]; exact hPj
        rw [hun] at this
        linarith [htI.2]
    have hnotPj1 : ¬P (j + 1) :=
      Nat.findGreatest_is_greatest (n := n) (by omega) (by omega)
    have ht_lt : t < u (j + 1) := by
      rcases lt_or_ge t (u (j + 1)) with h | h
      · exact h
      · exact absurd (le_antisymm h (not_lt.mp hnotPj1)).symm (htne (j + 1) (by omega))
    have hacc := stationary_curveAcceleration_eq_zero g hγ hstrict hu0 hun husm hmin
      hjn ⟨hPj, ht_lt⟩
    have haccV : curveAcceleration (I := I) g (V.curve 0) t = 0 := by
      rw [hcurve0]
      exact hacc
    rw [haccV]
    exact (g.inner (V.toFun 0 t) _).map_zero
  -- 9. combine: the jump pairs to zero against itself
  rw [hsum_eq, hIzero, sub_zero] at hD
  have hdiff : g.inner (γ q) ((w₀ : E)) ((w₀ : E)) = 0 := by
    have hmap : g.inner (γ q) ((w₀ : E)) ((vL : E)) - g.inner (γ q) ((w₀ : E)) ((vR : E))
        = g.inner (γ q) ((w₀ : E)) ((vL - vR : E)) :=
      (((g.inner (γ q)) ((w₀ : E))).map_sub vL vR).symm
    rw [hmap] at hD
    rw [← hw₀_def] at hD
    exact hD
  have hw₀0 : w₀ = 0 := by
    by_contra hne
    exact absurd hdiff (ne_of_gt (g.metricInner_self_pos (γ q) w₀ hne))
  have hsub0 : vL - vR = 0 := by
    rw [← hw₀_def]
    exact hw₀0
  exact sub_eq_zero.mp hsub0

/-- **Math.** **C² gluing at a break**: if a curve is smooth on `[p, q]` and on
`[q, r]`, its acceleration vanishes on both open pieces, and the one-sided
velocities at `q` (in the chart at `γ q`) agree, then the moving-foot geodesic
equation holds **at** `q`.  The geodesic ODE itself matches the one-sided
second derivatives — both are the limit `-Γ(v, v)(u q)` of the coordinate ODE
along the respective piece — so the chart reading is twice differentiable
across the break.  (Petersen glues with local uniqueness of geodesics; since
the Lean geodesic predicate only asks for C² data at each time, this direct
matching suffices.) -/
theorem hasGeodesicEquationAt_of_matching_break (g : RiemannianMetric I M)
    {γ : ℝ → M} {p q r : ℝ} (hpq : p < q) (hqr : q < r)
    (hγc : ContinuousOn γ (Icc p r))
    (hL : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc p q))
    (hR : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc q r))
    (haccL : ∀ t ∈ Ioo p q, curveAcceleration (I := I) g γ t = 0)
    (haccR : ∀ t ∈ Ioo q r, curveAcceleration (I := I) g γ t = 0)
    (hjump : (derivWithin (fun t => extChartAt I (γ q) (γ t)) (Icc p q) q : E)
      = derivWithin (fun t => extChartAt I (γ q) (γ t)) (Icc q r) q) :
    Geodesic.HasGeodesicEquationAt (I := I) g γ q := by
  classical
  -- 1. a symmetric window inside `(p, r)` mapping into the chart at `γ q`
  have hct : ContinuousAt γ q := hγc.continuousAt (Icc_mem_nhds hpq hqr)
  have hevsrc : ∀ᶠ t in 𝓝 q, γ t ∈ (extChartAt I (γ q)).source :=
    hct.eventually_mem ((isOpen_extChartAt_source (γ q)).mem_nhds
      (mem_extChartAt_source (I := I) (γ q)))
  obtain ⟨d, hd, hprop⟩ := Metric.eventually_nhds_iff.mp hevsrc
  set e := min (d / 2) (min (q - p) (r - q)) with he_def
  have he : 0 < e := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have he_d : e < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have he_p : p ≤ q - e := by
    have h1 : e ≤ min (q - p) (r - q) := min_le_right _ _
    have h2 : min (q - p) (r - q) ≤ q - p := min_le_left _ _
    linarith
  have he_r : q + e ≤ r := by
    have h1 : e ≤ min (q - p) (r - q) := min_le_right _ _
    have h2 : min (q - p) (r - q) ≤ r - q := min_le_right _ _
    linarith
  have hsrc : ∀ t ∈ Icc (q - e) (q + e), γ t ∈ (extChartAt I (γ q)).source := by
    intro t ht
    refine hprop ?_
    rw [Real.dist_eq, abs_lt]
    rcases ht with ⟨h1, h2⟩
    constructor <;> linarith
  set uc : ℝ → E := fun t => extChartAt I (γ q) (γ t) with huc_def
  have hqL : q - e < q := by linarith
  have hqR : q < q + e := by linarith
  -- 2. one-sided chart readings are smooth up to the break
  have hIccL_sub : Icc (q - e) q ⊆ Icc p q := fun x hx => ⟨le_trans he_p hx.1, hx.2⟩
  have hIccR_sub : Icc q (q + e) ⊆ Icc q r := fun x hx => ⟨hx.1, le_trans hx.2 he_r⟩
  have hsrcL : ∀ t ∈ Icc (q - e) q, γ t ∈ (extChartAt I (γ q)).source :=
    fun t ht => hsrc t ⟨ht.1, le_trans ht.2 (by linarith)⟩
  have hsrcR : ∀ t ∈ Icc q (q + e), γ t ∈ (extChartAt I (γ q)).source :=
    fun t ht => hsrc t ⟨le_trans (by linarith) ht.1, ht.2⟩
  have hucL : ContDiffOn ℝ ∞ uc (Icc (q - e) q) :=
    contDiffOn_extChartAt_comp (hL.mono hIccL_sub) hsrcL
  have hucR : ContDiffOn ℝ ∞ uc (Icc q (q + e)) :=
    contDiffOn_extChartAt_comp (hR.mono hIccR_sub) hsrcR
  have hucWL : ContDiffOn ℝ ∞ uc (Ioo (q - e) q) := hucL.mono Ioo_subset_Icc_self
  have hucWR : ContDiffOn ℝ ∞ uc (Ioo q (q + e)) := hucR.mono Ioo_subset_Icc_self
  have hWL_open : IsOpen (Ioo (q - e) q) := isOpen_Ioo
  have hWR_open : IsOpen (Ioo q (q + e)) := isOpen_Ioo
  -- 3. the common one-sided velocity `vq`
  have hsetL : Icc p q =ᶠ[𝓝 q] Icc (q - e) q := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [Ioo_mem_nhds hqL hqR] with x hx
    simp only [mem_Icc]
    exact ⟨fun h => ⟨hx.1.le, h.2⟩, fun h => ⟨le_trans he_p h.1, h.2⟩⟩
  have hsetR : Icc q r =ᶠ[𝓝 q] Icc q (q + e) := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [Ioo_mem_nhds hqL hqR] with x hx
    simp only [mem_Icc]
    exact ⟨fun h => ⟨h.1, hx.2.le⟩, fun h => ⟨h.1, le_trans h.2 he_r⟩⟩
  set vq : E := derivWithin uc (Icc (q - e) q) q with hvq_def
  have hvR_vq : derivWithin uc (Icc q (q + e)) q = vq := by
    rw [← derivWithin_congr_set hsetR, ← hjump, derivWithin_congr_set hsetL]
  -- 4. the two-sided first derivative at the break
  have hqmemL : q ∈ Icc (q - e) q := right_mem_Icc.mpr (by linarith)
  have hqmemR : q ∈ Icc q (q + e) := left_mem_Icc.mpr (by linarith)
  have hdL : HasDerivWithinAt uc vq (Icc (q - e) q) q :=
    ((hucL.differentiableOn (by norm_num)) q hqmemL).hasDerivWithinAt
  have hdR : HasDerivWithinAt uc vq (Icc q (q + e)) q := by
    have h := ((hucR.differentiableOn (by norm_num)) q hqmemR).hasDerivWithinAt
    rwa [hvR_vq] at h
  have hIccL_mem : Icc (q - e) q ∈ 𝓝[≤] q :=
    mem_nhdsWithin.mpr ⟨Ioi (q - e), isOpen_Ioi, by simpa using hqL,
      fun x hx => ⟨hx.1.le, hx.2⟩⟩
  have hIccR_mem : Icc q (q + e) ∈ 𝓝[≥] q :=
    mem_nhdsWithin.mpr ⟨Iio (q + e), isOpen_Iio, by simpa using hqR,
      fun x hx => ⟨hx.2, hx.1.le⟩⟩
  have hd2 : HasDerivAt uc vq q := by
    have h1 := (hdL.mono_of_mem_nhdsWithin hIccL_mem).union
      (hdR.mono_of_mem_nhdsWithin hIccR_mem)
    rw [Iic_union_Ici] at h1
    exact h1.hasDerivAt Filter.univ_mem
  have hderiv_q : deriv uc q = vq := hd2.deriv
  -- 5. the coordinate ODE holds on each open one-sided window
  have hode : ∀ t, t ∈ Ioo (q - e) q ∪ Ioo q (q + e) → deriv (deriv uc) t
      = - Geodesic.chartChristoffelContraction (I := I) g (γ q)
          (deriv uc t) (deriv uc t) (uc t) := by
    intro t ht
    have hopen : IsOpen (Ioo (q - e) q ∪ Ioo q (q + e)) := hWL_open.union hWR_open
    have hucW : ContDiffOn ℝ ∞ uc (Ioo (q - e) q ∪ Ioo q (q + e)) := by
      intro x hx
      rcases hx with hx | hx
      · exact ((hucWL x hx).contDiffAt (hWL_open.mem_nhds hx)).contDiffWithinAt
      · exact ((hucWR x hx).contDiffAt (hWR_open.mem_nhds hx)).contDiffWithinAt
    have hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I (γ q)).source := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      rcases hs with hs | hs
      · exact hsrcL s (Ioo_subset_Icc_self hs)
      · exact hsrcR s (Ioo_subset_Icc_self hs)
    have hu1 : ∀ᶠ s in 𝓝 t, HasDerivAt uc (deriv uc s) s := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      exact ((hucW.differentiableOn (by norm_num)).differentiableAt
        (hopen.mem_nhds hs)).hasDerivAt
    have hu2 : DifferentiableAt ℝ (deriv uc) t := by
      have h : ContDiffOn ℝ ∞ (deriv uc) (Ioo (q - e) q ∪ Ioo q (q + e)) :=
        hucW.deriv_of_isOpen hopen (le_of_eq (by rfl))
      exact (h.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds ht)
    have hacc : curveAcceleration (I := I) g γ t = 0 := by
      rcases ht with ht | ht
      · exact haccL t ⟨lt_of_le_of_lt he_p ht.1, ht.2⟩
      · exact haccR t ⟨ht.1, lt_of_lt_of_le ht.2 he_r⟩
    have h0 := chartAcceleration_eq_zero_of_curveAcceleration g hev hu1 hu2 hacc
    linear_combination (norm := module) h0
  -- 6. the left one-sided second derivative is the ODE limit
  have hlimit : ∀ (s₁ : Set ℝ), s₁ = Icc (q - e) q ∨ s₁ = Icc q (q + e) → True := fun _ _ => trivial
  clear hlimit
  have hside : ∀ (I₁ W : Set ℝ), (uc_smooth : ContDiffOn ℝ ∞ uc I₁) → True := fun _ _ _ => trivial
  clear hside
  -- left side
  have hg1L : ContDiffOn ℝ ∞ (derivWithin uc (Icc (q - e) q)) (Icc (q - e) q) :=
    hucL.derivWithin (uniqueDiffOn_Icc hqL) (le_of_eq (by rfl))
  have hg1L_eq : ∀ t ∈ Ioo (q - e) q, derivWithin uc (Icc (q - e) q) t = deriv uc t := by
    intro t ht
    exact ((hucWL.differentiableOn (by norm_num)).differentiableAt
      (hWL_open.mem_nhds ht)).derivWithin (uniqueDiffOn_Icc hqL t (Ioo_subset_Icc_self ht))
  have hNL_cont : ContinuousOn (fun t => - Geodesic.chartChristoffelContraction (I := I)
      g (γ q) (derivWithin uc (Icc (q - e) q) t)
      (derivWithin uc (Icc (q - e) q) t) (uc t)) (Icc (q - e) q) := by
    refine ContinuousOn.neg ?_
    exact continuousOn_chartChristoffelContraction_comp g (γ q) hucL.continuousOn
      hg1L.continuousOn hg1L.continuousOn
      (fun t ht => (extChartAt I (γ q)).map_source (hsrcL t ht))
  have hFL_cont : ContinuousOn (derivWithin (derivWithin uc (Icc (q - e) q))
      (Icc (q - e) q)) (Icc (q - e) q) :=
    hg1L.continuousOn_derivWithin (uniqueDiffOn_Icc hqL) (by norm_num)
  have hFL_eq_NL : ∀ t ∈ Ioo (q - e) q,
      derivWithin (derivWithin uc (Icc (q - e) q)) (Icc (q - e) q) t
        = - Geodesic.chartChristoffelContraction (I := I) g (γ q)
            (derivWithin uc (Icc (q - e) q) t)
            (derivWithin uc (Icc (q - e) q) t) (uc t) := by
    intro t ht
    have hev : derivWithin uc (Icc (q - e) q) =ᶠ[𝓝 t] deriv uc := by
      filter_upwards [hWL_open.mem_nhds ht] with s hs
      exact hg1L_eq s hs
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hev.deriv_eq,
      hode t (Or.inl ht), hg1L_eq t ht]
  haveI hNbotL : (𝓝[Ioo (q - e) q] q).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp
      (by rw [closure_Ioo hqL.ne]; exact right_mem_Icc.mpr hqL.le)
  have hALq : derivWithin (derivWithin uc (Icc (q - e) q)) (Icc (q - e) q) q
      = - Geodesic.chartChristoffelContraction (I := I) g (γ q) vq vq (uc q) := by
    have hFq : Tendsto (derivWithin (derivWithin uc (Icc (q - e) q)) (Icc (q - e) q))
        (𝓝[Ioo (q - e) q] q)
        (𝓝 (derivWithin (derivWithin uc (Icc (q - e) q)) (Icc (q - e) q) q)) :=
      (hFL_cont q hqmemL).mono_left (nhdsWithin_mono q Ioo_subset_Icc_self)
    have hNq : Tendsto (fun t => - Geodesic.chartChristoffelContraction (I := I)
        g (γ q) (derivWithin uc (Icc (q - e) q) t)
        (derivWithin uc (Icc (q - e) q) t) (uc t)) (𝓝[Ioo (q - e) q] q)
        (𝓝 (- Geodesic.chartChristoffelContraction (I := I) g (γ q) vq vq (uc q))) :=
      (hNL_cont q hqmemL).mono_left (nhdsWithin_mono q Ioo_subset_Icc_self)
    refine tendsto_nhds_unique (hFq.congr' ?_) hNq
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hFL_eq_NL t ht
  -- right side
  have hg1R : ContDiffOn ℝ ∞ (derivWithin uc (Icc q (q + e))) (Icc q (q + e)) :=
    hucR.derivWithin (uniqueDiffOn_Icc hqR) (le_of_eq (by rfl))
  have hg1R_eq : ∀ t ∈ Ioo q (q + e), derivWithin uc (Icc q (q + e)) t = deriv uc t := by
    intro t ht
    exact ((hucWR.differentiableOn (by norm_num)).differentiableAt
      (hWR_open.mem_nhds ht)).derivWithin (uniqueDiffOn_Icc hqR t (Ioo_subset_Icc_self ht))
  have hNR_cont : ContinuousOn (fun t => - Geodesic.chartChristoffelContraction (I := I)
      g (γ q) (derivWithin uc (Icc q (q + e)) t)
      (derivWithin uc (Icc q (q + e)) t) (uc t)) (Icc q (q + e)) := by
    refine ContinuousOn.neg ?_
    exact continuousOn_chartChristoffelContraction_comp g (γ q) hucR.continuousOn
      hg1R.continuousOn hg1R.continuousOn
      (fun t ht => (extChartAt I (γ q)).map_source (hsrcR t ht))
  have hFR_cont : ContinuousOn (derivWithin (derivWithin uc (Icc q (q + e)))
      (Icc q (q + e))) (Icc q (q + e)) :=
    hg1R.continuousOn_derivWithin (uniqueDiffOn_Icc hqR) (by norm_num)
  have hFR_eq_NR : ∀ t ∈ Ioo q (q + e),
      derivWithin (derivWithin uc (Icc q (q + e))) (Icc q (q + e)) t
        = - Geodesic.chartChristoffelContraction (I := I) g (γ q)
            (derivWithin uc (Icc q (q + e)) t)
            (derivWithin uc (Icc q (q + e)) t) (uc t) := by
    intro t ht
    have hev : derivWithin uc (Icc q (q + e)) =ᶠ[𝓝 t] deriv uc := by
      filter_upwards [hWR_open.mem_nhds ht] with s hs
      exact hg1R_eq s hs
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2), hev.deriv_eq,
      hode t (Or.inr ht), hg1R_eq t ht]
  haveI hNbotR : (𝓝[Ioo q (q + e)] q).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp
      (by rw [closure_Ioo hqR.ne]; exact left_mem_Icc.mpr hqR.le)
  have hARq : derivWithin (derivWithin uc (Icc q (q + e))) (Icc q (q + e)) q
      = - Geodesic.chartChristoffelContraction (I := I) g (γ q) vq vq (uc q) := by
    have hFq : Tendsto (derivWithin (derivWithin uc (Icc q (q + e))) (Icc q (q + e)))
        (𝓝[Ioo q (q + e)] q)
        (𝓝 (derivWithin (derivWithin uc (Icc q (q + e))) (Icc q (q + e)) q)) :=
      (hFR_cont q hqmemR).mono_left (nhdsWithin_mono q Ioo_subset_Icc_self)
    have hNq : Tendsto (fun t => - Geodesic.chartChristoffelContraction (I := I)
        g (γ q) (derivWithin uc (Icc q (q + e)) t)
        (derivWithin uc (Icc q (q + e)) t) (uc t)) (𝓝[Ioo q (q + e)] q)
        (𝓝 (- Geodesic.chartChristoffelContraction (I := I) g (γ q)
          (derivWithin uc (Icc q (q + e)) q)
          (derivWithin uc (Icc q (q + e)) q) (uc q))) :=
      (hNR_cont q hqmemR).mono_left (nhdsWithin_mono q Ioo_subset_Icc_self)
    rw [hvR_vq] at hNq
    refine tendsto_nhds_unique (hFq.congr' ?_) hNq
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hFR_eq_NR t ht
  -- 7. the one-sided second derivatives agree; `deriv uc` is differentiable at `q`
  have hg1L_hd : HasDerivWithinAt (derivWithin uc (Icc (q - e) q))
      (- Geodesic.chartChristoffelContraction (I := I) g (γ q) vq vq (uc q))
      (Icc (q - e) q) q := by
    have h := ((hg1L.differentiableOn (by norm_num)) q hqmemL).hasDerivWithinAt
    rwa [hALq] at h
  have hg1R_hd : HasDerivWithinAt (derivWithin uc (Icc q (q + e)))
      (- Geodesic.chartChristoffelContraction (I := I) g (γ q) vq vq (uc q))
      (Icc q (q + e)) q := by
    have h := ((hg1R.differentiableOn (by norm_num)) q hqmemR).hasDerivWithinAt
    rwa [hARq] at h
  have hDL : HasDerivWithinAt (deriv uc)
      (- Geodesic.chartChristoffelContraction (I := I) g (γ q) vq vq (uc q))
      (Ioc (q - e) q) q := by
    refine (hg1L_hd.mono Ioc_subset_Icc_self).congr ?_ ?_
    · intro x hx
      rcases eq_or_lt_of_le hx.2 with heq | hlt
      · rw [heq, hderiv_q, hvq_def]
      · exact (hg1L_eq x ⟨hx.1, hlt⟩).symm
    · rw [hderiv_q, hvq_def]
  have hDR : HasDerivWithinAt (deriv uc)
      (- Geodesic.chartChristoffelContraction (I := I) g (γ q) vq vq (uc q))
      (Ico q (q + e)) q := by
    refine (hg1R_hd.mono Ico_subset_Icc_self).congr ?_ ?_
    · intro x hx
      rcases eq_or_lt_of_le hx.1 with heq | hlt
      · rw [← heq, hderiv_q, ← hvR_vq]
      · exact (hg1R_eq x ⟨hlt, hx.2⟩).symm
    · rw [hderiv_q, ← hvR_vq]
  have hIoc_mem : Ioc (q - e) q ∈ 𝓝[≤] q :=
    mem_nhdsWithin.mpr ⟨Ioi (q - e), isOpen_Ioi, by simpa using hqL,
      fun x hx => ⟨hx.1, hx.2⟩⟩
  have hIco_mem : Ico q (q + e) ∈ 𝓝[≥] q :=
    mem_nhdsWithin.mpr ⟨Iio (q + e), isOpen_Iio, by simpa using hqR,
      fun x hx => ⟨hx.2, hx.1⟩⟩
  have hDD : HasDerivAt (deriv uc)
      (- Geodesic.chartChristoffelContraction (I := I) g (γ q) vq vq (uc q)) q := by
    have h1 := (hDL.mono_of_mem_nhdsWithin hIoc_mem).union
      (hDR.mono_of_mem_nhdsWithin hIco_mem)
    rw [Iic_union_Ici] at h1
    exact h1.hasDerivAt Filter.univ_mem
  -- 8. assemble the moving-foot geodesic equation at the break
  have hcl : Geodesic.chartLocalCurve (I := I) γ q = uc := rfl
  refine (hasGeodesicEquationAt_iff_curveAcceleration (I := I) g γ q).mpr ⟨⟨?_, ?_⟩, ?_⟩
  · -- eventual differentiability of the chart reading
    rw [hcl]
    filter_upwards [Ioo_mem_nhds hqL hqR] with s hs
    rcases lt_trichotomy s q with h | h | h
    · exact ((hucWL.differentiableOn (by norm_num)).differentiableAt
        (hWL_open.mem_nhds ⟨hs.1, h⟩)).hasDerivAt
    · subst h
      rw [hderiv_q]
      exact hd2
    · exact ((hucWR.differentiableOn (by norm_num)).differentiableAt
        (hWR_open.mem_nhds ⟨h, hs.2⟩)).hasDerivAt
  · rw [hcl]
    exact hDD.differentiableAt
  · -- the acceleration vanishes at the break
    show (deriv (deriv (Geodesic.chartLocalCurve (I := I) γ q)) q +
        Geodesic.chartChristoffelContraction (I := I) g (γ q)
          (deriv (Geodesic.chartLocalCurve (I := I) γ q) q)
          (deriv (Geodesic.chartLocalCurve (I := I) γ q) q)
          (extChartAt I (γ q) (γ q)) : E) = 0
    rw [hcl, hDD.deriv, hderiv_q]
    have huq : uc q = extChartAt I (γ q) (γ q) := rfl
    rw [← huq]
    linear_combination (norm := module)

/-! ## Assembly — local minima of energy are geodesics (Theorem 5.4.3) -/

/-- **Eng.** Locate a time strictly interior to `[u 0, u n]` relative to a
`ℕ`-indexed partition `u`: it is either interior to a piece
`Ioo (u i) (u (i + 1))` (`i < n`) or lands on an interior node `u (i + 1)`
(`i + 1 < n`).  (No monotonicity is needed: take the least `k` with `t < u k`.) -/
theorem strictPartition_locate {n : ℕ} {u : ℕ → ℝ}
    {t : ℝ} (ht : t ∈ Ioo (u 0) (u n)) :
    (∃ i, i < n ∧ t ∈ Ioo (u i) (u (i + 1))) ∨ (∃ i, i + 1 < n ∧ t = u (i + 1)) := by
  classical
  have hP : ∃ k, t < u k := ⟨n, ht.2⟩
  obtain ⟨k, hkspec, hkle, hkmin⟩ :
      ∃ k, t < u k ∧ k ≤ n ∧ ∀ j < k, u j ≤ t :=
    ⟨Nat.find hP, Nat.find_spec hP, Nat.find_le ht.2,
      fun j hj => not_lt.mp (Nat.find_min hP hj)⟩
  have hk0 : k ≠ 0 := by
    intro h; rw [h] at hkspec; exact absurd hkspec (not_lt.mpr ht.1.le)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjle : u j ≤ t := hkmin j (Nat.lt_succ_self j)
  rcases eq_or_lt_of_le hjle with heq | hlt
  · -- `t = u j` lands on an interior node
    have hj0 : j ≠ 0 := by
      intro h; rw [h] at heq; exact absurd heq.symm (ne_of_gt ht.1)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    exact Or.inr ⟨m, by omega, heq.symm⟩
  · -- `u j < t < u (j + 1)` lies interior to piece `j`
    exact Or.inl ⟨j, by omega, hlt, hkspec⟩

/-- **Math.** At a time interior to a smooth piece, the vanishing of the
acceleration is exactly the moving-foot geodesic equation: the chart reading
`u = φ_{γ t} ∘ γ` is `C^∞` on a neighbourhood of `t`, so the `C²`-regularity
required by `hasGeodesicEquationAt_iff_curveAcceleration` is automatic. -/
theorem hasGeodesicEquationAt_of_isOpen_contMDiffOn (g : RiemannianMetric I M)
    {γ : ℝ → M} {s : Set ℝ} (hs : IsOpen s) {t : ℝ} (ht : t ∈ s)
    (hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ s)
    (hacc : curveAcceleration (I := I) g γ t = 0) :
    Geodesic.HasGeodesicEquationAt (I := I) g γ t := by
  have hct : ContinuousAt γ t := hsm.continuousOn.continuousAt (hs.mem_nhds ht)
  have hevsrc : ∀ᶠ s' in 𝓝 t, γ s' ∈ (extChartAt I (γ t)).source :=
    hct.eventually_mem ((isOpen_extChartAt_source (γ t)).mem_nhds
      (mem_extChartAt_source (I := I) (γ t)))
  obtain ⟨d, hd, hprop⟩ := Metric.eventually_nhds_iff.mp
    (hevsrc.and (Filter.eventually_of_mem (hs.mem_nhds ht) fun x hx => hx))
  set S := Metric.ball t d with hS_def
  have hS_open : IsOpen S := Metric.isOpen_ball
  have htS : t ∈ S := Metric.mem_ball_self hd
  have hsrcS : ∀ y ∈ S, γ y ∈ (extChartAt I (γ t)).source :=
    fun y hy => (hprop (Metric.mem_ball.mp hy)).1
  have hγS : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ S :=
    hsm.mono fun y hy => (hprop (Metric.mem_ball.mp hy)).2
  set uc : ℝ → E := fun s' => extChartAt I (γ t) (γ s') with huc_def
  have huc : ContDiffOn ℝ ∞ uc S := contDiffOn_extChartAt_comp hγS hsrcS
  have hcl : Geodesic.chartLocalCurve (I := I) γ t = uc := rfl
  refine (hasGeodesicEquationAt_iff_curveAcceleration (I := I) g γ t).mpr ⟨⟨?_, ?_⟩, hacc⟩
  · rw [hcl]
    filter_upwards [hS_open.mem_nhds htS] with s' hs'
    exact ((huc.differentiableOn (by norm_num)).differentiableAt
      (hS_open.mem_nhds hs')).hasDerivAt
  · rw [hcl]
    have h : ContDiffOn ℝ ∞ (deriv uc) S :=
      huc.deriv_of_isOpen hS_open (le_of_eq (by rfl))
    exact (h.differentiableOn (by norm_num)).differentiableAt (hS_open.mem_nhds htS)

/-- **Math.** Petersen Ch. 5, §5.4, Theorem 5.4.3
(`thm:pet-ch5-energy-minima-geodesics`): a piecewise smooth curve that is a
local minimum of the energy functional among proper variations is a geodesic
on the open parameter interval.  Interior to each smooth piece the acceleration
vanishes (`stationary_curveAcceleration_eq_zero`); at each interior break the
one-sided velocities agree (`stationary_velocityJump_eq_zero`), and the geodesic
ODE glues the two `C^∞` pieces into a `C²` reading across the break
(`hasGeodesicEquationAt_of_matching_break`), so the moving-foot geodesic
equation `Geodesic.HasGeodesicEquationAt` holds at every time of `(a, b)`. -/
theorem energyLocalMinimum_isGeodesic (g : RiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b)
    (hmin : ∀ V : CurveVariation (I := I) γ a b, IsProperVariation V →
      IsLocalMin (fun s => energyFunctional (I := I) g (V.curve s) a b) 0) :
    Geodesic.IsGeodesicOn (I := I) g γ (Ioo a b) := by
  obtain ⟨n, u, hstrict, hu0, hun, husm⟩ := hγ.exists_strictMono_partition
  have humono := strictPartition_mono hstrict
  intro t ht
  have ht' : t ∈ Ioo (u 0) (u n) := by rw [hu0, hun]; exact ht
  rcases strictPartition_locate ht' with ⟨i, hi, hti⟩ | ⟨i, hi, hti⟩
  · -- interior to smooth piece `i`
    have hacc : curveAcceleration (I := I) g γ t = 0 :=
      stationary_curveAcceleration_eq_zero g hγ hstrict hu0 hun husm hmin hi hti
    exact hasGeodesicEquationAt_of_isOpen_contMDiffOn g isOpen_Ioo hti
      ((husm i hi).mono Ioo_subset_Icc_self) hacc
  · -- interior break at `u (i + 1)`
    rw [hti]
    have hpq : u i < u (i + 1) := hstrict i (by omega)
    have hqr : u (i + 1) < u (i + 2) := hstrict (i + 1) hi
    have ha_le : a ≤ u i := by rw [← hu0]; exact humono 0 i (Nat.zero_le _) (by omega)
    have hle_b : u (i + 2) ≤ b := by
      rw [← hun]; exact humono (i + 2) n (by omega) le_rfl
    have hγc : ContinuousOn γ (Icc (u i) (u (i + 2))) :=
      hγ.1.mono (Icc_subset_Icc ha_le hle_b)
    have haccL : ∀ s' ∈ Ioo (u i) (u (i + 1)), curveAcceleration (I := I) g γ s' = 0 :=
      fun s' hs' => stationary_curveAcceleration_eq_zero g hγ hstrict hu0 hun husm hmin
        (by omega) hs'
    have haccR : ∀ s' ∈ Ioo (u (i + 1)) (u (i + 2)),
        curveAcceleration (I := I) g γ s' = 0 :=
      fun s' hs' => stationary_curveAcceleration_eq_zero (i := i + 1) g hγ hstrict hu0 hun
        husm hmin hi hs'
    have hjump := stationary_velocityJump_eq_zero g hγ hstrict hu0 hun husm hmin hi
    exact hasGeodesicEquationAt_of_matching_break g hpq hqr hγc
      (husm i (by omega)) (husm (i + 1) hi) haccL haccR hjump

/-! ## Corollary — piecewise smooth segments are geodesics (Cor. 5.4.3) -/

/-- **Math.** The energy over `[a, b]` only reads the curve on `(a, b)`: two
curves agreeing on the open interval have equal energy (the squared speed at an
interior time only depends on the germ there, and the endpoints are null). -/
theorem energyFunctional_congr_of_eqOn_Ioo (g : RiemannianMetric I M)
    {γ γ' : ℝ → M} {a b : ℝ} (hab : a ≤ b) (h : Set.EqOn γ γ' (Ioo a b)) :
    energyFunctional (I := I) g γ a b = energyFunctional (I := I) g γ' a b := by
  rw [energyFunctional_def, energyFunctional_def]
  congr 1
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  exact curveSpeedSq_congr_nhds (I := I) g
    (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun x hx => h hx)

/-- **Math.** A curve whose partial length grows linearly, `L(σ)|_a^t = k·(t-a)`,
has constant speed `k` off the finite non-smoothness set.  At each interior
smooth time `t` the arclength integral `∫_a^t √|σ̇|²` has derivative `√|σ̇(t)|²`
(fundamental theorem of calculus, the integrand being continuous there); since it
also equals `k·(t-a)`, its derivative is `k`, so `|σ̇(t)|² = k²`. -/
theorem isConstantSpeedCurve_of_curveLength_proportional (g : RiemannianMetric I M)
    {σ : ℝ → M} {a b k : ℝ} (hk : 0 ≤ k)
    (hσ : IsPiecewiseSmoothCurve (I := I) σ a b)
    (hlen : ∀ t ∈ Icc a b, curveLength (I := I) g σ a t = k * (t - a)) :
    IsConstantSpeedCurve (I := I) g σ a b := by
  classical
  obtain ⟨n, u, hstrict, hu0, hun, husm⟩ := hσ.exists_strictMono_partition
  have hInt_ab : IntervalIntegrable (fun x => Real.sqrt (curveSpeedSq (I := I) g σ x))
      MeasureTheory.volume a b := hσ.intervalIntegrable_sqrt_curveSpeedSq g
  refine ⟨k, hk, Finset.image u (Finset.range (n + 1)), fun t ht => ?_⟩
  obtain ⟨htab, htnot⟩ := ht
  have hnode : ∀ i, i ≤ n → t ≠ u i := fun i hi hti =>
    htnot (Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨i, Finset.mem_range.mpr (by omega), hti.symm⟩))
  have hat : a < t := lt_of_le_of_ne htab.1
    (fun h => hnode 0 (Nat.zero_le n) (by rw [hu0]; exact h.symm))
  have htb : t < b := lt_of_le_of_ne htab.2
    (fun h => hnode n le_rfl (by rw [hun]; exact h))
  have ht' : t ∈ Ioo (u 0) (u n) := by rw [hu0, hun]; exact ⟨hat, htb⟩
  rcases strictPartition_locate ht' with ⟨i, hi, hti⟩ | ⟨i, hi, hti⟩
  · -- interior of piece `i`: differentiate the length integral at `t`
    have hsmIoo : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ (Ioo (u i) (u (i + 1))) :=
      (husm i hi).mono Ioo_subset_Icc_self
    have hspeed_cont : ContinuousOn (curveSpeedSq (I := I) g σ) (Ioo (u i) (u (i + 1))) :=
      fun x hx => (contDiffAt_curveSpeedSq g isOpen_Ioo hsmIoo hx).continuousAt.continuousWithinAt
    have hf_contOn : ContinuousOn (fun x => Real.sqrt (curveSpeedSq (I := I) g σ x))
        (Ioo (u i) (u (i + 1))) := Real.continuous_sqrt.comp_continuousOn hspeed_cont
    have hcontAt : ContinuousAt (fun x => Real.sqrt (curveSpeedSq (I := I) g σ x)) t :=
      hf_contOn.continuousAt (isOpen_Ioo.mem_nhds hti)
    have hInt_at : IntervalIntegrable (fun x => Real.sqrt (curveSpeedSq (I := I) g σ x))
        MeasureTheory.volume a t :=
      hInt_ab.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
        (Set.mem_uIcc.mpr (Or.inl ⟨hat.le, htab.2⟩)))
    have hmeas : StronglyMeasurableAtFilter
        (fun x => Real.sqrt (curveSpeedSq (I := I) g σ x)) (𝓝 t) MeasureTheory.volume :=
      ⟨Ioo (u i) (u (i + 1)), isOpen_Ioo.mem_nhds hti,
        hf_contOn.aestronglyMeasurable measurableSet_Ioo⟩
    have hFTC : HasDerivAt (fun v => ∫ x in a..v, Real.sqrt (curveSpeedSq (I := I) g σ x))
        (Real.sqrt (curveSpeedSq (I := I) g σ t)) t :=
      intervalIntegral.integral_hasDerivAt_right hInt_at hmeas hcontAt
    have hlin : HasDerivAt (fun v => k * (v - a)) k t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul k
    have hcongr : (fun v => k * (v - a)) =ᶠ[𝓝 t]
        fun v => ∫ x in a..v, Real.sqrt (curveSpeedSq (I := I) g σ x) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo a b from ⟨hat, htb⟩)] with v hv
      rw [← curveLength_def, hlen v ⟨hv.1.le, hv.2.le⟩]
    have hst : Real.sqrt (curveSpeedSq (I := I) g σ t) = k :=
      (hFTC.congr_of_eventuallyEq hcongr).unique hlin
    have hsq := Real.sq_sqrt (curveSpeedSq_nonneg (I := I) g σ t)
    rw [hst] at hsq
    exact hsq.symm
  · exact absurd hti (hnode (i + 1) (by omega))

/-- **Math.** A curve that globally minimizes energy among piecewise smooth
competitors with the same endpoints is a local minimum of energy along every
proper variation: each variation curve `c_s` (for `|s|` small) is such a
competitor, and `c_0` has the same energy as the curve itself. -/
theorem energyLocalMin_of_energyMinimizer (g : RiemannianMetric I M)
    {σ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hmin : ∀ c : ℝ → M, IsPiecewiseSmoothCurve (I := I) c a b → c a = σ a → c b = σ b →
      energyFunctional (I := I) g σ a b ≤ energyFunctional (I := I) g c a b) :
    ∀ V : CurveVariation (I := I) σ a b, IsProperVariation V →
      IsLocalMin (fun s => energyFunctional (I := I) g (V.curve s) a b) 0 := by
  intro V hproper
  have hzero : energyFunctional (I := I) g (V.curve 0) a b
      = energyFunctional (I := I) g σ a b :=
    energyFunctional_congr_of_eqOn_Ioo g hab
      (fun t ht => V.init t (Ioo_subset_Icc_self ht))
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr V.width_pos) V.width_pos] with s hs
  show energyFunctional (I := I) g (V.curve 0) a b
      ≤ energyFunctional (I := I) g (V.curve s) a b
  rw [hzero]
  obtain ⟨hsa, hsb⟩ := hproper s hs
  exact hmin (V.curve s) (V.isPiecewiseSmoothCurve hs)
    (by rw [CurveVariation.curve_apply]; exact hsa)
    (by rw [CurveVariation.curve_apply]; exact hsb)

/-- **Math.** Petersen Ch. 5, §5.4, Corollary 5.4.3
(`cor:pet-ch5-segments-are-geodesics`): any piecewise smooth segment on `[0, 1]`
is a geodesic.  A segment is a constant-speed length minimizer, hence
(Prop. 5.4.1) an energy minimizer, hence a local energy minimum along every
proper variation, hence a geodesic by Theorem 5.4.3. -/
theorem segment_isGeodesic (g : RiemannianMetric I M) {σ : ℝ → M}
    (hσ : IsSegment (I := I) g σ 0 1) :
    Geodesic.IsGeodesicOn (I := I) g σ (Ioo 0 1) := by
  obtain ⟨hpw, hLdist, k, hk, hprop⟩ := hσ
  have hLmin : ∀ c : ℝ → M, IsPiecewiseSmoothCurve (I := I) c 0 1 →
      c 0 = σ 0 → c 1 = σ 1 →
      curveLength (I := I) g σ 0 1 ≤ curveLength (I := I) g c 0 1 := by
    intro c hc hc0 hc1
    rw [hLdist, ← hc0, ← hc1]
    exact riemannianDistance_le_curveLength g hc rfl rfl
  have hconst : IsConstantSpeedCurve (I := I) g σ 0 1 :=
    isConstantSpeedCurve_of_curveLength_proportional g hk hpw hprop
  have hEmin := energyMinimizer_of_constantSpeed_lengthMinimizer g hconst hLmin
  exact energyLocalMinimum_isGeodesic g hpw
    (energyLocalMin_of_energyMinimizer g zero_le_one hEmin)