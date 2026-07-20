import PetersenLib.Ch05.RadialSmooth
import PetersenLib.Riemannian.Exponential.RayGeodesic
import PetersenLib.Riemannian.Geodesic.IntrinsicUniqueness
import PetersenLib.Riemannian.Geodesic.Completeness

/-!
# Petersen Ch. 5, §5.2/§5.3 — geodesics are piecewise `C^∞` curves

The intrinsic geodesics of the vendored do Carmo cone (`IsGeodesicOn`) are only
known to be `C¹` a priori: `IsGeodesicOn` is a second-order ODE condition read
in the moving chart, and the ODE-regularity bootstrap that upgrades a solution
to `C^∞` has been carried out only for the *radial* curve `t ↦ exp_p(t v)`
(`exists_contMDiffOn_expMap_ray`, `PetersenLib/Ch05/RadialSmooth.lean`).

Petersen's metric layer, however, speaks of **piecewise `C^∞`** curves
(`IsPiecewiseSmoothCurve`, `def:pet-ch5-piecewise-smooth-curve`), so a geodesic
is not yet an admissible competitor curve, let alone a segment. This file closes
that gap:

* `PetersenLib.IsGeodesicOn.exists_eqOn_expMap_ray` — the **local identification**:
  after rescaling time by a small `κ`, a geodesic *is* a short radial ray
  `t ↦ exp_{γ t₀}(t · u)` on `[0, 1]`, with `‖u‖` below any threshold the caller
  chooses. This is intrinsic ODE uniqueness
  (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) against the ray, and is the
  reusable workhorse of the file.
* `PetersenLib.IsGeodesicOn.exists_contMDiffOn_comp_affine`,
  `PetersenLib.IsGeodesicOn.exists_contMDiffOn_Icc` — the **local regularity**:
  transporting the ray's `C^∞` regularity (`exists_contMDiffOn_expMap_ray`)
  back along that identification, `γ` is `C^∞` on `[t₀ - δ, t₀]` and on
  `[t₀, t₀ + δ]` for some `δ > 0`.
* `PetersenLib.IsGeodesicOn.isPiecewiseSmoothCurve` — the **global** statement:
  a continuous geodesic on an open `s ⊇ [a, b]` is a Petersen piecewise `C^∞`
  curve on `[a, b]`. The partition is built by a continuous-induction (sup)
  argument on `{x ∈ [a, b] | IsPiecewiseSmoothCurve γ a x}`, the local statement
  supplying both the "sup is attained" and the "sup can be pushed" steps, and
  `IsPiecewiseSmoothCurve.snoc` doing the bookkeeping.
* `PetersenLib.IsGeodesic.isPiecewiseSmoothCurve` — the global-geodesic corollary.

Nothing here is a blueprint node; it is the regularity bridge between the
vendored geodesic theory and Petersen's §5.3 definitions.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff

namespace PetersenLib

open PetersenLib.Geodesic PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]
  [T2Space M] [ConnectedSpace M]

/-- **Math.** **Time-rescaled local identification of a geodesic with a radial
ray.** Let `γ` be a continuous intrinsic geodesic on an open time-set `s` and
`t₀ ∈ s`. There is `δ > 0` such that for every rescaling factor `κ` with
`|κ| ≤ δ` the time-rescaled curve `t ↦ γ (κ t + t₀)` coincides on `[0, 1]` with
the radial ray `t ↦ exp_{γ t₀}(t · u)` of some `u : E` with `‖u‖ < ε`, where the
threshold `ε > 0` is the caller's to choose.

Both smallness requirements on `δ` are used: `κ · [0,1] + t₀` must stay inside
`s` (so the rescaled curve is still a geodesic there), and the rescaled initial
chart velocity `κ • v` must be small enough for the radial ray `t ↦ exp_{γ t₀}(t · κ v)`
to be defined and geodesic on `[0, 1]` and to fall below the caller's threshold
`ε`. Intrinsic ODE uniqueness (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`)
then identifies the two curves. -/
theorem IsGeodesicOn.exists_eqOn_expMap_ray (g : RiemannianMetric I M)
    {γ : ℝ → M} {s : Set ℝ} {t₀ : ℝ} (hs : IsOpen s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hc : ContinuousOn γ s) (ht₀ : t₀ ∈ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ κ : ℝ, |κ| ≤ δ → ∃ u : E, ‖u‖ < ε ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ (κ * t + t₀) =
        Exponential.expMap (I := I) g (γ t₀) ((t • u : E) : TangentSpace I (γ t₀)) := by
  obtain ⟨ρ, bb, hρ, hbb, hadm, hray⟩ :=
    Exponential.exists_isGeodesicOn_expMap_ray (I := I) g (γ t₀)
  obtain ⟨v, acc, hv, -, -, -⟩ := hγ t₀ ht₀
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs t₀ ht₀
  set b'' : ℝ := min bb 2 with hb''
  have hb''1 : 1 < b'' := lt_min hbb one_lt_two
  have hb''bb : Ioo (-b'') b'' ⊆ Ioo (-bb) bb := by
    intro t ht
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left bb 2)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left bb 2)⟩
  have hb''2 : b'' ≤ 2 := min_le_right _ _
  set m : ℝ := min ρ ε with hm
  have hm0 : 0 < m := lt_min hρ hε
  refine ⟨min (r / 4) (m / (2 * (‖v‖ + 1))), by positivity, ?_⟩
  intro κ hκ
  set δ : ℝ := min (r / 4) (m / (2 * (‖v‖ + 1))) with hδ
  have hδr : δ ≤ r / 4 := min_le_left _ _
  have hδm : δ ≤ m / (2 * (‖v‖ + 1)) := min_le_right _ _
  set u : E := κ • v with hu
  have hunorm : ‖u‖ < m := by
    have h1 : ‖u‖ = |κ| * ‖v‖ := by rw [hu, norm_smul, Real.norm_eq_abs]
    have h2 : |κ| * ‖v‖ ≤ δ * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right hκ (norm_nonneg v)
    have h3 : δ * ‖v‖ ≤ (m / (2 * (‖v‖ + 1))) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hδm (norm_nonneg v)
    have h4 : (m / (2 * (‖v‖ + 1))) * ‖v‖ < m := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v, hm0]
    linarith [h1 ▸ (le_of_eq h1 : ‖u‖ ≤ |κ| * ‖v‖)]
  have huρ : ‖u‖ < ρ := lt_of_lt_of_le hunorm (min_le_left _ _)
  have huε : ‖u‖ < ε := lt_of_lt_of_le hunorm (min_le_right _ _)
  -- the affine time-change maps the working interval into `s`
  have hmaps : ∀ t ∈ Ioo (-b'') b'', κ * t + t₀ ∈ s := by
    intro t ht
    refine hrs ?_
    have hδ0 : 0 < δ := by
      rw [hδ]; positivity
    have habs : |κ * t + t₀ - t₀| = |κ| * |t| := by
      rw [add_sub_cancel_right, abs_mul]
    have ht2 : |t| < 2 := by
      rw [abs_lt]
      exact ⟨lt_of_le_of_lt (by linarith [hb''2]) ht.1, lt_of_lt_of_le ht.2 hb''2⟩
    have : |κ| * |t| < r := by
      calc |κ| * |t| ≤ δ * 2 := by
            refine mul_le_mul hκ ht2.le (abs_nonneg t) hδ0.le
        _ ≤ (r / 4) * 2 := by linarith
        _ < r := by linarith
    simpa [Metric.mem_ball, Real.dist_eq, habs] using this
  set γf : ℝ → M := fun t : ℝ => γ (κ * t + t₀) with hγf
  set ray : ℝ → M := fun t : ℝ =>
    Exponential.expMap (I := I) g (γ t₀) ((t • u : E) : TangentSpace I (γ t₀)) with hraydef
  obtain ⟨hray0, hrayv, hraycont, hraygeo⟩ := hray u huρ
  -- geodesic and continuity data on the working interval
  have hγf_geo : IsGeodesicOn (I := I) g γf (Ioo (-b'') b'') := by
    have := Geodesic.isGeodesicOn_comp_affine (I := I) (κ := κ) (c := t₀) hγ
    exact fun t ht => this t (hmaps t ht)
  have hγf_cont : ContinuousOn γf (Ioo (-b'') b'') := by
    refine ContinuousOn.comp hc ?_ hmaps
    exact (Continuous.continuousOn (by fun_prop))
  have h0mem : (0 : ℝ) ∈ Ioo (-b'') b'' := ⟨by linarith, by linarith⟩
  have hγf0 : γf 0 = γ t₀ := by simp [hγf]
  -- velocity matching at time `0`
  have hA : HasDerivAt (fun t : ℝ => κ * t + t₀) κ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul κ).add_const t₀
  have hγf_vel : HasDerivAt (fun τ : ℝ => extChartAt I (γ t₀) (γf τ)) u 0 := by
    have hv' : HasDerivAt (fun τ : ℝ => extChartAt I (γ t₀) (γ τ)) v (κ * 0 + t₀) := by
      simpa using hv
    have := hv'.scomp (0 : ℝ) hA
    simpa [hγf, Function.comp_def, hu] using this
  -- intrinsic ODE uniqueness identifies the rescaled geodesic with the ray
  have heq : EqOn γf ray (Ioo (-b'') b'') := by
    refine IsGeodesicOn.eqOn_of_deriv_chartReading_eq (I := I) (β := γ t₀)
      isOpen_Ioo isPreconnected_Ioo hγf_geo (hraygeo.mono hb''bb)
      hγf_cont (hraycont.mono hb''bb) h0mem ?_ ?_ ?_
    · rw [hγf0]; exact hray0.symm
    · rw [hγf0]; exact mem_chart_source H (γ t₀)
    · show deriv (fun τ : ℝ => extChartAt I (γ t₀) (γf τ)) 0
        = deriv (fun τ : ℝ => extChartAt I (γ t₀) (ray τ)) 0
      rw [hγf_vel.deriv, hrayv.deriv]
  have hIcc : Icc (0 : ℝ) 1 ⊆ Ioo (-b'') b'' := by
    intro t ht
    exact ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hb''1⟩
  exact ⟨u, huε, fun t ht => heq (hIcc ht)⟩

/-- **Math.** **Time-rescaled local `C^∞` regularity of a geodesic.** Let `γ` be
a continuous intrinsic geodesic on an open time-set `s` and `t₀ ∈ s`. There is
`δ > 0` such that for every rescaling factor `κ` with `|κ| ≤ δ` the rescaled
curve `t ↦ γ (κ t + t₀)` is `C^∞` on `[0, 1]`: it *is* a short radial ray
(`IsGeodesicOn.exists_eqOn_expMap_ray`), and short radial rays are `C^∞`
(`exists_contMDiffOn_expMap_ray`). -/
theorem IsGeodesicOn.exists_contMDiffOn_comp_affine (g : RiemannianMetric I M)
    {γ : ℝ → M} {s : Set ℝ} {t₀ : ℝ} (hs : IsOpen s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hc : ContinuousOn γ s) (ht₀ : t₀ ∈ s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ κ : ℝ, |κ| ≤ δ →
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => γ (κ * t + t₀)) (Icc 0 1) := by
  obtain ⟨ε, hε, hsm⟩ := exists_contMDiffOn_expMap_ray (I := I) g (γ t₀)
  obtain ⟨δ, hδ, hmain⟩ :=
    IsGeodesicOn.exists_eqOn_expMap_ray (I := I) g hs hγ hc ht₀ hε
  refine ⟨δ, hδ, fun κ hκ => ?_⟩
  obtain ⟨u, hu, heq⟩ := hmain κ hκ
  exact (hsm u hu).congr heq

/-- **Math.** **A geodesic is `C^∞` near every time of its (open) time-set.**
For every `t₀ ∈ s` there is `δ > 0` such that the continuous geodesic `γ` is
`C^∞` (as a manifold map) on `[t₀ - δ, t₀]` and on `[t₀, t₀ + δ]`.

The one-sided intervals are the images of `[0, 1]` under the two time-rescalings
`t ↦ ±δ t + t₀` of `IsGeodesicOn.exists_contMDiffOn_comp_affine`; the inverse
rescalings are smooth maps `ℝ → ℝ`, so the regularity transports. -/
theorem IsGeodesicOn.exists_contMDiffOn_Icc (g : RiemannianMetric I M)
    {γ : ℝ → M} {s : Set ℝ} {t₀ : ℝ} (hs : IsOpen s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hc : ContinuousOn γ s) (ht₀ : t₀ ∈ s) :
    ∃ δ : ℝ, 0 < δ ∧ ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (t₀ - δ) t₀) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc t₀ (t₀ + δ)) := by
  obtain ⟨δ, hδ, hmain⟩ :=
    IsGeodesicOn.exists_contMDiffOn_comp_affine (I := I) g hs hγ hc ht₀
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  refine ⟨δ, hδ, ?_, ?_⟩
  · -- backward piece: `γ τ = (fun t => γ ((-δ) t + t₀)) ((t₀ - τ)/δ)`
    have hf : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun τ : ℝ => (t₀ - τ) / δ)
        (Icc (t₀ - δ) t₀) := by
      have : ContDiff ℝ ∞ (fun τ : ℝ => (t₀ - τ) / δ) := by fun_prop
      exact this.contMDiff.contMDiffOn
    have hmt : MapsTo (fun τ : ℝ => (t₀ - τ) / δ) (Icc (t₀ - δ) t₀) (Icc 0 1) := by
      intro τ hτ
      constructor
      · exact div_nonneg (by linarith [hτ.2]) hδ.le
      · rw [div_le_one hδ]; linarith [hτ.1]
    have hcomp := ((hmain (-δ) (by rw [abs_neg, abs_of_pos hδ])).comp hf hmt)
    refine hcomp.congr ?_
    intro τ hτ
    show γ τ = γ ((-δ) * ((t₀ - τ) / δ) + t₀)
    have : (-δ) * ((t₀ - τ) / δ) + t₀ = τ := by field_simp; ring
    rw [this]
  · -- forward piece: `γ τ = (fun t => γ (δ t + t₀)) ((τ - t₀)/δ)`
    have hf : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun τ : ℝ => (τ - t₀) / δ)
        (Icc t₀ (t₀ + δ)) := by
      have : ContDiff ℝ ∞ (fun τ : ℝ => (τ - t₀) / δ) := by fun_prop
      exact this.contMDiff.contMDiffOn
    have hmt : MapsTo (fun τ : ℝ => (τ - t₀) / δ) (Icc t₀ (t₀ + δ)) (Icc 0 1) := by
      intro τ hτ
      constructor
      · exact div_nonneg (by linarith [hτ.1]) hδ.le
      · rw [div_le_one hδ]; linarith [hτ.2]
    have hcomp := ((hmain δ (by rw [abs_of_pos hδ])).comp hf hmt)
    refine hcomp.congr ?_
    intro τ hτ
    show γ τ = γ (δ * ((τ - t₀) / δ) + t₀)
    have : δ * ((τ - t₀) / δ) + t₀ = τ := by field_simp; ring
    rw [this]

/-- **Math.** The degenerate case of Petersen's piecewise `C^∞` condition
(`def:pet-ch5-piecewise-smooth-curve`): on the one-point interval `[a, a]` the
trivial partition `n = 0`, `u = ![a]` has no pieces, so continuity alone
suffices. -/
theorem isPiecewiseSmoothCurve_self {γ : ℝ → M} {a : ℝ}
    (hc : ContinuousOn γ (Icc a a)) :
    IsPiecewiseSmoothCurve (I := I) γ a a := by
  refine ⟨hc, 0, ![a], ?_, ?_, ?_, ?_⟩
  · intro i j _
    fin_cases i; fin_cases j; exact le_rfl
  · simp
  · simp
  · exact fun i => i.elim0

/-- **Math.** **A geodesic is a Petersen piecewise `C^∞` curve.** If `γ` is a
continuous intrinsic geodesic on an open time-set `s` containing `[a, b]`
(`a ≤ b`), then `γ` is piecewise `C^∞` on `[a, b]` in Petersen's sense
(`def:pet-ch5-piecewise-smooth-curve`), hence an admissible competitor curve for
the Riemannian distance.

This is the regularity bridge: `IsGeodesicOn` is only a `C¹`/second-order-ODE
condition, while Petersen's curves must be `C^∞` on each piece of a finite
partition. The partition is produced by continuous induction on
`S = {x ∈ [a, b] | γ is piecewise C^∞ on [a, x]}`: with `c = sup S`, the
one-sided local `C^∞` regularity `IsGeodesicOn.exists_contMDiffOn_Icc` at `c`
shows both that `c ∈ S` (append the last `C^∞` piece `[x, c]` for some `x ∈ S`
close to `c`) and that `c < b` is impossible (append `[c, min b (c + δ)]`). -/
theorem IsGeodesicOn.isPiecewiseSmoothCurve (g : RiemannianMetric I M)
    {γ : ℝ → M} {s : Set ℝ} {a b : ℝ} (hs : IsOpen s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hc : ContinuousOn γ s)
    (hab : a ≤ b) (hsub : Icc a b ⊆ s) :
    IsPiecewiseSmoothCurve (I := I) γ a b := by
  have hcont : ContinuousOn γ (Icc a b) := hc.mono hsub
  set S : Set ℝ := {x : ℝ | x ∈ Icc a b ∧ IsPiecewiseSmoothCurve (I := I) γ a x} with hS
  have haS : a ∈ S :=
    ⟨left_mem_Icc.2 hab,
      isPiecewiseSmoothCurve_self (hcont.mono (Icc_subset_Icc le_rfl hab))⟩
  have hne : S.Nonempty := ⟨a, haS⟩
  have hbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  set c : ℝ := sSup S with hc_def
  have hcmem : c ∈ Icc a b :=
    ⟨le_csSup hbdd haS, csSup_le hne fun x hx => hx.1.2⟩
  obtain ⟨δ, hδ, hback, hfwd⟩ :=
    IsGeodesicOn.exists_contMDiffOn_Icc (I := I) g hs hγ hc (hsub hcmem)
  -- the supremum is attained
  have hcS : c ∈ S := by
    refine ⟨hcmem, ?_⟩
    obtain ⟨x, hxS, hx⟩ :=
      exists_lt_of_lt_csSup hne (show c - δ < c by linarith)
    have hxc : x ≤ c := le_csSup hbdd hxS
    refine hxS.2.snoc hxc (hcont.mono (Icc_subset_Icc le_rfl hcmem.2)) ?_
    exact hback.mono (Icc_subset_Icc (by linarith) le_rfl)
  -- and it equals `b`
  have hcb : c = b := by
    rcases eq_or_lt_of_le hcmem.2 with heq | hlt
    · exact heq
    · exfalso
      have hcc' : c < min b (c + δ) := lt_min hlt (by linarith)
      have hc'b : min b (c + δ) ≤ b := min_le_left _ _
      have hmem : min b (c + δ) ∈ S :=
        ⟨⟨le_trans hcmem.1 hcc'.le, hc'b⟩,
          hcS.2.snoc hcc'.le (hcont.mono (Icc_subset_Icc le_rfl hc'b))
            (hfwd.mono (Icc_subset_Icc le_rfl (min_le_right _ _)))⟩
      exact absurd (le_csSup hbdd hmem) (not_le.2 hcc')
  exact hcb ▸ hcS.2

/-- **Math.** **A global geodesic is a Petersen piecewise `C^∞` curve** on every
interval `[a, b]`: the `s = univ` case of `IsGeodesicOn.isPiecewiseSmoothCurve`. -/
theorem IsGeodesic.isPiecewiseSmoothCurve (g : RiemannianMetric I M)
    {γ : ℝ → M} (hγ : IsGeodesic (I := I) g γ) (hcont : Continuous γ)
    {a b : ℝ} (hab : a ≤ b) :
    IsPiecewiseSmoothCurve (I := I) γ a b :=
  IsGeodesicOn.isPiecewiseSmoothCurve (I := I) g isOpen_univ
    (PetersenLib.Geodesic.IsGeodesic.isGeodesicOn hγ univ)
    hcont.continuousOn hab (subset_univ _)

end PetersenLib
