import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import DoCarmoLib.Riemannian.Exponential.LocalDiffeo
import DoCarmoLib.Riemannian.Exponential.C2Ball

set_option linter.unusedSectionVars false

/-!
# The exponential map is a `C²` local diffeomorphism

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 2.9, upgraded to `C²`
regularity of the inverse: `exp_p` restricted to a small ball around
`0 ∈ T_pM` is a diffeomorphism onto an open subset of `M` whose local inverse
is `C²` on the chart image.

* `exists_c2_local_diffeomorphism_expMap` — there is `ε > 0` such that `exp_p`
  is injective on `B_ε(0)` with open image in `M`, the chart reading
  `f = φ_p ∘ exp_p` is `C²` on `B_ε(0)` with open image in `E`, and there is a
  local inverse `finv` with `finv ∘ f = id` on `B_ε(0)` which is `C²` on the
  open chart image `f(B_ε(0))`.

The `C¹` statement is `exists_c1_local_diffeomorphism_expMap`
(`LocalDiffeo.lean`), whose inverse-regularity came from the inverse function
theorem at the origin only. Here the inverse function theorem for `C²` maps
(`ContDiffAt.to_localInverse`) is applied at *every* point of the ball — the
chart reading is `C²` there (`exists_contDiffOn_two_extChartAt_expMap_ball`)
with invertible strict derivative
(`exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball`) — and the globally
defined inverse of the injective `f` agrees with each local inverse near the
corresponding image point (`HasStrictFDerivAt.localInverse_unique`), so it
inherits `C²` regularity on the whole open image.

This is the regularity of `exp_p⁻¹` consumed by do Carmo's §4 (convex
neighborhoods): the second time-derivative of
`F(t) = |exp_p⁻¹(γ(t))|²` along a geodesic `γ` involves the first and second
derivatives of `exp_p⁻¹`.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian
namespace Exponential

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **`exp_p` is a `C²` diffeomorphism of a ball around `0 ∈ T_pM` onto
an open subset of `M`** (do Carmo Ch. 3, Prop. 2.9, at `C²` regularity of the
map *and its inverse*). There is `ε > 0` such that:

* the ball `B_ε(0) ⊂ T_pM` lies in the exponential domain and its image under
  `exp_p` stays in the chart at `p`;
* `exp_p` is injective on `B_ε(0)` and its image is open in `M`;
* the chart reading `f : w ↦ φ_p(exp_p(w))` is `C²` on `B_ε(0)` and its image
  `f(B_ε(0))` is open in `E`;
* there is a local inverse `finv` with `finv(f(w)) = w` on `B_ε(0)`, which is
  `C²` on the open chart image `f(B_ε(0))`.

The inverse function theorem for `C²` maps applied at every point of the ball,
where the chart reading is `C²`
(`exists_contDiffOn_two_extChartAt_expMap_ball`) with derivative a continuous
linear equivalence
(`exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball`); the globally
defined inverse of the injective chart reading agrees with each local inverse
near the corresponding image point, hence is `C²` there. -/
theorem exists_c2_local_diffeomorphism_expMap
    (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ε →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ε) ∧
      IsOpen ((fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
        ball (0 : E) ε) ∧
      ContDiffOn ℝ 2
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (ball (0 : E) ε) ∧
      IsOpen ((fun w : E => extChartAt I p
        (expMap (I := I) g p (w : TangentSpace I p))) '' ball (0 : E) ε) ∧
      ∃ finv : E → E,
        (∀ w : E, ‖w‖ < ε →
          finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) ∧
        ContDiffOn ℝ 2 finv
          ((fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
            '' ball (0 : E) ε) := by
  classical
  obtain ⟨ρ₁, hρ₁, hdom₁, hsrc₁, hinv⟩ :=
    exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball (I := I) g p
  obtain ⟨ρ₂, hρ₂, hinj, hdom₂⟩ := exists_injOn_expMap (I := I) g p
  obtain ⟨ρ₃, hρ₃, hdom₃, hsrc₃, hcd⟩ :=
    exists_contDiffOn_two_extChartAt_expMap_ball (I := I) g p
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  set ε : ℝ := min (min ρ₁ ρ₂) ρ₃ with hεdef
  have hε : 0 < ε := lt_min (lt_min hρ₁ hρ₂) hρ₃
  have hε₁ : ε ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₂ : ε ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hε₃ : ε ≤ ρ₃ := min_le_right _ _
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  -- injectivity of `exp_p`, hence of the chart reading, on the ball
  have hinjε : Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
      (ball (0 : E) ε) := hinj.mono (ball_subset_ball hε₂)
  have hfinj : Set.InjOn f (ball (0 : E) ε) := by
    intro a ha b hb hab
    refine hinjε ha hb ?_
    have hsrca : expMap (I := I) g p (a : TangentSpace I p) ∈
        (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hsrc₁ a ((mem_ball_zero_iff.mp ha).trans_le hε₁)
    have hsrcb : expMap (I := I) g p (b : TangentSpace I p) ∈
        (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hsrc₁ b ((mem_ball_zero_iff.mp hb).trans_le hε₁)
    exact (extChartAt I p).injOn hsrca hsrcb hab
  -- the chart reading is an open map on the ball
  have hopen_f : IsOpen (f '' ball (0 : E) ε) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨D', hD'⟩ := hinv w ((mem_ball_zero_iff.mp hw).trans_le hε₁)
    rw [← hD'.map_nhds_eq_of_equiv]
    exact image_mem_map (isOpen_ball.mem_nhds hw)
  -- the image of `exp_p` is the chart pull-back of the (open) image of `f`
  have himg : (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
        ball (0 : E) ε
      = (extChartAt I p).source ∩ extChartAt I p ⁻¹' (f '' ball (0 : E) ε) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hsrcw : expMap (I := I) g p (w : TangentSpace I p) ∈
          (chartAt H p).source :=
        hsrc₁ w ((mem_ball_zero_iff.mp hw).trans_le hε₁)
      exact ⟨by rw [extChartAt_source]; exact hsrcw, ⟨w, hw, rfl⟩⟩
    · rintro ⟨hxsrc, ⟨w, hw, hfw⟩⟩
      refine ⟨w, hw, ?_⟩
      have hsrcw : expMap (I := I) g p (w : TangentSpace I p) ∈
          (extChartAt I p).source := by
        rw [extChartAt_source]
        exact hsrc₁ w ((mem_ball_zero_iff.mp hw).trans_le hε₁)
      exact (extChartAt I p).injOn hsrcw hxsrc hfw
  have hopen_exp : IsOpen ((fun w : E => expMap (I := I) g p
      (w : TangentSpace I p)) '' ball (0 : E) ε) := by
    rw [himg]
    exact (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_source p) hopen_f
  -- the globally defined inverse of the injective chart reading
  set finv : E → E := fun z =>
    if hz : z ∈ f '' ball (0 : E) ε then hz.choose else 0 with hfinvdef
  have hfinvspec : ∀ z (hz : z ∈ f '' ball (0 : E) ε),
      finv z ∈ ball (0 : E) ε ∧ f (finv z) = z := by
    intro z hz
    rw [hfinvdef]
    simp only [dif_pos hz]
    exact ⟨hz.choose_spec.1, hz.choose_spec.2⟩
  have hfinvleft : ∀ w ∈ ball (0 : E) ε, finv (f w) = w := by
    intro w hw
    have hz : f w ∈ f '' ball (0 : E) ε := mem_image_of_mem f hw
    obtain ⟨hball, heq⟩ := hfinvspec (f w) hz
    exact hfinj hball hw heq
  -- the inverse is `C²` at every point of the open image
  have hfinvC2 : ∀ z ∈ f '' ball (0 : E) ε, ContDiffAt ℝ 2 finv z := by
    rintro z ⟨v₀, hv₀, rfl⟩
    have hC2at : ContDiffAt ℝ 2 f v₀ :=
      (hcd.mono (ball_subset_ball hε₃)).contDiffAt (isOpen_ball.mem_nhds hv₀)
    obtain ⟨D', hD'⟩ := hinv v₀ ((mem_ball_zero_iff.mp hv₀).trans_le hε₁)
    have hf' : HasFDerivAt f (D' : E →L[ℝ] E) v₀ := hD'.hasFDerivAt
    have hlocC2 : ContDiffAt ℝ 2 (hC2at.localInverse hf' hn2) (f v₀) :=
      hC2at.to_localInverse hf' hn2
    have hg : ∀ᶠ w in 𝓝 v₀, finv (f w) = w := by
      filter_upwards [isOpen_ball.mem_nhds hv₀] with w hw
      exact hfinvleft w hw
    have hev : ∀ᶠ y in 𝓝 (f v₀), finv y = hC2at.localInverse hf' hn2 y :=
      (hC2at.hasStrictFDerivAt' hf' hn2).localInverse_unique hg
    exact hlocC2.congr_of_eventuallyEq hev
  refine ⟨ε, hε, fun w hw => hdom₁ w (hw.trans_le hε₁),
    fun w hw => hsrc₁ w (hw.trans_le hε₁), hinjε, hopen_exp,
    hcd.mono (ball_subset_ball hε₃), hopen_f, finv,
    fun w hw => hfinvleft w (mem_ball_zero_iff.mpr hw), ?_⟩
  exact fun z hz => (hfinvC2 z hz).contDiffWithinAt

end Exponential
end Riemannian
