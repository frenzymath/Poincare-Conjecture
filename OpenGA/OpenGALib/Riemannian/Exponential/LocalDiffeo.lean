import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import OpenGALib.Riemannian.Exponential.StrictDerivative
import OpenGALib.Riemannian.Exponential.StrictDerivativeBall

set_option linter.unusedSectionVars false

/-!
# The exponential map is a `C¹` local diffeomorphism

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 2.9: `exp_p` restricted to a
small ball around `0 ∈ T_pM` is a diffeomorphism onto an open subset of `M`. This
file closes the statement at the `C¹` regularity level:

* `exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball` — **the derivative of
  `exp_p` is invertible at every point of a ball around the origin**: the chart
  reading `w ↦ φ_p(exp_p(w))` has, at every `v₀` with `‖v₀‖ < ρ`, a strict Fréchet
  derivative realized by a continuous linear *equivalence*. Since `d(exp_p)_0 = id`
  (`exists_hasStrictFDerivAt_extChartAt_expMap`) and the derivative map is
  continuous on the ball (strict differentiability everywhere,
  `exists_hasStrictFDerivAt_extChartAt_expMap_ball`, self-improves to continuity of
  `fderiv`), near `0` the derivative stays in the open set of invertible operators:
  it is the Neumann-series unit `1 - t` with `t = 1 - d(exp_p)_{v₀}`, `‖t‖ < 1`.
* `exists_c1_local_diffeomorphism_expMap` — **`exp_p` is a `C¹` diffeomorphism of a
  ball around `0` onto an open subset of `M`** (do Carmo Ch. 3, Prop. 2.9, at `C¹`):
  there is `ε > 0` such that `exp_p` is injective on `B_ε(0)`, its image is open in
  `M`, the chart reading is `C¹` on `B_ε(0)`, and there is a local inverse which is
  `C¹` on the (open) chart image — the inverse function theorem
  (`ContDiffAt.localInverse`/`to_localInverse`) applied at the origin, where the
  derivative is the identity.

Together with `exists_injOn_expMap` and `map_expMap_nhds` this completes do Carmo's
Proposition 2.9 with "diffeomorphism" read as "`C¹` diffeomorphism"; the upgrade to
`C^k`, `k ≥ 2`, awaits `C^k` dependence of the geodesic flow on its initial
condition (differentiating the variational equation).
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

/-- **Math.** **The derivative of `exp_p` is invertible at every point of a ball
around the origin** (do Carmo Ch. 3, Prop. 2.9, invertibility clause). There is
`ρ > 0` such that every `w` with `‖w‖ < ρ` lies in the exponential domain,
`exp_p(w)` stays in the chart at `p`, and at every `v₀` with `‖v₀‖ < ρ` the chart
reading `w ↦ φ_p(exp_p(w))` has a strict Fréchet derivative realized by a
continuous linear equivalence.

`d(exp_p)_0 = id`, and the derivative map is continuous on the ball (pointwise
strict differentiability self-improves to continuity of `fderiv`); near `0` the
derivative is therefore the perturbation `1 - t` of the identity with `‖t‖ < 1`,
a unit by the Neumann series. -/
theorem exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v₀ : E, ‖v₀‖ < ρ →
        ∃ D' : E ≃L[ℝ] E,
          HasStrictFDerivAt
            (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
            (D' : E →L[ℝ] E) v₀) := by
  classical
  obtain ⟨ρ₀, hρ₀, hdom, hsrc, hstrict⟩ :=
    exists_hasStrictFDerivAt_extChartAt_expMap_ball (I := I) g p
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  -- every point of the ball carries `fderiv f` as a strict derivative
  have hstrict' : ∀ v₀ ∈ ball (0 : E) ρ₀,
      HasStrictFDerivAt f (fderiv ℝ f v₀) v₀ := by
    intro v₀ hv₀
    obtain ⟨D', hD'⟩ := hstrict v₀ (mem_ball_zero_iff.mp hv₀)
    rwa [hD'.hasFDerivAt.fderiv]
  -- the derivative map is continuous on the ball and equals the identity at `0`
  have hcont : ContinuousOn (fderiv ℝ f) (ball (0 : E) ρ₀) :=
    continuousOn_of_forall_hasStrictFDerivAt isOpen_ball hstrict'
  have hzero : fderiv ℝ f 0 = (1 : E →L[ℝ] E) := by
    obtain ⟨ρ₁, hρ₁, -, -, h0⟩ :=
      exists_hasStrictFDerivAt_extChartAt_expMap (I := I) g p
    rw [ContinuousLinearMap.one_def]
    exact h0.hasFDerivAt.fderiv
  have hat : ContinuousAt (fderiv ℝ f) 0 :=
    hcont.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hρ₀))
  -- near the origin the derivative is within distance `1` of the identity
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hat 1 one_pos
  refine ⟨min ρ₀ δ, lt_min hρ₀ hδ,
    fun w hw => hdom w (hw.trans_le (min_le_left _ _)),
    fun w hw => hsrc w (hw.trans_le (min_le_left _ _)), ?_⟩
  intro v₀ hv₀
  have hv₀ρ : ‖v₀‖ < ρ₀ := hv₀.trans_le (min_le_left _ _)
  have hv₀δ : dist v₀ (0 : E) < δ := by
    rw [dist_zero_right]; exact hv₀.trans_le (min_le_right _ _)
  have hnear : ‖(1 : E →L[ℝ] E) - fderiv ℝ f v₀‖ < 1 := by
    have h := hball hv₀δ
    rw [dist_eq_norm, hzero] at h
    rwa [norm_sub_rev]
  -- the derivative is the unit `1 - t` with `t = 1 - d(exp_p)_{v₀}`, `‖t‖ < 1`
  set u : (E →L[ℝ] E)ˣ :=
    Units.oneSub ((1 : E →L[ℝ] E) - fderiv ℝ f v₀) hnear with hudef
  have huval : (u : E →L[ℝ] E) = fderiv ℝ f v₀ := sub_sub_cancel _ _
  refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ E u, ?_⟩
  have hcoe : ((ContinuousLinearEquiv.unitsEquiv ℝ E u : E ≃L[ℝ] E) : E →L[ℝ] E)
      = fderiv ℝ f v₀ := by
    refine ContinuousLinearMap.ext fun x => ?_
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquiv_apply, huval]
  rw [hcoe]
  exact hstrict' v₀ (mem_ball_zero_iff.mpr hv₀ρ)

set_option maxHeartbeats 800000 in
/-- **Math.** **`exp_p` is a `C¹` diffeomorphism of a ball around `0 ∈ T_pM` onto an
open subset of `M`** (do Carmo Ch. 3, Prop. 2.9, at `C¹` regularity). There is
`ε > 0` such that:

* the ball `B_ε(0) ⊂ T_pM` lies in the exponential domain and its image under
  `exp_p` stays in the chart at `p`;
* `exp_p` is injective on `B_ε(0)`;
* the image `exp_p(B_ε(0))` is open in `M`;
* the chart reading `w ↦ φ_p(exp_p(w))` is `C¹` on `B_ε(0)`;
* there is a local inverse `finv` with `finv(φ_p(exp_p(w))) = w` on `B_ε(0)`,
  which is `C¹` on the chart image `φ_p(exp_p(B_ε(0)))`.

The inverse function theorem for `C¹` maps applied at the origin, where
`d(exp_p)_0 = id`; openness of the image uses the invertibility of the derivative
at *every* point of the ball
(`exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball`). -/
theorem exists_c1_local_diffeomorphism_expMap
    (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ε →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ε) ∧
      IsOpen ((fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
        ball (0 : E) ε) ∧
      ContDiffOn ℝ 1
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (ball (0 : E) ε) ∧
      ∃ finv : E → E,
        (∀ w : E, ‖w‖ < ε →
          finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) ∧
        ContDiffOn ℝ 1 finv
          ((fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
            '' ball (0 : E) ε) := by
  classical
  obtain ⟨ρ₁, hρ₁, hdom₁, hsrc₁, hinv⟩ :=
    exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball (I := I) g p
  obtain ⟨ρ₂, hρ₂, hinj, hdom₂⟩ := exists_injOn_expMap (I := I) g p
  obtain ⟨ρ₃, hρ₃, hdom₃, hsrc₃, hcd⟩ :=
    exists_contDiffOn_extChartAt_expMap_ball (I := I) g p
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  -- the `C¹` inverse function theorem at the origin, where the derivative is `id`
  have hC1at : ContDiffAt ℝ 1 f 0 :=
    hcd.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hρ₃))
  obtain ⟨ρ₄, hρ₄, -, -, hstrict0⟩ :=
    exists_hasStrictFDerivAt_extChartAt_expMap (I := I) g p
  have hf'0 : HasFDerivAt f
      (((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E)) : E →L[ℝ] E) 0 := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hstrict0.hasFDerivAt
  have hleft : ∀ᶠ w in 𝓝 (0 : E),
      ContDiffAt.localInverse hC1at hf'0 one_ne_zero (f w) = w :=
    HasStrictFDerivAt.eventually_left_inverse
      (hC1at.hasStrictFDerivAt' hf'0 one_ne_zero)
  have hinvC1 : ContDiffAt ℝ 1
      (ContDiffAt.localInverse hC1at hf'0 one_ne_zero) (f 0) :=
    ContDiffAt.to_localInverse hC1at hf'0 one_ne_zero
  -- an open neighbourhood of `f 0` on which the local inverse is `C¹`
  obtain ⟨V, hVopen, hV0, hVcd⟩ :
      ∃ V, IsOpen V ∧ f 0 ∈ V ∧
        ContDiffOn ℝ 1 (ContDiffAt.localInverse hC1at hf'0 one_ne_zero) V := by
    obtain ⟨v, hvo, hxv, hcd'⟩ := hinvC1.contDiffOn' le_rfl (by simp)
    exact ⟨v, hvo, hxv, by simpa using hcd'⟩
  -- choose the radius
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.eventually_nhds_iff_ball.mp hleft
  have hfV : f ⁻¹' V ∈ 𝓝 (0 : E) :=
    hC1at.continuousAt.preimage_mem_nhds (hVopen.mem_nhds hV0)
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.mem_nhds_iff.mp hfV
  set ε : ℝ := min (min ρ₁ ρ₂) (min ρ₃ (min δ₁ δ₂)) with hεdef
  have hε : 0 < ε := lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ (lt_min hδ₁ hδ₂))
  have hε₁ : ε ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₂ : ε ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hε₃ : ε ≤ ρ₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hεδ₁ : ε ≤ δ₁ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hεδ₂ : ε ≤ δ₂ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  -- the chart reading is an open map on the ball: invertible derivative everywhere
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
  refine ⟨ε, hε, fun w hw => hdom₁ w (hw.trans_le hε₁),
    fun w hw => hsrc₁ w (hw.trans_le hε₁),
    hinj.mono (ball_subset_ball hε₂), hopen_exp,
    hcd.mono (ball_subset_ball hε₃),
    ContDiffAt.localInverse hC1at hf'0 one_ne_zero, ?_, ?_⟩
  · intro w hw
    exact hδ₁sub w (mem_ball_zero_iff.mpr (hw.trans_le hεδ₁))
  · refine hVcd.mono ?_
    rintro y ⟨w, hw, rfl⟩
    exact hδ₂sub (ball_subset_ball hεδ₂ hw)

end Exponential
end Riemannian
