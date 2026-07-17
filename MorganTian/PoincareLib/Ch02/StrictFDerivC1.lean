import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Strict differentiability on an open set gives `C¹`

A classical fact of differential calculus missing from mathlib: if `f` has a
**strict** Fréchet derivative at every point of an open set, then the
derivative assignment is continuous there, so `f` is `C¹` on the set.

The pointwise statement is sharper: continuity of the derivative map at `a`
needs strictness only **at** `a`, plus plain differentiability (with the given
derivative) at nearby points. The proof is the textbook estimate: the strict
little-o at `a` controls difference quotients *uniformly* for base points `b`
near `a`, and the plain derivative at `b` identifies those quotients with
`f' b`, giving `‖f' b - f' a‖ ≤ ε`.

Main declarations:

* `HasStrictFDerivAt.continuousAt_derivMap` — strictness at `a` + plain
  differentiability near `a` makes the derivative map continuous at `a`.
* `contDiffOn_one_of_hasStrictFDerivAt` — a map with a strict derivative at
  every point of an open set is `C¹` there.

These feed the `C¹` regularity of the gradient flow (`FlowIsometryLocal`,
`FlowC1`): the variational-equation machinery of `FlowVariation` produces
strict derivatives of the local flow at every point of the flow ball, and this
file upgrades that to genuine `C¹` dependence on the initial condition.
-/

open Set Filter Metric
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace PoincareLib

/-- **Math.** **Strict differentiability at a point makes the derivative map
continuous there**: if `f` has the strict Fréchet derivative `f' a` at `a` and
plain Fréchet derivative `f' b` at every `b` near `a`, then `f'` is continuous
at `a`. The strict little-o at `a` bounds the difference quotients of `f`
uniformly over base points near `a`; the pointwise derivative identifies those
quotients with `f' b`. -/
theorem _root_.HasStrictFDerivAt.continuousAt_derivMap
    {f : E → F} {f' : E → E →L[𝕜] F} {a : E}
    (ha : HasStrictFDerivAt f (f' a) a)
    (hev : ∀ᶠ b in 𝓝 a, HasFDerivAt f (f' b) b) :
    ContinuousAt f' a := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have h4 : (0:ℝ) < ε / 4 := by linarith
  -- the strict estimate at `a`, on a product ball
  have hS : ∀ᶠ p : E × E in 𝓝 (a, a),
      ‖f p.1 - f p.2 - f' a (p.1 - p.2)‖ ≤ ε / 4 * ‖p.1 - p.2‖ :=
    ha.isLittleO.bound h4
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hS
  filter_upwards [hev, Metric.ball_mem_nhds a hδpos] with b hb hbδ
  rw [dist_eq_norm]
  refine lt_of_le_of_lt
    (ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun v => ?_)
    (by linarith : ε / 2 < ε)
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvnorm : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  -- the pointwise estimate at `b`, intersected with the strict ball
  have hT : ∀ᶠ x in 𝓝 b,
      ‖f x - f b - f' b (x - b)‖ ≤ ε / 4 * ‖x - b‖ ∧ x ∈ ball a δ :=
    (hb.isLittleO.bound h4).and (isOpen_ball.mem_nhds hbδ)
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.eventually_nhds_iff_ball.mp hT
  -- a scalar displacement small enough to stay in both balls
  obtain ⟨t, htpos, htlt⟩ :=
    NormedField.exists_norm_lt 𝕜 (div_pos hρpos hvnorm)
  set x : E := b + t • v with hx_def
  have hxb : x - b = t • v := by simp [hx_def]
  have hxball : x ∈ ball b ρ := by
    rw [mem_ball, dist_eq_norm, hxb, norm_smul]
    calc ‖t‖ * ‖v‖ < ρ / ‖v‖ * ‖v‖ := by
          exact mul_lt_mul_of_pos_right htlt hvnorm
      _ = ρ := div_mul_cancel₀ ρ hvnorm.ne'
  obtain ⟨hxest, hxδ⟩ := hρ x hxball
  -- the strict estimate at the pair `(x, b)`
  have hpair : (x, b) ∈ ball ((a : E), (a : E)) δ := by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (mem_ball.mp hxδ) (mem_ball.mp hbδ)
  have hstrict := hδ (x, b) hpair
  simp only at hstrict
  -- combine the two estimates and cancel the scalar
  have hcomb : ‖f' b (t • v) - f' a (t • v)‖ ≤ ε / 2 * ‖t • v‖ := by
    have h1 : f' b (t • v) - f' a (t • v)
        = (f x - f b - f' a (x - b)) - (f x - f b - f' b (x - b)) := by
      rw [hxb]; abel
    rw [h1]
    calc ‖(f x - f b - f' a (x - b)) - (f x - f b - f' b (x - b))‖
        ≤ ‖f x - f b - f' a (x - b)‖ + ‖f x - f b - f' b (x - b)‖ :=
          norm_sub_le _ _
      _ ≤ ε / 4 * ‖x - b‖ + ε / 4 * ‖x - b‖ := add_le_add hstrict hxest
      _ = ε / 2 * ‖x - b‖ := by ring
      _ = ε / 2 * ‖t • v‖ := by rw [hxb]
  have hsmul : ‖t‖ * ‖(f' b - f' a) v‖ ≤ ‖t‖ * (ε / 2 * ‖v‖) := by
    calc ‖t‖ * ‖(f' b - f' a) v‖ = ‖t • ((f' b - f' a) v)‖ := (norm_smul t _).symm
      _ = ‖f' b (t • v) - f' a (t • v)‖ := by
          rw [ContinuousLinearMap.sub_apply, smul_sub, (f' b).map_smul,
            (f' a).map_smul]
      _ ≤ ε / 2 * ‖t • v‖ := hcomb
      _ = ‖t‖ * (ε / 2 * ‖v‖) := by rw [norm_smul]; ring
  exact le_of_mul_le_mul_left hsmul htpos

/-- **Math.** **Strict differentiability on an open set gives `C¹`**: a map
with a strict Fréchet derivative at every point of an open set `s` is `C¹` on
`s`. The derivative map is continuous by
`HasStrictFDerivAt.continuousAt_derivMap`. -/
theorem contDiffOn_one_of_hasStrictFDerivAt
    {f : E → F} {f' : E → E →L[𝕜] F} {s : Set E}
    (hs : IsOpen s) (hf : ∀ x ∈ s, HasStrictFDerivAt f (f' x) x) :
    ContDiffOn 𝕜 1 f s := by
  have hdiff : DifferentiableOn 𝕜 f s := fun x hx =>
    ((hf x hx).hasFDerivAt).differentiableAt.differentiableWithinAt
  have hfderiv : ∀ x ∈ s, fderiv 𝕜 f x = f' x := fun x hx =>
    ((hf x hx).hasFDerivAt).fderiv
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm,
    contDiffOn_succ_iff_fderiv_of_isOpen hs]
  refine ⟨hdiff, by simp, ?_⟩
  rw [contDiffOn_zero]
  have hcont : ContinuousOn f' s := by
    intro x hx
    refine ((hf x hx).continuousAt_derivMap ?_).continuousWithinAt
    filter_upwards [hs.mem_nhds hx] with b hb
    exact (hf b hb).hasFDerivAt
  exact hcont.congr hfderiv

end PoincareLib
