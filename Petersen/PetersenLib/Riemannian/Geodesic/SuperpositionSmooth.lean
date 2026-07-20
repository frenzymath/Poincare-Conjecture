/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Geodesic/SuperpositionSmooth.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Geodesic.FlowDependence
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# `C^n` smoothness of the superposition (Nemytskii) operator

The **superposition** (Nemytskii) operator `N_f : C(K, E) → C(K, F)`, `α ↦ f ∘ α`, is the
operator that turns a nonlinear map `f : E → F` into a map between curve spaces. This file
proves the key analytic fact absent from mathlib:

> **`contDiff_superpositionGen`.** If `f : E → F` is `C^n`, then `N_f : C(K, E) → C(K, F)` is
> `C^n` (as a map of the *Banach spaces* of continuous curves).

This is the linchpin of the smooth dependence of an ODE flow on its initial condition. The flow
`x ↦ σ_x` of `x' = f(x)` is the solution of the Banach fixed-point equation
`picardResidual (x, α) = α - const x - ∫₀ᵗ f(α(s)) ds = 0`
(`FlowDependence.picardResidual`), and that residual is `C^n` in `(x, α)` precisely because the
integrand `α ↦ f ∘ α` is `C^n` — which is what is proved here. The `C^∞` implicit function
theorem then makes the flow `C^∞` in one stroke, with no jet tower.

## The argument

The derivative of the superposition operator is postcomposition by the superposition of the
derivative: along a base curve `α₀`,
`d(N_f)_{α₀} = postcompCurve (t ↦ f'(α₀ t)) = postcompCurve (N_{f'} α₀)`
(`FlowDependence.hasStrictFDerivAt_superposition`, here generalised to an arbitrary target `F`).
Reading this as an equality of *functions of `α`*,
`fderiv (N_f) = postcompCurveL ∘ N_{f'}`,
where `postcompCurveL : C(K, E →L[ℝ] F) →L[ℝ] (C(K,E) →L[ℝ] C(K,F))` is the bounded packaging
of `postcompCurve`. This is the induction: `N_f` is `C^{n+1}` iff its derivative is `C^n`, and
the derivative is `postcompCurveL ∘ N_{f'}`, which is `C^n` because `postcompCurveL` is a
continuous linear map and `N_{f'}` is `C^n` by the induction hypothesis (`f'` is `C^n` when `f`
is `C^{n+1}`). The target space changes at each level (`F ⟹ E →L[ℝ] F`), so the statement is
proved for **all** targets `F` simultaneously.

Reference: standard smooth-dependence theory for ODEs; do Carmo, *Riemannian Geometry*, Ch. 7,
where global `C^∞` smoothness of `exp_p` is the one remaining input to `thm:dc-ch7-3-1`.
-/

open Filter Set
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib.FlowDependence

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

section GeneralTarget

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
/-- **Math.** The general-target superposition (Nemytskii) operator `α ↦ f ∘ α`, from `C(K, E)`
to `C(K, F)`, extended by the junk value `0` when `f ∘ α` fails to be continuous (which never
happens for continuous `f`). Generalises `FlowDependence.superposition` (endomorphism target) to
an arbitrary codomain `F`, needed because the derivative of `N_f` is the superposition of
`f' : E → E →L[ℝ] F`. -/
def superpositionGen (f : E → F) : C(K, E) → C(K, F) := fun α =>
  if h : Continuous (f ∘ α) then ⟨f ∘ α, h⟩ else 0

lemma superpositionGen_apply_of_continuousOn {f : E → F} {s : Set E}
    (hf : ContinuousOn f s) (α : C(K, E)) (hα : ∀ t, α t ∈ s) (t : K) :
    superpositionGen f α t = f (α t) := by
  have h : Continuous (f ∘ α) := hf.comp_continuous α.continuous hα
  simp only [superpositionGen]
  rw [dif_pos h]
  rfl

lemma superpositionGen_apply {f : E → F} (hf : Continuous f) (α : C(K, E)) (t : K) :
    superpositionGen f α t = f (α t) :=
  superpositionGen_apply_of_continuousOn hf.continuousOn α (fun _ => Set.mem_univ _) t

/-- On endomorphisms, the general-target superposition operator *is* `FlowDependence.superposition`. -/
lemma superpositionGen_eq_superposition (f : E → E) :
    superpositionGen (K := K) f = superposition f := rfl

/-! ### Continuity of the superposition operator (the `C^0` base case) -/

/-- **Math.** The superposition operator of a continuous map is continuous. On the sup metric of
the curve space this is Heine's theorem along the compact range of the base curve: `f` is
uniformly continuous on a neighbourhood of the (compact) range of `α₀`, so uniformly close
curves have uniformly close images. -/
theorem continuous_superpositionGen {f : E → F} (hf : Continuous f) :
    Continuous (superpositionGen (K := K) f) := by
  rw [Metric.continuous_iff]
  intro α₀ ε hε
  have hcomp : IsCompact (Set.range α₀) := isCompact_range α₀.continuous
  obtain ⟨δ, hδ, H⟩ :=
    hcomp.exists_forall_dist_image_lt_of_continuousAt (fun x _ => hf.continuousAt) hε
  refine ⟨δ, hδ, fun α hα => ?_⟩
  rw [ContinuousMap.dist_lt_iff hε]
  intro t
  rw [superpositionGen_apply hf, superpositionGen_apply hf, dist_comm]
  refine H (α₀ t) (Set.mem_range_self t) (α t) ?_
  calc dist (α₀ t) (α t) ≤ dist α₀ α := ContinuousMap.dist_apply_le_dist t
    _ = dist α α₀ := dist_comm _ _
    _ < δ := hα

/-! ### The derivative of the superposition operator (general target) -/

/-- **Math.** Strict differentiability of the superposition operator at an arbitrary base curve,
general target. Verbatim generalisation of `FlowDependence.hasStrictFDerivAt_superposition` from
an endomorphism `f : E → E` to a map `f : E → F` with an arbitrary target `F`; the mean-value
proof never uses that the target is `E`. The derivative is postcomposition by the operator curve
`t ↦ f' (α₀ t)`. -/
theorem hasStrictFDerivAt_superpositionGen
    {f : E → F} {f' : E → E →L[ℝ] F} {u : Set E} (hu : IsOpen u)
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    {α₀ : C(K, E)} (hmem : ∀ t, α₀ t ∈ u)
    (hc : ∀ t, ContinuousAt f' (α₀ t))
    {A₀ : C(K, E →L[ℝ] F)} (hA₀ : ∀ t, A₀ t = f' (α₀ t)) :
    HasStrictFDerivAt (superpositionGen f) (postcompCurve A₀) α₀ := by
  have hcont : ContinuousOn f u := fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hrange : IsCompact (Set.range α₀) := isCompact_range α₀.continuous
  have hrangeu : Set.range α₀ ⊆ u := Set.range_subset_iff.mpr hmem
  obtain ⟨δ₁, hδ₁, hthick⟩ := hrange.exists_thickening_subset_open hu hrangeu
  refine .of_isLittleO (Asymptotics.isLittleO_iff.mpr fun ε hε => ?_)
  have hcrange : ∀ x ∈ Set.range α₀, ContinuousAt f' x := by
    rintro x ⟨t, rfl⟩; exact hc t
  obtain ⟨δ₂, hδ₂, hunif⟩ :=
    hrange.exists_forall_dist_image_lt_of_continuousAt hcrange (half_pos hε)
  have hδpos : (0:ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hball : ∀ t, Metric.ball (α₀ t) (min δ₁ δ₂) ⊆ u := fun t y hy =>
    hthick (Metric.mem_thickening_iff.mpr ⟨α₀ t, Set.mem_range_self t,
      (Metric.mem_ball.mp hy).trans_le (min_le_left _ _)⟩)
  have key : ∀ t : K, ∀ a ∈ Metric.ball (α₀ t) (min δ₁ δ₂),
      ∀ b ∈ Metric.ball (α₀ t) (min δ₁ δ₂),
      ‖f a - f b - f' (α₀ t) (a - b)‖ ≤ ε * ‖a - b‖ := by
    intro t a ha b hb
    have hg : ∀ y ∈ Metric.ball (α₀ t) (min δ₁ δ₂),
        HasFDerivWithinAt (fun z => f z - f' (α₀ t) z) (f' y - f' (α₀ t))
          (Metric.ball (α₀ t) (min δ₁ δ₂)) y := fun y hy =>
      ((hd y (hball t hy)).sub (f' (α₀ t)).hasFDerivAt).hasFDerivWithinAt
    have hbound : ∀ y ∈ Metric.ball (α₀ t) (min δ₁ δ₂), ‖f' y - f' (α₀ t)‖ ≤ ε :=
      fun y hy => by
        have h1 : dist (α₀ t) y < δ₂ := by
          rw [dist_comm]
          exact (Metric.mem_ball.mp hy).trans_le (min_le_right _ _)
        have h2 := hunif (α₀ t) (Set.mem_range_self t) y h1
        rw [dist_eq_norm] at h2
        calc ‖f' y - f' (α₀ t)‖ = ‖f' (α₀ t) - f' y‖ := norm_sub_rev _ _
          _ ≤ ε := by linarith
    have hmvt := (convex_ball (α₀ t) (min δ₁ δ₂)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hg hbound hb ha
    calc ‖f a - f b - f' (α₀ t) (a - b)‖
        = ‖(f a - f' (α₀ t) a) - (f b - f' (α₀ t) b)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ε * ‖a - b‖ := hmvt
  filter_upwards [prod_mem_nhds
    (Metric.ball_mem_nhds α₀ hδpos) (Metric.ball_mem_nhds α₀ hδpos)]
  rintro ⟨α, β⟩ ⟨hα, hβ⟩
  have hval : ∀ {γ : C(K, E)}, γ ∈ Metric.ball α₀ (min δ₁ δ₂) →
      ∀ t, γ t ∈ Metric.ball (α₀ t) (min δ₁ δ₂) := by
    intro γ hγ t
    rw [Metric.mem_ball, dist_eq_norm] at hγ ⊢
    calc ‖γ t - α₀ t‖ = ‖(γ - α₀) t‖ := by rw [ContinuousMap.sub_apply]
      _ ≤ ‖γ - α₀‖ := ContinuousMap.norm_coe_le_norm _ t
      _ < min δ₁ δ₂ := hγ
  have hαval : ∀ t, α t ∈ u := fun t => hball t (hval hα t)
  have hβval : ∀ t, β t ∈ u := fun t => hball t (hval hβ t)
  refine (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr fun t => ?_
  have hpt : (superpositionGen f α - superpositionGen f β - postcompCurve A₀ (α - β)) t
      = f (α t) - f (β t) - f' (α₀ t) (α t - β t) := by
    rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, postcompCurve_apply,
      ContinuousMap.sub_apply, hA₀,
      superpositionGen_apply_of_continuousOn hcont α hαval,
      superpositionGen_apply_of_continuousOn hcont β hβval]
  rw [hpt]
  have h2 : ‖α t - β t‖ ≤ ‖α - β‖ := by
    have h3 := ContinuousMap.norm_coe_le_norm (α - β) t
    rwa [ContinuousMap.sub_apply] at h3
  exact (key t _ (hval hα t) _ (hval hβ t)).trans (mul_le_mul_of_nonneg_left h2 hε.le)

end GeneralTarget

/-! ### `postcompCurve` as a continuous linear map -/

section PostcompL

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The underlying linear map of `postcompCurveL`. -/
def postcompCurveLM : C(K, E →L[ℝ] F) →ₗ[ℝ] (C(K, E) →L[ℝ] C(K, F)) where
  toFun A := postcompCurve A
  map_add' A B := by
    ext β t
    simp only [postcompCurve_apply, ContinuousLinearMap.add_apply, ContinuousMap.add_apply]
  map_smul' c A := by
    ext β t
    simp only [postcompCurve_apply, ContinuousLinearMap.smul_apply, ContinuousMap.smul_apply,
      RingHom.id_apply]

@[simp] lemma postcompCurveLM_apply (A : C(K, E →L[ℝ] F)) :
    postcompCurveLM A = postcompCurve A := rfl

/-- **Math.** `postcompCurve` packaged as a **continuous linear map**
`C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F))`. It is linear in the operator curve and bounded
by its sup norm (`norm_postcompCurve_le`). This is what makes `fderiv (N_f) = postcompCurveL ∘ N_{f'}`
a composition with a `C^∞` map, driving the smoothness induction. -/
def postcompCurveL : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  postcompCurveLM.mkContinuous 1
    (fun (A : C(K, E →L[ℝ] F)) => by rw [one_mul]; exact norm_postcompCurve_le A)

@[simp] lemma postcompCurveL_apply (A : C(K, E →L[ℝ] F)) :
    postcompCurveL A = postcompCurve A := by
  simp only [postcompCurveL, LinearMap.mkContinuous_apply, postcompCurveLM_apply]

end PostcompL

/-! ### The main theorem: the superposition operator is `C^n` -/

/-- **Math.** **The superposition (Nemytskii) operator of a `C^n` map is `C^n`.** If `f : E → F`
is `n`-times continuously differentiable, then `N_f : C(K, E) → C(K, F)`, `α ↦ f ∘ α`, is `C^n`
as a map of Banach spaces. Proved by induction on `n`, over **all** target spaces `F`
simultaneously (the derivative superposition has target `E →L[ℝ] F`):

* base `n = 0`: `N_f` is continuous when `f` is (`continuous_superpositionGen`);
* step: `fderiv (N_f) = postcompCurveL ∘ N_{fderiv f}`, which is `C^n` because `postcompCurveL`
  is a continuous linear map and `N_{fderiv f}` is `C^n` by the induction hypothesis
  (`fderiv f` is `C^n` since `f` is `C^{n+1}`); hence `N_f` is `C^{n+1}` by
  `contDiff_succ_iff_fderiv`. -/
theorem contDiff_superpositionGen_nat (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F},
      ContDiff ℝ (n : WithTop ℕ∞) f → ContDiff ℝ (n : WithTop ℕ∞) (superpositionGen (K := K) f) := by
  induction n with
  | zero =>
    intro F _ _ f hf
    rw [Nat.cast_zero, contDiff_zero] at hf ⊢
    exact continuous_superpositionGen hf
  | succ k ih =>
    intro F _ _ f hf
    rw [Nat.cast_succ] at hf ⊢
    -- `f` is `C^{k+1}`, so `fderiv f` is `C^k` and continuous
    obtain ⟨hf_diff, -, hf_fderiv⟩ := contDiff_succ_iff_fderiv.mp hf
    have hf_cont_fderiv : Continuous (fderiv ℝ f) :=
      hf.continuous_fderiv (by exact_mod_cast Nat.succ_ne_zero k)
    -- the derivative of `N_f` at `α`: postcomposition by the operator curve `t ↦ f'(α t)`
    have hHas : ∀ α : C(K, E),
        HasStrictFDerivAt (superpositionGen f)
          (postcompCurve (superpositionGen (fderiv ℝ f) α)) α := by
      intro α
      refine hasStrictFDerivAt_superpositionGen (f' := fderiv ℝ f) (u := Set.univ) isOpen_univ
        (fun x _ => hf_diff.differentiableAt.hasFDerivAt) (fun _ => Set.mem_univ _)
        (fun _ => hf_cont_fderiv.continuousAt) ?_
      intro t
      exact superpositionGen_apply hf_cont_fderiv α t
    -- `fderiv (N_f) = postcompCurveL ∘ N_{fderiv f}`
    have hfderiv_eq : fderiv ℝ (superpositionGen f)
        = fun (α : C(K, E)) => postcompCurveL (superpositionGen (fderiv ℝ f) α) := by
      funext α
      rw [(hHas α).hasFDerivAt.fderiv, postcompCurveL_apply]
    rw [contDiff_succ_iff_fderiv]
    refine ⟨fun α => (hHas α).hasFDerivAt.differentiableAt, fun h => absurd h (by simp), ?_⟩
    rw [hfderiv_eq]
    exact ContDiff.continuousLinearMap_comp postcompCurveL (ih hf_fderiv)

/-- **Math.** **`C^∞` form.** The superposition operator of a `C^∞` map is `C^∞`. -/
theorem contDiff_superpositionGen_infty {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (superpositionGen (K := K) f) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_superpositionGen_nat n (contDiff_infty.mp hf n)

/-- **Math.** **Endomorphism `C^∞` corollary**, the form consumed by the flow-smoothness
argument: the superposition operator `FlowDependence.superposition f` of a `C^∞` endomorphism
`f : E → E` is `C^∞`. This makes the Picard residual `picardResidual f` a `C^∞` map, feeding the
`C^∞` implicit function theorem. -/
theorem contDiff_superposition_infty {f : E → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (superposition (K := K) f) := by
  rw [← superpositionGen_eq_superposition]
  exact contDiff_superpositionGen_infty hf

end PetersenLib.FlowDependence

end
