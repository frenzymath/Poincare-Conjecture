/- Vendored from DoCarmo `OpenGALib/Riemannian/Geodesic/FlowDependence.lean`. Namespace `Riemannian` mapped to
   `PetersenLib`; engineering infrastructure only, not a blueprint node. -/
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecificLimits.Normed

set_option linter.unusedSectionVars false

/-! # C¹ dependence of ODE solutions on the initial condition

For an autonomous ODE `x' = f(x)` on a real Banach space `E`, a solution on `[0, T]` with
initial value `x` is exactly a fixed point of the Picard integral operator, i.e. a zero of the
**Picard residual**

`G(x, α) = α - const x - ∫₀ᵗ f(α(s)) ds`

viewed as a map `E × C([0,T], E) → C([0,T], E)` on the Banach space of continuous curves.
Let `α₀` be a base solution with initial value `x₀`, staying in an open set on which `f` is
differentiable with derivative `f'` continuous along `α₀`. The residual `G` is *strictly*
differentiable at `(x₀, α₀)`: the only nonlinearity is the superposition (Nemytskii) operator
`α ↦ f ∘ α`, whose strict derivative at `α₀` is postcomposition with the operator curve
`A₀ = (t ↦ f' (α₀ t))` — a mean-value-inequality argument, made uniform in `t` by compactness
of the range of `α₀` (Heine). If moreover `T · ‖A₀‖ < 1`, the partial derivative of
`G` in the curve variable is a perturbation `1 - J ∘ M` of the identity by an operator of norm
`< 1`, hence invertible by the Neumann series. The Banach-space implicit function theorem
(`Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain`) then yields: any solution family
`σ : E → C([0,T], E)` with `σ x₀ = α₀`, continuous at `x₀` and satisfying the integral
equation near `x₀`, is *strictly differentiable* at `x₀`, with derivative characterized by the
linearized (variational) integral equation `D v - ∫₀ᵗ A₀ (D v) = const v`.

The special case `α₀ = const x₀` at an equilibrium (`f x₀ = 0`) is stated separately
(`hasStrictFDerivAt_of_picardResidual`); there the derivative equation is solvable in closed
form when `f' x₀` is nilpotent, which is what the geodesic application at the center of a
normal neighborhood uses. The general (non-equilibrium) form is the C¹-dependence engine for
differentiating the geodesic flow — hence the exponential map — away from the zero section.

This is the "C¹ dependence on initial conditions" infrastructure of
do Carmo, *PetersenLib Geometry*, Ch. 3, §2.2/2.5/2.7 (smooth dependence on initial
conditions), in the form needed to differentiate the geodesic flow in its initial condition at
the center of a normal neighborhood: a downstream file applies the main theorem to the geodesic
spray (whose linearization at a zero-velocity equilibrium is two-step nilpotent) to obtain
`d(exp_p)_0 = id` as a *strict* derivative.

Main declarations:

* `PetersenLib.FlowDependence.intervalPrimitive` — the Volterra primitive
  `β ↦ (t ↦ ∫₀ᵗ β)` as a continuous linear operator of norm `≤ T`;
* `PetersenLib.FlowDependence.postcomp` — postcomposition `α ↦ A ∘ α` by a continuous linear
  map, with `‖postcomp A‖ ≤ ‖A‖`; `postcompCurve` — postcomposition by a continuous *family*
  `A : C(K, E →L[ℝ] F)` of linear maps, with `‖postcompCurve A‖ ≤ ‖A‖`;
* `PetersenLib.FlowDependence.superposition` — the Nemytskii operator `α ↦ f ∘ α`, and
  `hasStrictFDerivAt_superposition`, its strict differentiability at an arbitrary base curve
  (with the constant-curve special case `hasStrictFDerivAt_superposition_const`);
* `PetersenLib.FlowDependence.picardResidual` — the residual of the Picard integral equation,
  `picardResidual_eq_zero_of_hasDerivWithinAt` (solutions of the ODE are zeros) and
  `picardResidual_const_eq_zero` (the equilibrium constant curve is a zero);
* `PetersenLib.FlowDependence.hasStrictFDerivAt_of_picardResidual_curve` — the main theorem:
  strict differentiability of a solution family in its initial condition along an arbitrary
  base solution, with the existence form `exists_hasStrictFDerivAt_of_picardResidual_curve`
  (the derivative produced by the Neumann series), the evaluation corollary
  `hasStrictFDerivAt_eval_of_picardResidual_curve`, and the equilibrium special case
  `hasStrictFDerivAt_of_picardResidual` / `hasStrictFDerivAt_eval_of_picardResidual`;
* `PetersenLib.FlowDependence.linearRamp` and `sub_intervalPrimitive_postcomp_ramp` — the
  explicit solution `D = const + ramp ∘ A` of the derivative equation when `A ∘L A = 0`,
  discharging the characterization hypothesis in the nilpotent (geodesic) application.
-/

noncomputable section

open Filter MeasureTheory Asymptotics
open scoped Topology

namespace PetersenLib.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ}

/-! ## Postcomposition and superposition operators on curve spaces -/

section CompactDomain

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Math.** Postcomposition with a continuous linear map `A : E →L[ℝ] F`, as a continuous
linear operator `C(K, E) →L[ℝ] C(K, F)` on curve spaces, `(postcomp A) β = A ∘ β`. -/
def postcomp (A : E →L[ℝ] F) : C(K, E) →L[ℝ] C(K, F) :=
  A.compLeftContinuous ℝ K

@[simp] lemma postcomp_apply (A : E →L[ℝ] F) (β : C(K, E)) (t : K) :
    postcomp A β t = A (β t) := rfl

/-- **Math.** Postcomposition is bounded in operator norm by the norm of the composing map:
`‖postcomp A‖ ≤ ‖A‖` (in sup norm, `‖A ∘ β‖ ≤ ‖A‖ ‖β‖`). -/
lemma norm_postcomp_le (A : E →L[ℝ] F) :
    ‖(postcomp A : C(K, E) →L[ℝ] C(K, F))‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun β =>
    (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg β))).mpr fun t =>
      (A.le_opNorm (β t)).trans
        (mul_le_mul_of_nonneg_left (β.norm_coe_le_norm t) (norm_nonneg A))

/-- **Math.** Postcomposition with a continuous *family* of continuous linear maps
`A : C(K, E →L[ℝ] F)`, as a continuous linear operator on curve spaces:
`(postcompCurve A) β = (t ↦ A t (β t))`. For a constant family this is `postcomp`. It is the
shape of the derivative of the superposition operator at a non-constant base curve. -/
def postcompCurve (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun β => ⟨fun t => A t (β t), A.continuous.clm_apply β.continuous⟩
      map_add' := fun β γ => by ext t; simp
      map_smul' := fun c β => by ext t; simp }
    ‖A‖
    (fun β => (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg β))).mpr
      fun t => ((A t).le_opNorm (β t)).trans
        (mul_le_mul (A.norm_coe_le_norm t) (β.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] lemma postcompCurve_apply (A : C(K, E →L[ℝ] F)) (β : C(K, E)) (t : K) :
    postcompCurve A β t = A t (β t) := rfl

/-- **Math.** Postcomposition by an operator family is bounded in operator norm by the sup
norm of the family: `‖postcompCurve A‖ ≤ ‖A‖` (in sup norms, `‖t ↦ A t (β t)‖ ≤ ‖A‖ ‖β‖`). -/
lemma norm_postcompCurve_le (A : C(K, E →L[ℝ] F)) :
    ‖(postcompCurve A : C(K, E) →L[ℝ] C(K, F))‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-- **Math.** Postcomposition by the constant operator family is postcomposition by its
value: `postcompCurve (const A) = postcomp A`. -/
lemma postcompCurve_const (A : E →L[ℝ] F) :
    postcompCurve (ContinuousMap.const K A) = (postcomp A : C(K, E) →L[ℝ] C(K, F)) := by
  refine ContinuousLinearMap.ext fun β => ?_
  ext t
  rfl

open Classical in
/-- **Math.** The superposition (Nemytskii) operator `α ↦ f ∘ α` on the curve space `C(K, E)`,
extended by the junk value `0` when the composition fails to be continuous (which never happens
on the curves of interest, whose values stay in the continuity set of `f`). -/
def superposition (f : E → E) : C(K, E) → C(K, E) := fun α =>
  if h : Continuous (f ∘ α) then ⟨f ∘ α, h⟩ else 0

/-- **Math.** On a curve `α` whose values stay inside a set where `f` is continuous, the
superposition operator is honest composition: `superposition f α t = f (α t)`. -/
lemma superposition_apply_of_continuousOn {f : E → E} {s : Set E}
    (hf : ContinuousOn f s) (α : C(K, E)) (hα : ∀ t, α t ∈ s) (t : K) :
    superposition f α t = f (α t) := by
  have h : Continuous (f ∘ α) := hf.comp_continuous α.continuous hα
  simp only [superposition]
  rw [dif_pos h]
  rfl

/-- **Math.** Superposition sends the constant curve at `x` to the constant curve at `f x`. -/
lemma superposition_const (f : E → E) (x : E) :
    superposition f (ContinuousMap.const K x) = ContinuousMap.const K (f x) := by
  have h : Continuous (f ∘ ⇑(ContinuousMap.const K x)) := by
    have h2 : f ∘ ⇑(ContinuousMap.const K x) = fun _ => f x := rfl
    rw [h2]; exact continuous_const
  ext t
  simp only [superposition]
  rw [dif_pos h]
  rfl

/-- **Math.** Metric form of `IsCompact.uniformContinuousAt_of_continuousAt`: a map continuous
at every point of a compact set `s` is "uniformly continuous at `s`" — for every `ε > 0` there
is `δ > 0` such that `g y` is `ε`-close to `g x` whenever `x ∈ s` and `y` is `δ`-close to `x`
(`y` need not lie in `s`). This is the Heine-type input making the mean value estimate below
uniform along a compact base curve. -/
lemma _root_.IsCompact.exists_forall_dist_image_lt_of_continuousAt
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {s : Set X} (hs : IsCompact s) {g : X → Y} (hg : ∀ x ∈ s, ContinuousAt g x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y, dist x y < δ → dist (g x) (g y) < ε := by
  rcases Metric.mem_uniformity_dist.mp
      (hs.uniformContinuousAt_of_continuousAt g hg (Metric.dist_mem_uniformity hε)) with
    ⟨δ, hδ, H⟩
  exact ⟨δ, hδ, fun x hx y hxy => H hxy hx⟩

/-- **Math.** Strict differentiability of the superposition operator at an arbitrary base
curve: if `f` is differentiable on an open set `u` containing the (compact) range of
`α₀ : C(K, E)`, with derivative `f'` continuous at every point of that range, then `α ↦ f ∘ α`
is strictly differentiable at `α₀`, with derivative postcomposition by the operator curve
`t ↦ f' (α₀ t)` (supplied as any continuous family `A₀` agreeing with it pointwise).

The proof is the mean value inequality along the base curve, made uniform in `t` by
compactness of the range: `f'` is uniformly continuous at the range (Heine), so for curves
`α, β` uniformly close to `α₀` the pointwise error `f (α t) - f (β t) - f' (α₀ t) (α t - β t)`
is `≤ ε ‖α t - β t‖` simultaneously for all `t`. This generalizes the constant-curve case
`hasStrictFDerivAt_superposition_const` from equilibria to arbitrary base solutions — the step
needed to differentiate a flow in its initial condition away from an equilibrium. -/
theorem hasStrictFDerivAt_superposition
    {f : E → E} {f' : E → E →L[ℝ] E} {u : Set E} (hu : IsOpen u)
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    {α₀ : C(K, E)} (hmem : ∀ t, α₀ t ∈ u)
    (hc : ∀ t, ContinuousAt f' (α₀ t))
    {A₀ : C(K, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = f' (α₀ t)) :
    HasStrictFDerivAt (superposition f) (postcompCurve A₀) α₀ := by
  have hcont : ContinuousOn f u := fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hrange : IsCompact (Set.range α₀) := isCompact_range α₀.continuous
  have hrangeu : Set.range α₀ ⊆ u := Set.range_subset_iff.mpr hmem
  obtain ⟨δ₁, hδ₁, hthick⟩ := hrange.exists_thickening_subset_open hu hrangeu
  refine .of_isLittleO (Asymptotics.isLittleO_iff.mpr fun ε hε => ?_)
  -- uniform continuity of `f'` at the compact range of the base curve
  have hcrange : ∀ x ∈ Set.range α₀, ContinuousAt f' x := by
    rintro x ⟨t, rfl⟩; exact hc t
  obtain ⟨δ₂, hδ₂, hunif⟩ :=
    hrange.exists_forall_dist_image_lt_of_continuousAt hcrange (half_pos hε)
  have hδpos : (0:ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  -- balls of radius `min δ₁ δ₂` around points of the base curve lie in `u`
  have hball : ∀ t, Metric.ball (α₀ t) (min δ₁ δ₂) ⊆ u := fun t y hy =>
    hthick (Metric.mem_thickening_iff.mpr ⟨α₀ t, Set.mem_range_self t,
      (Metric.mem_ball.mp hy).trans_le (min_le_left _ _)⟩)
  -- pointwise mean value estimate on the moving small ball
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
  -- the eventuality: pairs of curves uniformly close to the base curve
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
  have hpt : (superposition f α - superposition f β - postcompCurve A₀ (α - β)) t
      = f (α t) - f (β t) - f' (α₀ t) (α t - β t) := by
    simp [superposition_apply_of_continuousOn hcont α hαval,
      superposition_apply_of_continuousOn hcont β hβval, hA₀]
  rw [hpt]
  have h2 : ‖α t - β t‖ ≤ ‖α - β‖ := by
    have h3 := ContinuousMap.norm_coe_le_norm (α - β) t
    rwa [ContinuousMap.sub_apply] at h3
  exact (key t _ (hval hα t) _ (hval hβ t)).trans (mul_le_mul_of_nonneg_left h2 hε.le)

/-- **Math.** Strict differentiability of the superposition operator at a constant curve: if
`f` is differentiable on a ball around `x₀` with derivative `f'` continuous at `x₀`, then
`α ↦ f ∘ α` is strictly differentiable at `const x₀` with derivative `postcomp (f' x₀)`.
Special case of `hasStrictFDerivAt_superposition` at the constant base curve. -/
theorem hasStrictFDerivAt_superposition_const
    {f : E → E} {f' : E → E →L[ℝ] E} {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : ∀ x ∈ Metric.ball x₀ ρ, HasFDerivAt f (f' x) x)
    (hc : ContinuousAt f' x₀) :
    HasStrictFDerivAt (superposition f) (postcomp (f' x₀)) (ContinuousMap.const K x₀) := by
  rw [← postcompCurve_const (K := K) (f' x₀)]
  exact hasStrictFDerivAt_superposition Metric.isOpen_ball hd
    (fun _ => Metric.mem_ball_self hρ) (fun _ => hc) (fun _ => rfl)

end CompactDomain

/-! ## The Volterra primitive on `C([0,T], E)` -/

/-- **Math.** The Volterra primitive operator on the curve space `C([0,T], E)`:
`(intervalPrimitive hT β) t = ∫₀ᵗ β(s) ds`, a continuous linear operator of norm `≤ T`.
(The integrand is extended constantly outside `[0,T]` via `Set.projIcc`.) -/
def intervalPrimitive (hT : (0:ℝ) ≤ T) :
    C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
  LinearMap.mkContinuous
    { toFun := fun β =>
        ⟨fun t => ∫ s in (0:ℝ)..(t:ℝ), β (Set.projIcc 0 T hT s),
          (intervalIntegral.continuous_primitive
            (fun a b => (β.continuous.comp continuous_projIcc).intervalIntegrable a b) 0).comp
            continuous_subtype_val⟩
      map_add' := fun β γ => by
        ext t
        have hβ : IntervalIntegrable (fun s => β (Set.projIcc 0 T hT s))
            volume 0 (t : ℝ) := (β.continuous.comp continuous_projIcc).intervalIntegrable _ _
        have hγ : IntervalIntegrable (fun s => γ (Set.projIcc 0 T hT s))
            volume 0 (t : ℝ) := (γ.continuous.comp continuous_projIcc).intervalIntegrable _ _
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
        rw [intervalIntegral.integral_add hβ hγ]
      map_smul' := fun c β => by
        ext t
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, RingHom.id_apply]
        rw [intervalIntegral.integral_smul] }
    T
    (fun β => (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg β))).mpr fun t => by
      calc ‖∫ s in (0:ℝ)..(t:ℝ), β (Set.projIcc 0 T hT s)‖
          ≤ ‖β‖ * |(t:ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const
            fun s _ => β.norm_coe_le_norm _
        _ = (t:ℝ) * ‖β‖ := by rw [sub_zero, abs_of_nonneg t.2.1, mul_comm]
        _ ≤ T * ‖β‖ := mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg β))

@[simp] lemma intervalPrimitive_apply (hT : (0:ℝ) ≤ T) (β : C(Set.Icc (0:ℝ) T, E))
    (t : Set.Icc (0:ℝ) T) :
    intervalPrimitive hT β t = ∫ s in (0:ℝ)..(t:ℝ), β (Set.projIcc 0 T hT s) := rfl

/-- **Math.** The Volterra primitive over `[0,T]` has operator norm at most `T`. -/
lemma norm_intervalPrimitive_le (hT : (0:ℝ) ≤ T) :
    ‖(intervalPrimitive hT : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))‖ ≤ T :=
  LinearMap.mkContinuous_norm_le _ hT _

/-- **Math.** Composite bound `‖J ∘ M‖ ≤ T ‖A‖` for the Volterra primitive `J` following
postcomposition `M` with `A`; this is the contraction estimate making `1 - J ∘ M` invertible
when `T ‖A‖ < 1`. -/
lemma norm_intervalPrimitive_comp_postcomp_le (hT : (0:ℝ) ≤ T) (A : E →L[ℝ] E) :
    ‖(intervalPrimitive hT).comp (postcomp A)‖ ≤ T * ‖A‖ := by
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  exact mul_le_mul (norm_intervalPrimitive_le hT) (norm_postcomp_le A) (norm_nonneg _) hT

/-- **Math.** Composite bound `‖J ∘ M‖ ≤ T ‖A₀‖` for the Volterra primitive `J` following
postcomposition `M` with an operator curve `A₀`; this is the contraction estimate making
`1 - J ∘ M` invertible when `T ‖A₀‖ < 1`, along an arbitrary base solution. -/
lemma norm_intervalPrimitive_comp_postcompCurve_le (hT : (0:ℝ) ≤ T)
    (A : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)) :
    ‖(intervalPrimitive hT).comp (postcompCurve A)‖ ≤ T * ‖A‖ := by
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  exact mul_le_mul (norm_intervalPrimitive_le hT) (norm_postcompCurve_le A) (norm_nonneg _) hT

/-! ## The Picard residual -/

/-- **Math.** The residual of the Picard integral equation for the autonomous ODE `x' = f(x)`:
`picardResidual hT f (x, α) = α - const x - ∫₀ᵗ f(α(s)) ds`. A curve `α` solves the ODE on
`[0, T]` with initial value `x` iff the residual vanishes. -/
def picardResidual (hT : (0:ℝ) ≤ T) (f : E → E) :
    E × C(Set.Icc (0:ℝ) T, E) → C(Set.Icc (0:ℝ) T, E) := fun q =>
  q.2 - ContinuousMap.const _ q.1 - intervalPrimitive hT (superposition f q.2)

@[simp] lemma picardResidual_apply (hT : (0:ℝ) ≤ T) (f : E → E) (x : E)
    (α : C(Set.Icc (0:ℝ) T, E)) :
    picardResidual hT f (x, α)
      = α - ContinuousMap.const _ x - intervalPrimitive hT (superposition f α) := rfl

/-- **Math.** Solutions of the ODE `x' = f(x)` satisfy the Picard integral equation: if
`α : ℝ → E` has `α 0 = x`, stays in a set `u` where `f` is continuous, and has derivative
`f (α t)` within `[0,T]` at every `t ∈ [0,T]`, then any continuous curve `σ` agreeing with `α`
on `[0,T]` is a zero of the Picard residual. This is the bridge feeding Picard–Lindelöf flow
solutions into the implicit-function machinery. -/
theorem picardResidual_eq_zero_of_hasDerivWithinAt
    (hT : 0 < T) {f : E → E} {u : Set E} (hf : ContinuousOn f u)
    {x : E} {α : ℝ → E}
    (hα0 : α 0 = x)
    (hmem : ∀ t ∈ Set.Icc (0:ℝ) T, α t ∈ u)
    (hd : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt α (f (α t)) (Set.Icc (0:ℝ) T) t)
    (σ : C(Set.Icc (0:ℝ) T, E)) (hσ : ∀ t : Set.Icc (0:ℝ) T, σ t = α t) :
    picardResidual hT.le f (x, σ) = 0 := by
  have hσmem : ∀ t : Set.Icc (0:ℝ) T, σ t ∈ u := fun t => by
    rw [hσ t]; exact hmem t t.2
  have hNσ : ∀ t' : Set.Icc (0:ℝ) T, superposition f σ t' = f (σ t') :=
    superposition_apply_of_continuousOn hf σ hσmem
  have hαcont : ContinuousOn α (Set.Icc 0 T) := fun s hs => (hd s hs).continuousWithinAt
  ext t
  have key : (∫ s in (0:ℝ)..(t:ℝ), superposition f σ (Set.projIcc 0 T hT.le s))
      = α t - x := by
    have h1 : (∫ s in (0:ℝ)..(t:ℝ), superposition f σ (Set.projIcc 0 T hT.le s))
        = ∫ s in (0:ℝ)..(t:ℝ), f (α s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le t.2.1] at hs
      have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1, hs.2.trans t.2.2⟩
      rw [hNσ, Set.projIcc_of_mem hT.le hsT, hσ]
    rw [h1, intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.2.1
      (hαcont.mono (Set.Icc_subset_Icc le_rfl t.2.2)) ?_ ?_, hα0]
    · intro s hs
      have hsT : s < T := hs.2.trans_le t.2.2
      exact (hd s ⟨hs.1.le, hsT.le⟩).mono_of_mem_nhdsWithin
        (Set.ordConnected_Icc.mem_nhdsGT ⟨hs.1.le, hsT.le⟩
          (Set.right_mem_Icc.mpr hT.le) hsT)
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le t.2.1]
      exact hf.comp (hαcont.mono (Set.Icc_subset_Icc le_rfl t.2.2))
        fun s hs => hmem s ⟨hs.1, hs.2.trans t.2.2⟩
  simp only [picardResidual_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ContinuousMap.zero_apply, intervalPrimitive_apply, key, hσ t]
  abel

/-- **Math.** At an equilibrium `f x₀ = 0`, the constant curve at `x₀` is a zero of the Picard
residual (the integrand vanishes identically). -/
theorem picardResidual_const_eq_zero (hT : 0 < T) {f : E → E} {x₀ : E} (heq : f x₀ = 0) :
    picardResidual hT.le f (x₀, ContinuousMap.const _ x₀) = 0 := by
  ext t
  simp [picardResidual_apply, superposition_const, heq]

/-! ## The linear ramp and the primitive of a constant -/

/-- **Math.** The linear ramp embedding `v ↦ (t ↦ t • v)` of `E` into `C([0,T], E)`, a
continuous linear map of norm `≤ T`. It is the Volterra primitive of the constant curve. -/
def linearRamp (hT : (0:ℝ) ≤ T) : E →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun t => (t : ℝ) • v, continuous_subtype_val.smul continuous_const⟩
      map_add' := fun v w => by
        ext t
        simp [smul_add]
      map_smul' := fun c v => by
        ext t
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
    T
    (fun v => (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg v))).mpr fun t => by
      calc ‖(t:ℝ) • v‖ = (t:ℝ) * ‖v‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
        _ ≤ T * ‖v‖ := mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg v))

@[simp] lemma linearRamp_apply (hT : (0:ℝ) ≤ T) (v : E) (t : Set.Icc (0:ℝ) T) :
    linearRamp hT v t = (t : ℝ) • v := rfl

/-- **Math.** The Volterra primitive of the constant curve at `v` is the linear ramp `t • v`. -/
lemma intervalPrimitive_const (hT : (0:ℝ) ≤ T) (v : E) :
    intervalPrimitive hT (ContinuousMap.const (Set.Icc (0:ℝ) T) v) = linearRamp hT v := by
  ext t
  simp only [intervalPrimitive_apply, linearRamp_apply, ContinuousMap.const_apply,
    intervalIntegral.integral_const, sub_zero]

/-- **Math.** Explicit solution of the derivative equation in the nilpotent case: if
`A ∘L A = 0` then the curve `const v + ramp (A v)` solves the linear Picard equation
`β - ∫₀ᵗ A (β(s)) ds = const v`. Downstream this discharges the derivative characterization
for the geodesic spray, whose linearization at zero velocity is two-step nilpotent, giving
`D = const + ramp ∘ A`. -/
theorem sub_intervalPrimitive_postcomp_ramp (hT : (0:ℝ) ≤ T) {A : E →L[ℝ] E}
    (hA : A.comp A = 0) (v : E) :
    (ContinuousMap.const (Set.Icc (0:ℝ) T) v + linearRamp hT (A v))
        - intervalPrimitive hT
            (postcomp A (ContinuousMap.const (Set.Icc (0:ℝ) T) v + linearRamp hT (A v)))
      = ContinuousMap.const (Set.Icc (0:ℝ) T) v := by
  have hAA : ∀ y : E, A (A y) = 0 := fun y => by
    have h := congrArg (fun B : E →L[ℝ] E => B y) hA
    simpa using h
  have hpost : postcomp A (ContinuousMap.const (Set.Icc (0:ℝ) T) v + linearRamp hT (A v))
      = ContinuousMap.const (Set.Icc (0:ℝ) T) (A v) := by
    ext t
    simp [map_add, hAA]
  rw [hpost, intervalPrimitive_const, add_sub_cancel_right]

/-! ## Main theorem: strict differentiability in the initial condition -/

/-- **Math.** **Strict differentiability of a solution family in its initial condition, along
an arbitrary base solution** (do Carmo, PetersenLib Geometry, Ch. 3, §2.2/2.5/2.7 — C¹
dependence of ODE solutions on initial conditions, non-equilibrium case). Let `α₀` be a base
solution curve with initial value `x₀`, staying in an open set `u` on which `f` is
differentiable, with derivative `f'` continuous at every point of the curve, and let
`A₀ = (t ↦ f' (α₀ t))` be the operator curve along it. Suppose `T ‖A₀‖ < 1`. If
`σ : E → C([0,T], E)` is a family of curves with `σ x₀ = α₀`, continuous at `x₀`, satisfying
the Picard integral equation `picardResidual (x, σ x) = 0` for all `x` near `x₀`, and if `D`
solves the linearized (variational) integral equation `D v - ∫₀ᵗ A₀(s) ((D v)(s)) ds = const v`,
then `σ` is strictly differentiable at `x₀` with derivative `D`. The proof applies the Banach
implicit function theorem to the Picard residual, whose curve-partial derivative `1 - J ∘ M`
along the base solution is invertible by the Neumann series. -/
theorem hasStrictFDerivAt_of_picardResidual_curve
    (hT : 0 < T) {f : E → E} {f' : E → E →L[ℝ] E} {u : Set E} (hu : IsOpen u)
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    {x₀ : E} {α₀ : C(Set.Icc (0:ℝ) T, E)} (hmem : ∀ t, α₀ t ∈ u)
    (hc : ∀ t, ContinuousAt f' (α₀ t))
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = f' (α₀ t))
    (hTL : T * ‖A₀‖ < 1)
    {σ : E → C(Set.Icc (0:ℝ) T, E)}
    (hσ0 : σ x₀ = α₀)
    (hσc : ContinuousAt σ x₀)
    (hσ : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le f (x, σ x) = 0)
    {D : E →L[ℝ] C(Set.Icc (0:ℝ) T, E)}
    (hD : ∀ v : E, D v - intervalPrimitive hT.le (postcompCurve A₀ (D v))
          = ContinuousMap.const _ v) :
    HasStrictFDerivAt σ D x₀ := by
  set JP : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    (intervalPrimitive hT.le).comp (postcompCurve A₀) with hJP_def
  have hJPnorm : ‖JP‖ < 1 :=
    (norm_intervalPrimitive_comp_postcompCurve_le hT.le A₀).trans_lt hTL
  -- `1 - JP` is invertible by the Neumann series
  set w : (C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))ˣ :=
    Units.oneSub JP hJPnorm with hw_def
  have hval : ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP).comp
      (↑w⁻¹ : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))
      = ContinuousLinearMap.id ℝ _ := w.mul_inv
  have hinv : (↑w⁻¹ : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)).comp
      ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP)
      = ContinuousLinearMap.id ℝ _ := w.inv_mul
  have hinvertible :
      ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hval hinv
  -- the Picard residual and its strict derivative at the base point
  set pt : E × C(Set.Icc (0:ℝ) T, E) := (x₀, α₀) with hpt_def
  set constE : E →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T) with hconstE_def
  set G' : E × C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E))
      - constE.comp (ContinuousLinearMap.fst ℝ E (C(Set.Icc (0:ℝ) T, E)))
      - JP.comp (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E))) with hG'_def
  have hN : HasStrictFDerivAt (superposition f) (postcompCurve A₀) α₀ :=
    hasStrictFDerivAt_superposition hu hd hmem hc hA₀
  have hG : HasStrictFDerivAt (picardResidual hT.le f) G' pt := by
    have h1 : HasStrictFDerivAt (fun q : E × C(Set.Icc (0:ℝ) T, E) => q.2)
        (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E))) pt := hasStrictFDerivAt_snd
    have h2 : HasStrictFDerivAt
        (fun q : E × C(Set.Icc (0:ℝ) T, E) => (ContinuousMap.const (Set.Icc (0:ℝ) T) q.1))
        (constE.comp (ContinuousLinearMap.fst ℝ E (C(Set.Icc (0:ℝ) T, E)))) pt :=
      constE.hasStrictFDerivAt.comp pt hasStrictFDerivAt_fst
    have h3b : HasStrictFDerivAt
        (fun q : E × C(Set.Icc (0:ℝ) T, E) => superposition f q.2)
        ((postcompCurve A₀).comp (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E)))) pt :=
      hN.comp pt hasStrictFDerivAt_snd
    have h3 : HasStrictFDerivAt
        (fun q : E × C(Set.Icc (0:ℝ) T, E) => intervalPrimitive hT.le (superposition f q.2))
        (JP.comp (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E)))) pt :=
      (intervalPrimitive hT.le).hasStrictFDerivAt.comp pt h3b
    exact (h1.sub h2).sub h3
  -- the curve-partial derivative is `1 - JP`, the initial-condition-partial is `-constE`
  have hGinr : G' ∘L ContinuousLinearMap.inr ℝ E (C(Set.Icc (0:ℝ) T, E))
      = (1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP := by
    refine ContinuousLinearMap.ext fun β => ?_
    simp [hG'_def]
  have hGinl : G' ∘L ContinuousLinearMap.inl ℝ E (C(Set.Icc (0:ℝ) T, E)) = -constE := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp [hG'_def]
  have if₂u : (G' ∘L ContinuousLinearMap.inr ℝ E (C(Set.Icc (0:ℝ) T, E))).IsInvertible := by
    rw [hGinr]; exact hinvertible
  -- the residual vanishes at the base point (the base curve is itself a solution)
  have hG0 : picardResidual hT.le f pt = 0 := by
    have h := hσ.self_of_nhds
    rwa [hσ0] at h
  -- the implicit function agrees with `σ` near `x₀`
  have hptF : Tendsto (fun x : E => (x, σ x)) (𝓝 x₀) (𝓝 pt) := by
    have h : Tendsto (fun x : E => (x, σ x)) (𝓝 x₀) (𝓝 (x₀, σ x₀)) :=
      continuousAt_id.prodMk hσc
    rwa [hσ0] at h
  have hev : ∀ᶠ x in 𝓝 x₀, hG.implicitFunctionOfProdDomain if₂u x = σ x := by
    filter_upwards [hptF.eventually
      (hG.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u), hσ] with x hx hx0
    exact hx.mp (by rw [hx0, hG0])
  have hψ := hG.hasStrictFDerivAt_implicitFunctionOfProdDomain if₂u
  -- identify the implicit-function derivative with `D`
  have huD : ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP).comp D
      = constE := by
    refine ContinuousLinearMap.ext fun v => ?_
    simpa [hJP_def, hconstE_def] using hD v
  have hDid : -(G' ∘L ContinuousLinearMap.inr ℝ E (C(Set.Icc (0:ℝ) T, E))).inverse
      ∘L (G' ∘L ContinuousLinearMap.inl ℝ E (C(Set.Icc (0:ℝ) T, E))) = D := by
    rw [hGinr, hGinl, ContinuousLinearMap.comp_neg, neg_neg, ← huD,
      ← ContinuousLinearMap.comp_assoc, hinvertible.inverse_comp_self,
      ContinuousLinearMap.id_comp]
  rw [← hDid]
  exact hψ.congr_of_eventuallyEq hev

/-- **Math.** Existence form of `hasStrictFDerivAt_of_picardResidual_curve`: along an arbitrary
base solution with `T ‖A₀‖ < 1`, the derivative of the solution family in its initial
condition *exists* — it is the Neumann-series inverse `(1 - J ∘ M)⁻¹` applied to the constant
embedding — and it satisfies the linearized (variational) integral equation, which determines
it uniquely. Callers who cannot solve the variational equation in closed form use this form. -/
theorem exists_hasStrictFDerivAt_of_picardResidual_curve
    (hT : 0 < T) {f : E → E} {f' : E → E →L[ℝ] E} {u : Set E} (hu : IsOpen u)
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    {x₀ : E} {α₀ : C(Set.Icc (0:ℝ) T, E)} (hmem : ∀ t, α₀ t ∈ u)
    (hc : ∀ t, ContinuousAt f' (α₀ t))
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = f' (α₀ t))
    (hTL : T * ‖A₀‖ < 1)
    {σ : E → C(Set.Icc (0:ℝ) T, E)}
    (hσ0 : σ x₀ = α₀)
    (hσc : ContinuousAt σ x₀)
    (hσ : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le f (x, σ x) = 0) :
    ∃ D : E →L[ℝ] C(Set.Icc (0:ℝ) T, E),
      (∀ v : E, D v - intervalPrimitive hT.le (postcompCurve A₀ (D v))
        = ContinuousMap.const _ v)
      ∧ HasStrictFDerivAt σ D x₀ := by
  set JP : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    (intervalPrimitive hT.le).comp (postcompCurve A₀) with hJP_def
  have hJPnorm : ‖JP‖ < 1 :=
    (norm_intervalPrimitive_comp_postcompCurve_le hT.le A₀).trans_lt hTL
  set w : (C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))ˣ :=
    Units.oneSub JP hJPnorm with hw_def
  have hval : ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP).comp
      (↑w⁻¹ : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))
      = ContinuousLinearMap.id ℝ _ := w.mul_inv
  set constE : E →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T) with hconstE_def
  refine ⟨(↑w⁻¹ : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)).comp constE,
    fun v => ?_, ?_⟩
  · have h := congrArg
      (fun B : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) => B (constE v)) hval
    simpa [ContinuousLinearMap.sub_apply, sub_eq_iff_eq_add, hconstE_def] using h
  · exact hasStrictFDerivAt_of_picardResidual_curve hT hu hd hmem hc hA₀ hTL hσ0 hσc hσ
      fun v => by
        have h := congrArg
          (fun B : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) => B (constE v)) hval
        simpa [ContinuousLinearMap.sub_apply, sub_eq_iff_eq_add, hconstE_def] using h

/-- **Math.** Evaluation form of `hasStrictFDerivAt_of_picardResidual_curve`: for each fixed
time `t ∈ [0,T]`, the map `x ↦ σ x t` is strictly differentiable at `x₀` with derivative
`v ↦ D v t`. Applied at the endpoint `t = T`, this is C¹ dependence of the time-`T` flow map
on its initial condition, along an arbitrary base solution. -/
theorem hasStrictFDerivAt_eval_of_picardResidual_curve
    (hT : 0 < T) {f : E → E} {f' : E → E →L[ℝ] E} {u : Set E} (hu : IsOpen u)
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    {x₀ : E} {α₀ : C(Set.Icc (0:ℝ) T, E)} (hmem : ∀ t, α₀ t ∈ u)
    (hc : ∀ t, ContinuousAt f' (α₀ t))
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = f' (α₀ t))
    (hTL : T * ‖A₀‖ < 1)
    {σ : E → C(Set.Icc (0:ℝ) T, E)}
    (hσ0 : σ x₀ = α₀)
    (hσc : ContinuousAt σ x₀)
    (hσ : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le f (x, σ x) = 0)
    {D : E →L[ℝ] C(Set.Icc (0:ℝ) T, E)}
    (hD : ∀ v : E, D v - intervalPrimitive hT.le (postcompCurve A₀ (D v))
          = ContinuousMap.const _ v)
    (t : Set.Icc (0:ℝ) T) :
    HasStrictFDerivAt (fun x => σ x t) ((ContinuousMap.evalCLM ℝ t).comp D) x₀ :=
  (ContinuousMap.evalCLM ℝ t).hasStrictFDerivAt.comp x₀
    (hasStrictFDerivAt_of_picardResidual_curve hT hu hd hmem hc hA₀ hTL hσ0 hσc hσ hD)

/-- **Math.** **Strict differentiability of a solution family in its initial condition, at an
equilibrium** (do Carmo, PetersenLib Geometry, Ch. 3, §2.2/2.5/2.7, C¹ dependence on initial
conditions). Let `f` be differentiable on a ball around an equilibrium `x₀` (`f x₀ = 0`) with
derivative continuous at `x₀`, and suppose `T ‖f' x₀‖ < 1`. If `σ : E → C([0,T], E)` is a
family of curves with `σ x₀ = const x₀`, continuous at `x₀`, satisfying the Picard integral
equation `picardResidual (x, σ x) = 0` for all `x` near `x₀`, and if `D` solves the linear
integral equation `D v - ∫₀ᵗ f' x₀ (D v) = const v`, then `σ` is strictly differentiable at
`x₀` with derivative `D`. The proof applies the Banach implicit function theorem to the Picard
residual, whose curve-partial derivative `1 - J ∘ M` at the equilibrium point is invertible by
the Neumann series. -/
theorem hasStrictFDerivAt_of_picardResidual
    (hT : 0 < T) {f : E → E} {f' : E → E →L[ℝ] E} {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (heq : f x₀ = 0)
    (hd : ∀ x ∈ Metric.ball x₀ ρ, HasFDerivAt f (f' x) x)
    (hc : ContinuousAt f' x₀)
    (hTL : T * ‖f' x₀‖ < 1)
    {σ : E → C(Set.Icc (0:ℝ) T, E)}
    (hσ0 : σ x₀ = ContinuousMap.const _ x₀)
    (hσc : ContinuousAt σ x₀)
    (hσ : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le f (x, σ x) = 0)
    {D : E →L[ℝ] C(Set.Icc (0:ℝ) T, E)}
    (hD : ∀ v : E, D v - intervalPrimitive hT.le (postcomp (f' x₀) (D v))
          = ContinuousMap.const _ v) :
    HasStrictFDerivAt σ D x₀ := by
  set JP : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    (intervalPrimitive hT.le).comp (postcomp (f' x₀)) with hJP_def
  have hJPnorm : ‖JP‖ < 1 :=
    (norm_intervalPrimitive_comp_postcomp_le hT.le (f' x₀)).trans_lt hTL
  -- `1 - JP` is invertible by the Neumann series
  set w : (C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))ˣ :=
    Units.oneSub JP hJPnorm with hw_def
  have hval : ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP).comp
      (↑w⁻¹ : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))
      = ContinuousLinearMap.id ℝ _ := w.mul_inv
  have hinv : (↑w⁻¹ : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)).comp
      ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP)
      = ContinuousLinearMap.id ℝ _ := w.inv_mul
  have hu : ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hval hinv
  -- the Picard residual and its strict derivative at the equilibrium point
  set pt : E × C(Set.Icc (0:ℝ) T, E) := (x₀, ContinuousMap.const _ x₀) with hpt_def
  set constE : E →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T) with hconstE_def
  set G' : E × C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E))
      - constE.comp (ContinuousLinearMap.fst ℝ E (C(Set.Icc (0:ℝ) T, E)))
      - JP.comp (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E))) with hG'_def
  have hN : HasStrictFDerivAt (superposition f) (postcomp (f' x₀))
      (ContinuousMap.const (Set.Icc (0:ℝ) T) x₀) :=
    hasStrictFDerivAt_superposition_const hρ hd hc
  have hG : HasStrictFDerivAt (picardResidual hT.le f) G' pt := by
    have h1 : HasStrictFDerivAt (fun q : E × C(Set.Icc (0:ℝ) T, E) => q.2)
        (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E))) pt := hasStrictFDerivAt_snd
    have h2 : HasStrictFDerivAt
        (fun q : E × C(Set.Icc (0:ℝ) T, E) => (ContinuousMap.const (Set.Icc (0:ℝ) T) q.1))
        (constE.comp (ContinuousLinearMap.fst ℝ E (C(Set.Icc (0:ℝ) T, E)))) pt :=
      constE.hasStrictFDerivAt.comp pt hasStrictFDerivAt_fst
    have h3b : HasStrictFDerivAt
        (fun q : E × C(Set.Icc (0:ℝ) T, E) => superposition f q.2)
        ((postcomp (f' x₀)).comp (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E)))) pt :=
      hN.comp pt hasStrictFDerivAt_snd
    have h3 : HasStrictFDerivAt
        (fun q : E × C(Set.Icc (0:ℝ) T, E) => intervalPrimitive hT.le (superposition f q.2))
        (JP.comp (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E)))) pt :=
      (intervalPrimitive hT.le).hasStrictFDerivAt.comp pt h3b
    exact (h1.sub h2).sub h3
  -- the curve-partial derivative is `1 - JP`, the initial-condition-partial is `-constE`
  have hGinr : G' ∘L ContinuousLinearMap.inr ℝ E (C(Set.Icc (0:ℝ) T, E))
      = (1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP := by
    refine ContinuousLinearMap.ext fun β => ?_
    simp [hG'_def]
  have hGinl : G' ∘L ContinuousLinearMap.inl ℝ E (C(Set.Icc (0:ℝ) T, E)) = -constE := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp [hG'_def]
  have if₂u : (G' ∘L ContinuousLinearMap.inr ℝ E (C(Set.Icc (0:ℝ) T, E))).IsInvertible := by
    rw [hGinr]; exact hu
  -- the residual vanishes at the equilibrium point
  have hG0 : picardResidual hT.le f pt = 0 := picardResidual_const_eq_zero hT heq
  -- the implicit function agrees with `σ` near `x₀`
  have hptF : Tendsto (fun x : E => (x, σ x)) (𝓝 x₀) (𝓝 pt) := by
    have h : Tendsto (fun x : E => (x, σ x)) (𝓝 x₀) (𝓝 (x₀, σ x₀)) :=
      continuousAt_id.prodMk hσc
    rwa [hσ0] at h
  have hev : ∀ᶠ x in 𝓝 x₀, hG.implicitFunctionOfProdDomain if₂u x = σ x := by
    filter_upwards [hptF.eventually
      (hG.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u), hσ] with x hx hx0
    exact hx.mp (by rw [hx0, hG0])
  have hψ := hG.hasStrictFDerivAt_implicitFunctionOfProdDomain if₂u
  -- identify the implicit-function derivative with `D`
  have huD : ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP).comp D
      = constE := by
    refine ContinuousLinearMap.ext fun v => ?_
    simpa [hJP_def, hconstE_def] using hD v
  have hDid : -(G' ∘L ContinuousLinearMap.inr ℝ E (C(Set.Icc (0:ℝ) T, E))).inverse
      ∘L (G' ∘L ContinuousLinearMap.inl ℝ E (C(Set.Icc (0:ℝ) T, E))) = D := by
    rw [hGinr, hGinl, ContinuousLinearMap.comp_neg, neg_neg, ← huD,
      ← ContinuousLinearMap.comp_assoc, hu.inverse_comp_self, ContinuousLinearMap.id_comp]
  rw [← hDid]
  exact hψ.congr_of_eventuallyEq hev

/-! ## From pointwise strict differentiability to C¹

A function that is *strictly* differentiable at every point of an open set is automatically
`C¹` there: the strict estimates at two nearby base points hold on a common pair-ball, and
comparing them on that ball forces the two derivatives to be close in operator norm. This
upgrades the pointwise strict-differentiability conclusions of the theorems above (obtained
at each initial condition separately) to genuine `C¹` regularity on open sets. -/

section StrictToC1

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Math.** If `f` is strictly differentiable at every point of an open set `s`, then the
derivative map `x ↦ f' x` is continuous on `s`. (For `x, x'` close, the strict estimates at
`x` and at `x'` both control the same difference quotients on a small common ball, so
`‖f' x' - f' x‖` is small: pointwise strict differentiability self-improves to continuity of
the derivative.) -/
theorem continuousOn_of_forall_hasStrictFDerivAt
    {f : E' → G} {f' : E' → E' →L[ℝ] G} {s : Set E'} (hs : IsOpen s)
    (hf : ∀ x ∈ s, HasStrictFDerivAt f (f' x) x) :
    ContinuousOn f' s := by
  intro x hx
  refine ContinuousAt.continuousWithinAt (Metric.continuousAt_iff.mpr fun ε hε => ?_)
  have hε4 : 0 < ε / 4 := by positivity
  -- the strict estimate at `x`, on a pair-ball of radius `δ₁`
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.mp
    (Asymptotics.isLittleO_iff.mp (hf x hx).isLittleO hε4)
  obtain ⟨δ₀, hδ₀, hδ₀s⟩ := Metric.isOpen_iff.mp hs x hx
  refine ⟨min (δ₁ / 2) δ₀, lt_min (by positivity) hδ₀, fun {x'} hx' => ?_⟩
  have hx'x : dist x' x < δ₁ / 2 := hx'.trans_le (min_le_left _ _)
  have hx's : x' ∈ s := hδ₀s (Metric.mem_ball.mpr (hx'.trans_le (min_le_right _ _)))
  -- the strict estimate at `x'`, on a pair-ball of radius `δ₂`
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.eventually_nhds_iff_ball.mp
    (Asymptotics.isLittleO_iff.mp (hf x' hx's).isLittleO hε4)
  -- compare the two estimates on the common ball
  have hop : ‖f' x' - f' x‖ ≤ ε / 2 := by
    refine ContinuousLinearMap.opNorm_le_of_ball (lt_min (half_pos hδ₁) hδ₂)
      (by positivity) fun w hw => ?_
    rw [mem_ball_zero_iff] at hw
    have hw₁ : ‖w‖ < δ₁ / 2 := hw.trans_le (min_le_left _ _)
    have hw₂ : ‖w‖ < δ₂ := hw.trans_le (min_le_right _ _)
    have hp₁ : ((x' + w, x') : E' × E') ∈ Metric.ball ((x, x) : E' × E') δ₁ := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · calc dist (x' + w) x ≤ dist (x' + w) x' + dist x' x := dist_triangle _ _ _
          _ = ‖w‖ + dist x' x := by rw [dist_eq_norm, add_sub_cancel_left]
          _ < δ₁ / 2 + δ₁ / 2 := add_lt_add hw₁ hx'x
          _ = δ₁ := by ring
      · exact hx'x.trans (half_lt_self hδ₁)
    have hp₂ : ((x' + w, x') : E' × E') ∈ Metric.ball ((x', x') : E' × E') δ₂ := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [dist_eq_norm, add_sub_cancel_left]
        exact hw₂
      · simpa using hδ₂
    have h₁ := hb₁ _ hp₁
    have h₂ := hb₂ _ hp₂
    simp only [add_sub_cancel_left] at h₁ h₂
    calc ‖(f' x' - f' x) w‖
        = ‖(f (x' + w) - f x' - f' x w) - (f (x' + w) - f x' - f' x' w)‖ := by
          rw [ContinuousLinearMap.sub_apply]; congr 1; abel
      _ ≤ ‖f (x' + w) - f x' - f' x w‖ + ‖f (x' + w) - f x' - f' x' w‖ :=
          norm_sub_le _ _
      _ ≤ ε / 4 * ‖w‖ + ε / 4 * ‖w‖ := add_le_add h₁ h₂
      _ = ε / 2 * ‖w‖ := by ring
  calc dist (f' x') (f' x) = ‖f' x' - f' x‖ := dist_eq_norm _ _
    _ ≤ ε / 2 := hop
    _ < ε := half_lt_self hε

/-- **Math.** A function strictly differentiable at every point of an open set is `C¹`
there. Combined with the pointwise strict differentiability of a flow in its initial
condition (`hasStrictFDerivAt_of_picardResidual_curve` at each base point), this yields `C¹`
dependence of the flow on its initial condition on open sets of initial data. -/
theorem contDiffOn_one_of_forall_hasStrictFDerivAt
    {f : E' → G} {f' : E' → E' →L[ℝ] G} {s : Set E'} (hs : IsOpen s)
    (hf : ∀ x ∈ s, HasStrictFDerivAt f (f' x) x) :
    ContDiffOn ℝ 1 f s := by
  have hfderiv : ∀ x ∈ s, fderiv ℝ f x = f' x := fun x hx =>
    (hf x hx).hasFDerivAt.fderiv
  have h1 : (1 : WithTop ℕ∞) = 0 + 1 := (zero_add _).symm
  rw [h1, contDiffOn_succ_iff_fderiv_of_isOpen hs]
  refine ⟨fun x hx => ((hf x hx).hasFDerivAt.differentiableAt).differentiableWithinAt,
    fun h => by simp at h, ?_⟩
  rw [contDiffOn_zero]
  exact (continuousOn_of_forall_hasStrictFDerivAt hs hf).congr hfderiv

end StrictToC1

/-- **Math.** Evaluation form of `hasStrictFDerivAt_of_picardResidual`: for each fixed time
`t ∈ [0,T]`, the map `x ↦ σ x t` is strictly differentiable at the equilibrium `x₀` with
derivative `v ↦ D v t`. -/
theorem hasStrictFDerivAt_eval_of_picardResidual
    (hT : 0 < T) {f : E → E} {f' : E → E →L[ℝ] E} {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (heq : f x₀ = 0)
    (hd : ∀ x ∈ Metric.ball x₀ ρ, HasFDerivAt f (f' x) x)
    (hc : ContinuousAt f' x₀)
    (hTL : T * ‖f' x₀‖ < 1)
    {σ : E → C(Set.Icc (0:ℝ) T, E)}
    (hσ0 : σ x₀ = ContinuousMap.const _ x₀)
    (hσc : ContinuousAt σ x₀)
    (hσ : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le f (x, σ x) = 0)
    {D : E →L[ℝ] C(Set.Icc (0:ℝ) T, E)}
    (hD : ∀ v : E, D v - intervalPrimitive hT.le (postcomp (f' x₀) (D v))
          = ContinuousMap.const _ v)
    (t : Set.Icc (0:ℝ) T) :
    HasStrictFDerivAt (fun x => σ x t) ((ContinuousMap.evalCLM ℝ t).comp D) x₀ :=
  (ContinuousMap.evalCLM ℝ t).hasStrictFDerivAt.comp x₀
    (hasStrictFDerivAt_of_picardResidual hT hρ heq hd hc hTL hσ0 hσc hσ hD)

end PetersenLib.FlowDependence
