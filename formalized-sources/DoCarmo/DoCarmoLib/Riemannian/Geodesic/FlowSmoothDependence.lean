import DoCarmoLib.Riemannian.Geodesic.SuperpositionSmooth
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# `C^∞` dependence of an ODE flow on its initial condition (abstract Banach form)

This file assembles the `C^∞` smoothness of the local flow of an autonomous ODE `x' = f(x)` on
a Banach space `E`, out of the linchpin `contDiff_superposition_infty` and the `C^∞` inverse
function theorem — the route that upgrades the `C¹`/`C²` results of `FlowC1Dependence.lean` /
`FlowC2Dependence.lean` to all orders **without** a jet tower.

## The plan

The time-`T` Picard flow `σ : E → C([0,T], E)` of `x' = f(x)` is characterised by the vanishing
of the **Picard residual** `Φ(x, α) = α - const x - ∫₀ᵗ f(α(s)) ds`
(`FlowDependence.picardResidual`). The two facts proved here are:

* **`contDiff_picardResidual`** — `Φ` is `C^∞` jointly in `(x, α)` when `f` is `C^∞`. This is the
  payoff of `contDiff_superposition_infty`: the only nonlinear ingredient of `Φ` is the
  Nemytskii operator `α ↦ f ∘ α`, now known to be `C^∞`; everything else is continuous-linear
  (`ContinuousLinearMap.const`, `intervalPrimitive`, projections).

The remaining step of the route (a later increment) applies the `C^∞` inverse function theorem
to `Ψ(x, α) = (x, Φ(x, α))` — whose derivative at a fixed point is the block-triangular linear
equivalence `(v, h) ↦ (v, -const v + (1 - J∘M) h)` with `1 - J∘M` invertible by the Neumann
series (`FlowDependence.hasStrictFDerivAt_of_picardResidual_curve` already establishes this
invertibility) — to make the flow `σ(x) = π₂(Ψ⁻¹(x, 0))` `C^∞`, and then evaluates at time `T`.

Reference: standard smooth-dependence theory for ODEs; do Carmo, *Riemannian Geometry*, Ch. 7.
-/

open Filter Set
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Math.** **The Picard residual is `C^∞` jointly in `(x, α)`** when the vector field `f` is
`C^∞`. The residual `Φ(x, α) = α - const x - ∫₀ᵗ f(α(s)) ds` is a difference of three `C^∞` maps
of `(x, α)`:

* `(x, α) ↦ α` — the second projection, continuous linear;
* `(x, α) ↦ const x` — the constant embedding `ContinuousLinearMap.const` after the first
  projection, continuous linear;
* `(x, α) ↦ ∫₀ᵗ f(α(s)) ds` — the Volterra primitive `intervalPrimitive` (continuous linear)
  after the superposition operator `α ↦ f ∘ α` (`C^∞` by `contDiff_superposition_infty`) after
  the second projection.

This is the joint smoothness of the fixed-point map that the `C^∞` implicit/inverse function
theorem consumes to make the flow `C^∞`. -/
theorem contDiff_picardResidual {T : ℝ} (hT : 0 ≤ T) {f : E → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (picardResidual hT f) := by
  -- `(x, α) ↦ α`
  have h1 : ContDiff ℝ ∞ (fun q : E × C(Set.Icc (0:ℝ) T, E) => q.2) := contDiff_snd
  -- `(x, α) ↦ const x`
  have h2 : ContDiff ℝ ∞
      (fun q : E × C(Set.Icc (0:ℝ) T, E) => ContinuousMap.const (Set.Icc (0:ℝ) T) q.1) :=
    ContDiff.continuousLinearMap_comp
      (ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T) : E →L[ℝ] C(Set.Icc (0:ℝ) T, E))
      contDiff_fst
  -- `(x, α) ↦ ∫₀ᵗ f(α(s)) ds`
  have h3 : ContDiff ℝ ∞
      (fun q : E × C(Set.Icc (0:ℝ) T, E) => intervalPrimitive hT (superposition f q.2)) :=
    ContDiff.continuousLinearMap_comp (intervalPrimitive hT)
      ((contDiff_superposition_infty hf).comp contDiff_snd)
  exact (h1.sub h2).sub h3

/-- **Math.** **The strict derivative of the Picard residual in `(x, α)`.** Along a base solution
`α₀` staying in an open set `u` where `f` is differentiable with continuous derivative `f'`, the
residual `Φ(x, α) = α - const x - ∫₀ᵗ f(α(s)) ds` is strictly differentiable at `(x₀, α₀)` with
derivative `(v, h) ↦ h - const v - J∘M h`, where `J∘M = intervalPrimitive ∘ postcompCurve A₀` is
the linearised Volterra operator along `α₀`. Extracted from the internals of
`hasStrictFDerivAt_of_picardResidual_curve`. -/
theorem hasStrictFDerivAt_picardResidual {T : ℝ} (hT : 0 < T)
    {f : E → E} {f' : E → E →L[ℝ] E} {u : Set E} (hu : IsOpen u)
    (hd : ∀ x ∈ u, HasFDerivAt f (f' x) x)
    {x₀ : E} {α₀ : C(Set.Icc (0:ℝ) T, E)} (hmem : ∀ t, α₀ t ∈ u)
    (hc : ∀ t, ContinuousAt f' (α₀ t))
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = f' (α₀ t)) :
    HasStrictFDerivAt (picardResidual hT.le f)
      (ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E)
        - (ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T)).comp
            (ContinuousLinearMap.fst ℝ E C(Set.Icc (0:ℝ) T, E))
        - ((intervalPrimitive hT.le).comp (postcompCurve A₀)).comp
            (ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E))) (x₀, α₀) := by
  set pt : E × C(Set.Icc (0:ℝ) T, E) := (x₀, α₀) with hpt_def
  set constE : E →L[ℝ] C(Set.Icc (0:ℝ) T, E) := ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T)
  set JP : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    (intervalPrimitive hT.le).comp (postcompCurve A₀) with hJP_def
  have hN : HasStrictFDerivAt (superposition f) (postcompCurve A₀) α₀ :=
    hasStrictFDerivAt_superposition hu hd hmem hc hA₀
  have h1 : HasStrictFDerivAt (fun q : E × C(Set.Icc (0:ℝ) T, E) => q.2)
      (ContinuousLinearMap.snd ℝ E (C(Set.Icc (0:ℝ) T, E))) pt := hasStrictFDerivAt_snd
  have h2 : HasStrictFDerivAt
      (fun q : E × C(Set.Icc (0:ℝ) T, E) => ContinuousMap.const (Set.Icc (0:ℝ) T) q.1)
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

/-- **Math.** **`C^∞` dependence of the local flow on its initial condition.** Let `α₀` be a base
solution of `x' = f(x)` on `[0, T]` with initial value `x₀`, staying in an open set where the
globally `C^∞` field `f` is differentiable, and let `A₀ = (t ↦ f'(α₀ t))` satisfy the contraction
bound `T ‖A₀‖ < 1`. If `σ : E → C([0,T], E)` is any solution family with `σ x₀ = α₀`, continuous
at `x₀`, satisfying the Picard equation `picardResidual (x, σ x) = 0` near `x₀`, then `σ` is
`C^∞` at `x₀`.

The proof feeds the joint `C^∞` smoothness of the Picard residual (`contDiff_picardResidual`)
into mathlib's `C^∞` implicit function theorem (`ContDiffAt.contDiffAt_implicitFunction`), applied
to the residual whose `α`-partial derivative `1 - J∘M` at `(x₀, α₀)` is invertible by the Neumann
series (`T ‖A₀‖ < 1`). The resulting `C^∞` implicit function agrees with `σ` near `x₀`, since both
are zeros of the residual and the residual vanishes at `(x₀, α₀)`. This upgrades the `C¹`/`C²`
flow-dependence of `FlowC1Dependence`/`FlowC2Dependence` to all orders in one stroke, and is the
abstract heart of the smoothness of `exp_p`. -/
theorem contDiffAt_flow_of_picardResidual {T : ℝ} (hT : 0 < T)
    {f : E → E} (hf : ContDiff ℝ ∞ f)
    {x₀ : E} {α₀ : C(Set.Icc (0:ℝ) T, E)}
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} (hA₀ : ∀ t, A₀ t = fderiv ℝ f (α₀ t))
    (hTL : T * ‖A₀‖ < 1)
    {σ : E → C(Set.Icc (0:ℝ) T, E)}
    (hσ0 : σ x₀ = α₀) (hσc : ContinuousAt σ x₀)
    (hσ : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le f (x, σ x) = 0) :
    ContDiffAt ℝ ∞ σ x₀ := by
  classical
  set pt : E × C(Set.Icc (0:ℝ) T, E) := (x₀, α₀) with hpt_def
  set JP : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E) :=
    (intervalPrimitive hT.le).comp (postcompCurve A₀) with hJP_def
  -- the residual is `C^∞` jointly, and vanishes at the base point
  have hcdf : ContDiffAt ℝ ∞ (picardResidual hT.le f) pt :=
    (contDiff_picardResidual hT.le hf).contDiffAt
  have hpn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hu0 : picardResidual hT.le f pt = 0 := by
    have h := hσ.self_of_nhds; rw [hσ0] at h; exact h
  -- the strict derivative of the residual, and its `α`-partial `1 - JP`
  have hG : HasStrictFDerivAt (picardResidual hT.le f)
      (ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E)
        - (ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T)).comp
            (ContinuousLinearMap.fst ℝ E C(Set.Icc (0:ℝ) T, E))
        - JP.comp (ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E))) pt :=
    hasStrictFDerivAt_picardResidual hT isOpen_univ
      (fun x _ => (hf.differentiable (by simp)).differentiableAt.hasFDerivAt)
      (fun _ => Set.mem_univ _) (fun _ => (hf.continuous_fderiv (by simp)).continuousAt) hA₀
  have hfderiv : fderiv ℝ (picardResidual hT.le f) pt
      = ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E)
        - (ContinuousLinearMap.const ℝ (Set.Icc (0:ℝ) T)).comp
            (ContinuousLinearMap.fst ℝ E C(Set.Icc (0:ℝ) T, E))
        - JP.comp (ContinuousLinearMap.snd ℝ E C(Set.Icc (0:ℝ) T, E)) := hG.hasFDerivAt.fderiv
  -- `1 - JP` is invertible by the Neumann series
  have hJPnorm : ‖JP‖ < 1 :=
    (norm_intervalPrimitive_comp_postcompCurve_le hT.le A₀).trans_lt hTL
  set w : (C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E))ˣ :=
    Units.oneSub JP hJPnorm with hw_def
  have hinvertible :
      ((1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse w.mul_inv w.inv_mul
  -- the `α`-partial of the residual is `1 - JP`
  have hinr : fderiv ℝ (picardResidual hT.le f) pt
        ∘L ContinuousLinearMap.inr ℝ E C(Set.Icc (0:ℝ) T, E)
      = (1 : C(Set.Icc (0:ℝ) T, E) →L[ℝ] C(Set.Icc (0:ℝ) T, E)) - JP := by
    rw [hfderiv]
    refine ContinuousLinearMap.ext fun β => ?_
    simp
  have if₂ : (fderiv ℝ (picardResidual hT.le f) pt
      ∘L ContinuousLinearMap.inr ℝ E C(Set.Icc (0:ℝ) T, E)).IsInvertible := by
    rw [hinr]; exact hinvertible
  -- the `C^∞` implicit function, and its agreement with `σ`
  set ψ : E → C(Set.Icc (0:ℝ) T, E) := hcdf.implicitFunction hpn if₂ with hψ_def
  have hψcd : ContDiffAt ℝ ∞ ψ x₀ := hcdf.contDiffAt_implicitFunction hpn if₂
  have hmap : Filter.Tendsto (fun x : E => (x, σ x)) (𝓝 x₀) (𝓝 pt) := by
    have h : Filter.Tendsto (fun x : E => (x, σ x)) (𝓝 x₀) (𝓝 (x₀, σ x₀)) :=
      continuousAt_id.prodMk hσc
    rwa [hσ0] at h
  have hev : ∀ᶠ x in 𝓝 x₀, σ x = ψ x := by
    filter_upwards [hmap.eventually (hcdf.eventually_apply_eq_iff_implicitFunction hpn if₂), hσ]
      with x hx hx0
    exact (hx.mp (by rw [hx0, hu0])).symm
  exact hψcd.congr_of_eventuallyEq hev

end Riemannian.FlowDependence

end
