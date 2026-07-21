import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The adjoint representation and the "differentiate an isometric family" trick

This file supplies reusable infrastructure for Petersen Exercise 1.6.24 (3) — the
skew-symmetry of the infinitesimal adjoint action of a bi-invariant metric — and,
more generally, for any argument of the shape *"a smoothly varying family of
`g`-isometries has a `g`-skew infinitesimal generator"* (this is the mechanism
behind Killing fields in Chapter 8 as well).

## Main results

* `PetersenLib.curveIsometry_generator_skew`: if `ρ : ℝ → (V →L[ℝ] V)` is a curve
  of continuous linear maps with `ρ 0 = id`, every `ρ t` preserves a continuous
  bilinear form `bil`, and `ρ` has derivative `A` at `0`, then the generator `A`
  is `bil`-skew: `bil (A x) y + bil x (A y) = 0`. This is a pure normed-space
  calculus fact — no manifold structure is used — obtained by differentiating the
  constant map `t ↦ bil (ρ t x) (ρ t y)` and reading off the product rule at `0`.

* `PetersenLib.adjointMap`: the adjoint action `Ad_h = D(x ↦ h x h⁻¹)_e : 𝔤 → 𝔤`
  of a Lie group on its Lie algebra `𝔤 = T_eG`, with `adjointMap_one : Ad_1 = id`.

Combining the two reduces Exercise 1.6.24 (3) to the single manifold fact that the
adjoint orbit `t ↦ Ad_{c(t)}` (for a curve `c` realising `U ∈ 𝔤`) has velocity
`ad_U = [U, ·]` at `t = 0` — precisely the `exp`/`Ad`–`ad` correspondence that
Petersen defers to §2.1.4 and that Mathlib does not yet provide for abstract Lie
groups.
-/

open scoped ContDiff Manifold

namespace PetersenLib

/-! ## Differentiating a family of isometries -/

/-- **Math.** *The infinitesimal generator of a curve of isometries is skew.*
Let `bil : V →L[ℝ] V →L[ℝ] ℝ` be a continuous bilinear form and let
`ρ : ℝ → (V →L[ℝ] V)` be a curve of continuous linear operators with `ρ 0 = id`,
each of which preserves `bil` (`bil (ρ t x) (ρ t y) = bil x y`). If `ρ` is
differentiable at `0` with derivative `A`, then `A` is `bil`-skew:
`bil (A x) y + bil x (A y) = 0`.

Proof: the map `t ↦ bil (ρ t x) (ρ t y)` is constant (`= bil x y`), hence its
derivative at `0` vanishes; on the other hand the product rule computes that
derivative as `bil (A x) (ρ 0 y) + bil (ρ 0 x) (A y)`. With `ρ 0 = id` this is
`bil (A x) y + bil x (A y)`, and uniqueness of the derivative equates the two. -/
theorem curveIsometry_generator_skew
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (bil : V →L[ℝ] V →L[ℝ] ℝ) (ρ : ℝ → (V →L[ℝ] V)) (A : V →L[ℝ] V)
    (hρ : HasDerivAt ρ A 0) (hρ0 : ρ 0 = ContinuousLinearMap.id ℝ V)
    (hiso : ∀ (t : ℝ) (x y : V), bil (ρ t x) (ρ t y) = bil x y) (x y : V) :
    bil (A x) y + bil x (A y) = 0 := by
  -- Differentiate the pointwise evaluations `t ↦ ρ t x` and `t ↦ ρ t y`.
  have hρx : HasDerivAt (fun t => ρ t x) (A x) 0 := by
    simpa using hρ.clm_apply (hasDerivAt_const (0 : ℝ) x)
  have hρy : HasDerivAt (fun t => ρ t y) (A y) 0 := by
    simpa using hρ.clm_apply (hasDerivAt_const (0 : ℝ) y)
  -- Post-compose with the (linear, hence self-differentiating) form `bil`.
  have hp : HasDerivAt (fun t => bil (ρ t x)) (bil (A x)) 0 :=
    bil.hasFDerivAt.comp_hasDerivAt _ hρx
  -- Product rule for `t ↦ (bil (ρ t x)) (ρ t y)`.
  have hf : HasDerivAt (fun t => bil (ρ t x) (ρ t y))
      (bil (A x) (ρ 0 y) + bil (ρ 0 x) (A y)) 0 := hp.clm_apply hρy
  -- The same function is constant, so its derivative is `0`.
  have hconst : HasDerivAt (fun t => bil (ρ t x) (ρ t y)) 0 0 := by
    have hcst : (fun t => bil (ρ t x) (ρ t y)) = fun _ => bil x y := by
      funext t; exact hiso t x y
    rw [hcst]; exact hasDerivAt_const 0 (bil x y)
  have huniq := hf.unique hconst
  rw [hρ0] at huniq
  simpa using huniq

/-! ## The adjoint representation of a Lie group -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G]

variable (I) in
/-- **Math.** The **adjoint representation** `Ad_h = D(x ↦ h x h⁻¹)_e : 𝔤 → 𝔤` of
a Lie group `G` on its Lie algebra `𝔤 = T_eG`, the differential of conjugation
by `h` at the identity. (The codomain is `T_{h·1·h⁻¹}G = T_1G` up to the
definitional identification of tangent spaces with the model.) -/
noncomputable def adjointMap (h : G) :
    TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) :=
  mfderiv I I (fun x => h * x * h⁻¹) 1

omit [IsManifold I ∞ G] [LieGroup I ∞ G] in
@[simp]
theorem adjointMap_apply (h : G) (u : TangentSpace I (1 : G)) :
    adjointMap I h u = mfderiv I I (fun x => h * x * h⁻¹) 1 u := rfl

omit [IsManifold I ∞ G] [LieGroup I ∞ G] in
/-- **Math.** `Ad_e = id`: conjugation by the identity is the identity map, so its
differential at `e` is the identity operator on `𝔤`. -/
@[simp]
theorem adjointMap_one :
    adjointMap I (1 : G) = ContinuousLinearMap.id ℝ (TangentSpace I (1 : G)) := by
  have hfun : (fun x : G => (1 : G) * x * (1 : G)⁻¹) = _root_.id := by
    funext x; simp
  show mfderiv I I (fun x : G => (1 : G) * x * (1 : G)⁻¹) 1
      = ContinuousLinearMap.id ℝ (TangentSpace I (1 : G))
  rw [hfun, mfderiv_id]

end PetersenLib
