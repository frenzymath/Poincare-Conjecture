import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Morgan--Tian Chapter 3: affine time reparametrizations

An affine change of the real time variable is a smooth equivalence whenever its
linear coefficient is nonzero.  This file records the bundled equivalence and
the corresponding manifold diffeomorph, together with the product map obtained
by adjoining the identity on a second real factor.
-/

open scoped ContDiff Manifold

noncomputable section

namespace MorganTianLib

/-- The affine map `t ↦ a * t + b`, bundled as a continuous affine equivalence.

The nonzero coefficient is represented by the unit `Units.mk0 a ha`; this gives
both the inverse map and the continuity data without introducing an analytic
side condition beyond `a ≠ 0`.
-/
def affineTimeContinuousAffineEquiv (a b : ℝ) (ha : a ≠ 0) : ℝ ≃ᴬ[ℝ] ℝ :=
  (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 a ha)).toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ ℝ b)

/-- Pointwise formula for `affineTimeContinuousAffineEquiv`. -/
theorem affineTimeContinuousAffineEquiv_apply (a b t : ℝ) (ha : a ≠ 0) :
    affineTimeContinuousAffineEquiv a b ha t = a * t + b := by
  change b + (t * a) = a * t + b
  ring

/-- Function extensionality form of the affine time reparametrization formula. -/
theorem affineTimeContinuousAffineEquiv_fun (a b : ℝ) (ha : a ≠ 0) :
    (affineTimeContinuousAffineEquiv a b ha : ℝ → ℝ) = fun t => a * t + b := by
  funext t
  exact affineTimeContinuousAffineEquiv_apply a b t ha

/-- The affine time reparametrization as a smooth diffeomorph of the real line. -/
def affineTimeDiffeomorph (a b : ℝ) (ha : a ≠ 0) :
    Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
  { toEquiv := (affineTimeContinuousAffineEquiv a b ha).toAffineEquiv.toEquiv
    contMDiff_toFun :=
      (ContinuousAffineMap.contDiff
        (affineTimeContinuousAffineEquiv a b ha).toContinuousAffineMap).contMDiff
    contMDiff_invFun :=
      (ContinuousAffineMap.contDiff
        (affineTimeContinuousAffineEquiv a b ha).symm.toContinuousAffineMap).contMDiff }

/-- The product of the identity on a spatial factor with the affine time map. -/
def affineTimeProductDiffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a b : ℝ) (ha : a ≠ 0) :
    Diffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ)) ((𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ))
      (E × ℝ) (E × ℝ) ∞ :=
  (Diffeomorph.refl 𝓘(ℝ, E) E ∞).prodCongr
    (affineTimeDiffeomorph a b ha)

/-- Pointwise formula for the scalar affine diffeomorph. -/
theorem affineTimeDiffeomorph_apply (a b t : ℝ) (ha : a ≠ 0) :
    affineTimeDiffeomorph a b ha t = a * t + b := by
  change affineTimeContinuousAffineEquiv a b ha t = a * t + b
  exact affineTimeContinuousAffineEquiv_apply a b t ha

/-- Pointwise formula for the product affine diffeomorph. -/
theorem affineTimeProductDiffeomorph_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (ha : a ≠ 0) (x : E) (t : ℝ) :
    affineTimeProductDiffeomorph a b ha (x, t) = (x, a * t + b) := by
  simp only [affineTimeProductDiffeomorph, Diffeomorph.coe_prodCongr,
    Prod.map_apply, Diffeomorph.coe_refl]
  exact congrArg (fun y => (x, y)) (affineTimeDiffeomorph_apply a b t ha)

/-- The scalar affine time map has constant derivative `a`. -/
theorem affineTimeContinuousAffineEquiv_hasDerivAt (a b t : ℝ) (ha : a ≠ 0) :
    HasDerivAt (affineTimeContinuousAffineEquiv a b ha : ℝ → ℝ) a t := by
  rw [affineTimeContinuousAffineEquiv_fun a b ha]
  simpa using (hasDerivAt_const_mul (x := t) a).add_const b

/-- The scalar affine time map has derivative `a` at every point. -/
theorem affineTimeContinuousAffineEquiv_deriv (a b t : ℝ) (ha : a ≠ 0) :
    deriv (affineTimeContinuousAffineEquiv a b ha : ℝ → ℝ) t = a :=
  (affineTimeContinuousAffineEquiv_hasDerivAt a b t ha).deriv

/-- The scalar affine diffeomorph has the same constant derivative. -/
theorem affineTimeDiffeomorph_hasDerivAt (a b t : ℝ) (ha : a ≠ 0) :
    HasDerivAt (affineTimeDiffeomorph a b ha : ℝ → ℝ) a t := by
  change HasDerivAt (affineTimeContinuousAffineEquiv a b ha : ℝ → ℝ) a t
  exact affineTimeContinuousAffineEquiv_hasDerivAt a b t ha

/-- Derivative formula for the scalar affine diffeomorph. -/
theorem affineTimeDiffeomorph_deriv (a b t : ℝ) (ha : a ≠ 0) :
    deriv (affineTimeDiffeomorph a b ha : ℝ → ℝ) t = a :=
  (affineTimeDiffeomorph_hasDerivAt a b t ha).deriv

end MorganTianLib
