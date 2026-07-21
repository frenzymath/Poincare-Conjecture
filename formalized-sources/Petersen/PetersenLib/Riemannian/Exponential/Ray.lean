/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Exponential/Ray.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Exponential.Defs
import PetersenLib.Riemannian.Geodesic.Homogeneity
import PetersenLib.Riemannian.Geodesic.InitialVelocity

set_option linter.unusedSectionVars false

/-!
# The exponential map along rays

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, the exponential map traces the
geodesic along each ray of the tangent space:

`exp_p (t • v) = γ(t, p, v)`.

This is do Carmo's description "`exp_q v` is obtained by going a length `|v|`
from `q` along the geodesic with velocity `v / |v|`" (Ch. 3, after Prop. 2.7),
and it is the computational heart of `d(exp_p)_0 = id` (Ch. 3, Prop. 2.9): the
curve `t ↦ exp_p (t v)` *is* the geodesic `t ↦ γ(t, p, v)`, so its velocity at
`t = 0` is `v`.

The chart-validity clause `hsrc` is inherited from the value-level homogeneity
`maximalGeodesic_fiberScale`: the canonical maximal geodesic is built from the
chart-`p`-fixed spray, which degenerates off the chart at `p`.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace PetersenLib
namespace Exponential

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The exponential map along a ray is the geodesic** (do Carmo Ch. 3,
after Prop. 2.7): `exp_p (t • v) = γ(t, p, v)` whenever `t` lies in the maximal
interval of the geodesic with initial data `(p, v)`. The chart-validity clause
`hsrc` requires geodesic witnesses with initial data `(p, t • v)` to keep their
foot in the chart at `p` (as in `maximalGeodesic_fiberScale`). -/
theorem expMap_smul (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ}
    (hmem : t ∈ maximalGeodesicInterval (I := I) g p v)
    (hsrc : ∀ (γ : ℝ → M) (J : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ J p (t • v) →
        ∀ s ∈ J, γ s ∈ (chartAt H p).source) :
    expMap (I := I) g p (t • v) = maximalGeodesic (I := I) g p v t := by
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [zero_smul, expMap_zero, maximalGeodesic_zero]
  · unfold expMap
    have h1 : t * 1 ∈ maximalGeodesicInterval (I := I) g p v := by rwa [mul_one]
    have h := maximalGeodesic_fiberScale (I := I) (g := g) (p := p) (v := v)
      (a := t) (t := 1) ht0 h1 hsrc
    rwa [mul_one] at h

/-- **Math.** **`d(exp_p)_0 = id` along rays** (do Carmo Ch. 3, the computation in
Prop. 2.9): read in the chart at `p`, the curve `t ↦ exp_p(t • v)` has derivative
`v` at `t = 0`:
$$d(\exp_p)_0(v) = \frac{d}{dt}\exp_p(t v)\Big|_{t=0}
  = \frac{d}{dt}\gamma(t, p, v)\Big|_{t=0} = v.$$
The chart-validity clause `hsrc` is inherited from the homogeneity of the
canonical maximal geodesic: witnesses with initial data `(p, t • v)` must keep
their foot in the chart at `p`. -/
theorem hasDerivAt_extChartAt_expMap_smul
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (hsrc : ∀ (t : ℝ) (γ : ℝ → M) (J : Set ℝ),
      IsGeodesicOnWithInitial (I := I) g γ J p (t • v) →
        ∀ s ∈ J, γ s ∈ (chartAt H p).source) :
    HasDerivAt (fun t : ℝ => extChartAt I p (expMap (I := I) g p (t • v))) v 0 := by
  -- near `0`, `exp_p(t • v)` is the canonical geodesic `γ(t, p, v)`
  have hev : (fun t : ℝ => expMap (I := I) g p (t • v)) =ᶠ[𝓝 (0 : ℝ)]
      maximalGeodesic (I := I) g p v := by
    have hI : maximalGeodesicInterval (I := I) g p v ∈ 𝓝 (0 : ℝ) :=
      (maximalGeodesicInterval_isOpen (I := I) g p v).mem_nhds
        (zero_mem_maximalGeodesicInterval (I := I) g p v)
    filter_upwards [hI] with t ht
    exact expMap_smul (I := I) g p v ht (hsrc t)
  -- the canonical geodesic has velocity `v` at `0`
  have hvel : HasDerivAt
      (fun s => extChartAt I p (maximalGeodesic (I := I) g p v s)) v 0 := by
    refine hasDerivAt_extChartAt_maximalGeodesic (I := I) ?_
    intro γ' J' hγ'
    have := hsrc 1
    rw [one_smul] at this
    exact this γ' J' hγ'
  refine hvel.congr_of_eventuallyEq ?_
  filter_upwards [hev] with t ht
  rw [ht]

end Exponential
end PetersenLib

end
