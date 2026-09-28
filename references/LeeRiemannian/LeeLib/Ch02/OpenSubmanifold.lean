/-
Open submanifolds: the differential of the inclusion.

An open subset `U ⊆ M` of a manifold is again a manifold modelled on the same
space (mathlib's `TopologicalSpace.Opens.instChartedSpace`, and the matching
`IsManifold` instance), its charts being the restrictions of the charts of `M`.
Every tangent space `T_x U` is therefore `T_{↑x} M = E`, and the differential of
the inclusion `ι : U ↪ M` *ought* to be the identity.

Mathlib does not say so.  It proves the inclusion smooth (`contMDiff_subtype_val`)
but computes no `mfderiv` for it; the only comparable computation in the pinned
mathlib is `mfderiv_subtype_coe_Icc_one`, for the very different case of the closed
interval `Icc x y` regarded as a manifold with boundary
(`Mathlib/Geometry/Manifold/Instances/Icc.lean:195`).  So any statement about a
metric, a curve or a map *on an open subset* has an `mfderiv` in it that is stuck.

That is the gap this file fills.

## Why it is nearly definitional

The charts of `U` are *literally* the charts of `M` restricted
(`TopologicalSpace.Opens.chartAt_eq`), so for `y : U` the two extended charts
agree on the nose:
`extChartAt I (↑x) ↑y = extChartAt I x y` by `rfl`.  Hence the chart
representation `writtenInExtChartAt I I x ι` is *definitionally*
`extChartAt I x ∘ (extChartAt I x).symm`, which is the identity on the chart's
target — a neighbourhood of `extChartAt I x x` within `range I`, which is exactly
the filter `HasMFDerivAt` asks about.  No comparison of the charts of `U` with
those of `M` is needed; that identification is what `Opens.chartAt_eq` already
is.

## Downstream

The general form is what Proposition 2.37 needs: there the open submanifold is
the regular set `ℛ = {x : df_x ≠ 0}` of a function on an arbitrary manifold, and
the reduction of `M_c = f⁻¹(c) ∩ ℛ` to a regular level set of `f|_ℛ` turns on
`d(ℛ ↪ M)` being an isomorphism.  The special case `W : Opens F` with `F` a
normed space (`I = 𝓘(ℝ, F)`) is what lets `ℝ⁺ = (0, ∞)` be used as a Riemannian
manifold in its own right (see `PolarCoordinates.lean`): `openSubmanifoldMetric`
needs exactly the injectivity of `dι`.
-/
import LeeLib.Ch02.PullbackMetric

namespace LeeLib.Ch02

open Set Function Manifold Metric TopologicalSpace
open scoped Manifold Topology ContDiff

noncomputable section

/-! ## The inclusion of an open submanifold of an arbitrary manifold -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The chart representation of an open-submanifold inclusion is the identity**
on the chart's target.

`U`'s chart at `x` is `M`'s chart at `↑x` restricted, so
`writtenInExtChartAt I I x ι` is definitionally `extChartAt I x ∘ (extChartAt I x).symm`;
the claim is then just `PartialEquiv.right_inv`.  The filter is `𝓝[range I]`, not
`𝓝`: off `range I` the chart's inverse is not a right inverse, so the unrestricted
statement is false in general (it holds for boundaryless `I`, where `range I = univ`). -/
theorem writtenInExtChartAt_opens_subtypeVal (U : Opens M) (x : U) :
    writtenInExtChartAt I I x (fun y : U => (y : M))
      =ᶠ[𝓝[range I] (extChartAt I x x)] id := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
  exact (extChartAt I x).right_inv hz

/-- **The inclusion of an open submanifold has the identity as its differential.**

Both `T_x U` and `T_{↑x} M` are `E`, and `U`'s charts are `M`'s charts restricted,
so the chart representation of `ι` is the identity where it is defined. -/
theorem hasMFDerivAt_opens_subtypeVal (U : Opens M) (x : U) :
    HasMFDerivAt I I (fun y : U => (y : M)) x (ContinuousLinearMap.id ℝ E) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  refine (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq
    (writtenInExtChartAt_opens_subtypeVal U x) ?_
  exact (extChartAt I x).right_inv (mem_extChartAt_target x)

/-- `dι_x = id` for the inclusion `ι : U ↪ M` of an open submanifold. -/
theorem mfderiv_opens_subtypeVal (U : Opens M) (x : U) :
    mfderiv I I (fun y : U => (y : M)) x = ContinuousLinearMap.id ℝ E :=
  (hasMFDerivAt_opens_subtypeVal U x).mfderiv

/-- `dι_x v = v`: the pointwise form of `mfderiv_opens_subtypeVal`, which is the
shape in which the computation is actually used. -/
@[simp] theorem mfderiv_opens_subtypeVal_apply (U : Opens M) (x : U) (v : TangentSpace I x) :
    (mfderiv I I (fun y : U => (y : M)) x) v = (show E from v) := by
  rw [mfderiv_opens_subtypeVal]; rfl

/-- The inclusion of an open submanifold is an immersion — immediate from
`mfderiv_opens_subtypeVal`, and the hypothesis `pullbackMetric` needs. -/
theorem injective_mfderiv_opens_subtypeVal (U : Opens M) (x : U) :
    Function.Injective (mfderiv I I (fun y : U => (y : M)) x) := by
  intro v w h
  simpa using h

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- **Restricting a map to an open submanifold does not change its differential.**

`d(F ∘ ι)_x = dF_{↑x} ∘ dι_x = dF_{↑x}`, since `dι_x = id`.  This is the step that
lets a statement about `F` on an open subset be read off from the statement about
`F` on the whole manifold — in particular it is what makes `c` a *regular value*
of `f|_ℛ` on the regular set `ℛ` of `f`, by construction rather than by
hypothesis. -/
theorem mfderiv_opens_restrict (U : Opens M) (F : M → M') {x : U}
    (hF : MDifferentiableAt I I' F ↑x) :
    mfderiv I I' (fun y : U => F ↑y) x = mfderiv I I' F ↑x := by
  have hcomp : mfderiv I I' ((fun z : M => F z) ∘ (fun y : U => (y : M))) x
      = (mfderiv I I' F ↑x).comp (mfderiv I I (fun y : U => (y : M)) x) :=
    mfderiv_comp x hF (hasMFDerivAt_opens_subtypeVal U x).mdifferentiableAt
  rw [Function.comp_def] at hcomp
  rw [hcomp, mfderiv_opens_subtypeVal]
  ext v
  rfl

end General

/-! ## The flat case: an open subset of a normed space

Here the ambient manifold is the model space itself, `I = 𝓘(ℝ, F)`, so the
general results above apply verbatim. -/

section Flat

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The metric induced on an open subset `W ⊆ F`** by a metric on the ambient
normed space: `ι^* g`, for `ι : W ↪ F` the inclusion.

This is Lee's "open submanifold" case of the induced metric of §2.3.  Because
`dι = id`, `openSubmanifoldMetric g W` is just `g` read at points of `W`
(`openSubmanifoldMetric_innerAt`); it is a separate object only because its base
manifold is `↥W` rather than `F`. -/
def openSubmanifoldMetric (g : RiemannianMetric 𝓘(ℝ, F) F) (W : Opens F) :
    RiemannianMetric 𝓘(ℝ, F) W :=
  pullbackMetric g (fun y : W => (y : F)) contMDiff_subtype_val
    (injective_mfderiv_opens_subtypeVal W)

/-- The induced metric on an open subset is the ambient metric, read at points of
the subset: no restriction of vectors takes place, since `T_x W = F = T_{↑x} F`. -/
@[simp] theorem openSubmanifoldMetric_innerAt (g : RiemannianMetric 𝓘(ℝ, F) F) (W : Opens F)
    (x : W) (v w : TangentSpace 𝓘(ℝ, F) x) :
    (openSubmanifoldMetric g W).innerAt x v w = g.innerAt (x : F) (show F from v) (show F from w) := by
  show pullbackForm g (fun y : W => (y : F)) x v w = _
  rw [pullbackForm_apply]
  simp

end Flat

end

end LeeLib.Ch02
