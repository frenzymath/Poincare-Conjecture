import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3SurfaceRegularity
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.CurveReadback
import DoCarmoLib.Riemannian.Jacobi.SurfaceCurvatureCommutation

/-!
# Surface partials read in a fixed chart (do Carmo Ch. 3, Definitions 3.1 and 3.3)

The parametrized-surface interface of `DoCarmoCh3` defines the intrinsic
partials `∂s/∂u`, `∂s/∂v` of a surface `s : ℝ × ℝ → M` as `mfderiv`s in the
coordinate directions `(1,0)`, `(0,1)`.  The symmetry lemma
(`SymmetryLemma.lean`) and the Gauss-lemma computations instead work with the
*chart reading* `F = φ_α ∘ s` and its Fréchet derivative `DF`.  Nothing so far
identified the two: `partialU_eq_slice_mfderiv` reduces the ambient partial to a
slice derivative but stays chart-free, while
`Geodesic.mfderiv_eq_of_hasDerivAt_extChartAt` converts a *curve* velocity to a
chart reading.  This file composes them, so a statement about `∂s/∂u`, `∂s/∂v`
can be exchanged for one about `DF·(1,0)`, `DF·(0,1)`.

* `mfderiv_fst_eq_of_hasFDerivAt_extChartAt` /
  `mfderiv_snd_eq_of_hasFDerivAt_extChartAt` — the coordinate-direction
  `mfderiv` of a surface is the trivialization readback of the corresponding
  chart-reading partial.
* `ParametrizedSurface.partialU_eq_of_hasFDerivAt_extChartAt` /
  `partialV_eq_of_hasFDerivAt_extChartAt` — the same for the bundled
  `partialU`, `partialV`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 3, Definition 3.3 and Lemma 3.4.
-/

open Bundle Manifold Set
open scoped ContDiff Manifold Topology ENNReal

noncomputable section

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The `u`-partial of a surface, read in the chart at `α`: if the
chart reading `F = φ_α ∘ s` is differentiable at `q` with derivative `DF`, then
the intrinsic partial `∂s/∂u (q) = mfderiv s q (1,0)` is the tangent coordinate
change of the coordinate partial `DF·(1,0)`.

This is the two-parameter analogue of
`mfderiv_eq_of_hasDerivAt_extChartAt`, obtained by restricting to the fixed-`v`
slice through `q`. -/
theorem mfderiv_fst_eq_of_hasFDerivAt_extChartAt {s : ℝ × ℝ → M} {q : ℝ × ℝ}
    {DF : (ℝ × ℝ) →L[ℝ] E} {α : M}
    (hcont : ContinuousAt s q) (hsrc : s q ∈ (chartAt H α).source)
    (hd : HasFDerivAt (fun p => extChartAt I α (s p)) DF q) :
    mfderiv 𝓘(ℝ, ℝ) I (surfaceSliceU s q.2) q.1 1
      = tangentCoordChange I α (s q) (s q) (DF (1, 0)) := by
  have hslice : ContinuousAt (surfaceSliceU s q.2) q.1 := by
    have hpair : ContinuousAt (fun u : ℝ => (u, q.2)) q.1 := by fun_prop
    exact show ContinuousAt (s ∘ fun u : ℝ => (u, q.2)) q.1 from
      hcont.comp (x := q.1) (by simpa using hpair)
  have hderiv : HasDerivAt (fun u => extChartAt I α (surfaceSliceU s q.2 u))
      (DF (1, 0)) q.1 :=
    Riemannian.Jacobi.hasDerivAt_comp_fst
      (F := fun p => extChartAt I α (s p)) (DF := DF) (by simpa using hd)
  simpa [surfaceSliceU] using
    mfderiv_eq_of_hasDerivAt_extChartAt (I := I) (γ := surfaceSliceU s q.2) (α := α)
      hslice (by simpa [surfaceSliceU] using hsrc) hderiv

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The `v`-partial of a surface, read in the chart at `α`: the
intrinsic partial `∂s/∂v (q) = mfderiv s q (0,1)` is the tangent coordinate
change of the coordinate partial `DF·(0,1)`. -/
theorem mfderiv_snd_eq_of_hasFDerivAt_extChartAt {s : ℝ × ℝ → M} {q : ℝ × ℝ}
    {DF : (ℝ × ℝ) →L[ℝ] E} {α : M}
    (hcont : ContinuousAt s q) (hsrc : s q ∈ (chartAt H α).source)
    (hd : HasFDerivAt (fun p => extChartAt I α (s p)) DF q) :
    mfderiv 𝓘(ℝ, ℝ) I (surfaceSliceV s q.1) q.2 1
      = tangentCoordChange I α (s q) (s q) (DF (0, 1)) := by
  have hslice : ContinuousAt (surfaceSliceV s q.1) q.2 := by
    have hpair : ContinuousAt (fun v : ℝ => (q.1, v)) q.2 := by fun_prop
    exact show ContinuousAt (s ∘ fun v : ℝ => (q.1, v)) q.2 from
      hcont.comp (x := q.2) (by simpa using hpair)
  have hderiv : HasDerivAt (fun v => extChartAt I α (surfaceSliceV s q.1 v))
      (DF (0, 1)) q.2 :=
    Riemannian.Jacobi.hasDerivAt_comp_snd
      (F := fun p => extChartAt I α (s p)) (DF := DF) (by simpa using hd)
  simpa [surfaceSliceV] using
    mfderiv_eq_of_hasDerivAt_extChartAt (I := I) (γ := surfaceSliceV s q.1) (α := α)
      hslice (by simpa [surfaceSliceV] using hsrc) hderiv

namespace ParametrizedSurface

variable {r : ℕ∞ω}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** do Carmo Ch. 3, Definition 3.3, read in a chart: the bundled
intrinsic partial `∂s/∂u` is the tangent coordinate change of the chart-reading
partial `DF·(1,0)`.  Together with `partialV_eq_of_hasFDerivAt_extChartAt` this
is the dictionary that lets the chart-coordinate symmetry lemma
(`covariant_sndFDeriv_symm_of_eventually`) be read as a statement about the
book's `∂s/∂u`, `∂s/∂v`. -/
theorem partialU_eq_of_hasFDerivAt_extChartAt
    (S : ParametrizedSurface (I := I) (M := M))
    (hS : IsExtendedParametrizedSurfaceOfOrder I r S.domain S.toFun)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ S.domain)
    {DF : (ℝ × ℝ) →L[ℝ] E} {α : M}
    (hcont : ContinuousAt S.toFun q) (hsrc : S.toFun q ∈ (chartAt H α).source)
    (hd : HasFDerivAt (fun p => extChartAt I α (S.toFun p)) DF q) :
    S.partialU q = tangentCoordChange I α (S.toFun q) (S.toFun q) (DF (1, 0)) :=
  (S.partialU_eq_slice_mfderiv hS hr hq).trans
    (mfderiv_fst_eq_of_hasFDerivAt_extChartAt (I := I) hcont hsrc hd)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** do Carmo Ch. 3, Definition 3.3, read in a chart: the bundled
intrinsic partial `∂s/∂v` is the tangent coordinate change of the chart-reading
partial `DF·(0,1)`. -/
theorem partialV_eq_of_hasFDerivAt_extChartAt
    (S : ParametrizedSurface (I := I) (M := M))
    (hS : IsExtendedParametrizedSurfaceOfOrder I r S.domain S.toFun)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ S.domain)
    {DF : (ℝ × ℝ) →L[ℝ] E} {α : M}
    (hcont : ContinuousAt S.toFun q) (hsrc : S.toFun q ∈ (chartAt H α).source)
    (hd : HasFDerivAt (fun p => extChartAt I α (S.toFun p)) DF q) :
    S.partialV q = tangentCoordChange I α (S.toFun q) (S.toFun q) (DF (0, 1)) :=
  (S.partialV_eq_slice_mfderiv hS hr hq).trans
    (mfderiv_snd_eq_of_hasFDerivAt_extChartAt (I := I) hcont hsrc hd)

end ParametrizedSurface

end Geodesic
end Riemannian
