import DoCarmoLib.Riemannian.Jacobi.CartanExpNormTransfer
import DoCarmoLib.Riemannian.Manifold.HadamardNonpos
import DoCarmoLib.Riemannian.Exponential.CInftyGlobal

/-!
# do Carmo Ch. 8, §2 — the two assembly atoms for E. Cartan's theorem (GAP D)

This file supplies the two ingredients that stand between the already-landed analytic core of
E. Cartan's theorem in constant curvature and the statement `cor:dc-ch8-2-2` actually wants,
`DCIsLocalIsometryAt` for `f = exp_{p̃} ∘ i ∘ exp_p⁻¹`:

* **the local-diffeomorphism bridge** — `exp_p` is a `C^∞` local diffeomorphism at any `v`
  that is not a conjugate parameter. This is what turns the chart-level derivative
  isomorphism (`expDifferential_isEquiv_jacobi_of_not_conjugate`) into an honest local
  inverse `exp_p⁻¹`: with `IsLocalDiffeomorphAt` in hand, mathlib's
  `IsLocalDiffeomorphAt.localInverse` produces `exp_p⁻¹` and its smoothness, so none of that
  has to be built by hand.
* **the polarization step** — a *linear* map that preserves the **quadratic form** `⟨·,·⟩`
  preserves the **bilinear form** too. The norm transfer already landed
  (`chartMetricInner_expDifferential_transfer_of_constantCurvature_of_speedSq`) delivers only
  `|df_q(u)| = |u|`, whereas `DCIsLocalIsometryAt` is stated with the full inner product
  `⟨u,v⟩_q = ⟨df_q u, df_q v⟩`. Polarization closes exactly that gap.

## Mathematics

**Local diffeomorphism.** The proof is the curvature-free half of
`isLocalDiffeomorphAt_expMapGlobal_of_nonpos` (`HadamardNonpos.lean`): that theorem uses its
nonpositive-curvature hypothesis `hK` in exactly one place — to obtain the differential
isomorphism from `expDifferential_isEquiv_of_nonpos`. Everything after that (the target-chart
reading is `C^∞`, the normed-space inverse function theorem, composing with the chart inverse)
is curvature-free. Swapping that single input for
`expDifferential_isEquiv_of_not_conjugate` gives the same conclusion under the weaker and
sign-free hypothesis `¬ IsConjugatePointAt`, which is the form `cor:dc-ch8-2-2` needs — it must
work in **positive** curvature too, where `hK` is unavailable. The global smoothness of `exp_p`
(`contMDiff_expMapGlobal`, unconditional since the Ch. 7 work) discharges the `hsmooth`
hypothesis that `HadamardNonpos.lean` still carries, so this version is unconditional.

**Polarization.** Over `ℝ`, a symmetric bilinear form is recovered from its diagonal:

  `⟨u,v⟩ = (⟨u+v,u+v⟩ − ⟨u,u⟩ − ⟨v,v⟩)/2`.

So if `L` is additive and `⟨L w, L w⟩' = ⟨w,w⟩` for every `w`, then applying the identity on
both sides and using additivity at `w = u+v` gives `⟨L u, L v⟩' = ⟨u,v⟩`. Note this needs `L`
**additive** — a norm-preserving *nonlinear* map need not preserve inner products; in the
application `L = df_q` is linear, so the hypothesis is free.

## Contents

* `metricInner_polarization` — `⟨u,v⟩ = (⟨u+v,u+v⟩ − ⟨u,u⟩ − ⟨v,v⟩)/2`.
* `metricInner_transfer_of_norm_transfer` — an additive quadratic-form-preserving map
  preserves the bilinear form (the polarization step of `DCIsLocalIsometryAt`).
* `isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate` — `exp_p` is a `C^∞` local
  diffeomorphism at a non-conjugate `v`, unconditionally.

Blueprint: `lem:dc-ch8-2-1-exp-local-diffeo`, `lem:dc-ch8-2-1-polarization`, feeding
`cor:dc-ch8-2-2`, `cor:dc-ch8-2-3`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8, §2.
-/

open Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### Polarization: the diagonal determines a symmetric bilinear form -/

/-- **Math.** **The polarization identity for a Riemannian metric.** Over `ℝ` the symmetric
bilinear form `g` is recovered from its diagonal (the squared norm):

  `⟨u,v⟩ = (⟨u+v,u+v⟩ − ⟨u,u⟩ − ⟨v,v⟩)/2`.

Immediate from bilinearity and symmetry. Stated over `TangentSpace I x` so that the
`metricInner_add_left/right` lemmas apply directly — they do **not** fire on `E`-typed sums,
since `TangentSpace I x` is a semireducible def of `E`. -/
theorem metricInner_polarization (g : RiemannianMetric I M) (x : M) (u v : TangentSpace I x) :
    g.metricInner x u v
      = (g.metricInner x (u + v) (u + v) - g.metricInner x u u - g.metricInner x v v) / 2 := by
  have hc : g.metricInner x v u = g.metricInner x u v := g.metricInner_comm x v u
  simp only [g.metricInner_add_left, g.metricInner_add_right, hc]
  ring

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-- **Math.** **An additive map preserving squared norms preserves the inner product.**
If `L : T_qM → T_{q'}M'` is **additive** and `|L w|²_{q'} = |w|²_q` for every `w`, then
`⟨L u, L v⟩_{q'} = ⟨u,v⟩_q` for all `u, v`.

This is the step from the norm transfer
(`chartMetricInner_expDifferential_transfer_of_constantCurvature_of_speedSq`, which gives only
the diagonal `|df_q u| = |u|`) to `DCIsLocalIsometryAt`, which is stated with the full inner
product. Both sides are expanded with `metricInner_polarization` and matched using additivity
at `u + v`.

Additivity is essential: a norm-preserving *nonlinear* map need not preserve inner products.
In the application `L = df_q` is a continuous linear map, so `hadd` is free. -/
theorem metricInner_transfer_of_norm_transfer (g : RiemannianMetric I M)
    (g' : RiemannianMetric I' M') (q : M) (q' : M') (L : E → E)
    (hadd : ∀ u v : E, L (u + v) = L u + L v)
    (hnorm : ∀ w : E, g'.metricInner q' (L w) (L w) = g.metricInner q w w) (u v : E) :
    g'.metricInner q' (L u) (L v) = g.metricInner q u v := by
  have hLuv : L (u + v) = L u + L v := hadd u v
  calc g'.metricInner q' (L u) (L v)
      = (g'.metricInner q' (L u + L v) (L u + L v) - g'.metricInner q' (L u) (L u)
          - g'.metricInner q' (L v) (L v)) / 2 :=
        metricInner_polarization g' q' (L u : TangentSpace I' q') (L v)
    _ = (g'.metricInner q' (L (u + v)) (L (u + v)) - g'.metricInner q' (L u) (L u)
          - g'.metricInner q' (L v) (L v)) / 2 := by rw [hLuv]
    _ = (g.metricInner q (u + v) (u + v) - g.metricInner q u u - g.metricInner q v v) / 2 := by
        rw [hnorm (u + v), hnorm u, hnorm v]
    _ = g.metricInner q u v :=
        (metricInner_polarization g q (u : TangentSpace I q) v).symm

/-! ### `exp_p` is a `C^∞` local diffeomorphism away from conjugate points -/

/-- **Math.** **`exp_p` is a `C^∞` local diffeomorphism at a non-conjugate `v`.** If the
parameter `1` is not conjugate along `γ_v` — equivalently, no nontrivial Jacobi field along
`γ_v` vanishes at both ends — then `exp_p` is a `C^∞` local diffeomorphism at `v`.

This is the sign-free strengthening of `isLocalDiffeomorphAt_expMapGlobal_of_nonpos`
(`HadamardNonpos.lean`), which reaches the same conclusion only under `K ≤ 0`. That hypothesis
enters its proof at exactly one point — obtaining the differential isomorphism from
`expDifferential_isEquiv_of_nonpos` — so replacing that single input with
`expDifferential_isEquiv_of_not_conjugate` yields this version verbatim. The distinction
matters for do Carmo Ch. 8: `cor:dc-ch8-2-2` must handle spaces of **positive** constant
curvature, where `K ≤ 0` is unavailable but non-conjugacy still holds on a small enough ball.

Unlike the `HadamardNonpos.lean` original this carries **no** `hsmooth` hypothesis: the global
`C^∞` smoothness of `exp_p` is now unconditional (`contMDiff_expMapGlobal`).

With `IsLocalDiffeomorphAt` established, mathlib's `IsLocalDiffeomorphAt.localInverse` supplies
`exp_p⁻¹` together with its smoothness — so the `f = exp_{p̃} ∘ i ∘ exp_p⁻¹` of Cartan's theorem
can be assembled without hand-building the inverse.

Blueprint: `lem:dc-ch8-2-1-exp-local-diffeo`. -/
theorem isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) {v : E}
    (hnc : ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (fun w : E => expMapGlobal (I := I) g hg p w) v := by
  classical
  -- the ONLY line differing from `isLocalDiffeomorphAt_expMapGlobal_of_nonpos`: the
  -- differential isomorphism comes from non-conjugacy rather than from `K ≤ 0`
  obtain ⟨ζ, D, hζ, hFD⟩ := expDifferential_isEquiv_of_not_conjugate (I := I) g hg p hnc
  -- global smoothness of `exp_p` is unconditional since the Ch. 7 work
  have hsmooth : ContMDiff 𝓘(ℝ, E) I ∞ (fun w : E => expMapGlobal (I := I) g hg p w) :=
    Riemannian.Exponential.contMDiff_expMapGlobal g hg p
  set f : E → M := fun w : E => expMapGlobal (I := I) g hg p w with hfdef
  set gζ : E → E := fun w => extChartAt I ζ (f w) with hgζdef
  have hsrc : f v ∈ (extChartAt I ζ).source := by
    rw [extChartAt_source]; exact hζ
  set s : Set E := f ⁻¹' (extChartAt I ζ).source with hsdef
  have hs_open : IsOpen s :=
    hsmooth.continuous.isOpen_preimage _ (isOpen_extChartAt_source ζ)
  have hvs : v ∈ s := hsrc
  have hmaps : Set.MapsTo f s (chartAt H ζ).source := by
    intro w hw
    rw [← extChartAt_source (I := I)]; exact hw
  -- the target-chart reading of `exp_p` is `C^∞` on `s`
  have hgζ_cd : ContDiffOn ℝ ∞ gζ s := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_extChartAt (I := I) (x := ζ)).comp hsmooth.contMDiffOn hmaps
  -- and has the isomorphism `D` as its (strict, hence Fréchet) derivative at `v`
  have hFD' : HasFDerivAt gζ (D : E →L[ℝ] E) v := hFD.hasFDerivAt
  -- normed-space inverse function theorem: the reading is a local diffeomorphism at `v`
  have hg_ld : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ gζ v :=
    isLocalDiffeomorphAt_of_hasFDerivAt_equiv hs_open hvs hgζ_cd hFD'
  -- the chart inverse is a local diffeomorphism at `gζ v`
  have htgt : gζ v ∈ (extChartAt I ζ).target := PartialEquiv.map_source _ hsrc
  have hc2 : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (extChartAt I ζ).symm (gζ v) :=
    isLocalDiffeomorphAt_extChartAt_symm htgt
  have hcomp : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ ((extChartAt I ζ).symm ∘ gζ) v := hc2.comp hg_ld
  -- and `(extChartAt I ζ).symm ∘ gζ = exp_p` near `v`
  refine IsLocalDiffeomorphAt.congr_of_eventuallyEq hcomp ?_
  filter_upwards [hs_open.mem_nhds hvs] with w hw
  show f w = (extChartAt I ζ).symm (gζ w)
  exact ((extChartAt I ζ).left_inv hw).symm

end Riemannian.Jacobi

end
