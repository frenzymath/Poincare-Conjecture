import DoCarmoLib.Riemannian.Jacobi.CartanCurvatureBridge
import DoCarmoLib.Riemannian.Jacobi.JacobiFrameCoefficients
import DoCarmoLib.Riemannian.Jacobi.CartanParallelFrame
import DoCarmoLib.Riemannian.Jacobi.JacobiVelocityField
import DoCarmoLib.Riemannian.Jacobi.JacobiConstantCurvatureConjugate

/-!
# do Carmo Ch. 8, Thm. 2.1 — the frame/chart interface

E. Cartan's theorem compares two Jacobi fields by putting their **frame coefficients** into
the same scalar ODE.  Two halves of that comparison were already built and are `\leanok`:

* the **analytic engine**, `chartMetricInner_transfer_of_jacobiCoef_match`
  (`Jacobi/JacobiFrameCoefficients.lean`): matching coefficient matrices ⟹ equal Jacobi
  norms, by ODE uniqueness.  It asks for its hypothesis `hmatch` between the **chart** frame
  coefficients `jacobiCoef … (chartCurvatureOp g α u) e i j t`, with `e` a parallel
  orthonormal frame *in one fixed chart* and the velocity appearing as `deriv u t`.
* the **curvature conversion**, `chartMetricInner_chartCurvatureEndo_transfer_of_curvatureFormAt`
  (`Jacobi/CartanCurvatureBridge.lean`): E. Cartan's intrinsic hypothesis (the curvature forms
  correspond under `φ`) ⟹ the chart-read coefficients agree — but with each vector presented
  as `tangentCoordChange I q α q ·`, the chart reading of an **intrinsic** tangent vector *at
  its own foot*, and with `φ`-images in the other slots.

Unifying the two was the residual of `thm:dc-ch8-2-1`.  This file does that.

## The three identifications, and why they are cheap

* **The frame vectors.**  Instantiate the chart frame as `chartVectorRep γ α (Efr k)` for an
  *intrinsic* frame `Efr`.  Since `chartVectorRep γ α J τ` is *by definition*
  `tangentCoordChange I (γ τ) α (γ τ) (J τ)`, the conversion's own-foot reading **is** the
  frame vector, by `rfl`.  The identification is a choice of representation, not a rewrite.
* **The velocity.**  `chartVectorRep_velocity` (`Jacobi/JacobiVelocityField.lean`) already
  says `deriv u t` **is** the own-foot chart reading of `γ'(t)` — exactly the slot the
  conversion fills.
* **The curvature layer.**  `chartCurvatureOp` (along a curve, what the ODE consumes) and
  `chartCurvatureEndo` (pointwise, what the conversion speaks) both normalize to
  `chartCurvature`, but nothing said so; `chartCurvatureOp_eq_chartCurvatureEndo` below does.

do Carmo's `e_n = γ'` is **not** among them: he writes the coefficients as
`⟨R(e_n, e_i)e_n, e_j⟩`, but `jacobiCoef` contracts the curvature with `deriv u t` *inside*
`chartCurvatureOp` and never with a frame member, so `e_n = γ'` is not needed.  Nor is
orthonormality: nothing here constrains the frames beyond `φ_t` carrying one to the other.
(Orthonormality is needed by the *consumer*, `chartMetricInner_transfer_of_jacobiCoef_match`,
which reads the Jacobi norm off the coefficients — it just is not needed to match them.)

## Contents

* `chartCurvatureOp_eq_chartCurvatureEndo` — the two chart curvature layers agree.
* `extChartAt_mem_interior_target` — a point of the chart source reads into the chart
  target's interior (`I.Boundaryless`), the side condition the layer identification needs.
* `jacobiCoef_match_of_curvatureFormAt` — **the interface**, for an arbitrary family `φ_t`
  carrying velocity to velocity and frame to frame: E. Cartan's hypothesis ⟹ `hmatch`.
* `jacobiCoef_match_of_curvatureFormAt_parallelTransportConjugate` — the same at do Carmo's
  own `φ_t = P̃_t ∘ i ∘ P_t⁻¹`, where the two structural hypotheses become theorems.

## Scope

Both statements take the single-chart hypotheses `hsrc`/`hsrcbar` (each geodesic stays in
one chart source) as **hypotheses**.  Discharging them for the geodesics of a normal
neighbourhood `V` of `thm:dc-ch8-2-1` — which need not lie in one `ChartedSpace` chart — is a
separate chart-chaining obligation, tracked as its own blueprint node.

Blueprint: `lem:dc-ch8-2-1-frame-chart-interface`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8, Thm. 2.1.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential Riemannian.Tensor

-- NOTE: this variable block mirrors `Jacobi/JacobiSectionalCurvature.lean` and
-- `Jacobi/CartanCurvatureBridge.lean` exactly (`MetricSpace M`, and `CompleteSpace E` left to
-- instance search via finite-dimensionality): any divergence makes the instances diamond.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ### The two chart curvature layers -/

/-- **Math.** **The Jacobi-equation curvature operator is the pointwise chart Jacobi
operator**, contracted at the chart velocity: `chartCurvatureOp g α u t = ℛ(·, u̇)u̇`.

`chartCurvatureOp` (the along-a-curve layer, which the Jacobi ODE consumes) and
`chartCurvatureEndo` (the pointwise layer, which the intrinsic curvature bridge
`chartMetricInner_chartCurvatureEndo_eq_curvatureFormAt` speaks) both normalize to
`chartCurvature`; this states that they agree. -/
theorem chartCurvatureOp_eq_chartCurvatureEndo (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) (t : ℝ) (w : E) (hy : u t ∈ interior (extChartAt I α).target) :
    chartCurvatureOp (I := I) g α u t w
      = chartCurvatureEndo (I := I) g α (u t) (deriv u t) w := by
  rw [chartCurvatureOp_eq_chartCurvature (I := I) g α u t w hy]
  rfl

/-- **Math.** The chart-`α` reading of a geodesic stays in the interior of the chart target,
whenever its foot lies in the chart source.  (`I.Boundaryless` makes the target open.) -/
theorem extChartAt_mem_interior_target {α : M} {x : M} (hx : x ∈ (chartAt H α).source) :
    extChartAt I α x ∈ interior (extChartAt I α).target := by
  rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
  exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact hx)

/-! ### E. Cartan's hypothesis discharges `hmatch`, in the frame/chart form the ODE needs -/

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-- **Math.** **do Carmo Ch. 8, Thm. 2.1 — the frame/chart interface** (blueprint
`lem:dc-ch8-2-1-frame-chart-interface`).

Let `γ`, `γ̃` be geodesics staying in the sources of the fixed charts at `α`, `α'`, let
`Efr`, `Ebar` be *intrinsic* own-foot frames along them, and let `φ_t` be any family of maps
`T_{γ(t)}M → T_{γ̃(t)}M̃` under which

* the curvature forms correspond (`hφ` — **E. Cartan's hypothesis**),
* the velocity goes to the velocity (`hvel`),
* the frame goes to the frame (`hfr`).

Then the **chart frame coefficients agree**: `hmatch` of
`chartMetricInner_transfer_of_jacobiCoef_match`, for the chart readings of these intrinsic
frames.  This is the single point at which E. Cartan's curvature hypothesis is consumed, and
it closes the chart↔intrinsic interface that was the residual of `thm:dc-ch8-2-1`.

`φ` is arbitrary data: no linearity, continuity or isometry is used, and no
parallel-transport theory appears — mirroring the deliberate generality of
`chartMetricInner_chartCurvatureEndo_transfer_of_curvatureFormAt`.  The instantiation
`φ = φ_t` is `jacobiCoef_match_of_curvatureFormAt_parallelTransportConjugate`.

**The frames are not required to contain the velocity.** do Carmo writes the coefficients as
`⟨R(e_n, e_i)e_n, e_j⟩` with `e_n = γ'`, but `jacobiCoef` contracts the curvature with
`deriv u t` *inside* `chartCurvatureOp` and never with a frame member, so `e_n = γ'` is not
needed here. -/
theorem jacobiCoef_match_of_curvatureFormAt
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M') (α : M) (α' : M')
    {γ : ℝ → M} {γbar : ℝ → M'} {a b : ℝ}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hgeobar : IsGeodesicOn (I := I') g' γbar (Icc a b))
    (hγcbar : ∀ t ∈ Icc a b, ContinuousAt γbar t)
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H α).source)
    (hsrcbar : ∀ t ∈ Icc a b, γbar t ∈ (chartAt H' α').source)
    (Efr Ebar : ι → ℝ → E) (φ : ℝ → E → E)
    (hvel : ∀ t ∈ Icc a b, φ t (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = mfderiv 𝓘(ℝ, ℝ) I' γbar t 1)
    (hfr : ∀ t ∈ Icc a b, ∀ k, φ t (Efr k t) = Ebar k t)
    (hφ : ∀ t ∈ Icc a b, ∀ x y z w : TangentSpace I (γ t),
      g.leviCivitaConnection.curvatureFormAt g (γ t) x y z w
        = g'.leviCivitaConnection.curvatureFormAt g' (γbar t)
            (φ t x) (φ t y) (φ t z) (φ t w))
    {t : ℝ} (ht : t ∈ Icc a b) (k l : ι) :
    jacobiCoef (I := I) g α (fun τ => extChartAt I α (γ τ))
        (chartCurvatureOp (I := I) g α (fun τ => extChartAt I α (γ τ)))
        (fun m => chartVectorRep (I := I) γ α (Efr m)) k l t
      = jacobiCoef (I := I') g' α' (fun τ => extChartAt I' α' (γbar τ))
        (chartCurvatureOp (I := I') g' α' (fun τ => extChartAt I' α' (γbar τ)))
        (fun m => chartVectorRep (I := I') γbar α' (Ebar m)) k l t := by
  classical
  have htsrc : γ t ∈ (chartAt H α).source := hsrc t ht
  have htsrcbar : γbar t ∈ (chartAt H' α').source := hsrcbar t ht
  -- the chart readings stay in the chart interior, so the `Op = Endo` identification applies
  have hy : (fun τ => extChartAt I α (γ τ)) t ∈ interior (extChartAt I α).target :=
    extChartAt_mem_interior_target (I := I) htsrc
  have hybar : (fun τ => extChartAt I' α' (γbar τ)) t ∈ interior (extChartAt I' α').target :=
    extChartAt_mem_interior_target (I := I') htsrcbar
  -- `deriv u t` IS the own-foot chart reading of `γ'(t)`
  have hvc : tangentCoordChange I (γ t) α (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
      = deriv (fun τ => extChartAt I α (γ τ)) t :=
    chartVectorRep_velocity (I := I) g α (hgeo.hasGeodesicEquationAt ht) (hγc t ht) htsrc
  have hvcbar : tangentCoordChange I' (γbar t) α' (γbar t) (mfderiv 𝓘(ℝ, ℝ) I' γbar t 1)
      = deriv (fun τ => extChartAt I' α' (γbar τ)) t :=
    chartVectorRep_velocity (I := I') g' α' (hgeobar.hasGeodesicEquationAt ht) (hγcbar t ht)
      htsrcbar
  -- unfold both `jacobiCoef`s into the pointwise `Endo` layer at the own-foot readings
  rw [jacobiCoef, jacobiCoef, chartCurvatureOp_eq_chartCurvatureEndo (I := I) g α _ t _ hy,
    chartCurvatureOp_eq_chartCurvatureEndo (I := I') g' α' _ t _ hybar, ← hvc, ← hvcbar]
  -- the frames appear as `chartVectorRep`; the bridge speaks the unfolded own-foot reading
  simp only [chartVectorRep_apply]
  -- now this is exactly E. Cartan's hypothesis, converted
  have hkey := chartMetricInner_chartCurvatureEndo_transfer_of_curvatureFormAt (I := I) (I' := I')
    g g' α α' htsrc htsrcbar (φ t) (hφ t ht) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (Efr k t) (Efr l t)
  rw [hkey, hvel t ht, hfr t ht k, hfr t ht l]

/-- **Math.** **The frame/chart interface for do Carmo's `φ_t = P̃_t ∘ i ∘ P_t⁻¹`.**

The instantiation of `jacobiCoef_match_of_curvatureFormAt` at the parallel-transport
conjugate.  Its two structural hypotheses become theorems:

* `hvel` — the velocity of a geodesic is parallel along it, on both sides, and the seeds
  match by `hvseed : γ̃'(a) = i(γ'(a))`, so `φ_t(γ'(t)) = γ̃'(t)` by
  `eq_parallelTransportConjugate_of_isParallelFieldAlongOn`;
* `hfr` — the same lemma applied to the frames, whose seeds match by `hEseed`; this is do
  Carmo's `ẽⱼ(t) = φ_t(eⱼ(t))`.

The frames and seeds are exactly what `exists_transportedParallelOrthoFrame_pair` produces. -/
theorem jacobiCoef_match_of_curvatureFormAt_parallelTransportConjugate
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M') (α : M) (α' : M')
    {γ : ℝ → M} {γbar : ℝ → M'} {a b : ℝ} {hab : a < b}
    {hgeo : IsGeodesicOn (I := I) g γ (Icc a b)}
    {hγc : ∀ t ∈ Icc a b, ContinuousAt γ t}
    {hgeobar : IsGeodesicOn (I := I') g' γbar (Icc a b)}
    {hγcbar : ∀ t ∈ Icc a b, ContinuousAt γbar t}
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H α).source)
    (hsrcbar : ∀ t ∈ Icc a b, γbar t ∈ (chartAt H' α').source)
    (i : E →ₗ[ℝ] E) (Efr Ebar : ι → ℝ → E)
    (hEpar : ∀ k, IsParallelFieldAlongOn (I := I) g γ (Efr k) a b)
    (hEbarpar : ∀ k, IsParallelFieldAlongOn (I := I') g' γbar (Ebar k) a b)
    (hEseed : ∀ k, Ebar k a = i (Efr k a))
    (hvseed : mfderiv 𝓘(ℝ, ℝ) I' γbar a 1 = i (mfderiv 𝓘(ℝ, ℝ) I γ a 1))
    (hφ : ∀ t, ∀ ht : t ∈ Icc a b, ∀ x y z w : TangentSpace I (γ t),
      g.leviCivitaConnection.curvatureFormAt g (γ t) x y z w
        = g'.leviCivitaConnection.curvatureFormAt g' (γbar t)
            (parallelTransportConjugate (I := I) (I' := I') hab hgeo hγc hgeobar hγcbar i ht x)
            (parallelTransportConjugate (I := I) (I' := I') hab hgeo hγc hgeobar hγcbar i ht y)
            (parallelTransportConjugate (I := I) (I' := I') hab hgeo hγc hgeobar hγcbar i ht z)
            (parallelTransportConjugate (I := I) (I' := I') hab hgeo hγc hgeobar hγcbar i ht w))
    {t : ℝ} (ht : t ∈ Icc a b) (k l : ι) :
    jacobiCoef (I := I) g α (fun τ => extChartAt I α (γ τ))
        (chartCurvatureOp (I := I) g α (fun τ => extChartAt I α (γ τ)))
        (fun m => chartVectorRep (I := I) γ α (Efr m)) k l t
      = jacobiCoef (I := I') g' α' (fun τ => extChartAt I' α' (γbar τ))
        (chartCurvatureOp (I := I') g' α' (fun τ => extChartAt I' α' (γbar τ)))
        (fun m => chartVectorRep (I := I') γbar α' (Ebar m)) k l t := by
  classical
  -- `φ_t` needs `t ∈ Icc a b` as an argument; package it as bare data off the window
  set φ : ℝ → E → E := fun s w =>
    if hs : s ∈ Icc a b then
      parallelTransportConjugate (I := I) (I' := I') hab hgeo hγc hgeobar hγcbar i hs w
    else 0 with hφdef
  have hφval : ∀ s, ∀ hs : s ∈ Icc a b, ∀ w : E,
      φ s w
        = parallelTransportConjugate (I := I) (I' := I') hab hgeo hγc hgeobar hγcbar i hs w := by
    intro s hs w
    simp only [hφdef, dif_pos hs]
  refine jacobiCoef_match_of_curvatureFormAt (I := I) (I' := I') g g' α α' hgeo hγc hgeobar
    hγcbar hsrc hsrcbar Efr Ebar φ ?_ ?_ ?_ ht k l
  · -- `hvel`: both velocities are parallel, and their seeds match by `hvseed`
    intro s hs
    rw [hφval s hs]
    exact (eq_parallelTransportConjugate_of_isParallelFieldAlongOn (I := I) (I' := I')
      (isParallelFieldAlongOn_velocity (I := I) g hab hgeo hγc)
      (isParallelFieldAlongOn_velocity (I := I') g' hab hgeobar hγcbar) hvseed hs).symm
  · -- `hfr`: do Carmo's `ẽⱼ(t) = φ_t(eⱼ(t))`
    intro s hs m
    rw [hφval s hs]
    exact (eq_parallelTransportConjugate_of_isParallelFieldAlongOn (I := I) (I' := I')
      (hEpar m) (hEbarpar m) (hEseed m) hs).symm
  · -- `hφ`: E. Cartan's hypothesis, at the packaged `φ`
    intro s hs x y z w
    rw [hφval s hs, hφval s hs, hφval s hs, hφval s hs]
    exact hφ s hs x y z w

end Riemannian.Jacobi

end
