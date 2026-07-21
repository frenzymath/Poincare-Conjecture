import DoCarmoLib.Riemannian.Jacobi.CartanFrameChartInterface

/-!
# do Carmo Ch. 8, Thm. 2.1 — the Jacobi norm transfer, at the manifold level

E. Cartan's theorem compares two Jacobi fields through their frame coefficients.  The
comparison itself (`chartMetricInner_transfer_of_jacobiCoef_match`) and the conversion of
E. Cartan's curvature hypothesis into the coefficient matching
(`jacobiCoef_match_of_curvatureFormAt`, `Jacobi/CartanFrameChartInterface.lean`) both live in
the chart, against a frame read there.  This file assembles them into a single **intrinsic**
statement — `|J̃(t)| = |J(t)|` between manifold Jacobi fields — by discharging every
chart-level hypothesis from manifold data.

## Why this is the variable-curvature route, and why it needs the frame

`metricInner_jacobiField_transfer_of_constantCurvature_of_speedSq`
(`Jacobi/JacobiConstCurvatureNorm.lean`) proves the same conclusion when `K ≡ K₀`, and it is
four lines, with no chart and no frame anywhere.  It can afford that because constant
curvature gives `|J(t)|²` a *closed form* in `(K₀, |γ'|², t)` and two scalar invariants: the
two manifolds are then compared by comparing numbers.

In variable curvature there is no closed form.  The only comparison available is **ODE
uniqueness on the coefficient system** — which forces a frame to write the coefficients in,
which forces the frame to be read in a chart, which is why the chart↔intrinsic interface had
to be built at all.  That is the whole architectural difference between the two routes.

## The discharge

Each chart hypothesis of the engine comes from existing manifold-level infrastructure:

| hypothesis | source |
|---|---|
| the two chart Jacobi fields | `IsJacobiFieldAlongOn.isJacobiFieldOn_of_mem_source` |
| `hepar`, `he` | `IsParallelFieldAlongOn.covariantDerivCoord_eq_zero` / `.differentiableAt_chartVectorRep` |
| `horth` | `metricInner_eq_chartMetricInner_rep` — the chart reading is norm-faithful |
| `hu`, `hRcont` | `IsGeodesicOn.differentiableAt_extChartAt`, `.continuousAt_deriv_extChartAt`, `continuousOn_chartCurvatureOp` |
| `hmem` | `extChartAt_mem_interior_target` |
| `hmatch` | `jacobiCoef_match_of_curvatureFormAt` — **E. Cartan's hypothesis** |

The window `Icc a b ⊆ Ioo a' b'` is load-bearing rather than cosmetic: `covariantDerivCoord`
is a two-sided derivative while a parallel field's chart certificate is one-sided, so the
frame must be run on an interval strictly larger than the one the conclusion is read on.

## Contents

* `metricInner_jacobiField_transfer_of_curvatureFormAt` — the transfer.

## Scope

The geodesics are required to stay in one chart source each (`hsrc`, `hsrcbar`), and `φ` is
taken as abstract data satisfying E. Cartan's hypothesis.  Discharging the single-chart
hypothesis for the geodesics of a normal neighbourhood is the remaining obligation of
`thm:dc-ch8-2-1`, tracked at `lem:dc-ch8-2-1-single-chart`.

Blueprint: `lem:dc-ch8-2-1-jacobi-norm-transfer-manifold`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8, Thm. 2.1.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-- **Math.** **do Carmo Ch. 8, Thm. 2.1 — the Jacobi norm transfer in variable curvature,
intrinsically.**

Let `γ`, `γ̃` be geodesics on `[a', b']`, each staying in the source of one chart, let
`Efr`, `Ebar` be parallel orthonormal frames along them, and let `φ_t` carry velocity to
velocity, frame to frame, and the curvature form to the curvature form (**E. Cartan's
hypothesis**).  If two Jacobi fields have the same frame data at `a`, then

  `|J̃(t)| = |J(t)|`  for all `t ∈ [a, b]`,

with `[a,b]` interior to `[a',b']`.

This is the intrinsic form of the analytic heart of `thm:dc-ch8-2-1`, and the variable-curvature
counterpart of `metricInner_jacobiField_transfer_of_constantCurvature_of_speedSq` — which had
to bypass the frame entirely, since it compares the two sides through a closed-form solution
that only exists when `K` is constant.  Here there is no closed form: the comparison runs ODE
uniqueness on the coefficient system, which is what forces the frame, and hence the
chart↔intrinsic interface `jacobiCoef_match_of_curvatureFormAt`.

The window `Icc a b ⊆ Ioo a' b'` is not cosmetic: the parallel frame's chart flatness is a
two-sided derivative statement, so the frame must be run on a strictly larger interval than
the one the conclusion is read on. -/
theorem metricInner_jacobiField_transfer_of_curvatureFormAt
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M') (α : M) (α' : M')
    {γ : ℝ → M} {γbar : ℝ → M'} {a' b' : ℝ}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a' b'))
    (hγc : ∀ t ∈ Icc a' b', ContinuousAt γ t)
    (hgeobar : IsGeodesicOn (I := I') g' γbar (Icc a' b'))
    (hγcbar : ∀ t ∈ Icc a' b', ContinuousAt γbar t)
    (hsrc : ∀ t ∈ Icc a' b', γ t ∈ (chartAt H α).source)
    (hsrcbar : ∀ t ∈ Icc a' b', γbar t ∈ (chartAt H' α').source)
    (Efr Ebar : ι → ℝ → E)
    (hEpar : ∀ k, IsParallelFieldAlongOn (I := I) g γ (Efr k) a' b')
    (hEbarpar : ∀ k, IsParallelFieldAlongOn (I := I') g' γbar (Ebar k) a' b')
    (hEorth : ∀ t ∈ Icc a' b', ∀ k l,
      g.metricInner (γ t) (Efr k t : TangentSpace I (γ t)) (Efr l t)
        = if k = l then (1 : ℝ) else 0)
    (hEbarorth : ∀ t ∈ Icc a' b', ∀ k l,
      g'.metricInner (γbar t) (Ebar k t : TangentSpace I' (γbar t)) (Ebar l t)
        = if k = l then (1 : ℝ) else 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    (φ : ℝ → E → E)
    (hvel : ∀ t ∈ Icc a' b', φ t (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = mfderiv 𝓘(ℝ, ℝ) I' γbar t 1)
    (hfr : ∀ t ∈ Icc a' b', ∀ k, φ t (Efr k t) = Ebar k t)
    (hφ : ∀ t ∈ Icc a' b', ∀ x y z w : TangentSpace I (γ t),
      g.leviCivitaConnection.curvatureFormAt g (γ t) x y z w
        = g'.leviCivitaConnection.curvatureFormAt g' (γbar t)
            (φ t x) (φ t y) (φ t z) (φ t w))
    (J DJ : ℝ → E) (hJF : IsJacobiFieldAlongOn (I := I) g γ J DJ a' b')
    (Jbar DJbar : ℝ → E) (hJFbar : IsJacobiFieldAlongOn (I := I') g' γbar Jbar DJbar a' b')
    {a b : ℝ} (hsub : Icc a b ⊆ Ioo a' b')
    (hF0 : ∀ k, g'.metricInner (γbar a) (Jbar a : TangentSpace I' (γbar a)) (Ebar k a)
      = g.metricInner (γ a) (J a : TangentSpace I (γ a)) (Efr k a))
    (hV0 : ∀ k, g'.metricInner (γbar a) (DJbar a : TangentSpace I' (γbar a)) (Ebar k a)
      = g.metricInner (γ a) (DJ a : TangentSpace I (γ a)) (Efr k a))
    {t : ℝ} (ht : t ∈ Icc a b) :
    g'.metricInner (γbar t) (Jbar t : TangentSpace I' (γbar t)) (Jbar t)
      = g.metricInner (γ t) (J t : TangentSpace I (γ t)) (J t) := by
  classical
  have hsub' : Icc a b ⊆ Icc a' b' := hsub.trans Ioo_subset_Icc_self
  have hamem : a ∈ Icc a b := left_mem_Icc.2 (le_trans ht.1 ht.2)
  -- the whole `[a',b']` is a neighbourhood of every point of `[a,b]`
  have hnhds : ∀ s ∈ Icc a b, Icc a' b' ∈ 𝓝 s := fun s hs =>
    Icc_mem_nhds (hsub hs).1 (hsub hs).2
  set u : ℝ → E := fun τ => extChartAt I α (γ τ) with hu_def
  set ubar : ℝ → E := fun τ => extChartAt I' α' (γbar τ) with hubar_def
  set e : ι → ℝ → E := fun m => chartVectorRep (I := I) γ α (Efr m) with he_def
  set ebar : ι → ℝ → E := fun m => chartVectorRep (I := I') γbar α' (Ebar m) with hebar_def
  -- ### chart-level regularity on `M`
  have hu : ∀ s ∈ Icc a b, DifferentiableAt ℝ u s := fun s hs =>
    hgeo.differentiableAt_extChartAt (hsub' hs) (hγc s (hsub' hs)) (hsrc s (hsub' hs))
  have hmem : ∀ s ∈ Icc a b, u s ∈ interior (extChartAt I α).target := fun s hs =>
    extChartAt_mem_interior_target (I := I) (hsrc s (hsub' hs))
  have hmemT : ∀ s ∈ Icc a b, u s ∈ (extChartAt I α).target := fun s hs =>
    interior_subset (hmem s hs)
  have hG : ∀ s ∈ Icc a b, ∀ p q, DifferentiableAt ℝ (chartGramOnE (I := I) g α p q) (u s) :=
    fun s hs p q => differentiableAt_chartGramOnE (I := I) g α (hmemT s hs) p q
  have hbase : ∀ s ∈ Icc a b,
      (extChartAt I α).symm (u s) ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    fun s hs => symm_extChartAt_mem_baseSet (I := I) (hsrc s (hsub' hs))
  have he : ∀ m, ∀ s ∈ Icc a b, DifferentiableAt ℝ (e m) s := fun m s hs =>
    (hEpar m).differentiableAt_chartVectorRep hgeo hγc subset_rfl hsrc (hnhds s hs)
  have hepar : ∀ m, ∀ s ∈ Icc a b, covariantDerivCoord (I := I) g α u (e m) s = 0 :=
    fun m s hs => (hEpar m).covariantDerivCoord_eq_zero hgeo hγc subset_rfl hsrc (hnhds s hs)
  have horth : ∀ s ∈ Icc a b, ∀ k l,
      chartMetricInner (I := I) g α (u s) (e k s) (e l s) = if k = l then (1 : ℝ) else 0 :=
    fun s hs k l => by
      rw [← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc s (hsub' hs)) (Efr k) (Efr l)]
      exact hEorth s (hsub' hs) k l
  -- ### chart-level regularity on `M̃`
  have hubar : ∀ s ∈ Icc a b, DifferentiableAt ℝ ubar s := fun s hs =>
    hgeobar.differentiableAt_extChartAt (hsub' hs) (hγcbar s (hsub' hs)) (hsrcbar s (hsub' hs))
  have hmembar : ∀ s ∈ Icc a b, ubar s ∈ interior (extChartAt I' α').target := fun s hs =>
    extChartAt_mem_interior_target (I := I') (hsrcbar s (hsub' hs))
  have hGbar : ∀ s ∈ Icc a b, ∀ p q,
      DifferentiableAt ℝ (chartGramOnE (I := I') g' α' p q) (ubar s) :=
    fun s hs p q => differentiableAt_chartGramOnE (I := I') g' α'
      (interior_subset (hmembar s hs)) p q
  have hbasebar : ∀ s ∈ Icc a b,
      (extChartAt I' α').symm (ubar s) ∈ (trivializationAt E (TangentSpace I') α').baseSet :=
    fun s hs => symm_extChartAt_mem_baseSet (I := I') (hsrcbar s (hsub' hs))
  have hebar : ∀ m, ∀ s ∈ Icc a b, DifferentiableAt ℝ (ebar m) s := fun m s hs =>
    (hEbarpar m).differentiableAt_chartVectorRep hgeobar hγcbar subset_rfl hsrcbar (hnhds s hs)
  have heparbar : ∀ m, ∀ s ∈ Icc a b,
      covariantDerivCoord (I := I') g' α' ubar (ebar m) s = 0 :=
    fun m s hs =>
      (hEbarpar m).covariantDerivCoord_eq_zero hgeobar hγcbar subset_rfl hsrcbar (hnhds s hs)
  have horthbar : ∀ s ∈ Icc a b, ∀ k l,
      chartMetricInner (I := I') g' α' (ubar s) (ebar k s) (ebar l s)
        = if k = l then (1 : ℝ) else 0 :=
    fun s hs k l => by
      rw [← metricInner_eq_chartMetricInner_rep (I := I') g' (hsrcbar s (hsub' hs))
        (Ebar k) (Ebar l)]
      exact hEbarorth s (hsub' hs) k l
  -- ### continuity, to run ODE uniqueness
  have hucont : ContinuousOn u (Icc a b) := fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hu'cont : ContinuousOn (deriv u) (Icc a b) := fun s hs =>
    (hgeo.continuousAt_deriv_extChartAt (hsub' hs) (hγc s (hsub' hs))
      (hsrc s (hsub' hs))).continuousWithinAt
  have hRcont : ContinuousOn (chartCurvatureOp (I := I) g α u) (Icc a b) :=
    continuousOn_chartCurvatureOp (I := I) g α u hucont hu'cont hmem
  have hecont : ∀ m, ContinuousOn (e m) (Icc a b) := fun m s hs =>
    (he m s hs).continuousAt.continuousWithinAt
  have hGcont : ∀ p q, ContinuousOn (fun s => chartGramOnE (I := I) g α p q (u s)) (Icc a b) :=
    fun p q s hs => ((hG s hs p q).continuousAt.comp_continuousWithinAt
      (hucont s hs))
  -- ### the two chart Jacobi fields
  have hJFchart : IsJacobiFieldOn (I := I) g α u (chartVectorRep (I := I) γ α J)
      (chartVectorRep (I := I) γ α DJ) a' b' :=
    hJF.isJacobiFieldOn_of_mem_source hgeo hγc subset_rfl hsrc
  have hJFchartbar : IsJacobiFieldOn (I := I') g' α' ubar (chartVectorRep (I := I') γbar α' Jbar)
      (chartVectorRep (I := I') γbar α' DJbar) a' b' :=
    hJFbar.isJacobiFieldOn_of_mem_source hgeobar hγcbar subset_rfl hsrcbar
  -- ### `hmatch`: E. Cartan's hypothesis, through the frame/chart interface
  have hmatch : ∀ s ∈ Icc a b, ∀ k l,
      jacobiCoef (I := I) g α u (chartCurvatureOp (I := I) g α u) e k l s
        = jacobiCoef (I := I') g' α' ubar (chartCurvatureOp (I := I') g' α' ubar) ebar k l s :=
    fun s hs k l => jacobiCoef_match_of_curvatureFormAt (I := I) (I' := I') g g' α α'
      hgeo hγc hgeobar hγcbar hsrc hsrcbar Efr Ebar φ hvel hfr hφ (hsub' hs) k l
  -- ### matching initial frame data, read in the charts
  have hF0' : frameCoeff (I := I) g α u e (chartVectorRep (I := I) γ α J) a
      = frameCoeff (I := I') g' α' ubar ebar (chartVectorRep (I := I') γbar α' Jbar) a := by
    funext k
    rw [frameCoeff_apply, frameCoeff_apply,
      ← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc a (hsub' hamem)) J (Efr k),
      ← metricInner_eq_chartMetricInner_rep (I := I') g' (hsrcbar a (hsub' hamem)) Jbar (Ebar k)]
    exact (hF0 k).symm
  have hV0' : frameCoeff (I := I) g α u e (chartVectorRep (I := I) γ α DJ) a
      = frameCoeff (I := I') g' α' ubar ebar (chartVectorRep (I := I') γbar α' DJbar) a := by
    funext k
    rw [frameCoeff_apply, frameCoeff_apply,
      ← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc a (hsub' hamem)) DJ (Efr k),
      ← metricInner_eq_chartMetricInner_rep (I := I') g' (hsrcbar a (hsub' hamem)) DJbar
        (Ebar k)]
    exact (hV0 k).symm
  -- ### run the engine, then read the chart norms back as intrinsic norms
  have hkey := chartMetricInner_transfer_of_jacobiCoef_match (I := I) (I' := I') g g' α α'
    u (chartVectorRep (I := I) γ α J) (chartVectorRep (I := I) γ α DJ) e
    ubar (chartVectorRep (I := I') γbar α' Jbar) (chartVectorRep (I := I') γbar α' DJbar) ebar
    hsub hJFchart hJFchartbar hu hmem hG hbase he hepar horth
    hubar hmembar hGbar hbasebar hebar heparbar horthbar hcard hRcont hecont hGcont
    hmatch hF0' hV0' ht
  rw [metricInner_eq_chartMetricInner_rep (I := I') g' (hsrcbar t (hsub' ht)) Jbar Jbar,
    metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t (hsub' ht)) J J]
  exact hkey

end Riemannian.Jacobi

end
