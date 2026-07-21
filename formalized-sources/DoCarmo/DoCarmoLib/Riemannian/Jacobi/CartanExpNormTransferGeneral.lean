import DoCarmoLib.Riemannian.Jacobi.CartanJacobiTransferManifold
import DoCarmoLib.Riemannian.Jacobi.CartanMFDerivBridge
import DoCarmoLib.Riemannian.Jacobi.JacobiInteriorData

/-!
# do Carmo Ch. 8, Thm. 2.1 — the exp-side chain, in **variable** curvature

`Jacobi/CartanExpNormTransfer.lean` and `Jacobi/CartanMFDerivBridge.lean` run the chain

  Jacobi norm transfer  ⟶  `|d(exp_p)_v Z|` transfer  ⟶  `df_q` preserves the metric

against `metricInner_jacobiField_transfer_of_constantCurvature_of_speedSq`, i.e. only when
`M` and `M̃` share a *constant* curvature `K₀`.  This file re-runs the same three steps
against `metricInner_jacobiField_transfer_of_curvatureFormAt`
(`Jacobi/CartanJacobiTransferManifold.lean`), the **variable**-curvature transfer, whose
input is E. Cartan's hypothesis on `φ_t` rather than a shared `K₀`.

## What changes, and why the interior seed is needed

The constant-curvature transfer reads the two Jacobi fields on `[0, 1]` and seeds them at the
**left endpoint** `0`, which is exactly what `exists_isJacobiFieldAlongOn` produces.  The
variable-curvature transfer cannot do that: its parallel frames carry a two-sided chart
flatness certificate, so it needs the fields on an outer window `[a', b']` with
`[0,1] ⊆ (a', b')`, while `cor:dc-ch5-2-5` still pins them by their data at `0` — now an
**interior** time.  `exists_isJacobiFieldAlongOn_at` (`Jacobi/JacobiInteriorData.lean`)
supplies precisely that, and it is the only new analytic input here; the fields are then cut
back to `[0,1]` with `IsJacobiFieldAlongOn.mono` to meet the exp-side clause.

The other change is do Carmo's normalization `φ_0 = i` (`hφ0`).  It is what makes the initial
frame data match: `Ẽ_k(0) = φ_0(E_k(0)) = i(E_k(0))`, so `⟨iZ, Ẽ_k(0)⟩_{p̃} = ⟨Z, E_k(0)⟩_p`
because `i` is a linear isometry.  No orthonormality of the frames and no particular seeding
of them is used for this step — the frames may be seeded anywhere on `[a', b']`.

Nothing here needs a speed or nondegeneracy hypothesis on `v`: unlike the constant-curvature
route, the variable-curvature transfer is not routed through a closed-form solution
parametrized by `K₀|γ'|²`, so `speedSq` and `v ≠ 0` never appear.

## What is **not** discharged here

* **The single-chart hypotheses.**  `hsrc` / `hsrcbar` — that each geodesic stays in the
  source of one chart on the whole outer window — are carried as hypotheses and are *not*
  proved anywhere in this file.  They are a real remaining obligation of `thm:dc-ch8-2-1`,
  tracked at `lem:dc-ch8-2-1-single-chart`.
* **Non-conjugacy.**  `hnc` / `hnc'` are **hypotheses**, not theorems.  In constant curvature
  they are produced from a numerical condition by
  `not_isConjugatePointAt_globalGeodesic_of_constantCurvature_of_lt_pi`; that producer has no
  variable-curvature analogue and none is invented here.
* **`φ` itself.**  `φ`, `hvel`, `hfr`, `hφ` are abstract data, exactly as in
  `metricInner_jacobiField_transfer_of_curvatureFormAt`; the frames and their parallelism and
  orthonormality are likewise hypotheses.

## Contents

* `chartMetricInner_expDifferential_transfer_of_curvatureFormAt` — the norm transfer for the
  chart-read differential of `exp`: `|d(exp_{p̃})_{iv}(iZ)| = |d(exp_p)_v(Z)|`, measured with
  the chart Gram form at the two endpoints.
* `metricInner_mfderiv_expMapGlobal_transfer_of_curvatureFormAt` — the same, intrinsically,
  with `mfderiv` in place of the chart-read `D`.
* `metricInner_mfderiv_eq_of_semiconjugacy_of_curvatureFormAt` — the composition: any `f`
  differentiable at `q = exp_p(v)` and semiconjugating `exp_p` to `exp_{p̃}` through `i` near
  `v` preserves the metric at `q`.

Blueprint: `lem:dc-ch8-2-1-exp-norm-transfer-general`.

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

/-! ### The norm transfer for the chart-read exponential differential -/

/-- **Math.** **do Carmo Ch. 8, `thm:dc-ch8-2-1` — the norm-preservation step at the level of
the exponential differential, in variable curvature.**

Let `γ_v` and `γ_{iv}` be the global geodesics of `v ∈ T_pM` and `iv ∈ T_{p̃}M̃`, each staying
in one chart source on a window `[a', b']` with `a' < 0` and `1 < b'`.  Let `E_k`, `Ẽ_k` be
parallel orthonormal frames along them, and let `φ_t` carry velocity to velocity, frame to
frame, and the curvature form to the curvature form (**E. Cartan's hypothesis**), with do
Carmo's normalization `φ_0 = i` for a linear isometry `i`.  Then

  `|d(exp_{p̃})_{iv}(iZ)| = |d(exp_p)_v(Z)|`,

measured with the chart Gram form at the respective endpoints.

Proof.  `cor:dc-ch5-2-5` identifies each side with the endpoint norm of a Jacobi field with
data `(0, Z)` resp. `(0, iZ)` at time `0` — data at an **interior** time of `[a', b']`, which
is why `exists_isJacobiFieldAlongOn_at` is needed to produce the fields on the whole outer
window; `IsJacobiFieldAlongOn.mono` cuts them back to `[0,1]` for the exp-side clause.  The
frame data then matches at `0`: both fields vanish there, and
`⟨iZ, Ẽ_k(0)⟩_{p̃} = ⟨iZ, i(E_k(0))⟩_{p̃} = ⟨Z, E_k(0)⟩_p` by `φ_0 = i` and `hi`.  Feeding
this to `metricInner_jacobiField_transfer_of_curvatureFormAt` at `t = 1` equates the two
norms.

Unlike the constant-curvature analogue
`chartMetricInner_expDifferential_transfer_of_constantCurvature_of_speedSq`, this takes no
speed hypothesis and does not require `v ≠ 0`.

The single-chart hypotheses `hsrc`, `hsrcbar` are **not** discharged here; they are an open
obligation of `thm:dc-ch8-2-1`, tracked at `lem:dc-ch8-2-1-single-chart`.

Blueprint: `lem:dc-ch8-2-1-exp-norm-transfer-general`. -/
theorem chartMetricInner_expDifferential_transfer_of_curvatureFormAt
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    (α : M) (α' : M') (p : M) (p' : M') (v Z : E)
    (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner p' (i u) (i w) = g.metricInner p u w)
    {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b')
    (hsrc : ∀ t ∈ Icc a' b', globalGeodesic (I := I) g hg p v t ∈ (chartAt H α).source)
    (hsrcbar : ∀ t ∈ Icc a' b',
      globalGeodesic (I := I') g' hg' p' (i v) t ∈ (chartAt H' α').source)
    (Efr Ebar : ι → ℝ → E)
    (hEpar : ∀ k, IsParallelFieldAlongOn (I := I) g
      (globalGeodesic (I := I) g hg p v) (Efr k) a' b')
    (hEbarpar : ∀ k, IsParallelFieldAlongOn (I := I') g'
      (globalGeodesic (I := I') g' hg' p' (i v)) (Ebar k) a' b')
    (hEorth : ∀ t ∈ Icc a' b', ∀ k l,
      g.metricInner (globalGeodesic (I := I) g hg p v t)
          (Efr k t : TangentSpace I (globalGeodesic (I := I) g hg p v t)) (Efr l t)
        = if k = l then (1 : ℝ) else 0)
    (hEbarorth : ∀ t ∈ Icc a' b', ∀ k l,
      g'.metricInner (globalGeodesic (I := I') g' hg' p' (i v) t)
          (Ebar k t : TangentSpace I' (globalGeodesic (I := I') g' hg' p' (i v) t)) (Ebar l t)
        = if k = l then (1 : ℝ) else 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    (φ : ℝ → E → E)
    (hvel : ∀ t ∈ Icc a' b',
      φ t (mfderiv 𝓘(ℝ, ℝ) I (globalGeodesic (I := I) g hg p v) t 1)
        = mfderiv 𝓘(ℝ, ℝ) I' (globalGeodesic (I := I') g' hg' p' (i v)) t 1)
    (hfr : ∀ t ∈ Icc a' b', ∀ k, φ t (Efr k t) = Ebar k t)
    (hφ : ∀ t ∈ Icc a' b',
      ∀ x y z w : TangentSpace I (globalGeodesic (I := I) g hg p v t),
      g.leviCivitaConnection.curvatureFormAt g (globalGeodesic (I := I) g hg p v t) x y z w
        = g'.leviCivitaConnection.curvatureFormAt g'
            (globalGeodesic (I := I') g' hg' p' (i v) t)
            (φ t x) (φ t y) (φ t z) (φ t w))
    (hφ0 : ∀ x : E, φ 0 x = i x)
    {ζ : M} {D : E →L[ℝ] E}
    (hζ : expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source)
    (hjac : ∀ J DJ : ℝ → E,
      IsJacobiFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p v) J DJ 0 1 →
      J 0 = 0 →
      D (DJ 0) = chartVectorRep (I := I) (globalGeodesic (I := I) g hg p v) ζ J 1)
    {ζ' : M'} {D' : E →L[ℝ] E}
    (hζ' : expMapGlobal (I := I') g' hg' p' (i v) ∈ (chartAt H' ζ').source)
    (hjac' : ∀ J DJ : ℝ → E,
      IsJacobiFieldAlongOn (I := I') g' (globalGeodesic (I := I') g' hg' p' (i v)) J DJ 0 1 →
      J 0 = 0 →
      D' (DJ 0)
        = chartVectorRep (I := I') (globalGeodesic (I := I') g' hg' p' (i v)) ζ' J 1) :
    chartMetricInner (I := I') g' ζ'
        (extChartAt I' ζ' (expMapGlobal (I := I') g' hg' p' (i v))) (D' (i Z)) (D' (i Z))
      = chartMetricInner (I := I) g ζ (extChartAt I ζ (expMapGlobal (I := I) g hg p v))
        (D Z) (D Z) := by
  classical
  have hab' : a' < b' := lt_trans ha' (lt_trans zero_lt_one hb')
  have h0mem : (0 : ℝ) ∈ Icc a' b' := ⟨ha'.le, le_trans zero_le_one hb'.le⟩
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
  set γbar : ℝ → M' := globalGeodesic (I := I') g' hg' p' (i v) with hγbardef
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p v
  have hγbar0 : γbar 0 = p' := globalGeodesic_zero g' hg' p' (i v)
  have hgeo : IsGeodesicOn (I := I) g γ (Icc a' b') := fun t _ =>
    isGeodesic_globalGeodesic g hg p v t
  have hgeobar : IsGeodesicOn (I := I') g' γbar (Icc a' b') := fun t _ =>
    isGeodesic_globalGeodesic g' hg' p' (i v) t
  have hγc : ∀ t ∈ Icc a' b', ContinuousAt γ t := fun t _ =>
    (continuous_globalGeodesic g hg p v).continuousAt
  have hγcbar : ∀ t ∈ Icc a' b', ContinuousAt γbar t := fun t _ =>
    (continuous_globalGeodesic g' hg' p' (i v)).continuousAt
  -- the two Jacobi fields on the **outer** window, seeded at the interior time `0`
  obtain ⟨J, DJ, hJ, hJ0, hDJ0⟩ :=
    exists_isJacobiFieldAlongOn_at (I := I) (g := g) (γ := γ) (a := a') (b := b') hab'
      hgeo hγc h0mem (0 : TangentSpace I (γ 0)) (Z : TangentSpace I (γ 0))
  obtain ⟨Jbar, DJbar, hJbar, hJbar0, hDJbar0⟩ :=
    exists_isJacobiFieldAlongOn_at (I := I') (g := g') (γ := γbar) (a := a') (b := b') hab'
      hgeobar hγcbar h0mem (0 : TangentSpace I' (γbar 0)) ((i Z : E) : TangentSpace I' (γbar 0))
  have hJ0' : J 0 = 0 := hJ0
  have hJbar0' : Jbar 0 = 0 := hJbar0
  have hDJ0' : DJ 0 = Z := hDJ0
  have hDJbar0' : DJbar 0 = i Z := hDJbar0
  -- restrict them to `[0, 1]`, the window the exp-side clause is stated on
  have hJ01 : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 1 :=
    hJ.mono ha'.le zero_lt_one hb'.le
  have hJbar01 : IsJacobiFieldAlongOn (I := I') g' γbar Jbar DJbar 0 1 :=
    hJbar.mono ha'.le zero_lt_one hb'.le
  -- each exponential differential is the endpoint value of its Jacobi field
  have hleft : chartMetricInner (I := I) g ζ
      (extChartAt I ζ (expMapGlobal (I := I) g hg p v)) (D Z) (D Z)
      = g.metricInner (γ 1) (J 1) (J 1) := by
    rw [← hDJ0']
    exact chartMetricInner_expDifferential_eq_metricInner_jacobiField (I := I) g hg p v
      hζ hjac J DJ hJ01 hJ0'
  have hright : chartMetricInner (I := I') g' ζ'
      (extChartAt I' ζ' (expMapGlobal (I := I') g' hg' p' (i v))) (D' (i Z)) (D' (i Z))
      = g'.metricInner (γbar 1) (Jbar 1) (Jbar 1) := by
    rw [← hDJbar0']
    exact chartMetricInner_expDifferential_eq_metricInner_jacobiField (I := I') g' hg' p' (i v)
      hζ' hjac' Jbar DJbar hJbar01 hJbar0'
  rw [hleft, hright]
  -- the frame data at `0` matches, and `[0,1] ⊆ (a', b')`
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo a' b' := fun t ht =>
    ⟨lt_of_lt_of_le ha' ht.1, lt_of_le_of_lt ht.2 hb'⟩
  have hF0 : ∀ k, g'.metricInner (γbar 0) (Jbar 0 : TangentSpace I' (γbar 0)) (Ebar k 0)
      = g.metricInner (γ 0) (J 0 : TangentSpace I (γ 0)) (Efr k 0) := by
    intro k
    have h1 : (Jbar 0 : TangentSpace I' (γbar 0)) = 0 := hJbar0
    have h2 : (J 0 : TangentSpace I (γ 0)) = 0 := hJ0
    have e1 : g'.metricInner (γbar 0) (0 : TangentSpace I' (γbar 0)) (Ebar k 0) = 0 :=
      g'.metricInner_zero_left _ _
    have e2 : g.metricInner (γ 0) (0 : TangentSpace I (γ 0)) (Efr k 0) = 0 :=
      g.metricInner_zero_left _ _
    rw [h1, h2]
    exact e1.trans e2.symm
  have hV0 : ∀ k, g'.metricInner (γbar 0) (DJbar 0 : TangentSpace I' (γbar 0)) (Ebar k 0)
      = g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (Efr k 0) := by
    intro k
    have h1 : (DJbar 0 : TangentSpace I' (γbar 0)) = i Z := hDJbar0
    have h2 : (DJ 0 : TangentSpace I (γ 0)) = Z := hDJ0
    have h3 : Ebar k 0 = i (Efr k 0) := by
      rw [← hφ0 (Efr k 0)]; exact (hfr 0 h0mem k).symm
    rw [h1, h2, h3, hγ0, hγbar0]
    exact hi Z (Efr k 0)
  exact metricInner_jacobiField_transfer_of_curvatureFormAt (I := I) (I' := I') g g' α α'
    hgeo hγc hgeobar hγcbar hsrc hsrcbar Efr Ebar hEpar hEbarpar hEorth hEbarorth hcard
    φ hvel hfr hφ J DJ hJ Jbar DJbar hJbar hsub hF0 hV0 (right_mem_Icc.mpr zero_le_one)

/-! ### The intrinsic (`mfderiv`) form -/

/-- **Math.** **do Carmo Ch. 8, `thm:dc-ch8-2-1` — the norm-preservation step, intrinsically,
in variable curvature.**  Under E. Cartan's hypothesis on `φ` and the normalization `φ_0 = i`,

  `|d(exp_{p̃})_{iv}(iZ)|_{exp_{p̃}(iv)} = |d(exp_p)_v(Z)|_{exp_p(v)}`

with both differentials the intrinsic `mfderiv`.  This is
`chartMetricInner_expDifferential_transfer_of_curvatureFormAt` pushed through the bridge
`chartMetricInner_expDifferential_eq_metricInner_mfderiv` on both sides, the differentials
being supplied in `E ≃L[ℝ] E` form with their Jacobi clause by
`expDifferential_isEquiv_jacobi_of_not_conjugate`.

Non-conjugacy of `1` along the two geodesics is taken as a **hypothesis**.  In constant
curvature it follows from a numerical condition
(`not_isConjugatePointAt_globalGeodesic_of_constantCurvature_of_lt_pi`); in variable curvature
there is no such producer, and none is claimed here.  The single-chart hypotheses `hsrc`,
`hsrcbar` are likewise undischarged (`lem:dc-ch8-2-1-single-chart`).

Blueprint: `lem:dc-ch8-2-1-exp-norm-transfer-general`. -/
theorem metricInner_mfderiv_expMapGlobal_transfer_of_curvatureFormAt
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    (α : M) (α' : M') (p : M) (p' : M') (v Z : E)
    (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner p' (i u) (i w) = g.metricInner p u w)
    {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b')
    (hsrc : ∀ t ∈ Icc a' b', globalGeodesic (I := I) g hg p v t ∈ (chartAt H α).source)
    (hsrcbar : ∀ t ∈ Icc a' b',
      globalGeodesic (I := I') g' hg' p' (i v) t ∈ (chartAt H' α').source)
    (Efr Ebar : ι → ℝ → E)
    (hEpar : ∀ k, IsParallelFieldAlongOn (I := I) g
      (globalGeodesic (I := I) g hg p v) (Efr k) a' b')
    (hEbarpar : ∀ k, IsParallelFieldAlongOn (I := I') g'
      (globalGeodesic (I := I') g' hg' p' (i v)) (Ebar k) a' b')
    (hEorth : ∀ t ∈ Icc a' b', ∀ k l,
      g.metricInner (globalGeodesic (I := I) g hg p v t)
          (Efr k t : TangentSpace I (globalGeodesic (I := I) g hg p v t)) (Efr l t)
        = if k = l then (1 : ℝ) else 0)
    (hEbarorth : ∀ t ∈ Icc a' b', ∀ k l,
      g'.metricInner (globalGeodesic (I := I') g' hg' p' (i v) t)
          (Ebar k t : TangentSpace I' (globalGeodesic (I := I') g' hg' p' (i v) t)) (Ebar l t)
        = if k = l then (1 : ℝ) else 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    (φ : ℝ → E → E)
    (hvel : ∀ t ∈ Icc a' b',
      φ t (mfderiv 𝓘(ℝ, ℝ) I (globalGeodesic (I := I) g hg p v) t 1)
        = mfderiv 𝓘(ℝ, ℝ) I' (globalGeodesic (I := I') g' hg' p' (i v)) t 1)
    (hfr : ∀ t ∈ Icc a' b', ∀ k, φ t (Efr k t) = Ebar k t)
    (hφ : ∀ t ∈ Icc a' b',
      ∀ x y z w : TangentSpace I (globalGeodesic (I := I) g hg p v t),
      g.leviCivitaConnection.curvatureFormAt g (globalGeodesic (I := I) g hg p v t) x y z w
        = g'.leviCivitaConnection.curvatureFormAt g'
            (globalGeodesic (I := I') g' hg' p' (i v) t)
            (φ t x) (φ t y) (φ t z) (φ t w))
    (hφ0 : ∀ x : E, φ 0 x = i x)
    (hnc : ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1)
    (hnc' : ¬ IsConjugatePointAt (I := I') g'
      (globalGeodesic (I := I') g' hg' p' (i v)) 1) :
    g'.metricInner (expMapGlobal (I := I') g' hg' p' (i v))
        (mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v) (i Z))
        (mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v) (i Z))
      = g.metricInner (expMapGlobal (I := I) g hg p v)
          (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v Z)
          (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v Z) := by
  obtain ⟨ζ, D, hζ, hFD, hjac⟩ :=
    expDifferential_isEquiv_jacobi_of_not_conjugate (I := I) g hg p hnc
  obtain ⟨ζ', D', hζ', hFD', hjac'⟩ :=
    expDifferential_isEquiv_jacobi_of_not_conjugate (I := I') g' hg' p' hnc'
  have htr := chartMetricInner_expDifferential_transfer_of_curvatureFormAt
    (I := I) (I' := I') g hg g' hg' α α' p p' v Z i hi ha' hb' hsrc hsrcbar
    Efr Ebar hEpar hEbarpar hEorth hEbarorth hcard φ hvel hfr hφ hφ0
    hζ hjac hζ' hjac'
  rw [chartMetricInner_expDifferential_eq_metricInner_mfderiv g' hg' p' (i v) hζ'
        hFD'.hasFDerivAt (i Z) (i Z),
      chartMetricInner_expDifferential_eq_metricInner_mfderiv g hg p v hζ
        hFD.hasFDerivAt Z Z] at htr
  exact htr

/-! ### Metric preservation along a semiconjugacy -/

/-- **Math.** **do Carmo Ch. 8, `thm:dc-ch8-2-1` — `f` preserves the metric at `q = exp_p(v)`,
in variable curvature.**  Let `i` be a linear isometry `T_pM → T_{p̃}M̃`, let E. Cartan's
hypothesis hold for `φ` along the geodesics of `v` and `iv` on an outer window `[a', b']`
(`a' < 0 < 1 < b'`) with `φ_0 = i`, and let `f` be **any** map differentiable at
`q = exp_p(v)` and satisfying the semiconjugacy `f ∘ exp_p = exp_{p̃} ∘ i` near `v`.  Then

  `⟨u, u'⟩_q = ⟨df_q u, df_q u'⟩_{f q}`  for all `u, u' ∈ T_qM`.

Proof.  Non-conjugacy at `1` along `γ_v` makes `d(exp_p)_v` surjective
(`surjective_mfderiv_expMapGlobal_of_not_conjugate`), so it suffices to test `df_q` on vectors
`d(exp_p)_v Z`.  The chain rule along the semiconjugacy — `hasMFDerivAt_unique` on the two
readings of `f ∘ exp_p` at `v` — gives `df_q(d(exp_p)_v Z) = d(exp_{p̃})_{iv}(iZ)`, and
`metricInner_mfderiv_expMapGlobal_transfer_of_curvatureFormAt` equates the two norms.
Polarization (`metricInner_transfer_of_norm_transfer`) upgrades the diagonal to the full
bilinear form.  Taking the semiconjugacy as the hypothesis, rather than
`f = exp_{p̃} ∘ i ∘ exp_p⁻¹`, avoids ever differentiating `exp_p⁻¹`.

This is the variable-curvature counterpart of `metricInner_mfderiv_eq_of_semiconjugacy`.  It
is *not* the whole of `thm:dc-ch8-2-1`: `hsrc`/`hsrcbar` (`lem:dc-ch8-2-1-single-chart`), the
non-conjugacy hypotheses `hnc`/`hnc'`, and the existence of a `φ` satisfying `hvel`/`hfr`/`hφ`
with `φ_0 = i` all remain to be supplied by the caller.

Blueprint: `lem:dc-ch8-2-1-exp-norm-transfer-general`. -/
theorem metricInner_mfderiv_eq_of_semiconjugacy_of_curvatureFormAt
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    (α : M) (α' : M') (p : M) (p' : M') (v : E)
    (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner p' (i u) (i w) = g.metricInner p u w)
    {a' b' : ℝ} (ha' : a' < 0) (hb' : (1 : ℝ) < b')
    (hsrc : ∀ t ∈ Icc a' b', globalGeodesic (I := I) g hg p v t ∈ (chartAt H α).source)
    (hsrcbar : ∀ t ∈ Icc a' b',
      globalGeodesic (I := I') g' hg' p' (i v) t ∈ (chartAt H' α').source)
    (Efr Ebar : ι → ℝ → E)
    (hEpar : ∀ k, IsParallelFieldAlongOn (I := I) g
      (globalGeodesic (I := I) g hg p v) (Efr k) a' b')
    (hEbarpar : ∀ k, IsParallelFieldAlongOn (I := I') g'
      (globalGeodesic (I := I') g' hg' p' (i v)) (Ebar k) a' b')
    (hEorth : ∀ t ∈ Icc a' b', ∀ k l,
      g.metricInner (globalGeodesic (I := I) g hg p v t)
          (Efr k t : TangentSpace I (globalGeodesic (I := I) g hg p v t)) (Efr l t)
        = if k = l then (1 : ℝ) else 0)
    (hEbarorth : ∀ t ∈ Icc a' b', ∀ k l,
      g'.metricInner (globalGeodesic (I := I') g' hg' p' (i v) t)
          (Ebar k t : TangentSpace I' (globalGeodesic (I := I') g' hg' p' (i v) t)) (Ebar l t)
        = if k = l then (1 : ℝ) else 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    (φ : ℝ → E → E)
    (hvel : ∀ t ∈ Icc a' b',
      φ t (mfderiv 𝓘(ℝ, ℝ) I (globalGeodesic (I := I) g hg p v) t 1)
        = mfderiv 𝓘(ℝ, ℝ) I' (globalGeodesic (I := I') g' hg' p' (i v)) t 1)
    (hfr : ∀ t ∈ Icc a' b', ∀ k, φ t (Efr k t) = Ebar k t)
    (hφ : ∀ t ∈ Icc a' b',
      ∀ x y z w : TangentSpace I (globalGeodesic (I := I) g hg p v t),
      g.leviCivitaConnection.curvatureFormAt g (globalGeodesic (I := I) g hg p v t) x y z w
        = g'.leviCivitaConnection.curvatureFormAt g'
            (globalGeodesic (I := I') g' hg' p' (i v) t)
            (φ t x) (φ t y) (φ t z) (φ t w))
    (hφ0 : ∀ x : E, φ 0 x = i x)
    (hnc : ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1)
    (hnc' : ¬ IsConjugatePointAt (I := I') g'
      (globalGeodesic (I := I') g' hg' p' (i v)) 1)
    (f : M → M')
    (hfd : MDifferentiableAt I I' f (expMapGlobal (I := I) g hg p v))
    (hsemi : ∀ᶠ w : E in nhds v, f (expMapGlobal (I := I) g hg p w)
      = expMapGlobal (I := I') g' hg' p' (i w))
    (u u' : TangentSpace I (expMapGlobal (I := I) g hg p v)) :
    g.metricInner (expMapGlobal (I := I) g hg p v) u u'
      = g'.metricInner (f (expMapGlobal (I := I) g hg p v))
          (mfderiv I I' f (expMapGlobal (I := I) g hg p v) u)
          (mfderiv I I' f (expMapGlobal (I := I) g hg p v) u') := by
  classical
  have hsurj := surjective_mfderiv_expMapGlobal_of_not_conjugate g hg p hnc
  have hfq : f (expMapGlobal (I := I) g hg p v) = expMapGlobal (I := I') g' hg' p' (i v) :=
    hsemi.self_of_nhds
  -- the chain rule along the semiconjugacy
  have hexpM : HasMFDerivAt 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v
      (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v) :=
    ((Riemannian.Exponential.contMDiff_expMapGlobal g hg p).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hexpM' : HasMFDerivAt 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v)
      (mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v)) :=
    ((Riemannian.Exponential.contMDiff_expMapGlobal g' hg' p').mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hiM : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun w : E => (i w : E)) v (i : E →L[ℝ] E) :=
    (i : E →L[ℝ] E).hasMFDerivAt
  have hB : HasMFDerivAt 𝓘(ℝ, E) I' (fun w : E => f (expMapGlobal (I := I) g hg p w)) v
      ((mfderiv I I' f (expMapGlobal (I := I) g hg p v)).comp
        (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v)) :=
    hfd.hasMFDerivAt.comp v hexpM
  have hA : HasMFDerivAt 𝓘(ℝ, E) I' (fun w : E => f (expMapGlobal (I := I) g hg p w)) v
      ((mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v)).comp
        (i : E →L[ℝ] E)) :=
    (hexpM'.comp v hiM).congr_of_eventuallyEq hsemi
  have hchain := hasMFDerivAt_unique hB hA
  -- the diagonal (norm) transfer, for every tangent vector at `q`
  have hnorm : ∀ w : E,
      g'.metricInner (f (expMapGlobal (I := I) g hg p v))
          (mfderiv I I' f (expMapGlobal (I := I) g hg p v) w)
          (mfderiv I I' f (expMapGlobal (I := I) g hg p v) w)
        = g.metricInner (expMapGlobal (I := I) g hg p v) w w := by
    intro w
    obtain ⟨Z, hZ⟩ := hsurj w
    have hpt : mfderiv I I' f (expMapGlobal (I := I) g hg p v)
        (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v Z)
          = mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v) (i Z) :=
      congrArg (fun L : E →L[ℝ] E => L Z) hchain
    rw [← hZ, hpt, hfq]
    exact metricInner_mfderiv_expMapGlobal_transfer_of_curvatureFormAt
      (I := I) (I' := I') g hg g' hg' α α' p p' v Z i hi ha' hb' hsrc hsrcbar
      Efr Ebar hEpar hEbarpar hEorth hEbarorth hcard φ hvel hfr hφ hφ0 hnc hnc'
  -- polarization
  exact (metricInner_transfer_of_norm_transfer g g' (expMapGlobal (I := I) g hg p v)
    (f (expMapGlobal (I := I) g hg p v))
    (fun w : E => mfderiv I I' f (expMapGlobal (I := I) g hg p v) w)
    (fun a b => (mfderiv I I' f (expMapGlobal (I := I) g hg p v)).map_add a b) hnorm u u').symm

end Riemannian.Jacobi

end
