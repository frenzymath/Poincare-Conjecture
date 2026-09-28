import DoCarmoLib.Riemannian.Variation.SurfaceCurvatureManifold

/-!
# The surface curvature commutation, chart-free (do Carmo Ch. 4, `lem:dc-ch4-4-1`)

do Carmo, *Riemannian Geometry*, Ch. 4, Lemma 4.1 (the Ricci identity on a parametrized
surface), read on a surface `f : ℝ × ℝ → M` **valued in the manifold**, with the two
covariant derivatives presented in the fully chart-free
`IsCovariantDerivFieldAlongOn` discipline of `Variation/CovariantField.lean`.  This is
the form Ch. 9 §2 uses at the curvature substitution in the proof of the second variation
formula (`prop:dc-ch9-2-8`).

`Variation/SurfaceCurvatureManifold.lean` already carries the identity to the point where
the four iterated covariant derivatives and the field are *chart readings*
(`chartMetricInner_surface_covariant_commutator_eq_curvatureFormAt`), with the curvature
as the intrinsic `curvatureFormAt` of do Carmo's Ch. 4 Def. 2.1 convention.  This file
removes the last chart from the statement, exactly as
`Variation/SurfaceSymmetryManifold.lean` does for the *symmetry* lemma (Ch. 3 Lemma 3.4):
the two velocity fields are `mfderiv`-based, the field `V` and its four iterated covariant
derivatives are `ℝ × ℝ → E` own-foot fields, and the two outer covariant derivatives
`D/∂t (D/∂s V)`, `D/∂s (D/∂t V)` are given as `IsCovariantDerivFieldAlongOn` pairs along the
two slice curves through `(s₀, t₀)`.

## The route, and where each piece comes from

The identity is transported, not reproved, by the same devices as the symmetry transfer,
now applied to the **iterated** derivative:

1. **Localize** each outer pair `hDtDsV`, `hDsDtV` into one chart at `α` and read off the
   operator, via `IsCovariantDerivFieldAlongOn.isCovariantDerivSolOn_of_mem_source` and
   `IsCovariantDerivSolOn.covariantDerivCoord_eq` at the interior time.
2. **Recognize the inner operator.**  The chart reading of the *inner* covariant derivative
   `D/∂s V` along the whole `t`-window is, at each nearby time, the surface operator
   `surfaceCovariantDerivS` of the chart readings `F = φ_α ∘ f`, `Vc = φ_α∗ ∘ V`: localize
   `hDsV t` and apply `covariantDerivCoord_eq` at the interior `s = s₀`.  This is an
   `eventuallyEq` in the outer variable, so `covariantDerivCoord_congr_of_eventuallyEq`
   turns step 1's output into `surfaceCovariantDerivT (surfaceCovariantDerivS Vc)`.
3. **Apply the chart-reading Ricci identity**
   `chartMetricInner_surface_covariant_commutator_eq_curvatureFormAt`, pairing the
   commutator against the chart reading of `W` by `chartMetricInner_tangentCoordChange`.
4. **Cancel the chart** on the curvature side: the velocity bridge
   `Geodesic.mfderiv_eq_of_hasDerivAt_extChartAt` identifies `∂F/∂s`, `∂F/∂t` with the
   chart readings of `S`, `T`, and the readback `Jacobi.chartFrameRealize_tangentCoordChange`
   collapses every chart-frame realization back to the intrinsic `S`, `T`, `V`, `W`.

## Scope — what is hypothesised

* a chart selector `α` with `f (s₀, t₀) ∈ (chartAt H α).source` is **supplied**, together
  with a two-dimensional chart window `[a, b] × [c, d]` (with `s₀ ∈ Ioo a b`,
  `t₀ ∈ Ioo c d`) on which `f` stays in `(chartAt H α).source`, is continuous, and has
  differentiable slice chart-readings.  A two-dimensional window is genuinely needed here
  (the symmetry transfer used only the two slice lines): step 2 localizes `D/∂s V` along
  every `s`-slice for `t` near `t₀`, and `D/∂t V` along every `t`-slice for `s` near `s₀`.
* the chart readings `F = φ_α ∘ f` and `Vc = φ_α∗ ∘ V` are `C²` near `(s₀, t₀)` in the
  `HasFDerivAt`-with-explicit-`DF`/`D2F` shape the chart-level Ricci identity consumes.
* the velocity fields `S`, `T` are pinned at `(s₀, t₀)` to the intrinsic slice velocities
  `∂f/∂s`, `∂f/∂t`.
* the four covariant derivatives are given as `IsCovariantDerivFieldAlongOn` pairs: `DsV`,
  `DtV` along every slice of the window, and the two outer `DtDsV`, `DsDtV` along the two
  slice lines through `(s₀, t₀)`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 4, Lemma 4.1; used at Ch. 9 §2 in the proof
of `prop:dc-ch9-2-8`.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi Riemannian.Geodesic Riemannian.Exponential Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** do Carmo Ch. 4, Lemma 4.1 (`lem:dc-ch4-4-1`, the Ricci identity on a
parametrized surface), **manifold level, metric-paired, at one point**.  For a parametrized
surface `f : ℝ × ℝ → M` and field `V` along it, the commutator of the two iterated covariant
derivatives, paired against `W ∈ T_{f(s₀,t₀)}M`, is the intrinsic curvature form of the two
velocities, the field, and `W`:
$$
\Big\langle \frac{D}{\partial t}\frac{D}{\partial s}V - \frac{D}{\partial s}\frac{D}{\partial t}V,\ W\Big\rangle
  = R\Big(\frac{\partial f}{\partial s},\ \frac{\partial f}{\partial t},\ V,\ W\Big)
  \qquad\text{at } (s_0, t_0),
$$
in do Carmo's Ch. 4 Def. 2.1 curvature sign (`⟨R(∂f/∂s, ∂f/∂t)V, W⟩`).

This is the fully chart-free transfer of `lem:dc-ch4-4-1` — the exact analogue of
`covariantDerivS_velT_eq_covariantDerivT_velS` (the symmetry lemma) with iterated covariant
derivatives and a nonzero (curvature) right-hand side.  The two outer covariant derivatives
`DtDsV`, `DsDtV` are presented by the chart-free `IsCovariantDerivFieldAlongOn` pairs along
the two slice lines; the inner derivatives `DsV`, `DtV` along every slice of the window; the
velocities `S`, `T` are pinned at the point to `∂f/∂s`, `∂f/∂t`. -/
theorem metricInner_covariantDerivT_covariantDerivS_commutator_eq_curvatureFormAt
    (g : RiemannianMetric I M) (f : ℝ × ℝ → M) (α : M)
    (S T V DsV DtV DtDsV DsDtV : ℝ × ℝ → E)
    (DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E)) (D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E)
    (DVc : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E)) (D2Vc : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E)
    {s₀ t₀ a b c d : ℝ} (W : TangentSpace I (f (s₀, t₀)))
    (hs₀ : s₀ ∈ Ioo a b) (ht₀ : t₀ ∈ Ioo c d)
    (hq : f (s₀, t₀) ∈ (chartAt H α).source)
    (hF : ∀ᶠ p in 𝓝 (s₀, t₀), HasFDerivAt (fun q => extChartAt I α (f q)) (DF p) p)
    (hF2 : HasFDerivAt DF D2F (s₀, t₀))
    (hVc : ∀ᶠ p in 𝓝 (s₀, t₀),
      HasFDerivAt (fun q => tangentCoordChange I (f q) α (f q) (V q)) (DVc p) p)
    (hVc2 : HasFDerivAt DVc D2Vc (s₀, t₀))
    (hS : S (s₀, t₀) = mfderiv 𝓘(ℝ, ℝ) I (fun σ => f (σ, t₀)) s₀ 1)
    (hT : T (s₀, t₀) = mfderiv 𝓘(ℝ, ℝ) I (fun τ => f (s₀, τ)) t₀ 1)
    (hsrc : ∀ σ ∈ Icc a b, ∀ τ ∈ Icc c d, f (σ, τ) ∈ (chartAt H α).source)
    (hcont : ∀ σ ∈ Icc a b, ∀ τ ∈ Icc c d, ContinuousAt f (σ, τ))
    (hdiffS : ∀ σ ∈ Icc a b, ∀ τ ∈ Icc c d,
      DifferentiableAt ℝ (fun σ' => extChartAt I α (f (σ', τ))) σ)
    (hdiffT : ∀ σ ∈ Icc a b, ∀ τ ∈ Icc c d,
      DifferentiableAt ℝ (fun τ' => extChartAt I α (f (σ, τ'))) τ)
    (hDsV : ∀ τ ∈ Icc c d, IsCovariantDerivFieldAlongOn (I := I) g (fun σ => f (σ, τ))
      (fun σ => V (σ, τ)) (fun σ => DsV (σ, τ)) a b)
    (hDtV : ∀ σ ∈ Icc a b, IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (σ, τ))
      (fun τ => V (σ, τ)) (fun τ => DtV (σ, τ)) c d)
    (hDtDsV : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (s₀, τ))
      (fun τ => DsV (s₀, τ)) (fun τ => DtDsV (s₀, τ)) c d)
    (hDsDtV : IsCovariantDerivFieldAlongOn (I := I) g (fun σ => f (σ, t₀))
      (fun σ => DtV (σ, t₀)) (fun σ => DsDtV (σ, t₀)) a b) :
    g.metricInner (f (s₀, t₀))
        (DtDsV (s₀, t₀) - DsDtV (s₀, t₀) : TangentSpace I (f (s₀, t₀))) W
      = g.leviCivitaConnection.curvatureFormAt g (f (s₀, t₀))
          (S (s₀, t₀)) (T (s₀, t₀)) (V (s₀, t₀)) W := by
  classical
  set F : ℝ × ℝ → E := fun p => extChartAt I α (f p) with hFdef
  set Vc : ℝ × ℝ → E := fun p => tangentCoordChange I (f p) α (f p) (V p) with hVcdef
  have hsIcc : s₀ ∈ Icc a b := Ioo_subset_Icc_self hs₀
  have htIcc : t₀ ∈ Icc c d := Ioo_subset_Icc_self ht₀
  -- ## the velocity bridges for `S`, `T` at the point
  have hd_s : HasDerivAt (fun σ => extChartAt I α (f (σ, t₀))) (DF (s₀, t₀) (1, 0)) s₀ :=
    hasDerivAt_comp_fst hF.self_of_nhds
  have hcs_s : ContinuousAt (fun σ => f (σ, t₀)) s₀ :=
    ContinuousAt.comp (g := f) (f := fun σ : ℝ => (σ, t₀)) (x := s₀)
      (hcont s₀ hsIcc t₀ htIcc) (by fun_prop)
  have hbridge_s := Geodesic.mfderiv_eq_of_hasDerivAt_extChartAt (I := I)
    (γ := fun σ => f (σ, t₀)) (α := α) hcs_s hq hd_s
  have hSbridge : DF (s₀, t₀) (1, 0)
      = tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀)) (S (s₀, t₀)) := by
    rw [hS, hbridge_s, tangentCoordChange_readback (I := I) hq]
  have hd_t : HasDerivAt (fun τ => extChartAt I α (f (s₀, τ))) (DF (s₀, t₀) (0, 1)) t₀ :=
    hasDerivAt_comp_snd hF.self_of_nhds
  have hcs_t : ContinuousAt (fun τ => f (s₀, τ)) t₀ :=
    ContinuousAt.comp (g := f) (f := fun τ : ℝ => (s₀, τ)) (x := t₀)
      (hcont s₀ hsIcc t₀ htIcc) (by fun_prop)
  have hbridge_t := Geodesic.mfderiv_eq_of_hasDerivAt_extChartAt (I := I)
    (γ := fun τ => f (s₀, τ)) (α := α) hcs_t hq hd_t
  have hTbridge : DF (s₀, t₀) (0, 1)
      = tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀)) (T (s₀, t₀)) := by
    rw [hT, hbridge_t, tangentCoordChange_readback (I := I) hq]
  -- ## step 1+2 : the outer iterated operator `D/∂t (D/∂s V)`
  have hTS : tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀)) (DtDsV (s₀, t₀))
      = surfaceCovariantDerivT (I := I) g α F (surfaceCovariantDerivS (I := I) g α F Vc)
          (s₀, t₀) := by
    have hchdT_s0 : IsChartDifferentiableOn (I := I) (fun τ => f (s₀, τ)) c d :=
      isChartDifferentiableOn_of_forall_mem
        (fun τ hτ => ContinuousAt.comp (g := f) (f := fun τ' : ℝ => (s₀, τ')) (x := τ)
          (hcont s₀ hsIcc τ hτ) (by fun_prop))
        (fun τ hτ => ⟨α, hsrc s₀ hsIcc τ hτ, hdiffT s₀ hsIcc τ hτ⟩)
    have hcontT_s0 : ∀ τ ∈ Icc c d, ContinuousAt (fun τ' => f (s₀, τ')) τ :=
      fun τ hτ => ContinuousAt.comp (g := f) (f := fun τ' : ℝ => (s₀, τ')) (x := τ)
        (hcont s₀ hsIcc τ hτ) (by fun_prop)
    have hsrcT_s0 : ∀ τ ∈ Icc c d, f (s₀, τ) ∈ (chartAt H α).source :=
      fun τ hτ => hsrc s₀ hsIcc τ hτ
    have hAouter := (hDtDsV.isCovariantDerivSolOn_of_mem_source hchdT_s0 hcontT_s0
      (β := α) Subset.rfl hsrcT_s0).covariantDerivCoord_eq ht₀
    have hevSlice : chartVectorRep (I := I) (fun τ => f (s₀, τ)) α (fun τ => DsV (s₀, τ))
        =ᶠ[𝓝 t₀] fun τ => surfaceCovariantDerivS (I := I) g α F Vc (s₀, τ) := by
      have hIcc : ∀ᶠ τ in 𝓝 t₀, τ ∈ Icc c d := by
        filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with τ hτ using Ioo_subset_Icc_self hτ
      filter_upwards [hIcc] with τ hτ
      have hchdS_τ : IsChartDifferentiableOn (I := I) (fun σ => f (σ, τ)) a b :=
        isChartDifferentiableOn_of_forall_mem
          (fun σ hσ => ContinuousAt.comp (g := f) (f := fun σ' : ℝ => (σ', τ)) (x := σ)
            (hcont σ hσ τ hτ) (by fun_prop))
          (fun σ hσ => ⟨α, hsrc σ hσ τ hτ, hdiffS σ hσ τ hτ⟩)
      have hcontS_τ : ∀ σ ∈ Icc a b, ContinuousAt (fun σ' => f (σ', τ)) σ :=
        fun σ hσ => ContinuousAt.comp (g := f) (f := fun σ' : ℝ => (σ', τ)) (x := σ)
          (hcont σ hσ τ hτ) (by fun_prop)
      have hsrcS_τ : ∀ σ ∈ Icc a b, f (σ, τ) ∈ (chartAt H α).source :=
        fun σ hσ => hsrc σ hσ τ hτ
      have hAinner := ((hDsV τ hτ).isCovariantDerivSolOn_of_mem_source hchdS_τ hcontS_τ
        (β := α) Subset.rfl hsrcS_τ).covariantDerivCoord_eq hs₀
      exact hAinner.symm
    have h1 : tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀)) (DtDsV (s₀, t₀))
        = covariantDerivCoord (I := I) g α (fun τ => extChartAt I α (f (s₀, τ)))
            (chartVectorRep (I := I) (fun τ => f (s₀, τ)) α (fun τ => DsV (s₀, τ))) t₀ :=
      hAouter.symm
    rw [h1]
    exact covariantDerivCoord_congr_of_eventuallyEq (I := I) g α
      (fun τ => extChartAt I α (f (s₀, τ))) hevSlice
  -- ## step 1+2 : the outer iterated operator `D/∂s (D/∂t V)`
  have hST : tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀)) (DsDtV (s₀, t₀))
      = surfaceCovariantDerivS (I := I) g α F (surfaceCovariantDerivT (I := I) g α F Vc)
          (s₀, t₀) := by
    have hchdS_t0 : IsChartDifferentiableOn (I := I) (fun σ => f (σ, t₀)) a b :=
      isChartDifferentiableOn_of_forall_mem
        (fun σ hσ => ContinuousAt.comp (g := f) (f := fun σ' : ℝ => (σ', t₀)) (x := σ)
          (hcont σ hσ t₀ htIcc) (by fun_prop))
        (fun σ hσ => ⟨α, hsrc σ hσ t₀ htIcc, hdiffS σ hσ t₀ htIcc⟩)
    have hcontS_t0 : ∀ σ ∈ Icc a b, ContinuousAt (fun σ' => f (σ', t₀)) σ :=
      fun σ hσ => ContinuousAt.comp (g := f) (f := fun σ' : ℝ => (σ', t₀)) (x := σ)
        (hcont σ hσ t₀ htIcc) (by fun_prop)
    have hsrcS_t0 : ∀ σ ∈ Icc a b, f (σ, t₀) ∈ (chartAt H α).source :=
      fun σ hσ => hsrc σ hσ t₀ htIcc
    have hAouter := (hDsDtV.isCovariantDerivSolOn_of_mem_source hchdS_t0 hcontS_t0
      (β := α) Subset.rfl hsrcS_t0).covariantDerivCoord_eq hs₀
    have hevSlice : chartVectorRep (I := I) (fun σ => f (σ, t₀)) α (fun σ => DtV (σ, t₀))
        =ᶠ[𝓝 s₀] fun σ => surfaceCovariantDerivT (I := I) g α F Vc (σ, t₀) := by
      have hIcc : ∀ᶠ σ in 𝓝 s₀, σ ∈ Icc a b := by
        filter_upwards [Ioo_mem_nhds hs₀.1 hs₀.2] with σ hσ using Ioo_subset_Icc_self hσ
      filter_upwards [hIcc] with σ hσ
      have hchdT_σ : IsChartDifferentiableOn (I := I) (fun τ => f (σ, τ)) c d :=
        isChartDifferentiableOn_of_forall_mem
          (fun τ hτ => ContinuousAt.comp (g := f) (f := fun τ' : ℝ => (σ, τ')) (x := τ)
            (hcont σ hσ τ hτ) (by fun_prop))
          (fun τ hτ => ⟨α, hsrc σ hσ τ hτ, hdiffT σ hσ τ hτ⟩)
      have hcontT_σ : ∀ τ ∈ Icc c d, ContinuousAt (fun τ' => f (σ, τ')) τ :=
        fun τ hτ => ContinuousAt.comp (g := f) (f := fun τ' : ℝ => (σ, τ')) (x := τ)
          (hcont σ hσ τ hτ) (by fun_prop)
      have hsrcT_σ : ∀ τ ∈ Icc c d, f (σ, τ) ∈ (chartAt H α).source :=
        fun τ hτ => hsrc σ hσ τ hτ
      have hAinner := ((hDtV σ hσ).isCovariantDerivSolOn_of_mem_source hchdT_σ hcontT_σ
        (β := α) Subset.rfl hsrcT_σ).covariantDerivCoord_eq ht₀
      exact hAinner.symm
    have h1 : tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀)) (DsDtV (s₀, t₀))
        = covariantDerivCoord (I := I) g α (fun σ => extChartAt I α (f (σ, t₀)))
            (chartVectorRep (I := I) (fun σ => f (σ, t₀)) α (fun σ => DtV (σ, t₀))) s₀ :=
      hAouter.symm
    rw [h1]
    exact covariantDerivCoord_congr_of_eventuallyEq (I := I) g α
      (fun σ => extChartAt I α (f (σ, t₀))) hevSlice
  -- ## step 3 : the chart-reading Ricci identity, metric-paired against `W`
  have hcomm := chartMetricInner_surface_covariant_commutator_eq_curvatureFormAt (I := I)
    g α F Vc DF DVc D2F D2Vc s₀ t₀ (tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀)) W)
    hF hF2 hVc hVc2 hq rfl
  -- ## step 4 : collapse the chart-frame realizations to the intrinsic vectors
  have e1 : (∑ i, Geodesic.chartCoord (E := E) i (DF (s₀, t₀) (1, 0))
        • chartBasisVecFiber (I := I) α i (f (s₀, t₀))) = S (s₀, t₀) := by
    rw [hSbridge]
    exact chartFrameRealize_tangentCoordChange (I := I) α hq (S (s₀, t₀))
  have e2 : (∑ i, Geodesic.chartCoord (E := E) i (DF (s₀, t₀) (0, 1))
        • chartBasisVecFiber (I := I) α i (f (s₀, t₀))) = T (s₀, t₀) := by
    rw [hTbridge]
    exact chartFrameRealize_tangentCoordChange (I := I) α hq (T (s₀, t₀))
  have e3 : (∑ i, Geodesic.chartCoord (E := E) i (Vc (s₀, t₀))
        • chartBasisVecFiber (I := I) α i (f (s₀, t₀))) = V (s₀, t₀) :=
    chartFrameRealize_tangentCoordChange (I := I) α hq (V (s₀, t₀))
  have e4 : (∑ i, Geodesic.chartCoord (E := E)
        i (tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀)) W)
        • chartBasisVecFiber (I := I) α i (f (s₀, t₀))) = W :=
    chartFrameRealize_tangentCoordChange (I := I) α hq W
  rw [e1, e2, e3, e4] at hcomm
  -- ## assemble
  rw [← chartMetricInner_tangentCoordChange (I := I) g hq
      (DtDsV (s₀, t₀) - DsDtV (s₀, t₀)) W, map_sub, hTS, hST]
  exact hcomm

end Riemannian.Variation

end
