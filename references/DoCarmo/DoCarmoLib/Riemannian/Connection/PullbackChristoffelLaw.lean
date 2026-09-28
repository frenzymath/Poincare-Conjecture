import DoCarmoLib.Riemannian.Connection.PullbackChristoffel
import DoCarmoLib.Riemannian.Connection.ChartChristoffelChange
import DoCarmoLib.Riemannian.Connection.ChartFrameBridge

/-!
# The Christoffel transformation law under a local isometry (pullback metric)

For a smooth immersion `f : M → M'` with *invertible* differential (a local diffeomorphism)
between manifolds modelled on the **same** model space `E`, and a Riemannian metric `g'` on
`M'`, the pulled-back metric `h = f^*g'` (`RiemannianMetric.pullbackOfSmoothImmersion`) has
Christoffel symbols related to those of `g'` by the classical inhomogeneous transformation law

`df(Γ^h(v, w)) = Γ^{g'}(df·v, df·w) + D²F(v, w)`,   `F = chart reading of f`.

This is the map-analog of `chartChristoffelContraction_change` (the chart-transition special
case). Because `f` is a local diffeomorphism between equidimensional manifolds, the chart reading
`F = φ'_{β'} ∘ f ∘ φ_α.symm : E → E` is a self-map of the model space `E` with invertible
derivative, so the algebra of `Connection/ChartChristoffelChange.lean` transfers verbatim, with
`F` in place of the chart transition `τ`.

The single new analytic input is the **Gram change law** for the pullback metric
(`chartGramOnE_mapReading`): `G^h_{ij}(y) = Σ_{pq} G^{g'}_{pq}(F y) A^p_i(y) A^q_j(y)`, where
`A^p_i = ∂F^p/∂y^i`. Its zeroth-order piece was isolated in `PullbackChristoffel.lean`
(`chartGramOnE_pullbackOfSmoothImmersion`); here it is upgraded to the `A`-coordinate form.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3 (`lem:dc-ch7-3-4-rays-are-geodesics`);
Lee, *Riemannian Manifolds*, Ch. 5 (the transformation law for the Christoffel symbols).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian

open Riemannian.Tensor RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'} [I'.Boundaryless]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ## The chart reading of `f` and its calculus -/

/-- **Math.** The chart reading of `f : M → M'` from the chart at `α` (source) to the chart at
`β'` (target): the self-map `F = φ'_{β'} ∘ f ∘ φ_α.symm : E → E` of the model space. -/
def mapReading (f : M → M') (α : M) (β' : M') : E → E :=
  extChartAt I' β' ∘ f ∘ (extChartAt I α).symm

@[simp] lemma mapReading_def (f : M → M') (α : M) (β' : M') (y : E) :
    mapReading (I := I) (I' := I') f α β' y
      = extChartAt I' β' (f ((extChartAt I α).symm y)) := rfl

/-- **Math.** The domain of the chart reading of `f`, in `α`-chart coordinates: the `y` in the
`α`-chart target whose foot `φ_α.symm y` is mapped by `f` into the chart source at `β'`. -/
def mapReadingSource (f : M → M') (α : M) (β' : M') : Set E :=
  (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (f ⁻¹' (extChartAt I' β').source)

lemma mem_mapReadingSource_iff {f : M → M'} {α : M} {β' : M'} {y : E} :
    y ∈ mapReadingSource (I := I) (I' := I') f α β'
      ↔ y ∈ (extChartAt I α).target
          ∧ f ((extChartAt I α).symm y) ∈ (extChartAt I' β').source := Iff.rfl

/-- **Math.** On the domain, the foot lies in the chart source at `α`. -/
lemma extChartAt_symm_mem_source_of_mem_mapReadingSource {f : M → M'} {α : M} {β' : M'} {y : E}
    (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β') :
    (extChartAt I α).symm y ∈ (chartAt H α).source := by
  have := (extChartAt I α).map_target hy.1
  rwa [extChartAt_source] at this

/-- **Math.** On the domain, `f` of the foot lies in the chart source at `β'`. -/
lemma image_mem_source_of_mem_mapReadingSource {f : M → M'} {α : M} {β' : M'} {y : E}
    (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β') :
    f ((extChartAt I α).symm y) ∈ (chartAt H' β').source := by
  have h : f ((extChartAt I α).symm y) ∈ (extChartAt I' β').source := hy.2
  rwa [extChartAt_source] at h

/-- **Math.** The domain of the chart reading of `f` is open (both charts boundaryless, `f`
continuous). -/
lemma isOpen_mapReadingSource {f : M → M'} (himm : DCSmoothImmersion (I := I) (I' := I') f)
    (α : M) (β' : M') :
    IsOpen (mapReadingSource (I := I) (I' := I') f α β') := by
  refine ContinuousOn.isOpen_inter_preimage (continuousOn_extChartAt_symm α)
    (isOpen_extChartAt_target α) ?_
  exact himm.1.continuous.isOpen_preimage _ (isOpen_extChartAt_source β')

/-- **Math.** On the domain, pulling the reading back through the target chart recovers `f` of the
foot. -/
lemma extChartAt_symm_mapReading {f : M → M'} {α : M} {β' : M'} {y : E}
    (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β') :
    (extChartAt I' β').symm (mapReading (I := I) (I' := I') f α β' y)
      = f ((extChartAt I α).symm y) := by
  rw [mapReading_def]
  exact (extChartAt I' β').left_inv hy.2

/-- **Math.** On the domain, the reading lands in the target-chart target. -/
lemma mapReading_mem_target {f : M → M'} {α : M} {β' : M'} {y : E}
    (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β') :
    mapReading (I := I) (I' := I') f α β' y ∈ (extChartAt I' β').target := by
  rw [mapReading_def]
  exact (extChartAt I' β').map_source hy.2

/-- **Math.** The chart reading of `f` is `C^∞` at each point of its (open) domain: a composite of
the smooth chart inverse, the smooth `f`, and the smooth chart. -/
lemma contDiffAt_mapReading {f : M → M'} (himm : DCSmoothImmersion (I := I) (I' := I') f)
    {α : M} {β' : M'} {y : E} (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β') :
    ContDiffAt ℝ ∞ (mapReading (I := I) (I' := I') f α β') y := by
  -- chart inverse: smooth `𝓘(ℝ,E) → I` at `y`
  have h1 : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm y := by
    have := contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
    exact this.contMDiffAt ((isOpen_extChartAt_target (I := I) α).mem_nhds hy.1)
  -- `f`: smooth everywhere
  have h2 : ContMDiffAt I I' ∞ f ((extChartAt I α).symm y) := himm.1.contMDiffAt
  -- chart: smooth `I' → 𝓘(ℝ,E)` at `f x`
  have hfsrc : f ((extChartAt I α).symm y) ∈ (chartAt H' β').source :=
    image_mem_source_of_mem_mapReadingSource (I := I) (I' := I') hy
  have h3 : ContMDiffAt I' 𝓘(ℝ, E) ∞ (extChartAt I' β') (f ((extChartAt I α).symm y)) :=
    (contMDiffOn_extChartAt (I := I') (n := ∞) (x := β')).contMDiffAt
      ((chartAt H' β').open_source.mem_nhds hfsrc)
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (mapReading (I := I) (I' := I') f α β') y :=
    (h3.comp _ h2).comp _ h1
  rw [contMDiffAt_iff_contDiffAt] at hcomp
  exact hcomp

/-- **Math.** A smooth local diffeomorphism `f : M → M'` (same model space `E`) is a smooth
immersion: its differential is a linear equivalence, hence injective. -/
lemma dcSmoothImmersion_of_isLocalDiffeomorph {f : M → M'}
    (hf : IsLocalDiffeomorph I I' ∞ f) :
    DCSmoothImmersion (I := I) (I' := I') f :=
  ⟨hf.contMDiff, fun x => by
    have hc := hf.mfderivToContinuousLinearEquiv_coe (n := ∞) (by simp) x
    simp only [← hc, ContinuousLinearEquiv.coe_coe]
    exact (hf.mfderivToContinuousLinearEquiv (by simp) x).injective⟩

/-! ## The derivative of the chart reading and its identification with `df` -/

/-- **Math.** The chart-inverse differential is invertible at every target point (boundaryless
model). -/
lemma isInvertible_mfderiv_extChartAt_symm' {α : M} {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y).IsInvertible := by
  have h := isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := α) hy
  rwa [I.range_eq_univ, mfderivWithin_univ] at h

/-- **Math.** The chart-inverse differential sends the model basis vector `finBasis i` to the
chart frame vector `chartBasisVecFiber α i` at the foot. Inverse of
`mfderiv_extChartAt_chartBasisVecFiber`. -/
lemma mfderiv_extChartAt_symm_finBasis {α : M} {y : E}
    (hy : y ∈ (extChartAt I α).target) (i : Fin (Module.finrank ℝ E)) :
    mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y ((Module.finBasis ℝ E) i)
      = chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y) := by
  have hxsrc : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    have := (extChartAt I α).map_target hy; rwa [extChartAt_source] at this
  have hxsrc' : (extChartAt I α).symm y ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hxsrc
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm y := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := α) hy
    rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hchart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) ((extChartAt I α).symm y) :=
    mdifferentiableAt_extChartAt (I := I) hxsrc
  -- `mfderiv φ (φ.symm y) ∘ mfderiv φ.symm y = id` from `φ ∘ φ.symm =ᶠ id` near `y`
  have hcomp := mfderiv_comp y (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E)) hchart hsymm
  have heq : (extChartAt I α) ∘ (extChartAt I α).symm =ᶠ[𝓝 y] id := by
    filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hy] with z hz
    exact (extChartAt I α).right_inv hz
  have hid : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((extChartAt I α) ∘ (extChartAt I α).symm) y
      = ContinuousLinearMap.id ℝ E := by
    rw [heq.mfderiv_eq]; exact mfderiv_id
  have hcompid : (mfderiv I 𝓘(ℝ, E) (extChartAt I α) ((extChartAt I α).symm y)).comp
      (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y) = ContinuousLinearMap.id ℝ E :=
    hcomp.symm.trans hid
  -- inject through `mfderiv φ (φ.symm y)`
  have hinj : Function.Injective (mfderiv I 𝓘(ℝ, E) (extChartAt I α) ((extChartAt I α).symm y)) :=
    (isInvertible_mfderiv_extChartAt (I := I) (x := α) hxsrc').injective
  apply hinj
  rw [mfderiv_extChartAt_chartBasisVecFiber (I := I) α i hxsrc,
    ← ContinuousLinearMap.comp_apply, hcompid]
  rfl

/-- **Math.** **The differential of the chart reading `F` reads `df` in coordinates.** On the
domain, `∂F/∂y^i(y) = dφ'_{β'}(df_x X_i)`, where `x = φ_α.symm y` and `X_i = chartBasisVecFiber`.
The chain rule for `F = φ'_{β'} ∘ f ∘ φ_α.symm`, using that `dφ_α.symm` sends `finBasis i` to the
chart frame vector `X_i` (`mfderiv_extChartAt_symm_finBasis`). -/
lemma fderiv_mapReading_finBasis {f : M → M'}
    (himm : DCSmoothImmersion (I := I) (I' := I') f)
    {α : M} {β' : M'} {y : E} (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β')
    (i : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (mapReading (I := I) (I' := I') f α β') y ((Module.finBasis ℝ E) i)
      = mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') (f ((extChartAt I α).symm y))
          (mfderiv I I' f ((extChartAt I α).symm y)
            (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))) := by
  have hfxsrc : f ((extChartAt I α).symm y) ∈ (chartAt H' β').source :=
    image_mem_source_of_mem_mapReadingSource (I := I) (I' := I') hy
  have hd_symm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm y := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := α) hy.1
    rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hd_f : MDifferentiableAt I I' f ((extChartAt I α).symm y) :=
    (himm.1.contMDiffAt).mdifferentiableAt (by simp)
  have hd_chart : MDifferentiableAt I' 𝓘(ℝ, E) (extChartAt I' β')
      (f ((extChartAt I α).symm y)) := mdifferentiableAt_extChartAt (I := I') hfxsrc
  -- Two applied chain rules (explicit inner functions to avoid decomposition ambiguity).
  have e1 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (mapReading (I := I) (I' := I') f α β') y
        ((Module.finBasis ℝ E) i)
      = mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') (f ((extChartAt I α).symm y))
          (mfderiv 𝓘(ℝ, E) I' (fun z => f ((extChartAt I α).symm z)) y
            ((Module.finBasis ℝ E) i)) :=
    mfderiv_comp_apply (g := extChartAt I' β') (f := fun z => f ((extChartAt I α).symm z))
      (x := y) hd_chart (hd_f.comp y hd_symm) ((Module.finBasis ℝ E) i)
  have e2 : mfderiv 𝓘(ℝ, E) I' (fun z => f ((extChartAt I α).symm z)) y
        ((Module.finBasis ℝ E) i)
      = mfderiv I I' f ((extChartAt I α).symm y)
          (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y ((Module.finBasis ℝ E) i)) :=
    mfderiv_comp_apply (g := f) (f := fun z => (extChartAt I α).symm z) (x := y)
      hd_f hd_symm ((Module.finBasis ℝ E) i)
  have hfd : fderiv ℝ (mapReading (I := I) (I' := I') f α β') y ((Module.finBasis ℝ E) i)
      = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (mapReading (I := I) (I' := I') f α β') y
          ((Module.finBasis ℝ E) i) :=
    (DFunLike.congr_fun mfderiv_eq_fderiv ((Module.finBasis ℝ E) i)).symm
  rw [hfd, e1, e2, mfderiv_extChartAt_symm_finBasis (I := I) hy.1 i]

/-! ## The Gram change law for the pullback metric -/

/-- **Math.** `A^p_i(y) = ∂F^p/∂y^i(y)`: the chart-frame components of `df`, the map-analog of
`transitionDeriv`. -/
def mapDeriv (f : M → M') (α : M) (β' : M') (p i : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  Geodesic.chartCoord (E := E) p
    (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y ((Module.finBasis ℝ E) i))

@[simp] lemma mapDeriv_def (f : M → M') (α : M) (β' : M')
    (p i : Fin (Module.finrank ℝ E)) (y : E) :
    mapDeriv (I := I) (I' := I') f α β' p i y
      = Geodesic.chartCoord (E := E) p
          (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y ((Module.finBasis ℝ E) i)) := rfl

/-- **Math.** `B^p_{ki}(y) = ∂²F^p/∂y^k∂y^i(y)`: the map-analog of `transitionSndDeriv`. -/
def mapSndDeriv (f : M → M') (α : M) (β' : M') (p k i : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  Geodesic.chartCoord (E := E) p
    (fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y ((Module.finBasis ℝ E) k)
      ((Module.finBasis ℝ E) i))

@[simp] lemma mapSndDeriv_def (f : M → M') (α : M) (β' : M')
    (p k i : Fin (Module.finrank ℝ E)) (y : E) :
    mapSndDeriv (I := I) (I' := I') f α β' p k i y
      = Geodesic.chartCoord (E := E) p
          (fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y
            ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) i)) := rfl

/-- **Math.** Linearity of `g'.metricInner` in the first argument over a `Finset`-indexed
smul-sum. -/
lemma metricInner_sum_smul_left (g' : RiemannianMetric I' M') {z : M'}
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (v : ι → TangentSpace I' z) (w : TangentSpace I' z) :
    g'.metricInner z (∑ p ∈ s, a p • v p) w
      = ∑ p ∈ s, a p * g'.metricInner z (v p) w := by
  rw [RiemannianMetric.metricInner_apply, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, RiemannianMetric.metricInner_apply]

/-- **Math.** Linearity of `g'.metricInner` in the second argument over a `Finset`-indexed
smul-sum. -/
lemma metricInner_sum_smul_right (g' : RiemannianMetric I' M') {z : M'}
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (v : TangentSpace I' z) (w : ι → TangentSpace I' z) :
    g'.metricInner z v (∑ q ∈ s, a q • w q)
      = ∑ q ∈ s, a q * g'.metricInner z v (w q) := by
  rw [RiemannianMetric.metricInner_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, smul_eq_mul, RiemannianMetric.metricInner_apply]

/-- **Math.** **Frame expansion of a tangent vector via the target chart.** Any tangent vector `w`
at `z ∈ (chartAt H' β').source` decomposes over the chart frame `X'_p(z)` with the chart
coordinates of its differential image as coefficients: `w = Σ_p (dφ'_{β'} w)^p X'_p(z)`. -/
lemma tangent_eq_sum_chartCoord_mfderiv {β' : M'} {z : M'}
    (hz : z ∈ (chartAt H' β').source) (w : TangentSpace I' z) :
    w = ∑ p, (Geodesic.chartCoord (E := E) p
        (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') z w))
      • chartBasisVecFiber (I := I') β' p z := by
  have hzsrc' : z ∈ (extChartAt I' β').source := by rw [extChartAt_source]; exact hz
  have hinj : Function.Injective (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') z) :=
    (isInvertible_mfderiv_extChartAt (I := I') (x := β') hzsrc').injective
  apply hinj
  have hLw : mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') z w
      = ∑ p, Geodesic.chartCoord (E := E) p
          (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') z w) • (Module.finBasis ℝ E) p := by
    conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr
      (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') z w)]
    exact Finset.sum_congr rfl fun p _ => by rw [Geodesic.chartCoord_def]
  have hR : mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') z
      (∑ p, Geodesic.chartCoord (E := E) p
          (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') z w)
        • chartBasisVecFiber (I := I') β' p z)
      = ∑ p, Geodesic.chartCoord (E := E) p
          (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') z w) • (Module.finBasis ℝ E) p := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul]
    congr 1
    exact mfderiv_extChartAt_chartBasisVecFiber (I := I') β' p hz
  rw [hR]; exact hLw

/-- **Math.** **The pullback metric's chart-Gram matrix in the `A`-coordinate (transformation
law) form.** On the domain of the chart reading,
`G^{f^*g'}_{ij}(y) = Σ_{pq} G^{g'}_{pq}(F y) A^p_i(y) A^q_j(y)`, the map-analog of
`chartGramOnE_chartTransition`. The zeroth-order step of the Christoffel transformation law under
`f`. Proof: expand `df X_i`, `df X_j` over the target chart frame
(`tangent_eq_sum_chartCoord_mfderiv`) with coefficients `A^p_i` (`fderiv_mapReading_finBasis`);
bilinearity of `g'` collects the target chart-Gram matrix. -/
theorem chartGramOnE_mapReading {f : M → M'}
    (himm : DCSmoothImmersion (I := I) (I' := I') f) (g' : RiemannianMetric I' M')
    {α : M} {β' : M'} {y : E} (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β')
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α i j y
      = ∑ p, ∑ q, chartGramOnE (I := I') g' β' p q
            (mapReading (I := I) (I' := I') f α β' y)
          * mapDeriv (I := I) (I' := I') f α β' p i y
          * mapDeriv (I := I) (I' := I') f α β' q j y := by
  classical
  set x := (extChartAt I α).symm y with hx
  have hxsrc : x ∈ (chartAt H α).source :=
    extChartAt_symm_mem_source_of_mem_mapReadingSource (I := I) (I' := I') hy
  have hfxsrc : f x ∈ (chartAt H' β').source :=
    image_mem_source_of_mem_mapReadingSource (I := I) (I' := I') hy
  -- The differential images `df X_i` expanded over the target chart frame, coefficients `A^p_i`.
  have hdfi : ∀ i, mfderiv I I' f x (chartBasisVecFiber (I := I) α i x)
      = ∑ p, mapDeriv (I := I) (I' := I') f α β' p i y
          • chartBasisVecFiber (I := I') β' p (f x) := by
    intro i
    have hframe := tangent_eq_sum_chartCoord_mfderiv (I' := I') (β' := β') hfxsrc
      (mfderiv I I' f x (chartBasisVecFiber (I := I) α i x))
    rw [hframe]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mapDeriv_def, fderiv_mapReading_finBasis (I := I) (I' := I') himm hy i, ← hx]
  -- Compute the LHS through the pullback Gram identity and bilinearity.
  rw [chartGramOnE_pullbackOfSmoothImmersion g' f himm α i j y, ← hx, hdfi i, hdfi j,
    metricInner_sum_smul_left]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [metricInner_sum_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hGpq : chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
      = g'.metricInner (f x) (chartBasisVecFiber (I := I') β' p (f x))
          (chartBasisVecFiber (I := I') β' q (f x)) := by
    rw [chartGramOnE_def, extChartAt_symm_mapReading (I := I) (I' := I') hy, ← hx,
      chartGramMatrix_apply, RiemannianMetric.metricInner_apply]
  rw [hGpq]
  ring

/-! ## Second-order calculus of the chart reading (mirrors the transition case) -/

/-- **Math.** The moving map derivative `y ↦ DF(y)` is differentiable on the domain, with
derivative the second derivative of `F`. -/
lemma hasFDerivAt_fderiv_mapReading {f : M → M'}
    (himm : DCSmoothImmersion (I := I) (I' := I') f) {α : M} {β' : M'} {y : E}
    (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β') :
    HasFDerivAt (fderiv ℝ (mapReading (I := I) (I' := I') f α β'))
      (fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y := by
    refine (contDiffAt_mapReading himm hy).fderiv_right ?_
    exact WithTop.coe_le_coe.2 le_top
  exact (h1.differentiableAt one_ne_zero).hasFDerivAt

/-- **Math.** The matrix entry `A^a_i` is differentiable on the domain, with partial derivatives
the second-derivative coefficients `B^a_{ki}`. -/
lemma hasFDerivAt_mapDeriv {f : M → M'}
    (himm : DCSmoothImmersion (I := I) (I' := I') f) {α : M} {β' : M'} {y : E}
    (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β')
    (a i : Fin (Module.finrank ℝ E)) :
    HasFDerivAt (mapDeriv (I := I) (I' := I') f α β' a i)
      ((Geodesic.chartCoordFunctional (E := E) a).comp
        ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).comp
          (fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y))) y := by
  have h2 := hasFDerivAt_fderiv_mapReading himm hy
  have h3 := ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).hasFDerivAt.comp y h2)
  exact (Geodesic.chartCoordFunctional (E := E) a).hasFDerivAt.comp y h3

/-- **Math.** **Schwarz symmetry** of the map's second derivative in the two differentiation
directions: `∂²F^a/∂y^k∂y^i = ∂²F^a/∂y^i∂y^k` on the domain. -/
lemma mapSndDeriv_symm {f : M → M'}
    (himm : DCSmoothImmersion (I := I) (I' := I') f) {α : M} {β' : M'} {y : E}
    (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β')
    (a k i : Fin (Module.finrank ℝ E)) :
    mapSndDeriv (I := I) (I' := I') f α β' a k i y
      = mapSndDeriv (I := I) (I' := I') f α β' a i k y := by
  have hsymm : IsSymmSndFDerivAt ℝ (mapReading (I := I) (I' := I') f α β') y := by
    refine (contDiffAt_mapReading himm hy).isSymmSndFDerivAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  rw [mapSndDeriv_def, mapSndDeriv_def, hsymm.eq]

/-- **Math.** The chart reading `F` differentiates at each domain point. -/
lemma hasFDerivAt_mapReading {f : M → M'}
    (himm : DCSmoothImmersion (I := I) (I' := I') f) {α : M} {β' : M'} {y : E}
    (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β') :
    HasFDerivAt (mapReading (I := I) (I' := I') f α β')
      (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y) y :=
  ((contDiffAt_mapReading himm hy).differentiableAt (by simp)).hasFDerivAt

/-! ## Step 2: the derivative of the Gram change law -/

/-- **Math.** **Derivative of the pullback Gram change law** (the first-order layer): on the
domain,
`∂_k G^{f^*g'}_{ij} = Σ_{pq} [(Σ_c ∂_c G^{g'}_{pq}(F y) A^c_k) A^p_i A^q_j
+ G^{g'}_{pq}(F y) (B^p_{ki} A^q_j + A^p_i B^q_{kj})]`.
Product rule on `chartGramOnE_mapReading`; the derivative of the moving map derivative brings in
the second derivative of `F` (the Hessian of `f`). Map-analog of
`partialDeriv_chartGramOnE_chartTransition`. -/
theorem partialDeriv_chartGramOnE_mapReading {f : M → M'}
    (himm : DCSmoothImmersion (I := I) (I' := I') f) (g' : RiemannianMetric I' M')
    {α : M} {β' : M'} {y : E} (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β')
    (k i j : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) k
        (chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α i j) y
      = ∑ p, ∑ q,
          ((∑ c, partialDeriv (E := E) c (chartGramOnE (I := I') g' β' p q)
                (mapReading (I := I) (I' := I') f α β' y)
              * mapDeriv (I := I) (I' := I') f α β' c k y)
            * mapDeriv (I := I) (I' := I') f α β' p i y
            * mapDeriv (I := I) (I' := I') f α β' q j y
          + chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
            * (mapSndDeriv (I := I) (I' := I') f α β' p k i y
                * mapDeriv (I := I) (I' := I') f α β' q j y
              + mapDeriv (I := I) (I' := I') f α β' p i y
                * mapSndDeriv (I := I) (I' := I') f α β' q k j y)) := by
  classical
  have heq : chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α i j =ᶠ[𝓝 y]
      (fun z => ∑ p, ∑ q,
        chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' z)
          * mapDeriv (I := I) (I' := I') f α β' p i z
          * mapDeriv (I := I) (I' := I') f α β' q j z) := by
    filter_upwards [(isOpen_mapReadingSource himm α β').mem_nhds hy] with z hz
    exact chartGramOnE_mapReading himm g' hz i j
  have hF' : HasFDerivAt (mapReading (I := I) (I' := I') f α β')
      (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y) y := hasFDerivAt_mapReading himm hy
  have hG : ∀ p q : Fin (Module.finrank ℝ E),
      HasFDerivAt (chartGramOnE (I := I') g' β' p q)
        (fderiv ℝ (chartGramOnE (I := I') g' β' p q)
          (mapReading (I := I) (I' := I') f α β' y))
        (mapReading (I := I) (I' := I') f α β' y) := fun p q => by
    have hcd : ContDiffAt ℝ ∞ (chartGramOnE (I := I') g' β' p q)
        (mapReading (I := I) (I' := I') f α β' y) :=
      (chartGramOnE_contDiffOn (I := I') g' β' p q).contDiffAt
        ((isOpen_extChartAt_target (I := I') β').mem_nhds (mapReading_mem_target hy))
    exact (hcd.differentiableAt (by simp)).hasFDerivAt
  have hcomp : ∀ p q : Fin (Module.finrank ℝ E),
      HasFDerivAt
        (fun z => chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' z))
        ((fderiv ℝ (chartGramOnE (I := I') g' β' p q)
            (mapReading (I := I) (I' := I') f α β' y)).comp
          (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y)) y :=
    fun p q => (hG p q).comp y hF'
  have hF : HasFDerivAt
      (fun z => ∑ p, ∑ q,
        chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' z)
          * mapDeriv (I := I) (I' := I') f α β' p i z
          * mapDeriv (I := I) (I' := I') f α β' q j z)
      (∑ p, ∑ q,
        ((chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
            * mapDeriv (I := I) (I' := I') f α β' p i y)
          • ((Geodesic.chartCoordFunctional (E := E) q).comp
              ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) j)).comp
                (fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y)))
        + mapDeriv (I := I) (I' := I') f α β' q j y
          • (chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
              • ((Geodesic.chartCoordFunctional (E := E) p).comp
                  ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).comp
                    (fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y)))
            + mapDeriv (I := I) (I' := I') f α β' p i y
              • ((fderiv ℝ (chartGramOnE (I := I') g' β' p q)
                    (mapReading (I := I) (I' := I') f α β' y)).comp
                  (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y))))) y := by
    exact HasFDerivAt.fun_sum fun p _ => HasFDerivAt.fun_sum fun q _ =>
      ((hcomp p q).fun_mul (hasFDerivAt_mapDeriv himm hy p i)).fun_mul
        (hasFDerivAt_mapDeriv himm hy q j)
  have hpd : partialDeriv (E := E) k
        (chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α i j) y
      = fderiv ℝ (chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α i j) y
          ((Module.finBasis ℝ E) k) := rfl
  rw [hpd, heq.fderiv_eq, hF.fderiv]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have hsum : fderiv ℝ (chartGramOnE (I := I') g' β' p q)
        (mapReading (I := I) (I' := I') f α β' y)
      (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y ((Module.finBasis ℝ E) k))
      = ∑ c, partialDeriv (E := E) c (chartGramOnE (I := I') g' β' p q)
            (mapReading (I := I) (I' := I') f α β' y)
          * Geodesic.chartCoord (E := E) c
              (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y ((Module.finBasis ℝ E) k)) := by
    rw [fderiv_apply_eq_sum_partialDeriv]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    Geodesic.chartCoordFunctional_apply, smul_eq_mul, mapDeriv_def, mapSndDeriv_def]
  rw [hsum]
  ring

/-! ## Step 3: invertibility and the transported contraction identity -/

/-- **Math.** The chart-reading derivative is the composite of the (bijective) chart-inverse
differential, the differential of `f`, and the (bijective) chart differential. -/
lemma fderiv_mapReading_comp {f : M → M'}
    (himm : DCSmoothImmersion (I := I) (I' := I') f) {α : M} {β' : M'} {y : E}
    (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β') :
    fderiv ℝ (mapReading (I := I) (I' := I') f α β') y
      = (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') (f ((extChartAt I α).symm y))).comp
          ((mfderiv I I' f ((extChartAt I α).symm y)).comp
            (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y)) := by
  have hfxsrc : f ((extChartAt I α).symm y) ∈ (chartAt H' β').source :=
    image_mem_source_of_mem_mapReadingSource (I := I) (I' := I') hy
  have hd_symm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm y := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := α) hy.1
    rwa [I.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hd_f : MDifferentiableAt I I' f ((extChartAt I α).symm y) :=
    (himm.1.contMDiffAt).mdifferentiableAt (by simp)
  have hd_chart : MDifferentiableAt I' 𝓘(ℝ, E) (extChartAt I' β')
      (f ((extChartAt I α).symm y)) := mdifferentiableAt_extChartAt (I := I') hfxsrc
  have hc1 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (mapReading (I := I) (I' := I') f α β') y
      = (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') (f ((extChartAt I α).symm y))).comp
          (mfderiv 𝓘(ℝ, E) I' (f ∘ (extChartAt I α).symm) y) :=
    mfderiv_comp y hd_chart (hd_f.comp y hd_symm)
  have hc2 : mfderiv 𝓘(ℝ, E) I' (f ∘ (extChartAt I α).symm) y
      = (mfderiv I I' f ((extChartAt I α).symm y)).comp
          (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y) :=
    mfderiv_comp y hd_f hd_symm
  rw [← mfderiv_eq_fderiv, hc1, hc2]

/-- **Math.** The chart-reading derivative is surjective (composite of bijections: `f` is a local
diffeomorphism, so `df` is a linear equivalence, and the chart differentials are invertible). -/
lemma surjective_fderiv_mapReading {f : M → M'} (hf : IsLocalDiffeomorph I I' ∞ f)
    {α : M} {β' : M'} {y : E} (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β') :
    Function.Surjective (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y) := by
  have himm := dcSmoothImmersion_of_isLocalDiffeomorph hf
  have hfxsrc' : f ((extChartAt I α).symm y) ∈ (extChartAt I' β').source := hy.2
  have hsymm_surj : Function.Surjective (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y) :=
    (isInvertible_mfderiv_extChartAt_symm' hy.1).surjective
  have hchart_surj : Function.Surjective
      (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') (f ((extChartAt I α).symm y))) :=
    (isInvertible_mfderiv_extChartAt (I := I') (x := β') hfxsrc').surjective
  have hf_surj : Function.Surjective (mfderiv I I' f ((extChartAt I α).symm y)) := by
    have hcoe := hf.mfderivToContinuousLinearEquiv_coe (n := ∞) (by simp)
      ((extChartAt I α).symm y)
    simp only [← hcoe, ContinuousLinearEquiv.coe_coe]
    exact (hf.mfderivToContinuousLinearEquiv (n := ∞) (by simp)
      ((extChartAt I α).symm y)).surjective
  rw [fderiv_mapReading_comp himm hy]
  exact hchart_surj.comp (hf_surj.comp hsymm_surj)

/-- **Math.** The chart-reading derivative is injective (composite of injections: `f` is a local
diffeomorphism and the chart differentials are invertible). This is what cancels `A` in the
geodesic map-transfer. -/
lemma injective_fderiv_mapReading {f : M → M'} (hf : IsLocalDiffeomorph I I' ∞ f)
    {α : M} {β' : M'} {y : E} (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β') :
    Function.Injective (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y) := by
  have himm := dcSmoothImmersion_of_isLocalDiffeomorph hf
  have hfxsrc' : f ((extChartAt I α).symm y) ∈ (extChartAt I' β').source := hy.2
  have hsymm_inj : Function.Injective (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y) :=
    (isInvertible_mfderiv_extChartAt_symm' hy.1).injective
  have hchart_inj : Function.Injective
      (mfderiv I' 𝓘(ℝ, E) (extChartAt I' β') (f ((extChartAt I α).symm y))) :=
    (isInvertible_mfderiv_extChartAt (I := I') (x := β') hfxsrc').injective
  have hf_inj : Function.Injective (mfderiv I I' f ((extChartAt I α).symm y)) := himm.2 _
  rw [fderiv_mapReading_comp himm hy]
  exact hchart_inj.comp (hf_inj.comp hsymm_inj)

/-- **Math.** Cancellation of the (surjective) map derivative: a covector that annihilates every
column `A e_a = df X_a` of the map derivative vanishes. -/
lemma eq_zero_of_forall_sum_mul_mapDeriv {f : M → M'} (hf : IsLocalDiffeomorph I I' ∞ f)
    {α : M} {β' : M'} {y : E} (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β')
    (u : Fin (Module.finrank ℝ E) → ℝ)
    (h : ∀ a, ∑ p, u p * mapDeriv (I := I) (I' := I') f α β' p a y = 0) :
    ∀ p, u p = 0 := by
  classical
  have hsurj := surjective_fderiv_mapReading hf hy
  -- the covector `Σ_p u_p (·)^p` vanishes on the whole image of `DF(y)`
  have hzero : ∀ w : E,
      ∑ p, u p * Geodesic.chartCoord (E := E) p
        (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y w) = 0 := by
    intro w
    have hexpand : ∀ p, Geodesic.chartCoord (E := E) p
        (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y w)
        = ∑ a, Geodesic.chartCoord (E := E) a w *
            Geodesic.chartCoord (E := E) p
              (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y ((Module.finBasis ℝ E) a)) :=
      fun p => chartCoord_clm_eq_sum (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y) p w
    simp only [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    have step : ∀ a : Fin (Module.finrank ℝ E),
        (∑ p, u p * (Geodesic.chartCoord (E := E) a w *
            Geodesic.chartCoord (E := E) p
              (fderiv ℝ (mapReading (I := I) (I' := I') f α β') y ((Module.finBasis ℝ E) a))))
          = Geodesic.chartCoord (E := E) a w *
              ∑ p, u p * mapDeriv (I := I) (I' := I') f α β' p a y := by
      intro a
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [mapDeriv_def]; ring
    simp only [step, h, mul_zero, Finset.sum_const_zero]
  intro p₀
  obtain ⟨w, hw⟩ := hsurj ((Module.finBasis ℝ E) p₀)
  have hval := hzero w
  rw [hw] at hval
  have hite : ∀ p, Geodesic.chartCoord (E := E) p ((Module.finBasis ℝ E) p₀)
      = if p₀ = p then (1 : ℝ) else 0 := fun p => chartCoord_finBasis p p₀
  simp only [hite, mul_ite, mul_one, mul_zero] at hval
  simpa [Fintype.sum_ite_eq] using hval

/-- **Math.** The purely algebraic core of the contraction-transport identity (identical to the
chart-transition case): substituting the differentiated Gram change law into the contraction
identity, the second-derivative cross-terms cancel (Schwarz symmetry of `B` and symmetry of `G`)
and the `∂G` combination reassembles by the contraction identity. -/
theorem christoffelTransport_key {n : ℕ} (G : Fin n → Fin n → ℝ)
    (dG : Fin n → Fin n → Fin n → ℝ) (A : Fin n → Fin n → ℝ)
    (B : Fin n → Fin n → Fin n → ℝ) (Γ : Fin n → Fin n → Fin n → ℝ) (a k i : Fin n)
    (hG : ∀ p q, G p q = G q p) (hB : ∀ p x z, B p x z = B p z x)
    (hΓ : ∀ p c d, (∑ q, G p q * Γ c d q)
      = (1 / 2 : ℝ) * (dG c p d + dG d p c - dG p c d)) :
    (1 / 2 : ℝ) * ((∑ p, ∑ q, ((∑ c, dG c p q * A c k) * A p a * A q i
          + G p q * (B p k a * A q i + A p a * B q k i)))
        + (∑ p, ∑ q, ((∑ c, dG c p q * A c i) * A p a * A q k
            + G p q * (B p i a * A q k + A p a * B q i k)))
        - (∑ p, ∑ q, ((∑ c, dG c p q * A c a) * A p k * A q i
            + G p q * (B p a k * A q i + A p k * B q a i))))
      = ∑ p, A p a * (∑ q, G p q * ((∑ c, ∑ d, Γ c d q * A c k * A d i)
          + B q k i)) := by
  have comm3 : ∀ (F : Fin n → Fin n → Fin n → ℝ),
      (∑ x, ∑ y, ∑ z, F x y z) = ∑ z, ∑ x, ∑ y, F x y z := by
    intro F
    have h1 : (∑ x, ∑ y, ∑ z, F x y z) = ∑ x, ∑ z, ∑ y, F x y z :=
      Finset.sum_congr rfl fun x _ => by rw [Finset.sum_comm]
    rw [h1, Finset.sum_comm]
  have hT1 : (∑ p, ∑ q, ((∑ c, dG c p q * A c k) * A p a * A q i
        + G p q * (B p k a * A q i + A p a * B q k i)))
      = (∑ p, ∑ q, ∑ c, dG c p q * A c k * A p a * A q i)
        + ((∑ p, ∑ q, G p q * (B p k a * A q i))
          + ∑ p, ∑ q, G p q * (A p a * B q k i)) := by
    simp only [Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  have hT2 : (∑ p, ∑ q, ((∑ c, dG c p q * A c i) * A p a * A q k
        + G p q * (B p i a * A q k + A p a * B q i k)))
      = (∑ p, ∑ q, ∑ c, dG c p q * A c i * A p a * A q k)
        + ((∑ p, ∑ q, G p q * (B p i a * A q k))
          + ∑ p, ∑ q, G p q * (A p a * B q i k)) := by
    simp only [Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  have hT3 : (∑ p, ∑ q, ((∑ c, dG c p q * A c a) * A p k * A q i
        + G p q * (B p a k * A q i + A p k * B q a i)))
      = (∑ p, ∑ q, ∑ c, dG c p q * A c a * A p k * A q i)
        + ((∑ p, ∑ q, G p q * (B p a k * A q i))
          + ∑ p, ∑ q, G p q * (A p k * B q a i)) := by
    simp only [Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  have hS15 : (∑ p, ∑ q, G p q * (B p k a * A q i))
      = ∑ p, ∑ q, G p q * (B p a k * A q i) :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rw [hB p k a]
  have hS42 : (∑ p, ∑ q, G p q * (A p a * B q i k))
      = ∑ p, ∑ q, G p q * (A p a * B q k i) :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rw [hB q i k]
  have hS36 : (∑ p, ∑ q, G p q * (B p i a * A q k))
      = ∑ p, ∑ q, G p q * (A p k * B q a i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rw [hG q p, hB q i a]; ring
  have hD1 : (∑ p, ∑ q, ∑ c, dG c p q * A c k * A p a * A q i)
      = ∑ p, ∑ c, ∑ d, dG c p d * (A p a * A c k * A d i) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
      ring
  have hD2 : (∑ p, ∑ q, ∑ c, dG c p q * A c i * A p a * A q k)
      = ∑ p, ∑ c, ∑ d, dG d p c * (A p a * A c k * A d i) :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by ring
  have hD3 : (∑ p, ∑ q, ∑ c, dG c p q * A c a * A p k * A q i)
      = ∑ p, ∑ c, ∑ d, dG p c d * (A p a * A c k * A d i) :=
    (comm3 fun x y z => dG z x y * A z a * A x k * A y i).trans
      (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun d _ => by ring)
  have hE : (∑ p, ∑ c, ∑ d, ((1 / 2 : ℝ) * (dG c p d + dG d p c - dG p c d))
        * (A p a * A c k * A d i))
      = (1 / 2 : ℝ) * ((∑ p, ∑ c, ∑ d, dG c p d * (A p a * A c k * A d i))
          + (∑ p, ∑ c, ∑ d, dG d p c * (A p a * A c k * A d i))
          - ∑ p, ∑ c, ∑ d, dG p c d * (A p a * A c k * A d i)) := by
    simp only [show ∀ x y z w : ℝ, ((1 / 2 : ℝ) * (x + y - z)) * w
        = (1 / 2 : ℝ) * (x * w) + (1 / 2 : ℝ) * (y * w) - (1 / 2 : ℝ) * (z * w)
        from fun x y z w => by ring,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have h1 : ∀ p, A p a * (∑ q, G p q * ((∑ c, ∑ d, Γ c d q * A c k * A d i)
        + B q k i))
      = (∑ c, ∑ d, ((1 / 2 : ℝ) * (dG c p d + dG d p c - dG p c d))
          * (A p a * A c k * A d i))
        + ∑ q, G p q * (A p a * B q k i) := by
    intro p
    simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    congr 1
    · refine (comm3 fun x y z =>
        A p a * (G p z * (Γ x y z * A x k * A y i))).symm.trans ?_
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      rw [← hΓ p c d, Finset.sum_mul]
      exact Finset.sum_congr rfl fun q _ => by ring
    · exact Finset.sum_congr rfl fun q _ => by ring
  have hR : (∑ p, A p a * (∑ q, G p q * ((∑ c, ∑ d, Γ c d q * A c k * A d i)
        + B q k i)))
      = (∑ p, ∑ c, ∑ d, ((1 / 2 : ℝ) * (dG c p d + dG d p c - dG p c d))
          * (A p a * A c k * A d i))
        + ∑ p, ∑ q, G p q * (A p a * B q k i) := by
    rw [Finset.sum_congr rfl fun p _ => h1 p]
    exact Finset.sum_add_distrib
  rw [hT1, hT2, hT3, hR, hE, hD1, hD2, hD3, hS15, hS36, hS42]
  ring

/-- **Math.** **The transported contraction identity for the pullback metric.** Substituting the
differentiated pullback Gram change law into the source contraction identity, the map-analog of
`sum_gram_mul_christoffel_transition`. -/
theorem sum_gram_mul_christoffel_mapReading {f : M → M'}
    (himm : DCSmoothImmersion (I := I) (I' := I') f) (g' : RiemannianMetric I' M')
    {α : M} {β' : M'} {y : E} (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β')
    (a k i : Fin (Module.finrank ℝ E)) :
    ∑ m, chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α a m y
        * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y
      = ∑ p, mapDeriv (I := I) (I' := I') f α β' p a y
          * (∑ q, chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
              * ((∑ c, ∑ d,
                    chartChristoffel (I := I') g' β' c d q
                        (mapReading (I := I) (I' := I') f α β' y)
                      * mapDeriv (I := I) (I' := I') f α β' c k y
                      * mapDeriv (I := I) (I' := I') f α β' d i y)
                + mapSndDeriv (I := I) (I' := I') f α β' q k i y)) := by
  classical
  have hxsrc : (extChartAt I α).symm y ∈ (chartAt H α).source :=
    extChartAt_symm_mem_source_of_mem_mapReadingSource (I := I) (I' := I') hy
  have hfxsrc : f ((extChartAt I α).symm y) ∈ (chartAt H' β').source :=
    image_mem_source_of_mem_mapReadingSource (I := I) (I' := I') hy
  have hfootsrc : (extChartAt I α).symm y
      ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hxsrc
  have hfoottgt : (extChartAt I' β').symm (mapReading (I := I) (I' := I') f α β' y)
      ∈ (trivializationAt E (TangentSpace I') β').baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      extChartAt_symm_mapReading (I := I) (I' := I') hy]
    exact hfxsrc
  rw [chartGram_christoffel_contraction (I := I) (pullbackOfSmoothImmersion g' f himm)
      α a k i y hfootsrc,
    partialDeriv_chartGramOnE_mapReading himm g' hy k a i,
    partialDeriv_chartGramOnE_mapReading himm g' hy i a k,
    partialDeriv_chartGramOnE_mapReading himm g' hy a k i]
  exact christoffelTransport_key
    (fun p q => chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y))
    (fun c p q => partialDeriv (E := E) c (chartGramOnE (I := I') g' β' p q)
      (mapReading (I := I) (I' := I') f α β' y))
    (fun p x => mapDeriv (I := I) (I' := I') f α β' p x y)
    (fun p x z => mapSndDeriv (I := I) (I' := I') f α β' p x z y)
    (fun c d q => chartChristoffel (I := I') g' β' c d q
      (mapReading (I := I) (I' := I') f α β' y))
    a k i
    (fun p q => chartGramOnE_symm (I := I') g' β' p q _)
    (fun p x z => mapSndDeriv_symm himm hy p x z)
    (fun p c d => chartGram_christoffel_contraction (I := I') g' β' p c d
      (mapReading (I := I) (I' := I') f α β' y) hfoottgt)

/-- **Math.** Direct expansion of the same contraction through the pullback Gram change law
(map-analog of `sum_gram_mul_christoffel_expand`). -/
theorem sum_gram_mul_christoffel_expand_mapReading {f : M → M'}
    (himm : DCSmoothImmersion (I := I) (I' := I') f) (g' : RiemannianMetric I' M')
    {α : M} {β' : M'} {y : E} (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β')
    (a k i : Fin (Module.finrank ℝ E)) :
    ∑ m, chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α a m y
        * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y
      = ∑ p, mapDeriv (I := I) (I' := I') f α β' p a y
          * (∑ q, chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
              * (∑ m, mapDeriv (I := I) (I' := I') f α β' q m y
                  * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y)) := by
  classical
  have hG : ∀ m, chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α a m y
      = ∑ p, ∑ q, chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
          * mapDeriv (I := I) (I' := I') f α β' p a y
          * mapDeriv (I := I) (I' := I') f α β' q m y :=
    fun m => chartGramOnE_mapReading himm g' hy a m
  have hLHS : ∑ m, chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α a m y
        * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y
      = ∑ p, ∑ q, ∑ m,
          chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
          * mapDeriv (I := I) (I' := I') f α β' p a y
          * mapDeriv (I := I) (I' := I') f α β' q m y
          * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y := by
    calc ∑ m, chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α a m y
          * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y
        = ∑ m, (∑ p, ∑ q,
              chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
              * mapDeriv (I := I) (I' := I') f α β' p a y
              * mapDeriv (I := I) (I' := I') f α β' q m y)
            * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y :=
          Finset.sum_congr rfl fun m _ => by rw [hG m]
      _ = ∑ m, ∑ p, ∑ q,
              chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
              * mapDeriv (I := I) (I' := I') f α β' p a y
              * mapDeriv (I := I) (I' := I') f α β' q m y
              * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y := by
          simp_rw [Finset.sum_mul]
      _ = ∑ p, ∑ q, ∑ m,
              chartGramOnE (I := I') g' β' p q (mapReading (I := I) (I' := I') f α β' y)
              * mapDeriv (I := I) (I' := I') f α β' p a y
              * mapDeriv (I := I) (I' := I') f α β' q m y
              * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
  rw [hLHS]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **Math.** **Transformation law for the chart Christoffel symbols under `f`, index form.** On
the domain, `Σ_m A^q_m Γ^{h,m}_{ki} = Σ_{cd} Γ^{g',q}_{cd}(F y) A^c_k A^d_i + B^q_{ki}` — the
classical inhomogeneous transformation law, with the Hessian of `f` as inhomogeneity. Map-analog
of `sum_transitionDeriv_mul_chartChristoffel`. -/
theorem sum_mapDeriv_mul_chartChristoffel {f : M → M'} (hf : IsLocalDiffeomorph I I' ∞ f)
    (g' : RiemannianMetric I' M') {α : M} {β' : M'} {y : E}
    (hy : y ∈ mapReadingSource (I := I) (I' := I') f α β')
    (k i q : Fin (Module.finrank ℝ E)) :
    ∑ m, mapDeriv (I := I) (I' := I') f α β' q m y
        * chartChristoffel (I := I)
            (pullbackOfSmoothImmersion g' f (dcSmoothImmersion_of_isLocalDiffeomorph hf)) α k i m y
      = (∑ c, ∑ d,
          chartChristoffel (I := I') g' β' c d q (mapReading (I := I) (I' := I') f α β' y)
            * mapDeriv (I := I) (I' := I') f α β' c k y
            * mapDeriv (I := I) (I' := I') f α β' d i y)
        + mapSndDeriv (I := I) (I' := I') f α β' q k i y := by
  classical
  set himm := dcSmoothImmersion_of_isLocalDiffeomorph hf with hhimm
  set W : Fin (Module.finrank ℝ E) → ℝ := fun q' =>
      (∑ m, mapDeriv (I := I) (I' := I') f α β' q' m y
          * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y)
        - ((∑ c, ∑ d,
              chartChristoffel (I := I') g' β' c d q' (mapReading (I := I) (I' := I') f α β' y)
                * mapDeriv (I := I) (I' := I') f α β' c k y
                * mapDeriv (I := I) (I' := I') f α β' d i y)
            + mapSndDeriv (I := I) (I' := I') f α β' q' k i y) with hW_def
  set U : Fin (Module.finrank ℝ E) → ℝ := fun p =>
      ∑ q', chartGramOnE (I := I') g' β' p q' (mapReading (I := I) (I' := I') f α β' y) * W q'
    with hU_def
  have hzero' : ∀ a, ∑ p, mapDeriv (I := I) (I' := I') f α β' p a y * U p = 0 := by
    intro a
    have hexp := sum_gram_mul_christoffel_expand_mapReading himm g' hy a k i
    have htra := sum_gram_mul_christoffel_mapReading himm g' hy a k i
    have key : ∑ p, mapDeriv (I := I) (I' := I') f α β' p a y * U p
        = (∑ p, mapDeriv (I := I) (I' := I') f α β' p a y
              * (∑ q', chartGramOnE (I := I') g' β' p q'
                  (mapReading (I := I) (I' := I') f α β' y)
                  * (∑ m, mapDeriv (I := I) (I' := I') f α β' q' m y
                      * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm)
                          α k i m y)))
          - (∑ p, mapDeriv (I := I) (I' := I') f α β' p a y
              * (∑ q', chartGramOnE (I := I') g' β' p q'
                  (mapReading (I := I) (I' := I') f α β' y)
                  * ((∑ c, ∑ d,
                        chartChristoffel (I := I') g' β' c d q'
                            (mapReading (I := I) (I' := I') f α β' y)
                          * mapDeriv (I := I) (I' := I') f α β' c k y
                          * mapDeriv (I := I) (I' := I') f α β' d i y)
                    + mapSndDeriv (I := I) (I' := I') f α β' q' k i y))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← mul_sub]
      congr 1
      simp only [hU_def, hW_def]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q' _ => ?_
      rw [← mul_sub]
    rw [key, ← hexp, ← htra, sub_self]
  have hzero : ∀ a, ∑ p, U p * mapDeriv (I := I) (I' := I') f α β' p a y = 0 := by
    intro a
    rw [← hzero' a]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  have hU0 : ∀ p, U p = 0 :=
    eq_zero_of_forall_sum_mul_mapDeriv hf hy U hzero
  have hfoottgt : (extChartAt I' β').symm (mapReading (I := I) (I' := I') f α β' y)
      ∈ (trivializationAt E (TangentSpace I') β').baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      extChartAt_symm_mapReading (I := I) (I' := I') hy]
    exact image_mem_source_of_mem_mapReadingSource (I := I) (I' := I') hy
  have hW0 : ∀ q', W q' = 0 :=
    eq_zero_of_forall_sum_chartGramOnE_mul (I := I') g' (α := β')
      (y' := mapReading (I := I) (I' := I') f α β' y) hfoottgt W hU0
  have := hW0 q
  simp only [hW_def] at this
  exact sub_eq_zero.mp this

/-! ## Step 4: the bilinear transformation law -/

/-- **Math.** **Christoffel transformation law under `f`, bilinear form** (do Carmo Ch. 7,
`lem:dc-ch7-3-4-rays-are-geodesics`; the naturality of the Levi-Civita connection under a local
diffeomorphism). With `A = dF(φ_α x) = df` read in coordinates and `D²F` the Hessian of `f`,
`A (Γ^{f^*g'}(v, w)(φ_α x)) = Γ^{g'}(A v, A w)(φ_β' (f x)) + D²F(v, w)`.
Equivalently the geodesic operator `γ'' + Γ(γ', γ')` transforms by `A` alone, so `γ` is an
`f^*g'`-geodesic iff `f ∘ γ` is a `g'`-geodesic. Map-analog of
`chartChristoffelContraction_change`. -/
theorem chartChristoffelContraction_mapReading {f : M → M'} (hf : IsLocalDiffeomorph I I' ∞ f)
    (g' : RiemannianMetric I' M') {α : M} {β' : M'} {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ' : f x ∈ (chartAt H' β').source) (v w : E) :
    fderiv ℝ (mapReading (I := I) (I' := I') f α β') (extChartAt I α x)
        (Geodesic.chartChristoffelContraction (I := I)
          (pullbackOfSmoothImmersion g' f (dcSmoothImmersion_of_isLocalDiffeomorph hf)) α v w
          (extChartAt I α x))
      = Geodesic.chartChristoffelContraction (I := I') g' β'
          (fderiv ℝ (mapReading (I := I) (I' := I') f α β') (extChartAt I α x) v)
          (fderiv ℝ (mapReading (I := I) (I' := I') f α β') (extChartAt I α x) w)
          (extChartAt I' β' (f x))
        + fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) (extChartAt I α x) v w := by
  classical
  set himm := dcSmoothImmersion_of_isLocalDiffeomorph hf with hhimm
  have hxα' : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hxα
  have hxβ'' : f x ∈ (extChartAt I' β').source := by rw [extChartAt_source]; exact hxβ'
  have hy : extChartAt I α x ∈ mapReadingSource (I := I) (I' := I') f α β' := by
    refine ⟨(extChartAt I α).map_source hxα', ?_⟩
    rw [mem_preimage, (extChartAt I α).left_inv hxα']
    exact hxβ''
  have hxsymm : (extChartAt I α).symm (extChartAt I α x) = x := (extChartAt I α).left_inv hxα'
  have hτx : mapReading (I := I) (I' := I') f α β' (extChartAt I α x) = extChartAt I' β' (f x) := by
    rw [mapReading_def, hxsymm]
  set y := extChartAt I α x with hy_def
  set A : E →L[ℝ] E := fderiv ℝ (mapReading (I := I) (I' := I') f α β') y with hA_def
  have sum4_swap_outer : ∀ (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      (∑ c, ∑ d, ∑ k, ∑ i, F c d k i) = ∑ k, ∑ i, ∑ c, ∑ d, F c d k i := by
    intro F
    have key : (∑ z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          F z.1 z.2.1 z.2.2.1 z.2.2.2)
        = ∑ z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          F z.2.2.1 z.2.2.2 z.1 z.2.1 :=
      Fintype.sum_bijective (fun z => (z.2.2.1, z.2.2.2, z.1, z.2.1))
        (Function.Involutive.bijective (fun _ => rfl)) _ _ (fun _ => rfl)
    simpa only [Fintype.sum_prod_type] using key
  have sum3_rotate : ∀ (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ),
      (∑ m, ∑ k, ∑ i, F m k i) = ∑ k, ∑ i, ∑ m, F m k i := by
    intro F
    have hbij : Function.Bijective
        (fun z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E) => (z.2.1, z.2.2, z.1)) :=
      (Equiv.mk (fun z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) => (z.2.1, z.2.2, z.1))
        (fun z => (z.2.2, z.1, z.2.1)) (fun _ => rfl) (fun _ => rfl)).bijective
    have key : (∑ z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E), F z.1 z.2.1 z.2.2)
        = ∑ z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E), F z.2.2 z.1 z.2.1 :=
      Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
    simpa only [Fintype.sum_prod_type] using key
  refine (Module.finBasis ℝ E).ext_elem fun p => ?_
  rw [← Geodesic.chartCoord_def, ← Geodesic.chartCoord_def, Geodesic.chartCoord_add]
  have hLHS : Geodesic.chartCoord (E := E) p
      (A (Geodesic.chartChristoffelContraction (I := I)
        (pullbackOfSmoothImmersion g' f himm) α v w y))
      = (∑ k, ∑ i, Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w *
          (∑ c, ∑ d, chartChristoffel (I := I') g' β' c d p
                (mapReading (I := I) (I' := I') f α β' y)
              * mapDeriv (I := I) (I' := I') f α β' c k y
              * mapDeriv (I := I) (I' := I') f α β' d i y))
        + ∑ k, ∑ i, Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w *
            mapSndDeriv (I := I) (I' := I') f α β' p k i y := by
    rw [hA_def, chartCoord_clm_eq_sum]
    simp only [chartCoord_chartChristoffelContraction, ← mapDeriv_def, Finset.sum_mul]
    rw [sum3_rotate]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsub := sum_mapDeriv_mul_chartChristoffel hf g' hy k i p
    calc ∑ m, chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y
            * Geodesic.chartCoord (E := E) k v
            * Geodesic.chartCoord (E := E) i w * mapDeriv (I := I) (I' := I') f α β' p m y
        = Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w
            * ∑ m, mapDeriv (I := I) (I' := I') f α β' p m y
                * chartChristoffel (I := I) (pullbackOfSmoothImmersion g' f himm) α k i m y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
      _ = Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w
            * ((∑ c, ∑ d, chartChristoffel (I := I') g' β' c d p
                    (mapReading (I := I) (I' := I') f α β' y)
                  * mapDeriv (I := I) (I' := I') f α β' c k y
                  * mapDeriv (I := I) (I' := I') f α β' d i y)
              + mapSndDeriv (I := I) (I' := I') f α β' p k i y) := by rw [hsub]
      _ = _ := by ring
  have hR1 : Geodesic.chartCoord (E := E) p
      (Geodesic.chartChristoffelContraction (I := I') g' β' (A v) (A w) (extChartAt I' β' (f x)))
      = ∑ k, ∑ i, Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w *
          (∑ c, ∑ d, chartChristoffel (I := I') g' β' c d p
                (mapReading (I := I) (I' := I') f α β' y)
              * mapDeriv (I := I) (I' := I') f α β' c k y
              * mapDeriv (I := I) (I' := I') f α β' d i y) := by
    rw [← hτx, chartCoord_chartChristoffelContraction]
    have hcv : ∀ c, Geodesic.chartCoord (E := E) c (A v)
        = ∑ k, Geodesic.chartCoord (E := E) k v * mapDeriv (I := I) (I' := I') f α β' c k y := by
      intro c
      rw [hA_def, chartCoord_clm_eq_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mapDeriv_def]
    have hcw : ∀ d, Geodesic.chartCoord (E := E) d (A w)
        = ∑ i, Geodesic.chartCoord (E := E) i w * mapDeriv (I := I) (I' := I') f α β' d i y := by
      intro d
      rw [hA_def, chartCoord_clm_eq_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mapDeriv_def]
    simp only [hcv, hcw, Finset.mul_sum, Finset.sum_mul]
    rw [sum4_swap_outer, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hR2 : Geodesic.chartCoord (E := E) p
      (((fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y) v) w)
      = ∑ k, ∑ i, Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w *
          mapSndDeriv (I := I) (I' := I') f α β' p k i y := by
    have hgv : ∀ v', (((fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y) v') w)
        = ((ContinuousLinearMap.apply ℝ E w).comp
            (fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y)) v' := fun v' => rfl
    rw [hgv, chartCoord_clm_eq_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hgv2 : Geodesic.chartCoord (E := E) p
        (((ContinuousLinearMap.apply ℝ E w).comp
            (fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y))
              ((Module.finBasis ℝ E) k))
        = Geodesic.chartCoord (E := E) p
            (((fderiv ℝ (fderiv ℝ (mapReading (I := I) (I' := I') f α β')) y)
              ((Module.finBasis ℝ E) k)) w) := rfl
    rw [hgv2, chartCoord_clm_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mapSndDeriv_def]
    ring
  rw [hLHS, hR1, hR2]

end Riemannian

end
