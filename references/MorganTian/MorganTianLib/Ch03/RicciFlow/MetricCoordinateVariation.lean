import MorganTianLib.Ch03.RicciFlow.MetricVariation
import DoCarmoLib.Riemannian.Connection.ChartChristoffel

/-!
# Coordinate formulas for metric variations

This file transfers a pointwise metric variation to the fixed chart frames used
by the coordinate formulas for the Levi-Civita connection and curvature.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace MorganTianLib

section MixedPartial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

set_option maxHeartbeats 800000 in
/-- **Math.** Let `F` be `C²` in time and space near `(t, y)`. The time
derivative of the spatial component `DF(s,y)(0,v)` is the mixed second
derivative with the spatial direction first and the time direction second.
The order shown in the result is obtained from Schwarz symmetry. -/
theorem hasDerivAt_spatialFDeriv_timeLine
    {F : ℝ × V → ℝ} {t : ℝ} {y : V}
    (hF : ContDiffAt ℝ 2 F (t, y)) (v : V) :
    HasDerivAt
      (fun s => fderiv ℝ F (s, y) ((0 : ℝ), v))
      (fderiv ℝ (fderiv ℝ F) (t, y) ((0 : ℝ), v) ((1 : ℝ), 0)) t := by
  have hD : HasFDerivAt (fderiv ℝ F)
      (fderiv ℝ (fderiv ℝ F) (t, y)) (t, y) :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : V)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have happ := (hD.comp_hasDerivAt t hline).clm_apply
    (hasDerivAt_const t ((0 : ℝ), v))
  have hsymm := (hF.isSymmSndFDerivAt (by norm_num)).eq
    ((1 : ℝ), (0 : V)) ((0 : ℝ), v)
  have hderiv :
      fderiv ℝ (fderiv ℝ F) (t, y) ((1 : ℝ), (0 : V)) ((0 : ℝ), v)
          + (fderiv ℝ F (t, y)) 0 =
        fderiv ℝ (fderiv ℝ F) (t, y) ((0 : ℝ), v) ((1 : ℝ), (0 : V)) := by
    simpa using hsymm
  simpa only [Function.comp_apply] using happ.congr_deriv hderiv

set_option maxHeartbeats 800000 in
/-- **Math.** For a jointly smooth scalar function, a locally identified time
derivative may be differentiated in a fixed spatial direction. This converts
the joint Fréchet mixed derivative into the partial derivative of the time
variation. -/
theorem hasDerivAt_spatialPartial_timeLine
    {F : ℝ × V → ℝ} {K : V → ℝ} {J : Set ℝ} {U : Set V}
    (hjoint : ContDiffOn ℝ ∞ F (J ×ˢ U))
    {t : ℝ} (ht : t ∈ interior J) {y : V} (hy : y ∈ U)
    (hU : IsOpen U)
    (htime : ∀ y' ∈ U, HasDerivAt (fun s => F (s, y')) (K y') t)
    (v : V) :
    HasDerivAt
      (fun s => fderiv ℝ (fun y' => F (s, y')) y v)
      (fderiv ℝ K y v) t := by
  have hF : ContDiffAt ℝ 2 F (t, y) := by
    exact (contDiffOn_infty.mp hjoint 2).contDiffAt
      (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) (hU.mem_nhds hy))
  have htimeEq : K =ᶠ[nhds y]
      (fun y' => fderiv ℝ F (t, y') ((1 : ℝ), (0 : V))) := by
    filter_upwards [hU.mem_nhds hy] with y' hy'
    have hFy' : ContDiffAt ℝ 1 F (t, y') := by
      exact (contDiffOn_infty.mp hjoint 1).contDiffAt
        (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) (hU.mem_nhds hy'))
    have hlineDiff : DifferentiableAt ℝ (fun s : ℝ => (s, y')) t :=
      differentiableAt_id.prodMk (differentiableAt_const y')
    have hlineDeriv : deriv (fun s : ℝ => (s, y')) t = ((1 : ℝ), (0 : V)) :=
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y')).deriv
    have hchain := fderiv_comp_deriv t
      (hFy'.differentiableAt (by norm_num)) hlineDiff
    rw [hlineDeriv] at hchain
    calc
      K y' = deriv (fun s => F (s, y')) t := (htime y' hy').deriv.symm
      _ = fderiv ℝ F (t, y') ((1 : ℝ), (0 : V)) := by
        simpa [Function.comp_def] using hchain
  have hD : HasFDerivAt (fderiv ℝ F)
      (fderiv ℝ (fderiv ℝ F) (t, y)) (t, y) :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hspace : HasFDerivAt (fun y' : V => (t, y'))
      ((0 : V →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ V)) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have htimeMap : HasFDerivAt
      ((fderiv ℝ F) ∘ fun y' : V => (t, y'))
      ((fderiv ℝ (fderiv ℝ F) (t, y)).comp
        ((0 : V →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ V))) y :=
    @HasFDerivAt.comp ℝ _ V _ _ (ℝ × V) _ _ ((ℝ × V) →L[ℝ] ℝ) _ _
      (fun y' : V => (t, y'))
      ((0 : V →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ V)) y
      (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (t, y)) hD hspace
  change HasFDerivAt (fun y' : V => fderiv ℝ F (t, y')) _ y at htimeMap
  have htimeDirection := htimeMap.clm_apply
    (hasFDerivAt_const ((1 : ℝ), (0 : V)) y)
  have hK : fderiv ℝ K y v =
      fderiv ℝ (fderiv ℝ F) (t, y) ((0 : ℝ), v) ((1 : ℝ), (0 : V)) := by
    rw [htimeEq.fderiv_eq]
    have heq := congrArg (fun L : V →L[ℝ] ℝ => L v) htimeDirection.fderiv
    simpa using heq
  have hsliceEq :
      (fun s => fderiv ℝ (fun y' => F (s, y')) y v) =ᶠ[nhds t]
      (fun s => fderiv ℝ F (s, y) ((0 : ℝ), v)) := by
    filter_upwards [isOpen_interior.mem_nhds ht] with s hs
    have hFs : ContDiffAt ℝ 1 F (s, y) := by
      exact (contDiffOn_infty.mp hjoint 1).contDiffAt
        (prod_mem_nhds (mem_interior_iff_mem_nhds.mp hs) (hU.mem_nhds hy))
    have hembed : HasFDerivAt (fun y' : V => (s, y'))
        ((0 : V →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ V)) y :=
      (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
    have hslice :=
      (hFs.differentiableAt (by norm_num)).hasFDerivAt.comp y hembed
    have heq := congrArg (fun L : V →L[ℝ] ℝ => L v) hslice.fderiv
    simpa [Function.comp_def] using heq
  have hmixed := hasDerivAt_spatialFDeriv_timeLine hF v
  exact (hmixed.congr_deriv hK.symm).congr_of_eventuallyEq hsliceEq

end MixedPartial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

set_option synthInstance.maxHeartbeats 100000 in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Joint smoothness of an evolving metric section gives joint
smoothness of every Gram-matrix entry in a fixed chart frame, on the chart
trivialization base and the prescribed time set. -/
theorem contMDiffOn_chartGramMatrix_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ =>
        Riemannian.Tensor.chartGramMatrix (I := I) (g z.2) α z.1 i j)
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ J) := by
  let e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun z : M × ℝ =>
      HorizontalTangentSpace I M z →L[ℝ]
        HorizontalTangentSpace I M z →L[ℝ] ℝ) (α, 0)
  have hebase : e.baseSet =
      (trivializationAt E (TangentSpace I) α).baseSet ×ˢ (Set.univ : Set ℝ) := by
    ext z
    simp [e, HorizontalTangentSpace]
    change z.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet ↔ _
    rw [trivializationAt_baseSet_eq_chartAt_source]
  have hsection : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (horizontalMetricSection g)
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ J) :=
    hg.mono fun z hz => ⟨Set.mem_univ z.1, hz.2⟩
  have hmaps : Set.MapsTo (horizontalMetricSection g)
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ J) e.source := by
    intro z hz
    apply e.mem_source.mpr
    rw [hebase]
    exact ⟨hz.1, Set.mem_univ z.2⟩
  have hcoord := (((e.contMDiffOn_iff hmaps).mp hsection).2)
  have hentry :=
    (hcoord.clm_apply (f := fun _ => (Module.finBasis ℝ E) i) contMDiffOn_const).clm_apply
      (f := fun _ => (Module.finBasis ℝ E) j) contMDiffOn_const
  refine hentry.congr fun z hz => ?_
  have hzbase : z ∈ (trivializationAt E (HorizontalTangentSpace I M) (α, 0)).baseSet := by
    change z.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact hz.1
  change _ = (ContinuousLinearMap.inCoordinates E (HorizontalTangentSpace I M)
      (E →L[ℝ] ℝ)
      (fun q : M × ℝ => HorizontalTangentSpace I M q →L[ℝ] ℝ)
      (α, 0) z (α, 0) z ((g z.2).inner z.1))
        ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial (M × ℝ) ℝ)
    hzbase hzbase (by simp)]
  have heHsymm (v : E) :
      (trivializationAt E (HorizontalTangentSpace I M) (α, 0)).symm z v =
        (trivializationAt E (TangentSpace I) α).symm z.1 v := by
    let eH := trivializationAt E (HorizontalTangentSpace I M) (α, 0)
    let eT := trivializationAt E (TangentSpace I) α
    apply (eT.continuousLinearEquivAt ℝ z.1 hz.1).injective
    change (eT ⟨z.1, eH.symm z v⟩).2 = (eT ⟨z.1, eT.symm z.1 v⟩).2
    have heH_apply (w : HorizontalTangentSpace I M z) :
        (eH ⟨z, w⟩).2 = (eT ⟨z.1, w⟩).2 := by
      let f : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; I, M⟯ := ContMDiffMap.fst
      change ((@trivializationAt (M × ℝ) E _ _
        ((f : M × ℝ → M) *ᵖ (TangentSpace I : M → Type _))
        (Pullback.TotalSpace.topologicalSpace E (TangentSpace I) f) _
        (FiberBundle.pullback f) (α, 0)) ⟨z, w⟩).2 = _
      change ((((trivializationAt E (TangentSpace I) (f (α, 0))).pullback f)
        ⟨z, w⟩).2) = _
      rfl
    rw [← heH_apply]
    have hH := congrArg Prod.snd (eH.apply_mk_symm hzbase v)
    have hT := congrArg Prod.snd (eT.apply_mk_symm hz.1 v)
    exact hH.trans hT.symm
  have htriv : (trivializationAt ℝ (Bundle.Trivial (M × ℝ) ℝ) (α, 0)) =
      Bundle.Trivial.trivialization (M × ℝ) ℝ :=
    Bundle.Trivial.eq_trivialization (M × ℝ) ℝ _
  simp only [htriv, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  rw [heHsymm, heHsymm]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** In a fixed chart, the Gram entries of a smooth metric family are
jointly smooth in time and Euclidean chart coordinates. -/
theorem contDiffOn_chartGramOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartGramOnE (I := I) (g z.1) α i j z.2)
      (J ×ˢ (extChartAt I α).target) := by
  have hsymm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
      (fun z : ℝ × E => (extChartAt I α).symm z.2)
      (J ×ˢ (extChartAt I α).target) :=
    (contMDiffOn_extChartAt_symm (I := I) α).comp
      contMDiffOn_snd fun z hz => hz.2
  have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × E => ((extChartAt I α).symm z.2, z.1))
      (J ×ˢ (extChartAt I α).target) :=
    hsymm.prodMk contMDiffOn_fst
  have hmaps : MapsTo
      (fun z : ℝ × E => ((extChartAt I α).symm z.2, z.1))
      (J ×ˢ (extChartAt I α).target)
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ J) := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    refine ⟨?_, hs⟩
    change (extChartAt I α).symm y ∈ (chartAt H α).source
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I α]
    exact (extChartAt I α).map_target hy
  have hcomp :=
    (contMDiffOn_chartGramMatrix_timeSpace hg α i j).comp hmap hmaps
  rw [@chartedSpaceSelf_prod ℝ E _ _] at hcomp
  rw [← @modelWithCornersSelf_prod ℝ _ ℝ _ _ E _ _] at hcomp
  simpa [Function.comp_def, chartGramOnE_def] using hcomp.contDiffOn

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** At an interior time and inside the chart target, a jointly smooth
Gram entry is `C²`; hence its time and spatial derivatives commute. -/
theorem contDiffAt_chartGramOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ interior J)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    ContDiffAt ℝ 2
      (fun z : ℝ × E => chartGramOnE (I := I) (g z.1) α i j z.2)
      (t, y) := by
  exact (contDiffOn_infty.mp (contDiffOn_chartGramOnE_timeSpace hg α i j) 2).contDiffAt
    (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht)
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hy))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The fixed-chart component of a covariant two-tensor variation. -/
def chartMetricVariationOnE
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  h t ((extChartAt I α).symm y)
    (Tensor.chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
    (Tensor.chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The fixed-chart inverse-metric variation
`∂ₜG⁻¹ = -G⁻¹(∂ₜG)G⁻¹`. -/
def chartInvMetricVariationOnE
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (α : M) (c b : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  - ∑ a, ∑ d,
      Tensor.chartInvGramMatrix (I := I) (g t) α ((extChartAt I α).symm y) c a
        * chartMetricVariationOnE (I := I) h t α a d y
        * Tensor.chartInvGramMatrix (I := I) (g t) α ((extChartAt I α).symm y) d b

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The fixed-chart first variation of a Levi-Civita Christoffel
symbol, obtained by differentiating its inverse-Gram/first-Gram-derivative
formula. -/
def chartChristoffelVariationOnE
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (α : M) (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, (
    chartInvMetricVariationOnE (I := I) g h t α k l y *
      (partialDeriv (E := E) i (chartGramOnE (I := I) (g t) α l j) y +
       partialDeriv (E := E) j (chartGramOnE (I := I) (g t) α l i) y -
       partialDeriv (E := E) l (chartGramOnE (I := I) (g t) α i j) y) +
    Tensor.chartInvGramMatrix (I := I) (g t) α ((extChartAt I α).symm y) k l *
      (partialDeriv (E := E) i (chartMetricVariationOnE (I := I) h t α l j) y +
       partialDeriv (E := E) j (chartMetricVariationOnE (I := I) h t α l i) y -
       partialDeriv (E := E) l (chartMetricVariationOnE (I := I) h t α i j) y))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The entries of the inverse chart Gram matrix of a smooth metric
family are jointly smooth in time and chart coordinates. -/
theorem contDiffOn_chartInvGramOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E =>
        Tensor.chartInvGramMatrix (I := I) (g z.1) α
          ((extChartAt I α).symm z.2) i j)
      (J ×ˢ (extChartAt I α).target) := by
  classical
  let G : ℝ × E → Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ :=
    fun z a b => chartGramOnE (I := I) (g z.1) α a b z.2
  have hentry : ∀ a b, ContDiffOn ℝ ∞ (fun z => G z a b)
      (J ×ˢ (extChartAt I α).target) := by
    intro a b
    exact contDiffOn_chartGramOnE_timeSpace hg α a b
  have hdet : ContDiffOn ℝ ∞ (fun z => (G z).det)
      (J ×ˢ (extChartAt I α).target) := by
    simp only [Matrix.det_apply]
    refine ContDiffOn.sum fun σ _ => ?_
    exact (contDiffOn_prod fun k _ => hentry (σ k) k).const_smul _
  have hadj : ContDiffOn ℝ ∞ (fun z => (G z).adjugate i j)
      (J ×ˢ (extChartAt I α).target) := by
    have hadjEq : (fun z => (G z).adjugate i j) =
        (fun z => ((G z).updateRow j (Pi.single i (1 : ℝ))).det) := by
      funext z
      exact Matrix.adjugate_apply _ _ _
    rw [hadjEq]
    simp only [Matrix.det_apply]
    refine ContDiffOn.sum fun σ _ => ?_
    apply ContDiffOn.const_smul
    refine contDiffOn_prod fun k _ => ?_
    by_cases hσk : σ k = j
    · have heq :
          (fun z => (G z).updateRow j (Pi.single i (1 : ℝ)) (σ k) k) =
            (fun _ : ℝ × E => (Pi.single
              (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i (1 : ℝ)) k) := by
        funext z
        rw [hσk, Matrix.updateRow_self]
      rw [heq]
      exact contDiffOn_const
    · have heq :
          (fun z => (G z).updateRow j (Pi.single i (1 : ℝ)) (σ k) k) =
            (fun z => G z (σ k) k) := by
        funext z
        rw [Matrix.updateRow_ne hσk]
      rw [heq]
      exact hentry (σ k) k
  have hdet_ne : ∀ z ∈ J ×ˢ (extChartAt I α).target, (G z).det ≠ 0 := by
    rintro ⟨s, y⟩ ⟨_, hy⟩
    have hp : (extChartAt I α).symm y ∈
        (trivializationAt E (TangentSpace I) α).baseSet := by
      change (extChartAt I α).symm y ∈ (chartAt H α).source
      rw [← extChartAt_source (𝕜 := ℝ) (E := E) I α]
      exact (extChartAt I α).map_target hy
    change (Tensor.chartGramMatrix (I := I) (g s) α
      ((extChartAt I α).symm y)).det ≠ 0
    exact ne_of_gt (Tensor.chartGramMatrix_det_pos (I := I) (g s) α hp)
  have hinvEq :
      (fun z : ℝ × E =>
        Tensor.chartInvGramMatrix (I := I) (g z.1) α
          ((extChartAt I α).symm z.2) i j) =
        (fun z => ((G z).det)⁻¹ * (G z).adjugate i j) := by
    funext z
    unfold Tensor.chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (G z).det • (G z).adjugate) i j =
      ((G z).det)⁻¹ * (G z).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hinvEq]
  exact (hdet.inv hdet_ne).mul hadj

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A spatial derivative of a chart Gram entry remains jointly
smooth at interior times. -/
theorem contDiffOn_partialDeriv_chartGramOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    (i j r : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) r
        (chartGramOnE (I := I) (g z.1) α i j) z.2)
      (interior J ×ˢ (extChartAt I α).target) := by
  let F : ℝ × E → ℝ :=
    fun z => chartGramOnE (I := I) (g z.1) α i j z.2
  let S : Set (ℝ × E) := interior J ×ˢ (extChartAt I α).target
  have hS : IsOpen S := isOpen_interior.prod (isOpen_extChartAt_target (I := I) α)
  have hF : ContDiffOn ℝ ∞ F S :=
    (contDiffOn_chartGramOnE_timeSpace hg α i j).mono
      (Set.prod_mono interior_subset Subset.rfl)
  have hDF : ContDiffOn ℝ ∞ (fderiv ℝ F) S :=
    hF.fderiv_of_isOpen hS (by simp)
  have happ : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ F z ((0 : ℝ), (Module.finBasis ℝ E) r)) S := by
    exact hDF.clm_apply contDiffOn_const
  refine happ.congr fun z hz => ?_
  have hFz : DifferentiableAt ℝ F z :=
    ((contDiffOn_infty.mp hF 1).contDiffAt (hS.mem_nhds hz)).differentiableAt
      (by norm_num)
  have hembed : HasFDerivAt (fun y' : E => (z.1, y'))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hslice := hFz.hasFDerivAt.comp z.2 hembed
  have heq := congrArg
    (fun L : E →L[ℝ] ℝ => L ((Module.finBasis ℝ E) r)) hslice.fderiv
  change fderiv ℝ (fun y' => F (z.1, y')) z.2 ((Module.finBasis ℝ E) r) =
    fderiv ℝ F z ((0 : ℝ), (Module.finBasis ℝ E) r)
  simpa [Function.comp_def] using heq

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Christoffel symbols of a smooth metric family are jointly smooth
in time and fixed chart coordinates at interior times. -/
theorem contDiffOn_chartChristoffel_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartChristoffel (I := I) (g z.1) α i j k z.2)
      (interior J ×ˢ (extChartAt I α).target) := by
  classical
  rw [show (fun z : ℝ × E => chartChristoffel (I := I) (g z.1) α i j k z.2) =
      fun z => (1 / 2 : ℝ) * ∑ l,
        Tensor.chartInvGramMatrix (I := I) (g z.1) α
            ((extChartAt I α).symm z.2) k l *
          (partialDeriv (E := E) i (chartGramOnE (I := I) (g z.1) α l j) z.2 +
           partialDeriv (E := E) j (chartGramOnE (I := I) (g z.1) α l i) z.2 -
           partialDeriv (E := E) l (chartGramOnE (I := I) (g z.1) α i j) z.2) by
    funext z
    rw [chartChristoffel_def]]
  exact (contDiffOn_const (c := (1 / 2 : ℝ))).mul
    (ContDiffOn.sum fun l _ => ContDiffOn.mul
      ((contDiffOn_chartInvGramOnE_timeSpace hg α k l).mono
        (Set.prod_mono interior_subset Subset.rfl))
      (((contDiffOn_partialDeriv_chartGramOnE_timeSpace hg α l j i).add
        (contDiffOn_partialDeriv_chartGramOnE_timeSpace hg α l i j)).sub
        (contDiffOn_partialDeriv_chartGramOnE_timeSpace hg α i j l)))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** In a fixed chart frame, the time derivative of the Gram matrix
of a metric family is the matrix of the metric variation in that frame. -/
theorem hasDerivWithinAt_chartGramMatrix
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hh : IsMetricVariationOn g h J)
    {t : ℝ} (ht : t ∈ J) (α p : M) :
    HasDerivWithinAt
      (fun s i j => Riemannian.Tensor.chartGramMatrix (I := I) (g s) α p i j)
      (fun i j => h t p
        (Tensor.chartBasisVecFiber (I := I) α i p)
        (Tensor.chartBasisVecFiber (I := I) α j p)) J t := by
  rw [hasDerivWithinAt_pi]
  intro i
  rw [hasDerivWithinAt_pi]
  intro j
  simpa only [Riemannian.Tensor.chartGramMatrix_apply,
    ← RiemannianMetric.metricInner_apply] using
    hh t ht p (Tensor.chartBasisVecFiber (I := I) α i p)
      (Tensor.chartBasisVecFiber (I := I) α j p)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** After pulling a chart Gram entry back to the model space, its
time derivative is the corresponding chart-frame component of the variation. -/
theorem hasDerivWithinAt_chartGramOnE
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hh : IsMetricVariationOn g h J)
    {t : ℝ} (ht : t ∈ J) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    HasDerivWithinAt
      (fun s => chartGramOnE (I := I) (g s) α i j y)
      (h t ((extChartAt I α).symm y)
        (Tensor.chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
        (Tensor.chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))) J t := by
  simpa only [chartGramOnE_def, Riemannian.Tensor.chartGramMatrix_apply,
    ← RiemannianMetric.metricInner_apply] using
    hh t ht ((extChartAt I α).symm y)
      (Tensor.chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
      (Tensor.chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** For a smooth metric family with variation `h`, time
differentiation commutes with a fixed chart partial derivative:
`∂ₜ(∂ᵣ Gᵢⱼ) = ∂ᵣ hᵢⱼ`. This is the mixed time/space input in the first
variation of the Levi-Civita connection. -/
theorem hasDerivAt_partialDeriv_chartGramOnE
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (hh : IsMetricVariationOn g h J) (α : M)
    (i j r : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ interior J)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    HasDerivAt
      (fun s => partialDeriv (E := E) r
        (chartGramOnE (I := I) (g s) α i j) y)
      (partialDeriv (E := E) r (chartMetricVariationOnE (I := I) h t α i j) y) t := by
  let F : ℝ × E → ℝ :=
    fun z => chartGramOnE (I := I) (g z.1) α i j z.2
  let K : E → ℝ := chartMetricVariationOnE (I := I) h t α i j
  have hjoint : ContDiffOn ℝ ∞ F (J ×ˢ (extChartAt I α).target) :=
    contDiffOn_chartGramOnE_timeSpace hg α i j
  have hF : ContDiffAt ℝ 2 F (t, y) := by
    exact (contDiffOn_infty.mp hjoint 2).contDiffAt
      (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht)
        ((isOpen_extChartAt_target (I := I) α).mem_nhds hy))
  have htimeEq : K =ᶠ[nhds y]
      (fun y' => fderiv ℝ F (t, y') ((1 : ℝ), (0 : E))) := by
    filter_upwards [((isOpen_extChartAt_target (I := I) α).mem_nhds hy)] with y' hy'
    have hmetric : HasDerivAt (fun s => F (s, y')) (K y') t := by
      simpa [F, K, chartMetricVariationOnE] using
        (hasDerivWithinAt_chartGramOnE hh (interior_subset ht) α i j y').hasDerivAt
          (mem_interior_iff_mem_nhds.mp ht)
    have hFy' : ContDiffAt ℝ 1 F (t, y') := by
      exact (contDiffOn_infty.mp hjoint 1).contDiffAt
        (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht)
          ((isOpen_extChartAt_target (I := I) α).mem_nhds hy'))
    have hlineDiff : DifferentiableAt ℝ (fun s : ℝ => (s, y')) t :=
      differentiableAt_id.prodMk (differentiableAt_const y')
    have hlineDeriv : deriv (fun s : ℝ => (s, y')) t = ((1 : ℝ), (0 : E)) :=
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y')).deriv
    have hchain := fderiv_comp_deriv t
      (hFy'.differentiableAt (by norm_num)) hlineDiff
    rw [hlineDeriv] at hchain
    calc
      K y' = deriv (fun s => F (s, y')) t := hmetric.deriv.symm
      _ = fderiv ℝ F (t, y') ((1 : ℝ), (0 : E)) := by
        simpa [Function.comp_def] using hchain
  have hD : HasFDerivAt (fderiv ℝ F)
      (fderiv ℝ (fderiv ℝ F) (t, y)) (t, y) :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hspace : HasFDerivAt (fun y' : E => (t, y'))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have htimeMap : HasFDerivAt
      ((fderiv ℝ F) ∘ fun y' : E => (t, y'))
      ((fderiv ℝ (fderiv ℝ F) (t, y)).comp
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E))) y :=
    @HasFDerivAt.comp ℝ _ E _ _ (ℝ × E) _ _ ((ℝ × E) →L[ℝ] ℝ) _ _
      (fun y' : E => (t, y'))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) y
      (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (t, y)) hD hspace
  change HasFDerivAt (fun y' : E => fderiv ℝ F (t, y')) _ y at htimeMap
  have htimeDirection := htimeMap.clm_apply
    (hasFDerivAt_const ((1 : ℝ), (0 : E)) y)
  have hK : fderiv ℝ K y ((Module.finBasis ℝ E) r) =
      fderiv ℝ (fderiv ℝ F) (t, y)
        ((0 : ℝ), (Module.finBasis ℝ E) r) ((1 : ℝ), (0 : E)) := by
    rw [htimeEq.fderiv_eq]
    have heq := congrArg (fun L : E →L[ℝ] ℝ => L ((Module.finBasis ℝ E) r))
      htimeDirection.fderiv
    simpa using heq
  have hsliceEq :
      (fun s => partialDeriv (E := E) r
        (chartGramOnE (I := I) (g s) α i j) y) =ᶠ[nhds t]
      (fun s => fderiv ℝ F (s, y)
        ((0 : ℝ), (Module.finBasis ℝ E) r)) := by
    filter_upwards [(isOpen_interior.mem_nhds ht)] with s hs
    have hFs : ContDiffAt ℝ 1 F (s, y) := by
      exact (contDiffOn_infty.mp hjoint 1).contDiffAt
        (prod_mem_nhds (mem_interior_iff_mem_nhds.mp hs)
          ((isOpen_extChartAt_target (I := I) α).mem_nhds hy))
    have hembed : HasFDerivAt (fun y' : E => (s, y'))
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) y :=
      (hasFDerivAt_const s y).prodMk (hasFDerivAt_id y)
    have hslice :=
      (hFs.differentiableAt (by norm_num)).hasFDerivAt.comp y hembed
    have heq := congrArg (fun L : E →L[ℝ] ℝ => L ((Module.finBasis ℝ E) r))
      hslice.fderiv
    change fderiv ℝ (fun y' => F (s, y')) y ((Module.finBasis ℝ E) r) = _
    simpa [Function.comp_def] using heq
  have hmixed :=
    hasDerivAt_spatialFDeriv_timeLine hF ((Module.finBasis ℝ E) r)
  have hmixedK := hmixed.congr_deriv hK.symm
  have hresult := hmixedK.congr_of_eventuallyEq hsliceEq
  simpa [K, partialDeriv] using hresult

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Every entry of the inverse chart Gram matrix is differentiable
in time along a metric variation. This is the analytic input for
differentiating `G⁻¹G = 1`. -/
private theorem differentiableWithinAt_chartInvGramMatrix_apply
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hh : IsMetricVariationOn g h J)
    {t : ℝ} (ht : t ∈ J) (α p : M)
    (hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    DifferentiableWithinAt ℝ
      (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p i j) J t := by
  classical
  let G : ℝ → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun s => Riemannian.Tensor.chartGramMatrix (I := I) (g s) α p
  have hentry : ∀ a b, DifferentiableWithinAt ℝ (fun s => G s a b) J t := by
    intro a b
    exact (hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp
      (hasDerivWithinAt_chartGramMatrix hh ht α p) a) b).differentiableWithinAt
  have hdet : DifferentiableWithinAt ℝ (fun s => (G s).det) J t := by
    simp only [Matrix.det_apply]
    refine DifferentiableWithinAt.fun_sum fun σ _ => ?_
    exact (DifferentiableWithinAt.fun_finsetProd fun k _ => hentry (σ k) k).const_smul _
  have hadj : DifferentiableWithinAt ℝ (fun s => (G s).adjugate i j) J t := by
    have hadjEq : (fun s => (G s).adjugate i j) =
        (fun s => ((G s).updateRow j (Pi.single i (1 : ℝ))).det) := by
      funext s
      exact Matrix.adjugate_apply _ _ _
    rw [hadjEq]
    simp only [Matrix.det_apply]
    refine DifferentiableWithinAt.fun_sum fun σ _ => ?_
    apply DifferentiableWithinAt.const_smul
    refine DifferentiableWithinAt.fun_finsetProd fun k _ => ?_
    by_cases hσk : σ k = j
    · have heq :
          (fun s => (G s).updateRow j (Pi.single i (1 : ℝ)) (σ k) k) =
            (fun _ : ℝ => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ)
              i (1 : ℝ)) k) := by
        funext s
        rw [hσk, Matrix.updateRow_self]
      rw [heq]
      exact differentiableWithinAt_const _
    · have heq :
          (fun s => (G s).updateRow j (Pi.single i (1 : ℝ)) (σ k) k) =
            (fun s => G s (σ k) k) := by
        funext s
        rw [Matrix.updateRow_ne hσk]
      rw [heq]
      exact hentry (σ k) k
  have hinvEq :
      (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p i j) =
        (fun s => ((G s).det)⁻¹ * (G s).adjugate i j) := by
    funext s
    unfold Riemannian.Tensor.chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (G s).det • (G s).adjugate) i j =
      ((G s).det)⁻¹ * (G s).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [hinvEq]
  exact (hdet.inv (ne_of_gt
    (Riemannian.Tensor.chartGramMatrix_det_pos (I := I) (g t) α hp))).mul hadj

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** If `h = ∂ₜ g`, then the inverse metric in a fixed chart frame
satisfies `∂ₜ g⁻¹ = -g⁻¹ h g⁻¹`, entry by entry. -/
theorem hasDerivWithinAt_chartInvGramMatrix_apply
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hh : IsMetricVariationOn g h J)
    {t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (α p : M) (hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (c b : Fin (Module.finrank ℝ E)) :
    HasDerivWithinAt
      (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c b)
      (- ∑ a, ∑ d,
        Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p c a
          * h t p (Tensor.chartBasisVecFiber (I := I) α a p)
              (Tensor.chartBasisVecFiber (I := I) α d p)
          * Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p d b) J t := by
  classical
  have hGram : ∀ a d, HasDerivWithinAt
      (fun s => Riemannian.Tensor.chartGramMatrix (I := I) (g s) α p a d)
      (h t p (Tensor.chartBasisVecFiber (I := I) α a p)
        (Tensor.chartBasisVecFiber (I := I) α d p)) J t := by
    intro a d
    exact hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp
      (hasDerivWithinAt_chartGramMatrix hh ht α p) a) d
  have hInvDiff : ∀ a, DifferentiableWithinAt ℝ
      (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c a) J t :=
    fun a => differentiableWithinAt_chartInvGramMatrix_apply hh ht α p hp c a
  have hrel : ∀ d,
      ∑ a, derivWithin
          (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c a) J t
            * Riemannian.Tensor.chartGramMatrix (I := I) (g t) α p a d
        = - ∑ a, Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p c a
            * h t p (Tensor.chartBasisVecFiber (I := I) α a p)
                (Tensor.chartBasisVecFiber (I := I) α d p) := by
    intro d
    have hprod : HasDerivWithinAt
        (fun s => ∑ a,
          Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c a
            * Riemannian.Tensor.chartGramMatrix (I := I) (g s) α p a d)
        (∑ a, (derivWithin
            (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c a) J t
              * Riemannian.Tensor.chartGramMatrix (I := I) (g t) α p a d
            + Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p c a
              * h t p (Tensor.chartBasisVecFiber (I := I) α a p)
                  (Tensor.chartBasisVecFiber (I := I) α d p))) J t := by
      refine HasDerivWithinAt.fun_sum fun a _ => ?_
      exact (hInvDiff a).hasDerivWithinAt.mul (hGram a d)
    have hfun :
        (fun s => ∑ a,
          Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c a
            * Riemannian.Tensor.chartGramMatrix (I := I) (g s) α p a d) =
          (fun _ => if c = d then (1 : ℝ) else 0) := by
      funext s
      have hinv := Riemannian.Tensor.chartInvGramMatrix_mul_chartGramMatrix
        (I := I) (g s) α hp
      simpa only [Matrix.mul_apply, Matrix.one_apply] using
        congrFun (congrFun hinv c) d
    have hzero :
        (∑ a, (derivWithin
            (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c a) J t
              * Riemannian.Tensor.chartGramMatrix (I := I) (g t) α p a d
            + Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p c a
              * h t p (Tensor.chartBasisVecFiber (I := I) α a p)
                  (Tensor.chartBasisVecFiber (I := I) α d p))) = 0 := by
      apply hJ.eq_deriv J hprod
      rw [hfun]
      exact hasDerivWithinAt_const t J _
    rw [Finset.sum_add_distrib] at hzero
    linarith [hzero]
  have hderiv : derivWithin
      (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c b) J t =
      - ∑ a, ∑ d,
        Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p c a
          * h t p (Tensor.chartBasisVecFiber (I := I) α a p)
              (Tensor.chartBasisVecFiber (I := I) α d p)
          * Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p d b := by
    calc
      derivWithin
          (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c b) J t
          = ∑ a, derivWithin
              (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c a) J t
                * (if a = b then (1 : ℝ) else 0) := by simp
      _ = ∑ a, derivWithin
              (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c a) J t
                * ∑ d, Riemannian.Tensor.chartGramMatrix (I := I) (g t) α p a d
                  * Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p d b := by
            refine Finset.sum_congr rfl fun a _ => ?_
            have hinv := Riemannian.Tensor.chartGramMatrix_mul_chartInvGramMatrix
              (I := I) (g t) α hp
            rw [show (∑ d, Riemannian.Tensor.chartGramMatrix (I := I) (g t) α p a d
                * Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p d b) =
                (if a = b then (1 : ℝ) else 0) by
              simpa only [Matrix.mul_apply, Matrix.one_apply] using
                congrFun (congrFun hinv a) b]
      _ = ∑ a, ∑ d, derivWithin
              (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c a) J t
                * Riemannian.Tensor.chartGramMatrix (I := I) (g t) α p a d
                * Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p d b := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun d _ => by ring
      _ = ∑ d, (∑ a, derivWithin
              (fun s => Riemannian.Tensor.chartInvGramMatrix (I := I) (g s) α p c a) J t
                * Riemannian.Tensor.chartGramMatrix (I := I) (g t) α p a d)
                * Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p d b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ d, (- ∑ a,
              Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p c a
                * h t p (Tensor.chartBasisVecFiber (I := I) α a p)
                    (Tensor.chartBasisVecFiber (I := I) α d p))
                * Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p d b := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [hrel d]
      _ = - ∑ a, ∑ d,
            Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p c a
              * h t p (Tensor.chartBasisVecFiber (I := I) α a p)
                  (Tensor.chartBasisVecFiber (I := I) α d p)
              * Riemannian.Tensor.chartInvGramMatrix (I := I) (g t) α p d b := by
            rw [Finset.sum_congr rfl fun d (_ : d ∈ Finset.univ) => by
              rw [neg_mul, Finset.sum_mul], Finset.sum_neg_distrib, Finset.sum_comm]
  exact (hInvDiff b).hasDerivWithinAt.congr_deriv hderiv

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The first variation of the Levi-Civita connection in a fixed
chart: differentiating the Christoffel symbol gives the explicit inverse-metric
and spatial metric-variation formula `chartChristoffelVariationOnE`. -/
theorem hasDerivAt_chartChristoffel
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (hh : IsMetricVariationOn g h J) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ interior J)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    HasDerivAt
      (fun s => chartChristoffel (I := I) (g s) α i j k y)
      (chartChristoffelVariationOnE (I := I) g h t α i j k y) t := by
  classical
  let p : M := (extChartAt I α).symm y
  have hJ : J ∈ nhds t := mem_interior_iff_mem_nhds.mp ht
  have hp : p ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change p ∈ (chartAt H α).source
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I α]
    exact (extChartAt I α).map_target hy
  have hInv (l : Fin (Module.finrank ℝ E)) : HasDerivAt
      (fun s => Tensor.chartInvGramMatrix (I := I) (g s) α p k l)
      (chartInvMetricVariationOnE (I := I) g h t α k l y) t := by
    simpa [p, chartInvMetricVariationOnE, chartMetricVariationOnE] using
      (hasDerivWithinAt_chartInvGramMatrix_apply hh (interior_subset ht)
        (uniqueDiffWithinAt_of_mem_nhds hJ) α p hp k l).hasDerivAt hJ
  have hPartial (a b r : Fin (Module.finrank ℝ E)) : HasDerivAt
      (fun s => partialDeriv (E := E) r
        (chartGramOnE (I := I) (g s) α a b) y)
      (partialDeriv (E := E) r
        (chartMetricVariationOnE (I := I) h t α a b) y) t :=
    hasDerivAt_partialDeriv_chartGramOnE hg hh α a b r ht hy
  have hBracket (l : Fin (Module.finrank ℝ E)) : HasDerivAt
      (fun s =>
        partialDeriv (E := E) i (chartGramOnE (I := I) (g s) α l j) y +
        partialDeriv (E := E) j (chartGramOnE (I := I) (g s) α l i) y -
        partialDeriv (E := E) l (chartGramOnE (I := I) (g s) α i j) y)
      (partialDeriv (E := E) i
          (chartMetricVariationOnE (I := I) h t α l j) y +
        partialDeriv (E := E) j
          (chartMetricVariationOnE (I := I) h t α l i) y -
        partialDeriv (E := E) l
          (chartMetricVariationOnE (I := I) h t α i j) y) t :=
    ((hPartial l j i).add (hPartial l i j)).sub (hPartial i j l)
  have hsum : HasDerivAt
      (fun s => ∑ l,
        Tensor.chartInvGramMatrix (I := I) (g s) α p k l *
          (partialDeriv (E := E) i (chartGramOnE (I := I) (g s) α l j) y +
           partialDeriv (E := E) j (chartGramOnE (I := I) (g s) α l i) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) (g s) α i j) y))
      (∑ l, (
        chartInvMetricVariationOnE (I := I) g h t α k l y *
          (partialDeriv (E := E) i (chartGramOnE (I := I) (g t) α l j) y +
           partialDeriv (E := E) j (chartGramOnE (I := I) (g t) α l i) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) (g t) α i j) y) +
        Tensor.chartInvGramMatrix (I := I) (g t) α p k l *
          (partialDeriv (E := E) i
              (chartMetricVariationOnE (I := I) h t α l j) y +
           partialDeriv (E := E) j
              (chartMetricVariationOnE (I := I) h t α l i) y -
           partialDeriv (E := E) l
              (chartMetricVariationOnE (I := I) h t α i j) y))) t := by
    exact HasDerivAt.fun_sum fun l _ => (hInv l).mul (hBracket l)
  have hresult := hsum.const_mul (1 / 2 : ℝ)
  simpa [p, chartChristoffel_def, chartChristoffelVariationOnE] using hresult

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Time differentiation commutes with a fixed chart derivative of
a Christoffel symbol: `∂ₜ(∂ᵣΓ) = ∂ᵣ(δΓ)`. This is the second mixed derivative
needed to differentiate the coordinate curvature formula. -/
theorem hasDerivAt_partialDeriv_chartChristoffel
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (hh : IsMetricVariationOn g h J) (α : M)
    (i j k r : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ interior J)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    HasDerivAt
      (fun s => partialDeriv (E := E) r
        (chartChristoffel (I := I) (g s) α i j k) y)
      (partialDeriv (E := E) r
        (chartChristoffelVariationOnE (I := I) g h t α i j k) y) t := by
  let F : ℝ × E → ℝ :=
    fun z => chartChristoffel (I := I) (g z.1) α i j k z.2
  let K : E → ℝ := chartChristoffelVariationOnE (I := I) g h t α i j k
  have ht' : t ∈ interior (interior J) := by
    rwa [interior_interior]
  have hresult := hasDerivAt_spatialPartial_timeLine
    (F := F) (K := K) (J := interior J) (U := (extChartAt I α).target)
    (contDiffOn_chartChristoffel_timeSpace hg α i j k) ht' hy
    (isOpen_extChartAt_target (I := I) α)
    (fun y' hy' => by
      change HasDerivAt
        (fun s => chartChristoffel (I := I) (g s) α i j k y')
        (chartChristoffelVariationOnE (I := I) g h t α i j k y') t
      exact hasDerivAt_chartChristoffel hg hh α i j k ht hy')
    ((Module.finBasis ℝ E) r)
  simpa only [partialDeriv] using hresult

#print axioms MorganTianLib.hasDerivWithinAt_chartGramMatrix
#print axioms MorganTianLib.hasDerivWithinAt_chartGramOnE
#print axioms MorganTianLib.hasDerivWithinAt_chartInvGramMatrix_apply
#print axioms MorganTianLib.hasDerivAt_spatialFDeriv_timeLine
#print axioms MorganTianLib.contMDiffOn_chartGramMatrix_timeSpace
#print axioms MorganTianLib.contDiffOn_chartGramOnE_timeSpace
#print axioms MorganTianLib.hasDerivAt_partialDeriv_chartGramOnE
#print axioms MorganTianLib.hasDerivAt_chartChristoffel
#print axioms MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace
#print axioms MorganTianLib.contDiffOn_chartChristoffel_timeSpace
#print axioms MorganTianLib.hasDerivAt_partialDeriv_chartChristoffel

end MorganTianLib

end
