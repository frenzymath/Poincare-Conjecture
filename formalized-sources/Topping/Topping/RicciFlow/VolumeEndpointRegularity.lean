import MorganTianLib.Ch01.RiemannianMeasure
import MorganTianLib.Ch03.RicciFlow.MetricCoordinateVariation

/-!
# Endpoint regularity of the volume density

The coordinate volume density of a smooth metric family is jointly smooth on
the full prescribed time set and a fixed chart target.  When the time set has
unique derivatives, its within-time derivative inherits the same regularity.
-/

open scoped ContDiff Manifold Topology Bundle Matrix RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** In a fixed chart, the coordinate volume density of a smooth
metric family is jointly smooth on the full prescribed time set. -/
theorem contDiffOn_chartVolumeDensity_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E =>
        MorganTianLib.chartVolumeDensity (I := I) (g z.1) alpha z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  let G : ℝ × E → Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ :=
    fun z i j => Riemannian.chartGramOnE
      (I := I) (g z.1) alpha i j z.2
  have hentry : ∀ i j, ContDiffOn ℝ ∞ (fun z => G z i j)
      (J ×ˢ (extChartAt I alpha).target) := by
    intro i j
    exact MorganTianLib.contDiffOn_chartGramOnE_timeSpace hg alpha i j
  have hdet : ContDiffOn ℝ ∞ (fun z => (G z).det)
      (J ×ˢ (extChartAt I alpha).target) := by
    simp only [Matrix.det_apply]
    refine ContDiffOn.sum fun sigma _ => ?_
    exact (contDiffOn_prod fun k _ => hentry (sigma k) k).const_smul _
  change ContDiffOn ℝ ∞ (fun z => Real.sqrt ((G z).det))
    (J ×ˢ (extChartAt I alpha).target)
  refine hdet.sqrt ?_
  rintro ⟨s, y⟩ ⟨_, hy⟩
  change (Riemannian.Tensor.chartGramMatrix (I := I) (g s) alpha
    ((extChartAt I alpha).symm y)).det ≠ 0
  exact ne_of_gt (Riemannian.Tensor.chartGramMatrix_det_pos
    (I := I) (g s) alpha (by
      rw [trivializationAt_baseSet_eq_chartAt_source,
        ← extChartAt_source_eq_chartAt_source (I := I)]
      exact (extChartAt I alpha).map_target hy))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** If the time set has unique derivatives, the within-time
derivative of the coordinate volume density is jointly smooth there. -/
theorem contDiffOn_derivWithin_chartVolumeDensity_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J)
    (hJ : UniqueDiffOn ℝ J) (alpha : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E =>
        derivWithin
          (fun s => MorganTianLib.chartVolumeDensity (I := I) (g s) alpha z.2)
          J z.1)
      (J ×ˢ (extChartAt I alpha).target) := by
  let S : Set (ℝ × E) := J ×ˢ (extChartAt I alpha).target
  let rho : ℝ × E → ℝ := fun z =>
    MorganTianLib.chartVolumeDensity (I := I) (g z.1) alpha z.2
  have hrho : ContDiffOn ℝ ∞ rho S :=
    contDiffOn_chartVolumeDensity_timeSpace hg alpha
  let F : (ℝ × E) → ℝ → ℝ := fun z s => rho (s, z.2)
  have hmap : ContDiffOn ℝ ∞
      (fun w : (ℝ × E) × ℝ => (w.2, w.1.2)) (S ×ˢ J) :=
    contDiffOn_snd.prodMk contDiffOn_fst.snd
  have hmaps : MapsTo
      (fun w : (ℝ × E) × ℝ => (w.2, w.1.2)) (S ×ˢ J) S := by
    rintro ⟨z, s⟩ ⟨hz, hs⟩
    exact ⟨hs, hz.2⟩
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (S ×ˢ J) := by
    change ContDiffOn ℝ ∞
      (fun w : (ℝ × E) × ℝ => rho (w.2, w.1.2)) (S ×ˢ J)
    exact hrho.comp hmap hmaps
  intro z hz
  have hk : ContDiffWithinAt ℝ ∞ (fun _ : ℝ × E => (1 : ℝ)) S z :=
    contDiffWithinAt_const
  have hderiv :=
    (hF (z, z.1) ⟨hz, hz.1⟩).fderivWithin_apply
      contDiffWithinAt_fst hk hJ
      (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ from le_rfl) hz (fun w hw => hw.1)
  simpa only [F, rho, fderivWithin_derivWithin] using hderiv

#print axioms Topping.contDiffOn_chartVolumeDensity_timeSpace
#print axioms Topping.contDiffOn_derivWithin_chartVolumeDensity_timeSpace

end Topping
