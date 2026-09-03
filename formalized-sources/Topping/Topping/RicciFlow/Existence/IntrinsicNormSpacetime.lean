import Topping.RicciFlow.Existence.IntrinsicNormContinuityBridge

/-!
# Joint intrinsic spacetime regularity of the Riemann norm square

`IntrinsicNormContinuity` proves joint regularity of the full contraction in a
fixed chart.  The bridge in the companion module identifies that contraction
with the intrinsic squared Riemann norm on the chart target.  This file performs
the standard chart-local-to-manifold assembly, retaining the prescribed time
set (and hence its endpoints) in the statement.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The squared intrinsic Riemann norm of a smooth metric family is
jointly manifold-smooth in space and time on the whole prescribed time set. -/
theorem riemannNormAt_sq_contMDiffOn_of_isSmoothMetricFamilyOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
      ((Set.univ : Set M) ×ˢ J) := by
  rintro z hz
  rcases z with ⟨p, t⟩
  have ht : t ∈ J := hz.2
  have hp : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  have hpy : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hp
  let S : Set (ℝ × E) := J ×ˢ (extChartAt I p).target
  let D : Set (M × ℝ) := (extChartAt I p).source ×ˢ J
  have hcoord : ContDiffWithinAt ℝ ∞
      (fun w : ℝ × E => chartRiemannNormSqOnE
        (I := I) (g w.1) p w.2)
      S (t, extChartAt I p p) :=
    contDiffOn_chartRiemannNormSqOnE_timeSpace hg p
      (t, extChartAt I p p) ⟨ht, hpy⟩
  have hcoordM : ContMDiffWithinAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun w : ℝ × E => chartRiemannNormSqOnE
        (I := I) (g w.1) p w.2)
      S (t, extChartAt I p p) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hcoord.contMDiffWithinAt
  have hchart : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun w : M × ℝ => extChartAt I p w.1) (p, t) :=
    (contMDiffAt_extChartAt (I := I) (x := p)).comp (p, t) contMDiffAt_fst
  have hread : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun w : M × ℝ => (w.2, extChartAt I p w.1)) D (p, t) :=
    contMDiffWithinAt_snd.prodMk hchart.contMDiffWithinAt
  have hmaps : MapsTo
      (fun w : M × ℝ => (w.2, extChartAt I p w.1)) D S := by
    intro w hw
    exact ⟨hw.2, (extChartAt I p).map_source hw.1⟩
  have hcomp : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => chartRiemannNormSqOnE
        (I := I) (g w.2) p (extChartAt I p w.1))
      D (p, t) :=
    ContMDiffWithinAt.comp
      (f := fun w : M × ℝ => (w.2, extChartAt I p w.1))
      (g := fun q : ℝ × E => chartRiemannNormSqOnE
        (I := I) (g q.1) p q.2) (p, t) hcoordM hread hmaps
  have hintrinsic : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => riemannNormAt (g w.2) w.1 ^ 2)
      D (p, t) := by
    refine hcomp.congr ?_ ?_
    · intro w hw
      have htarget : extChartAt I p w.1 ∈ (extChartAt I p).target :=
        (extChartAt I p).map_source hw.1
      have hbridge := chartRiemannNormSqOnE_eq_riemannNormAt_sq
        (I := I) (g w.2) p htarget
      rw [(extChartAt I p).left_inv hw.1] at hbridge
      exact hbridge.symm
    · have hbridge := chartRiemannNormSqOnE_eq_riemannNormAt_sq
        (I := I) (g t) p hpy
      rw [(extChartAt I p).left_inv hp] at hbridge
      exact hbridge.symm
  have hsets : D =ᶠ[𝓝 (p, t)] ((Set.univ : Set M) ×ˢ J) := by
    filter_upwards
      [((isOpen_extChartAt_source (I := I) p).prod isOpen_univ).mem_nhds
        ⟨hp, mem_univ t⟩] with w hw
    apply propext
    change (w.1 ∈ (extChartAt I p).source ∧ w.2 ∈ J) ↔
      (w.1 ∈ (Set.univ : Set M) ∧ w.2 ∈ J)
    constructor
    · intro h
      exact ⟨mem_univ _, h.2⟩
    · intro h
      exact ⟨hw.1, h.2⟩
  exact hintrinsic.congr_set hsets

/-- **Math.** The joint regularity above yields the `ContinuousOn` interface
used by the curvature maximum-principle and endpoint consumers. -/
theorem continuousOn_riemannNormAt_sq_of_isSmoothMetricFamilyOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) :
    ContinuousOn
      (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
      ((Set.univ : Set M) ×ˢ J) :=
  (riemannNormAt_sq_contMDiffOn_of_isSmoothMetricFamilyOn hg).continuousOn

#print axioms riemannNormAt_sq_contMDiffOn_of_isSmoothMetricFamilyOn
#print axioms continuousOn_riemannNormAt_sq_of_isSmoothMetricFamilyOn

end Topping

end
