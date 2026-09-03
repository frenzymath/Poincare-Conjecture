import Topping.RicciFlow.Existence.GaugeFlow
import MorganTianLib.Ch02.FrameBridge
import MorganTianLib.Ch02.FlowVariationJoint
import MorganTianLib.Ch02.FlowIsometryBridges

/-!
# Smooth consumers for the non-autonomous flow box

The compact-slice construction in `GaugeFlow.lean` records joint continuity
of its local flow.  This file keeps the stronger regularity boundary explicit:
when a later analytic argument supplies a joint `ContMDiff` witness for the
uncurried flow, composition with the distinguished slice and projection gives
the corresponding smooth trajectory and spatial flow.  No smoothness witness
is manufactured from the continuous flow-box data here.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Function Metric Riemannian

set_option linter.unusedSectionVars false

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A smooth vector field admits a positive-time local flow whose
uncurried map is jointly `C¹` in the initial point and elapsed time.  The
construction is chart-local: Picard--Lindelöf supplies the coordinate flow,
and the chart inverse transfers its integral-curve equation to the manifold.
Only positive elapsed times are asserted, matching the one-sided regularity
of the local flow theorem; this does not construct a global gauge family. -/
theorem exists_local_jointSmoothFlow_box
    (X : SmoothVectorField I M) (z : M) :
    ∃ (δ : ℝ) (V : Set M) (Φ : ℝ → M → M),
      0 < δ ∧ IsOpen V ∧ z ∈ V ∧
      (∀ x ∈ V, Φ 0 x = x) ∧
      (∀ x ∈ V, IsMIntegralCurveOn (Φ · x) (fun q => X q) (Ioo (-δ) δ)) ∧
      (∀ x ∈ V, ∀ s ∈ Ioo (0 : ℝ) δ,
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1
          (fun p : ℝ × M => Φ p.1 p.2) (s, x)) := by
  classical
  have hΩ : IsOpen (extChartAt I z).target := isOpen_extChartAt_target (I := I) z
  have hz₀ : extChartAt I z z ∈ (extChartAt I z).target := mem_extChartAt_target z
  have hX1 : ContDiffOn ℝ 1
      (MorganTianLib.fieldChartRep (I := I) z X) (extChartAt I z).target := by
    rw [← contMDiffOn_iff_contDiffOn]
    change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (fun y => MorganTianLib.fieldRep (I := I) z X ((extChartAt I z).symm y))
      (extChartAt I z).target
    have hrep : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun y => MorganTianLib.fieldRep (I := I) z X ((extChartAt I z).symm y))
        (extChartAt I z).target := by
      have h := (MorganTianLib.contMDiffOn_fieldRep (I := I) z X).comp
        (contMDiffOn_extChartAt_symm (I := I) z)
        (s := (extChartAt I z).target)
        (t := (trivializationAt E (TangentSpace I) z).baseSet) ?_
      · convert h using 1
        ext y
        rfl
      · intro y hy
        rw [Riemannian.trivializationAt_baseSet_eq_chartAt_source,
          ← extChartAt_source (I := I)]
        exact (extChartAt I z).map_target hy
    exact hrep.of_le (by norm_num)
  obtain ⟨r, ε, T, Z, Dx, hr, hε, hT, hTε, hflow, hZcont, hDx, hDxcont,
    hjoint, hC1⟩ :=
    MorganTianLib.exists_localFlow_hasStrictFDerivAt_uncurry hΩ hz₀ hX1
  let V : Set M := (extChartAt I z).source ∩
    extChartAt I z ⁻¹' ball (extChartAt I z z) r
  let Φ : ℝ → M → M := fun s x =>
    (extChartAt I z).symm (Z (extChartAt I z x) s)
  have hVopen : IsOpen V := isOpen_extChartAt_preimage' z isOpen_ball
  have hzV : z ∈ V := by
    exact ⟨mem_extChartAt_source z, mem_ball_self hr⟩
  refine ⟨T, V, Φ, hT, hVopen, hzV, ?_, ?_, ?_⟩
  · intro x hx
    have hxsrc : x ∈ (extChartAt I z).source := hx.1
    change (extChartAt I z).symm (Z (extChartAt I z x) 0) = x
    rw [(hflow _ (ball_subset_closedBall hx.2)).1,
      (extChartAt I z).left_inv hxsrc]
  · intro x hx
    have hxball : extChartAt I z x ∈ ball (extChartAt I z z) r := hx.2
    have hu : ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (Z (extChartAt I z x))
          (MorganTianLib.fieldChartRep (I := I) z X
            (Z (extChartAt I z x) t)) t := by
      intro t ht
      exact ((hflow _ (ball_subset_closedBall hxball)).2.1 t
        (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hmemt : ∀ t ∈ Ioo (-ε) ε,
        Z (extChartAt I z x) t ∈ (extChartAt I z).target := by
      intro t ht
      exact (hflow _ (ball_subset_closedBall hxball)).2.2 t
        (Ioo_subset_Icc_self ht)
    have hcurve := MorganTianLib.isMIntegralCurveOn_extChartAt_symm_comp
      X z hmemt hu
    simpa [Φ] using hcurve.mono
      (Ioo_subset_Ioo (neg_le_neg hTε.le) hTε.le)
  · intro x hx s hs
    have hxsrc : x ∈ (extChartAt I z).source := hx.1
    have hxsrc' : x ∈ (chartAt H z).source := by
      rw [← extChartAt_source (I := I)]
      exact hxsrc
    have hxball : extChartAt I z x ∈ ball (extChartAt I z z) r := hx.2
    have hsε : s ∈ Ioo (-ε) ε :=
      ⟨lt_of_lt_of_le (neg_lt_zero.mpr hε) hs.1.le, lt_trans hs.2 hTε⟩
    have hφ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) 1
        (fun p : ℝ × M => extChartAt I z p.2) (s, x) :=
      (contMDiffAt_extChartAt' hxsrc').comp (s, x) contMDiffAt_snd
    have hfst : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
        (fun p : ℝ × M => p.1) (s, x) := contMDiffAt_fst
    have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E × ℝ) 1
        (fun p : ℝ × M => (extChartAt I z p.2, p.1)) (s, x) :=
      hφ.prodMk_space hfst
    have hZC : ContDiffAt ℝ 1 (fun q : E × ℝ => Z q.1 q.2)
        (extChartAt I z x, s) := by
      exact hC1.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
        (⟨hxball, hs⟩ : (extChartAt I z x, s) ∈
          ball (extChartAt I z z) r ×ˢ Ioo 0 T))
    have hZM : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) 1
        (fun p : ℝ × M => Z (extChartAt I z p.2) p.1) (s, x) :=
      hZC.comp_contMDiffAt (x := ((s, x) : ℝ × M)) hpair
    have hsIcc : s ∈ Icc (-ε) ε := Ioo_subset_Icc_self hsε
    have hZsmem : Z (extChartAt I z x) s ∈ (extChartAt I z).target :=
      (hflow _ (ball_subset_closedBall hxball)).2.2 s hsIcc
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I 1
        (extChartAt I z).symm (Z (extChartAt I z x) s) :=
      (contMDiffOn_extChartAt_symm z).contMDiffAt
        ((isOpen_extChartAt_target z).mem_nhds hZsmem)
    have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1
        (fun p : ℝ × M =>
          (extChartAt I z).symm (Z (extChartAt I z p.2) p.1)) (s, x) :=
      hsymm.comp (s, x) hZM
    simpa [Φ] using hcomp

/-- **Math.** A joint smoothness witness for the uncurried flow gives a smooth trajectory
on the distinguished time slice. -/
theorem TimeDependentFlowBox.contMDiff_trajectory_of_contMDiff
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀)
    (hΦ : ContMDiff ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : (M × ℝ) × ℝ => B.Φ z.1 z.2)) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun q : M × ℝ => B.Φ (q.1, t₀) q.2) := by
  let A : M × ℝ → (M × ℝ) × ℝ := fun q => ((q.1, t₀), q.2)
  have hA₁ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      ∞ (fun q : M × ℝ => (q.1, t₀)) :=
    contMDiff_fst.prodMk contMDiff_const
  have hA : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞ A :=
    hA₁.prodMk contMDiff_snd
  have hcomp := hΦ.comp hA
  simpa [A, Function.comp_def] using hcomp

/-- **Math.** Under the same explicit joint smoothness witness, the spatial part of the
flow is jointly smooth in its initial point and elapsed time. -/
theorem TimeDependentFlowBox.contMDiff_spatialFlow_of_contMDiff
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀)
    (hΦ : ContMDiff ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : (M × ℝ) × ℝ => B.Φ z.1 z.2)) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : M × ℝ => B.spatialFlow q.1 q.2) := by
  have htraj := B.contMDiff_trajectory_of_contMDiff hΦ
  have hproj := htraj.fst
  simpa [TimeDependentFlowBox.spatialFlow] using hproj

/-- **Math.** Every fixed elapsed time slice of a jointly smooth spatial flow is a smooth
map of the initial point. -/
theorem TimeDependentFlowBox.contMDiff_spatialFlow_fixed_of_contMDiff
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀)
    (hΦ : ContMDiff ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : (M × ℝ) × ℝ => B.Φ z.1 z.2)) (s : ℝ) :
    ContMDiff I I ∞ (fun p : M => B.spatialFlow p s) := by
  have hsp := B.contMDiff_spatialFlow_of_contMDiff hΦ
  have harg : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : M => (p, s)) :=
    contMDiff_id.prodMk contMDiff_const
  have hcomp := hsp.comp harg
  simpa [Function.comp_def] using hcomp

end Topping

end
