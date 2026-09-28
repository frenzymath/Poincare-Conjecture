import MorganTianLib.Ch03.RicciFlow.ScalarSpacetimeSmooth

/-!
# Joint regularity of the scalar-curvature time derivative

The actual time derivative of intrinsic scalar curvature is jointly smooth in
space and time in the interior of the prescribed time set. The proof
differentiates the coordinate scalar curvature and transfers through charts.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private theorem contDiffOn_timeDeriv
    {V : Set ℝ} {U : Set E} (hV : IsOpen V) {F : ℝ × E → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => deriv (fun t => F (t, z.2)) z.1)
      (V ×ˢ U) := by
  let S : Set (ℝ × E) := V ×ˢ U
  let P : (ℝ × E) → ℝ → ℝ := fun z t => F (t, z.2)
  let gs : (ℝ × E) → ℝ := fun z => z.1
  let ks : (ℝ × E) → ℝ := fun _ => 1
  have hP : ContDiffOn ℝ ∞ (Function.uncurry P) (S ×ˢ V) := by
    change ContDiffOn ℝ ∞
      (fun w : (ℝ × E) × ℝ => F (w.2, w.1.2)) (S ×ˢ V)
    have hmap : ContDiffOn ℝ ∞
        (fun w : (ℝ × E) × ℝ => (w.2, w.1.2)) (S ×ˢ V) :=
      contDiffOn_snd.prodMk contDiffOn_fst.snd
    have hmaps : MapsTo
        (fun w : (ℝ × E) × ℝ => (w.2, w.1.2)) (S ×ˢ V) S := by
      rintro ⟨z, t⟩ ⟨hz, ht⟩
      exact ⟨ht, hz.2⟩
    exact hF.comp hmap hmaps
  intro z hz
  have hgs : ContDiffWithinAt ℝ ∞ gs S z := contDiffWithinAt_fst
  have hks : ContDiffWithinAt ℝ ∞ ks S z := contDiffWithinAt_const
  have hpartial := (hP (z, gs z) ⟨hz, hz.1⟩).fderivWithin_apply
    hgs hks hV.uniqueDiffOn
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ from le_rfl) hz (by
      intro w hw
      exact hw.1)
  refine hpartial.congr_of_eventuallyEq_of_mem ?_ hz
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact congrArg (fun L : ℝ →L[ℝ] ℝ => L 1)
    (fderivWithin_of_isOpen hV hw.1).symm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** The time derivative of coordinate scalar curvature is jointly smooth on
the interior time set. -/
theorem contDiffOn_timeDeriv_chartScalarCurvatureOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => deriv
        (fun t => chartScalarCurvatureOnE (I := I) (g t) alpha z.2) z.1)
      (interior J ×ˢ (extChartAt I alpha).target) := by
  apply contDiffOn_timeDeriv (F := fun z : ℝ × E =>
    chartScalarCurvatureOnE (I := I) (g z.1) alpha z.2) isOpen_interior
  exact (contDiffOn_chartScalarCurvatureOnE_timeSpace hg alpha).mono
    (Set.prod_mono interior_subset Subset.rfl)

omit [I.Boundaryless] in
private theorem scalarTimeDerivativeCanonicalLC (g : RiemannianMetric I M) :
    g.leviCivitaConnection.IsLeviCivita g :=
  g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)

/-- **Math.** The actual time derivative of intrinsic scalar curvature is jointly smooth
in space and time on the interior time set of a smooth metric family. -/
theorem scalarCurvature_timeDeriv_contMDiffOn_of_isSmoothMetricFamilyOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => deriv (fun t =>
        scalarCurvatureAt (g t) (g t).leviCivitaConnection
          (scalarTimeDerivativeCanonicalLC (g t)) z.1) z.2)
      ((Set.univ : Set M) ×ˢ interior J) := by
  rintro ⟨p, t⟩ hz
  have hp : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  have hpy : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hp
  let S : Set (ℝ × E) := interior J ×ˢ (extChartAt I p).target
  let D : Set (M × ℝ) := (extChartAt I p).source ×ˢ interior J
  have hcoord : ContDiffWithinAt ℝ ∞
      (fun w : ℝ × E => deriv
        (fun s => chartScalarCurvatureOnE (I := I) (g s) p w.2) w.1)
      S (t, extChartAt I p p) :=
    contDiffOn_timeDeriv_chartScalarCurvatureOnE_timeSpace hg p
      (t, extChartAt I p p) ⟨hz.2, hpy⟩
  have hcoordM : ContMDiffWithinAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun w : ℝ × E => deriv
        (fun s => chartScalarCurvatureOnE (I := I) (g s) p w.2) w.1)
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
  have hcomp : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => deriv (fun s => chartScalarCurvatureOnE
        (I := I) (g s) p (extChartAt I p w.1)) w.2) D (p, t) :=
    ContMDiffWithinAt.comp
      (f := fun w : M × ℝ => (w.2, extChartAt I p w.1))
      (g := fun q : ℝ × E => deriv
        (fun s => chartScalarCurvatureOnE (I := I) (g s) p q.2) q.1)
      (p, t) hcoordM hread hmaps
  have heq : ∀ w ∈ D,
      deriv (fun s => scalarCurvatureAt (g s) (g s).leviCivitaConnection
          (scalarTimeDerivativeCanonicalLC (g s)) w.1) w.2 =
        deriv (fun s => chartScalarCurvatureOnE
          (I := I) (g s) p (extChartAt I p w.1)) w.2 := by
    intro w hw
    apply congrArg (fun f : ℝ → ℝ => deriv f w.2)
    funext s
    have htarget := (extChartAt I p).map_source hw.1
    have hscalar := chartScalarCurvatureOnE_eq_scalarCurvatureAt
      (I := I) (g s) p htarget (scalarTimeDerivativeCanonicalLC (g s))
    rw [(extChartAt I p).left_inv hw.1] at hscalar
    exact hscalar.symm
  have hintrinsic : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => deriv (fun s =>
        scalarCurvatureAt (g s) (g s).leviCivitaConnection
          (scalarTimeDerivativeCanonicalLC (g s)) w.1) w.2) D (p, t) :=
    hcomp.congr heq (heq (p, t) ⟨hp, hz.2⟩)
  have hsets : D =ᶠ[𝓝 (p, t)] ((Set.univ : Set M) ×ˢ interior J) := by
    filter_upwards
      [((isOpen_extChartAt_source (I := I) p).prod isOpen_univ).mem_nhds
        ⟨hp, mem_univ t⟩] with w hw
    apply propext
    change (w.1 ∈ (extChartAt I p).source ∧ w.2 ∈ interior J) ↔
      (w.1 ∈ (Set.univ : Set M) ∧ w.2 ∈ interior J)
    exact ⟨fun h => ⟨mem_univ _, h.2⟩, fun h => ⟨hw.1, h.2⟩⟩
  exact hintrinsic.congr_set hsets

/-- **Math.** A Ricci flow supplies joint continuity of the actual scalar-curvature time
derivative on the interior time set. -/
theorem scalarCurvature_timeDeriv_continuousOn_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) :
    ContinuousOn
      (fun z : M × ℝ => deriv (fun t =>
        scalarCurvatureAt (g t) (g t).leviCivitaConnection
          (scalarTimeDerivativeCanonicalLC (g t)) z.1) z.2)
      ((Set.univ : Set M) ×ˢ interior J) :=
  (scalarCurvature_timeDeriv_contMDiffOn_of_isSmoothMetricFamilyOn
    hflow.smooth).continuousOn

end MorganTianLib

#print axioms MorganTianLib.scalarCurvature_timeDeriv_contMDiffOn_of_isSmoothMetricFamilyOn
#print axioms MorganTianLib.scalarCurvature_timeDeriv_continuousOn_of_isRicciFlowOn
