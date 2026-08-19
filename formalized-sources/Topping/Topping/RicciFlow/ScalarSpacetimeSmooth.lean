import MorganTianLib.Ch03.RicciFlow.ScalarTraceEvolution
import Topping.RicciFlow.ScalarEvolutionUnconditional

/-!
# Joint space-time smoothness of scalar curvature

The smooth-family structure used by Morgan--Tian is joint in space and time.
This file carries that regularity through the coordinate construction of
curvature and then reads the result back intrinsically.  The restriction to
`interior J` is genuine: differentiating the spatial Christoffel coefficients
uses an open space-time coordinate domain.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** A spatial derivative of a Christoffel coefficient remains jointly smooth
at interior times. -/
theorem contDiffOn_partialDeriv_chartChristoffel_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k r : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) r
        (chartChristoffel (I := I) (g z.1) alpha i j k) z.2)
      (interior J ×ˢ (extChartAt I alpha).target) := by
  let F : ℝ × E → ℝ :=
    fun z => chartChristoffel (I := I) (g z.1) alpha i j k z.2
  let S : Set (ℝ × E) := interior J ×ˢ (extChartAt I alpha).target
  have hS : IsOpen S :=
    isOpen_interior.prod (isOpen_extChartAt_target (I := I) alpha)
  have hF : ContDiffOn ℝ ∞ F S :=
    MorganTianLib.contDiffOn_chartChristoffel_timeSpace hg alpha i j k
  have hDF : ContDiffOn ℝ ∞ (fderiv ℝ F) S :=
    hF.fderiv_of_isOpen hS (by simp)
  have happ : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ F z ((0 : ℝ), (Module.finBasis ℝ E) r)) S :=
    hDF.clm_apply contDiffOn_const
  refine happ.congr fun z hz => ?_
  have hFz : DifferentiableAt ℝ F z :=
    ((contDiffOn_infty.mp hF 1).contDiffAt (hS.mem_nhds hz)).differentiableAt
      (by norm_num)
  have hembed : HasFDerivAt (fun y : E => (z.1, y))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hslice := hFz.hasFDerivAt.comp z.2 hembed
  have heq := congrArg
    (fun L : E →L[ℝ] ℝ => L ((Module.finBasis ℝ E) r)) hslice.fderiv
  change fderiv ℝ (fun y => F (z.1, y)) z.2 ((Module.finBasis ℝ E) r) =
    fderiv ℝ F z ((0 : ℝ), (Module.finBasis ℝ E) r)
  simpa [Function.comp_def, F, partialDeriv] using heq

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** Mixed-index coordinate curvature coefficients of a smooth metric family
are jointly smooth at interior times. -/
theorem contDiffOn_chartCurvatureCoef_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => Riemannian.Jacobi.chartCurvatureCoef
        (I := I) (g z.1) alpha i j k l z.2)
      (interior J ×ˢ (extChartAt I alpha).target) := by
  classical
  have hGamma : ∀ a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun z : ℝ × E => chartChristoffel (I := I) (g z.1) alpha a b c z.2)
        (interior J ×ˢ (extChartAt I alpha).target) :=
    fun a b c =>
      MorganTianLib.contDiffOn_chartChristoffel_timeSpace hg alpha a b c
  have hpartial : ∀ a b c d : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun z : ℝ × E => partialDeriv (E := E) a
          (chartChristoffel (I := I) (g z.1) alpha b c d) z.2)
        (interior J ×ˢ (extChartAt I alpha).target) :=
    fun a b c d =>
      contDiffOn_partialDeriv_chartChristoffel_timeSpace hg alpha b c d a
  unfold Riemannian.Jacobi.chartCurvatureCoef
  refine ((hpartial j i k l).sub (hpartial i j k l)).add ?_
  exact ContDiffOn.sum fun s _ =>
    ((hGamma i k s).mul (hGamma j s l)).sub
      ((hGamma j k s).mul (hGamma i s l))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** Coordinate Ricci coefficients of a smooth metric family are jointly
smooth at interior times. -/
theorem contDiffOn_chartRicciCoefOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartRicciCoefOnE
        (I := I) (g z.1) alpha j k z.2)
      (interior J ×ˢ (extChartAt I alpha).target) := by
  classical
  unfold MorganTianLib.chartRicciCoefOnE
  exact ContDiffOn.sum fun a _ =>
    contDiffOn_chartCurvatureCoef_timeSpace hg alpha j a k a

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** The coordinate scalar curvature of a smooth metric family is jointly
smooth at interior times. -/
theorem contDiffOn_chartScalarCurvatureOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartScalarCurvatureOnE
        (I := I) (g z.1) alpha z.2)
      (interior J ×ˢ (extChartAt I alpha).target) := by
  classical
  unfold MorganTianLib.chartScalarCurvatureOnE
  exact ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
    ((MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace hg alpha j k).mono
      (Set.prod_mono interior_subset Subset.rfl)).mul
      (contDiffOn_chartRicciCoefOnE_timeSpace hg alpha j k)

/-- **Math.** Scalar curvature is jointly smooth in space and time on the interior of
the time set of every smooth metric family. -/
theorem scalarCurvature_contMDiffOn_interior_of_isSmoothMetricFamilyOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ interior J) := by
  rintro z hz
  rcases z with ⟨p, t⟩
  have ht : t ∈ interior J := hz.2
  have hp : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  have hpy : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hp
  have hcoord : ContDiffAt ℝ ∞
      (fun w : ℝ × E => MorganTianLib.chartScalarCurvatureOnE
        (I := I) (g w.1) p w.2)
      (t, extChartAt I p p) :=
    (contDiffOn_chartScalarCurvatureOnE_timeSpace hg p).contDiffAt
      ((isOpen_interior.prod (isOpen_extChartAt_target (I := I) p)).mem_nhds
        ⟨ht, hpy⟩)
  have hcoordM : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun w : ℝ × E => MorganTianLib.chartScalarCurvatureOnE
        (I := I) (g w.1) p w.2)
      (t, extChartAt I p p) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hcoord.contMDiffAt
  have hchart : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun w : M × ℝ => extChartAt I p w.1) (p, t) :=
    (contMDiffAt_extChartAt (I := I) (x := p)).comp (p, t) contMDiffAt_fst
  have hread : ContMDiffAt (I.prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun w : M × ℝ => (w.2, extChartAt I p w.1)) (p, t) :=
    contMDiffAt_snd.prodMk hchart
  have hcomp : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => MorganTianLib.chartScalarCurvatureOnE
        (I := I) (g w.2) p (extChartAt I p w.1)) (p, t) :=
    ContMDiffAt.comp (f := fun w : M × ℝ => (w.2, extChartAt I p w.1))
      (g := fun q : ℝ × E => MorganTianLib.chartScalarCurvatureOnE
        (I := I) (g q.1) p q.2) (p, t) hcoordM hread
  refine (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [((isOpen_extChartAt_source (I := I) p).prod isOpen_interior).mem_nhds
      ⟨hp, ht⟩] with w hw
  have htarget : extChartAt I p w.1 ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hw.1
  have hchartScalar := MorganTianLib.chartScalarCurvatureOnE_eq_scalarCurvatureAt
    (I := I) (g w.2) p htarget (isLeviCivita_leviCivitaConnection (g w.2))
  rw [(extChartAt I p).left_inv hw.1] at hchartScalar
  calc
    scalarCurvatureAt (g w.2) w.1 =
        MorganTianLib.scalarCurvatureAt (g w.2) (g w.2).leviCivitaConnection
          (isLeviCivita_leviCivitaConnection (g w.2)) w.1 :=
      scalarCurvatureAt_eq_scalarCurvatureAt (g w.2) w.1
    _ = MorganTianLib.chartScalarCurvatureOnE
          (I := I) (g w.2) p (extChartAt I p w.1) := hchartScalar.symm

/-- **Math.** A Morgan--Tian Ricci flow supplies the joint scalar-curvature regularity
needed by interior maximum-principle arguments. -/
theorem scalarCurvature_contMDiffOn_interior_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ interior J) :=
  scalarCurvature_contMDiffOn_interior_of_isSmoothMetricFamilyOn hflow.smooth

#print axioms Topping.scalarCurvature_contMDiffOn_interior_of_isSmoothMetricFamilyOn
#print axioms Topping.scalarCurvature_contMDiffOn_interior_of_isRicciFlowOn

end Topping

end
