import MorganTianLib.Ch03.RicciFlow.CurvatureCoordinateVariation

/-!
# Joint smoothness of scalar curvature

Scalar curvature of a smooth metric family is jointly smooth on its prescribed
time set, including endpoints. Spatial differentiation is performed on open
chart targets and therefore does not require the time set to be open.

The coordinate argument is adapted from the read-only workspace source
`references/Topping/Topping/RicciFlow/ScalarSpacetimeSmooth.lean`, ledger
commit `c14e53ad67641db93d690fd92cd34cf12c0584d5`, using Morgan--Tian's intrinsic
scalar curvature directly. This supplies joint continuity of the scalar family
for the compact minimum-envelope argument of Chapter 4.
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
private theorem contDiffOn_spatialFDeriv_apply
    {J : Set ℝ} {U : Set E} (hU : IsOpen U) {F : ℝ × E → ℝ}
    (hF : ContDiffOn ℝ ∞ F (J ×ˢ U)) (v : E) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => fderiv ℝ (fun y => F (z.1, y)) z.2 v)
      (J ×ˢ U) := by
  let S : Set (ℝ × E) := J ×ˢ U
  let P : (ℝ × E) → E → ℝ := fun z y => F (z.1, y)
  let gs : (ℝ × E) → E := fun z => z.2
  let ks : (ℝ × E) → E := fun _ => v
  have hP : ContDiffOn ℝ ∞ (Function.uncurry P) (S ×ˢ U) := by
    change ContDiffOn ℝ ∞
      (fun w : (ℝ × E) × E => F (w.1.1, w.2)) (S ×ˢ U)
    have hmap : ContDiffOn ℝ ∞
        (fun w : (ℝ × E) × E => (w.1.1, w.2)) (S ×ˢ U) :=
      contDiffOn_fst.fst.prodMk contDiffOn_snd
    have hmaps : MapsTo
        (fun w : (ℝ × E) × E => (w.1.1, w.2)) (S ×ˢ U) S := by
      rintro ⟨z, y⟩ ⟨hz, hy⟩
      exact ⟨hz.1, hy⟩
    exact hF.comp hmap hmaps
  intro z hz
  have hgs : ContDiffWithinAt ℝ ∞ gs S z := contDiffWithinAt_snd
  have hks : ContDiffWithinAt ℝ ∞ ks S z := contDiffWithinAt_const
  have hpartial := (hP (z, gs z) ⟨hz, hz.2⟩).fderivWithin_apply
    hgs hks hU.uniqueDiffOn
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ from le_rfl) hz (by
      intro w hw
      exact hw.2)
  refine hpartial.congr_of_eventuallyEq_of_mem ?_ hz
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [fderivWithin_of_isOpen hU hw.2]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- A spatial derivative of a Gram coefficient is jointly smooth on the
whole time set of a smooth metric family. -/
theorem contDiffOn_partialDeriv_chartGramOnE_timeSpace_on_timeSet
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j r : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) r
        (chartGramOnE (I := I) (g z.1) alpha i j) z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  simpa only [partialDeriv] using
    contDiffOn_spatialFDeriv_apply
      (isOpen_extChartAt_target (I := I) alpha)
      (contDiffOn_chartGramOnE_timeSpace hg alpha i j)
      ((Module.finBasis ℝ E) r)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- Christoffel symbols are jointly smooth on the whole time set. -/
theorem contDiffOn_chartChristoffel_timeSpace_on_timeSet
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartChristoffel (I := I) (g z.1) alpha i j k z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  rw [show (fun z : ℝ × E =>
      chartChristoffel (I := I) (g z.1) alpha i j k z.2) =
      fun z => (1 / 2 : ℝ) * ∑ l,
        Tensor.chartInvGramMatrix (I := I) (g z.1) alpha
            ((extChartAt I alpha).symm z.2) k l *
          (partialDeriv (E := E) i
              (chartGramOnE (I := I) (g z.1) alpha l j) z.2 +
           partialDeriv (E := E) j
              (chartGramOnE (I := I) (g z.1) alpha l i) z.2 -
           partialDeriv (E := E) l
              (chartGramOnE (I := I) (g z.1) alpha i j) z.2) by
    funext z
    rw [chartChristoffel_def]]
  exact (contDiffOn_const (c := (1 / 2 : ℝ))).mul
    (ContDiffOn.sum fun l _ =>
      ContDiffOn.mul
        (contDiffOn_chartInvGramOnE_timeSpace hg alpha k l)
        (((contDiffOn_partialDeriv_chartGramOnE_timeSpace_on_timeSet
            hg alpha l j i).add
          (contDiffOn_partialDeriv_chartGramOnE_timeSpace_on_timeSet
            hg alpha l i j)).sub
          (contDiffOn_partialDeriv_chartGramOnE_timeSpace_on_timeSet
            hg alpha i j l)))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- Spatial derivatives of Christoffel symbols are jointly smooth on the
whole time set. -/
theorem contDiffOn_partialDeriv_chartChristoffel_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k r : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) r
        (chartChristoffel (I := I) (g z.1) alpha i j k) z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  simpa only [partialDeriv] using
    contDiffOn_spatialFDeriv_apply
      (isOpen_extChartAt_target (I := I) alpha)
      (contDiffOn_chartChristoffel_timeSpace_on_timeSet hg alpha i j k)
      ((Module.finBasis ℝ E) r)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- Mixed-index curvature coefficients are jointly smooth on the whole
time set of a smooth metric family. -/
theorem contDiffOn_chartCurvatureCoef_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => Jacobi.chartCurvatureCoef
        (I := I) (g z.1) alpha i j k l z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  have hGamma := contDiffOn_chartChristoffel_timeSpace_on_timeSet hg alpha
  have hpartial := contDiffOn_partialDeriv_chartChristoffel_timeSpace hg alpha
  unfold Jacobi.chartCurvatureCoef
  refine ((hpartial i k l j).sub (hpartial j k l i)).add ?_
  exact ContDiffOn.sum fun s _ =>
    ((hGamma i k s).mul (hGamma j s l)).sub
      ((hGamma j k s).mul (hGamma i s l))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- Coordinate Ricci coefficients are jointly smooth on the whole time set. -/
theorem contDiffOn_chartRicciCoefOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartRicciCoefOnE (I := I) (g z.1) alpha j k z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  unfold chartRicciCoefOnE
  exact ContDiffOn.sum fun a _ =>
    contDiffOn_chartCurvatureCoef_timeSpace hg alpha j a k a

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- The coordinate scalar curvature is jointly smooth on the whole time set. -/
theorem contDiffOn_chartScalarCurvatureOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartScalarCurvatureOnE (I := I) (g z.1) alpha z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  unfold chartScalarCurvatureOnE
  exact ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
    (contDiffOn_chartInvGramOnE_timeSpace hg alpha j k).mul
      (contDiffOn_chartRicciCoefOnE_timeSpace hg alpha j k)

omit [I.Boundaryless] in
private theorem scalarSpacetimeCanonicalLC (g : RiemannianMetric I M) :
    g.leviCivitaConnection.IsLeviCivita g :=
  g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)

/-- **Math.** Intrinsic scalar curvature is jointly smooth on the whole prescribed
time set of a smooth metric family, including endpoints. -/
theorem scalarCurvature_contMDiffOn_of_isSmoothMetricFamilyOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) (g z.2).leviCivitaConnection
        (scalarSpacetimeCanonicalLC (g z.2)) z.1)
      ((Set.univ : Set M) ×ˢ J) := by
  rintro ⟨p, t⟩ hz
  have hp : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  have hpy : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hp
  let S : Set (ℝ × E) := J ×ˢ (extChartAt I p).target
  let D : Set (M × ℝ) := (extChartAt I p).source ×ˢ J
  have hcoord : ContDiffWithinAt ℝ ∞
      (fun w : ℝ × E => chartScalarCurvatureOnE (I := I) (g w.1) p w.2)
      S (t, extChartAt I p p) :=
    contDiffOn_chartScalarCurvatureOnE_timeSpace hg p
      (t, extChartAt I p p) ⟨hz.2, hpy⟩
  have hcoordM : ContMDiffWithinAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun w : ℝ × E => chartScalarCurvatureOnE (I := I) (g w.1) p w.2)
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
      (fun w : M × ℝ => chartScalarCurvatureOnE
        (I := I) (g w.2) p (extChartAt I p w.1)) D (p, t) :=
    ContMDiffWithinAt.comp
      (f := fun w : M × ℝ => (w.2, extChartAt I p w.1))
      (g := fun q : ℝ × E => chartScalarCurvatureOnE (I := I) (g q.1) p q.2)
      (p, t) hcoordM hread hmaps
  have heq : ∀ w ∈ D,
      scalarCurvatureAt (g w.2) (g w.2).leviCivitaConnection
          (scalarSpacetimeCanonicalLC (g w.2)) w.1 =
        chartScalarCurvatureOnE (I := I) (g w.2) p (extChartAt I p w.1) := by
    intro w hw
    have htarget := (extChartAt I p).map_source hw.1
    have hscalar := chartScalarCurvatureOnE_eq_scalarCurvatureAt
      (I := I) (g w.2) p htarget (scalarSpacetimeCanonicalLC (g w.2))
    rw [(extChartAt I p).left_inv hw.1] at hscalar
    exact hscalar.symm
  have hintrinsic : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => scalarCurvatureAt (g w.2) (g w.2).leviCivitaConnection
        (scalarSpacetimeCanonicalLC (g w.2)) w.1) D (p, t) :=
    hcomp.congr heq (heq (p, t) ⟨hp, hz.2⟩)
  have hsets : D =ᶠ[𝓝 (p, t)] ((Set.univ : Set M) ×ˢ J) := by
    filter_upwards
      [((isOpen_extChartAt_source (I := I) p).prod isOpen_univ).mem_nhds
        ⟨hp, mem_univ t⟩] with w hw
    apply propext
    change (w.1 ∈ (extChartAt I p).source ∧ w.2 ∈ J) ↔
      (w.1 ∈ (Set.univ : Set M) ∧ w.2 ∈ J)
    exact ⟨fun h => ⟨mem_univ _, h.2⟩, fun h => ⟨hw.1, h.2⟩⟩
  exact hintrinsic.congr_set hsets

/-- **Math.** A Ricci flow supplies joint scalar-curvature continuity on its actual
time set, as required by compact spatial minimum arguments. -/
theorem scalarCurvature_continuousOn_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) :
    ContinuousOn
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) (g z.2).leviCivitaConnection
        (scalarSpacetimeCanonicalLC (g z.2)) z.1)
      ((Set.univ : Set M) ×ˢ J) :=
  (scalarCurvature_contMDiffOn_of_isSmoothMetricFamilyOn hflow.smooth).continuousOn

end MorganTianLib

#print axioms MorganTianLib.scalarCurvature_contMDiffOn_of_isSmoothMetricFamilyOn
#print axioms MorganTianLib.scalarCurvature_continuousOn_of_isRicciFlowOn
