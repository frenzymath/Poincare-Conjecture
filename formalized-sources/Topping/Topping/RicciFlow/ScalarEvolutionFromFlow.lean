import MorganTianLib.Ch03.RicciFlow.ScalarTraceEvolution
import Topping.MaximumPrinciple.ScalarConsequences
import Topping.Riemannian.Variation
import Topping.RicciFlow.ScalarEvolutionUnconditional
import Topping.RicciFlow.ScalarSpacetimeSmooth

/-!
# Scalar curvature evolution from a genuine Ricci flow

Morgan--Tian's coordinate calculation proves the scalar evolution equation at
every interior time of a smooth Ricci flow.  This file transports that theorem
across Topping's scalar curvature, Laplacian, and Ricci-norm conventions.  The
restriction to `interior J` is genuine: the imported theorem gives an ordinary
derivative there, not a one-sided derivative at an endpoint of `J`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Topping's Ricci tensor is the canonical Ricci tensor used in the
Morgan--Tian Ricci-flow equation. -/
theorem ricciTensorAt_eq_mtRicciTensorAt
    (g : RiemannianMetric I M) (p : M) (v w : TangentSpace I p) :
    ricciTensorAt g p v w = MorganTianLib.ricciTensorAt g p v w := by
  rw [ricciTensorAt_eq_ricciAt]
  exact MorganTianLib.ricciAt_leviCivita_eq_ricciTensorAt
    g (isLeviCivita_leviCivitaConnection g) p v w

/-- **Math.** Consequently the two squared Ricci-norm conventions agree. -/
theorem ricciNormSqAt_eq_mtRicciNormSqAt
    (g : RiemannianMetric I M) (p : M) :
    ricciNormSqAt g p = MorganTianLib.ricciNormSqAt g p := by
  have hric : ricciTensorAt g p = MorganTianLib.ricciTensorAt g p := by
    ext v w
    exact ricciTensorAt_eq_mtRicciTensorAt g p v w
  simp only [ricciNormSqAt, MorganTianLib.ricciNormSqAt,
    ricciEndomorphismAt, MorganTianLib.ricciEndomorphismAt]
  rw [hric]
  rfl

/-- **Math.** The full Morgan--Tian Ricci-flow equation is also Topping's
Ricci-flow equation after transporting the Ricci-tensor convention. -/
theorem isRicciFlowOn_of_morganTian_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) :
    Topping.IsRicciFlowOn g J := by
  intro t ht p x y
  simpa only [ricciTensorAt_eq_mtRicciTensorAt] using
    hflow.equation t ht p x y

/-- **Math.** Consequently a Morgan--Tian Ricci flow supplies Topping's
pointwise self-chart volume-form variation, including within-derivatives at
endpoints of its time set. -/
theorem hasVolumeFormVariationOn_selfChart_of_morganTian_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) :
    HasVolumeFormVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y)
      (fun t p => selfChartVolumeDensityAt (g t) p) J :=
  hasVolumeFormVariationOn_selfChart_of_isRicciFlowOn
    (isRicciFlowOn_of_morganTian_isRicciFlowOn hflow)

/-- **Math.** The corresponding self-chart density equation is
`partial_t rho = -R rho` on the whole Morgan--Tian flow time set. -/
theorem hasDerivWithinAt_selfChartVolumeDensityAt_of_morganTian_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ J) (p : M) :
    HasDerivWithinAt (fun s => selfChartVolumeDensityAt (g s) p)
      (-scalarCurvatureAt (g t) p * selfChartVolumeDensityAt (g t) p) J t :=
  hasDerivWithinAt_selfChartVolumeDensityAt_of_isRicciFlowOn
    (isRicciFlowOn_of_morganTian_isRicciFlowOn hflow) ht p

/-- **Math.** A smooth Ricci flow satisfies
`partial_t R = Delta R + 2 |Ric|^2` at every interior time. -/
theorem hasScalarCurvatureEvolutionOn_interior_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) :
    HasScalarCurvatureEvolutionOn g (interior J) := by
  intro t ht p
  let y := extChartAt I p p
  have hy : y ∈ (extChartAt I p).target := mem_extChartAt_target p
  have hpoint : (extChartAt I p).symm y = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source p)
  have hderiv :=
    MorganTianLib.hasDerivAt_scalarCurvatureAt_leviCivita_of_isRicciFlowOn_eq_laplacian_add_reaction
      hflow p ht hy
  rw [hpoint] at hderiv
  have htimeFunction :
      (fun s => MorganTianLib.scalarCurvatureAt (g s)
        (g s).leviCivitaConnection (isLeviCivita_leviCivitaConnection (g s)) p) =
        fun s => scalarCurvatureAt (g s) p := by
    funext s
    exact (scalarCurvatureAt_eq_scalarCurvatureAt (g s) p).symm
  have hspaceFunction :
      (fun q => MorganTianLib.scalarCurvatureAt (g t)
        (g t).leviCivitaConnection (isLeviCivita_leviCivitaConnection (g t)) q) =
        fun q => scalarCurvatureAt (g t) q := by
    funext q
    exact (scalarCurvatureAt_eq_scalarCurvatureAt (g t) q).symm
  have hdim : Module.finrank ℝ E ≠ 0 := NeZero.ne _
  have hvalue :
      MorganTianLib.laplacianAt (g t) (g t).leviCivitaConnection
          (MorganTianLib.scalarCurvatureAt (g t) (g t).leviCivitaConnection
            (isLeviCivita_leviCivitaConnection (g t))) p +
          2 * MorganTianLib.ricciNormSqAt (g t) p =
        metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
          2 * ricciNormSqAt (g t) p := by
    unfold metricLaplacianAt
    simp only [hdim, ↓reduceDIte]
    rw [← hspaceFunction, ricciNormSqAt_eq_mtRicciNormSqAt]
  rw [htimeFunction, hvalue] at hderiv
  exact hderiv.hasDerivWithinAt

/-! The coordinate calculation is stated on `interior J` because it uses an
ordinary time derivative.  Restricting that result to a smaller set is the
endpoint adapter needed by the maximum-principle consumers: a closed interval
`K` gets a genuine within-derivative at both endpoints whenever it sits inside
the ambient flow interval's interior. -/

/-- **Math.** A Ricci flow witnesses Topping's scalar evolution on every time
set contained in the interior of its ambient flow interval. -/
theorem hasScalarCurvatureEvolutionOn_of_isRicciFlowOn_of_subset_interior
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J)
    (hK : K ⊆ interior J) :
    HasScalarCurvatureEvolutionOn g K := by
  intro t ht p
  exact
    (hasScalarCurvatureEvolutionOn_interior_of_isRicciFlowOn hflow t (hK ht) p).mono hK

/-- **Math.** The same genuine flow therefore witnesses Topping's scalar first
variation formula in the direction `h = -2 Ric` at every interior time. -/
theorem hasScalarVariationOn_interior_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) :
    HasScalarVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y) (interior J) :=
  hasScalarVariationOn_of_hasScalarCurvatureEvolutionOn
    (hasScalarCurvatureEvolutionOn_interior_of_isRicciFlowOn hflow)

/-- **Math.** The same restriction supplies Topping's scalar first-variation
formula, including within-derivatives at endpoints of a smaller closed time
set. -/
theorem hasScalarVariationOn_of_isRicciFlowOn_of_subset_interior
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J)
    (hK : K ⊆ interior J) :
    HasScalarVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y) K :=
  hasScalarVariationOn_of_hasScalarCurvatureEvolutionOn
    (hasScalarCurvatureEvolutionOn_of_isRicciFlowOn_of_subset_interior hflow hK)

/-- **Math.** On an open flow domain, every target time set inherits the
scalar evolution, including its endpoints. -/
theorem hasScalarCurvatureEvolutionOn_of_isRicciFlowOn_of_isOpen
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) (hJ : IsOpen J)
    (hK : K ⊆ J) : HasScalarCurvatureEvolutionOn g K := by
  apply hasScalarCurvatureEvolutionOn_of_isRicciFlowOn_of_subset_interior hflow
  simpa [hJ.interior_eq] using hK

/-- **Math.** The scalar first-variation formula has the same open-domain
endpoint adapter. -/
theorem hasScalarVariationOn_of_isRicciFlowOn_of_isOpen
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) (hJ : IsOpen J)
    (hK : K ⊆ J) :
    HasScalarVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y) K := by
  apply hasScalarVariationOn_of_isRicciFlowOn_of_subset_interior hflow
  simpa [hJ.interior_eq] using hK

/-! A flow on `[0,T)` has no ordinary derivative obligation at its terminal
endpoint.  The maximum-principle consumers are stated on closed intervals, so
we exhaust each target time `t < T` by the closed interval `[0,t]` and use the
genuine evolution only on its positive-time part. -/

/-- **Math.** A lower scalar-curvature bound is preserved at every time of a
half-open Ricci flow.  The joint space-time smoothness needed by the maximum
principle remains an explicit antecedent; the flow itself supplies the genuine
scalar evolution on each positive-time exhaustion interval. -/
theorem scalarCurvature_ge_of_initial_ge_of_isRicciFlowOn_Ico
    {g : ℝ → RiemannianMetric I M} {T alpha : ℝ}
    [CompactSpace M]
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Ico 0 T → alpha ≤ scalarCurvatureAt (g t) p := by
  intro p t ht
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · exact hzero p
  · have hK : Ioc (0 : ℝ) t ⊆ interior (Ico 0 T) := by
      intro s hs
      rw [interior_Ico]
      exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hevolution :=
      hasScalarCurvatureEvolutionOn_of_isRicciFlowOn_of_subset_interior
        hflow hK
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := by
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2.le⟩
    have hRt : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
        ((Set.univ : Set M) ×ˢ Icc 0 t) :=
      hR.mono (by
        intro z hz
        exact ⟨hz.1, hsub hz.2⟩)
    exact
      (scalarCurvature_ge_of_initial_ge_of_evolution_on_Ioc
        (g := g) (T := t) (alpha := alpha) htpos hRt hevolution hzero)
        p t ⟨htpos.le, le_rfl⟩

/-- **Math.** The nonpositive quadratic scalar lower barrier is preserved at
every time of a half-open Ricci flow, with the denominator positivity supplied
by the sign of the initial bound. -/
theorem scalarLowerBarrier_le_of_initial_nonpos_of_isRicciFlowOn_Ico
    {g : ℝ → RiemannianMetric I M} {T alpha : ℝ}
    [CompactSpace M]
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (halpha : alpha ≤ 0)
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Ico 0 T →
      scalarLowerBarrier (Module.finrank ℝ E) alpha t ≤
        scalarCurvatureAt (g t) p := by
  intro p t ht
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · simpa [scalarLowerBarrier, quadraticBarrier] using hzero p
  · have hK : Ioc (0 : ℝ) t ⊆ interior (Ico 0 T) := by
      intro s hs
      rw [interior_Ico]
      exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hevolution :=
      hasScalarCurvatureEvolutionOn_of_isRicciFlowOn_of_subset_interior
        hflow hK
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := by
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2.le⟩
    have hRt : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
        ((Set.univ : Set M) ×ˢ Icc 0 t) :=
      hR.mono (by
        intro z hz
        exact ⟨hz.1, hsub hz.2⟩)
    exact
      (scalarLowerBarrier_le_of_initial_nonpos_on_Ioc
        (g := g) (T := t) (alpha := alpha) htpos hRt hevolution halpha hzero)
        p t ⟨htpos.le, le_rfl⟩

#print axioms Topping.hasScalarCurvatureEvolutionOn_interior_of_isRicciFlowOn
#print axioms Topping.hasScalarCurvatureEvolutionOn_of_isRicciFlowOn_of_subset_interior
#print axioms Topping.hasScalarCurvatureEvolutionOn_of_isRicciFlowOn_of_isOpen
#print axioms Topping.hasScalarVariationOn_interior_of_isRicciFlowOn
#print axioms Topping.hasScalarVariationOn_of_isRicciFlowOn_of_subset_interior
#print axioms Topping.hasScalarVariationOn_of_isRicciFlowOn_of_isOpen
#print axioms Topping.scalarCurvature_ge_of_initial_ge_of_isRicciFlowOn_Ico
#print axioms Topping.scalarLowerBarrier_le_of_initial_nonpos_of_isRicciFlowOn_Ico
#print axioms Topping.isRicciFlowOn_of_morganTian_isRicciFlowOn
#print axioms Topping.hasVolumeFormVariationOn_selfChart_of_morganTian_isRicciFlowOn
#print axioms Topping.hasDerivWithinAt_selfChartVolumeDensityAt_of_morganTian_isRicciFlowOn

end Topping

end
