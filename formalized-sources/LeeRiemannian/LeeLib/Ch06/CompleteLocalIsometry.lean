import LeeLib.Ch06.HopfRinow
import LeeLib.Ch02.RiemannianCovering
import DoCarmoLib.Riemannian.Manifold.CoveringMapConclusion
import DoCarmoLib.Riemannian.Manifold.LocalIsometryRigidity

/-!
# Lee Chapter 6: complete local isometries are Riemannian coverings

This file formalizes Lee's Theorem 6.23. A local isometry whose source is
complete has complete target and is a Riemannian covering map. The proof uses
Hopf--Rinow to make the source proper, the metric-expanding covering theorem,
and the fact that local isometries carry global geodesics to global geodesics.
-/

noncomputable section

namespace LeeLib.Ch06

open Manifold
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {Ht : Type*} [TopologicalSpace Ht] {It : ModelWithCorners ℝ E Ht} [It.Boundaryless]
  {Mt : Type*} [TopologicalSpace Mt] [ChartedSpace Ht Mt] [IsManifold It ∞ Mt]
  [T3Space Mt] [ConnectedSpace Mt]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T3Space M] [ConnectedSpace M]

private theorem leeMetric_isRiemannianDist
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
    {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    [T3Space N] [ConnectedSpace N]
    (g : LeeLib.Ch02.RiemannianMetric J N) :
    letI : MetricSpace N := g.toMetricSpace
    Riemannian.RiemannianMetric.IsRiemannianDist g := by
  letI : MetricSpace N := g.toMetricSpace
  letI : Bundle.RiemannianBundle (TangentSpace J : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ⟨fun _ _ ↦ rfl⟩

/-- **Math.** **Lee, Theorem 6.23.** Let `π : (M̃, g̃) → (M, g)` be a
local isometry between connected Riemannian manifolds. If the source `M̃` is
complete, then the target `M` is complete and `π` is a Riemannian covering
map. -/
theorem completeLocalIsometry
    (gt : LeeLib.Ch02.RiemannianMetric It Mt)
    (g : LeeLib.Ch02.RiemannianMetric I M)
    (π : C^∞⟮It, Mt; I, M⟯)
    (hπ : LeeLib.Ch02.IsLocalIsometry gt g (π : Mt → M)) :
    letI : MetricSpace Mt := gt.toMetricSpace
    letI : MetricSpace M := g.toMetricSpace
    CompleteSpace Mt →
      CompleteSpace M ∧ LeeLib.Ch02.IsRiemannianCovering gt g π := by
  letI : MetricSpace Mt := gt.toMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  intro hcomplete
  letI : CompleteSpace Mt := hcomplete
  letI : Bundle.RiemannianBundle (TangentSpace It : Mt → Type _) :=
    ⟨gt.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgt : Riemannian.RiemannianMetric.IsRiemannianDist gt :=
    leeMetric_isRiemannianDist gt
  have hg : Riemannian.RiemannianMetric.IsRiemannianDist g :=
    leeMetric_isRiemannianDist g
  have hgeot : Riemannian.Geodesic.IsGeodesicallyComplete gt :=
    Riemannian.Geodesic.isGeodesicallyComplete_of_complete gt hgt
  let pt0 : Mt := Classical.choice (inferInstance : Nonempty Mt)
  letI : ProperSpace Mt :=
    Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at gt hgt pt0 (hgeot pt0)
  have hpres : Riemannian.DCPreservesMetric gt g (π : Mt → M) :=
    fun p u v ↦ (hπ.isMetricPreserving.inner_mfderiv p u v).symm
  have hexp : Riemannian.DCExpandsMetric gt g (π : Mt → M) :=
    hpres.dcExpandsMetric
  have hsurj : Function.Surjective (π : Mt → M) :=
    hexp.surjective hgt hπ.isLocalDiffeomorph
  have hcover : IsCoveringMap (π : Mt → M) :=
    hexp.isCoveringMap hgt hπ.isLocalDiffeomorph
  have hsmooth : LeeLib.Ch02.IsSmoothCoveringMap π :=
    ⟨hsurj, hcover, hπ.isLocalDiffeomorph⟩
  have hgeo : Riemannian.Geodesic.IsGeodesicallyComplete g := by
    intro p v
    obtain ⟨pt, rfl⟩ := hsurj p
    let dπ : TangentSpace It pt ≃L[ℝ] TangentSpace I (π pt) :=
      hπ.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) pt
    let vt : TangentSpace It pt := dπ.symm v
    obtain ⟨γ, hγ0, hγv, hγcont, hγgeo⟩ := hgeot pt vt
    refine ⟨fun t ↦ π (γ t), ?_, ?_, ?_, ?_⟩
    · simp only [hγ0]
    · have hdiff : MDifferentiableAt It I (π : Mt → M) pt :=
        hπ.isLocalDiffeomorph.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      have hderiv := Riemannian.hasDerivAt_extChartAt_comp_of_hasFDerivAt_mapReading
        (Riemannian.hasFDerivAt_mapReading_self hdiff) hγ0 hγcont.continuousAt hγv
      have hdπ : mfderiv It I (π : Mt → M) pt vt = v := by
        change dπ (dπ.symm v) = v
        exact dπ.apply_symm_apply v
      exact hdπ ▸ hderiv
    · exact hπ.isLocalDiffeomorph.contMDiff.continuous.comp hγcont
    · exact Riemannian.Geodesic.isGeodesic_comp_of_isLocalDiffeomorph
        hπ.isLocalDiffeomorph gt g hpres hγcont hγgeo
  have hcompleteTarget : CompleteSpace M :=
    Riemannian.Geodesic.complete_of_isGeodesicallyComplete g hg hgeo
  exact ⟨hcompleteTarget, hsmooth, hπ.isMetricPreserving⟩

end LeeLib.Ch06

end
