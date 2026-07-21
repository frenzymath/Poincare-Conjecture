import LeeLib.Ch06.HopfRinow
import LeeLib.Ch02.RiemannianCovering
import DoCarmoLib.Riemannian.Manifold.CoveringMapConclusion
import DoCarmoLib.Riemannian.Manifold.LocalIsometryRigidity
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-!
# Lee Chapter 6: complete local isometries are Riemannian coverings

This file formalizes Lee's Theorem 6.23. A local isometry whose source is
complete has complete target and is a Riemannian covering map. The proof uses
Hopf--Rinow to make the source proper, the metric-expanding covering theorem,
and the fact that local isometries carry global geodesics to global geodesics.
-/

noncomputable section

namespace LeeLib.Ch06

open Filter Manifold Set
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

set_option linter.unusedSectionVars false in
private theorem localInverse_value
    {f : Mt → M} {x : Mt} (hf : IsLocalDiffeomorphAt It I ∞ f x) :
    hf.localInverse (f x) = x := by
  exact hf.localInverse_left_inv hf.localInverse_mem_target

/-- **Math.** The chart expression of the local inverse to a local diffeomorphism is smooth at the
basepoint. This is the regularity input needed to differentiate a continuous path lift twice. -/
private theorem localInverse_mapReading_contDiffAt
    {f : Mt → M} {x : Mt} (hf : IsLocalDiffeomorphAt It I ∞ f x) :
    ContDiffAt ℝ ∞
      (Riemannian.mapReading (I := I) (I' := It) hf.localInverse
        (f x) x) (extChartAt I (f x) (f x)) := by
  have hs : ContMDiffAt I It ∞ (hf.localInverse : M → Mt) (f x) :=
    hf.localInverse_contMDiffAt
  have hs' := (contMDiffAt_iff.mp hs).2
  rw [I.range_eq_univ, contDiffWithinAt_univ] at hs'
  rw [localInverse_value hf] at hs'
  simpa [Riemannian.mapReading, Function.comp_def] using hs'

set_option linter.unusedSectionVars false in
/-- **Math.** A continuous lift agrees locally with the smooth local inverse applied to its
projection. -/
private theorem chartReading_lift_eventuallyEq_localInverse
    {f : Mt → M} (hf : IsLocalDiffeomorph It I ∞ f)
    {c : ℝ → M} {γ : ℝ → Mt} {t : ℝ}
    (hc : ContinuousAt c t) (hγ : ContinuousAt γ t)
    (hlift : ∀ τ, f (γ τ) = c τ) :
    Riemannian.Geodesic.chartReading (I := It) (γ t) γ =ᶠ[𝓝 t]
      fun τ => Riemannian.mapReading (I := I) (I' := It)
        (hf (γ t)).localInverse (c t) (γ t)
          (Riemannian.Geodesic.chartReading (I := I) (c t) c τ) := by
  let hft := hf (γ t)
  have hleft : hft.localInverse ∘ f =ᶠ[𝓝 (γ t)] id :=
    hft.localInverse_eventuallyEq_left
  have hleft' : ∀ᶠ τ in 𝓝 t, hft.localInverse (f (γ τ)) = γ τ := by
    exact hγ.eventually hleft
  have hcsrc : ∀ᶠ τ in 𝓝 t, c τ ∈ (extChartAt I (c t)).source :=
    hc.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) (c t))
  filter_upwards [hleft', hcsrc] with τ hτ hτsrc
  simp only [Riemannian.Geodesic.chartReading_def, Riemannian.mapReading_def]
  rw [(extChartAt I (c t)).left_inv hτsrc, ← hlift τ, hτ]

/-- **Math.** The first two chart derivatives of a continuous lift exist whenever its projection
is a geodesic. Locally the lift is `localInverse ∘ c`, so this is ordinary second-order calculus. -/
private theorem lift_chart_regular_of_isLocalDiffeomorph
    {f : Mt → M} (hf : IsLocalDiffeomorph It I ∞ f)
    {g : Riemannian.RiemannianMetric I M} {c : ℝ → M} {γ : ℝ → Mt}
    (hc : Continuous c) (hγ : Continuous γ)
    (hlift : ∀ τ, f (γ τ) = c τ)
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g c) (t : ℝ) :
    ∃ a : E,
      (∀ᶠ τ in 𝓝 t,
        HasDerivAt (Riemannian.Geodesic.chartReading (I := It) (γ t) γ)
          (deriv (Riemannian.Geodesic.chartReading (I := It) (γ t) γ) τ) τ) ∧
      HasDerivAt (deriv (Riemannian.Geodesic.chartReading (I := It) (γ t) γ)) a t := by
  let hft := hf (γ t)
  let u : ℝ → E := Riemannian.Geodesic.chartReading (I := It) (γ t) γ
  let W : ℝ → E := Riemannian.Geodesic.chartReading (I := I) (f (γ t)) c
  let S : E → E := Riemannian.mapReading (I := I) (I' := It)
    hft.localInverse (f (γ t)) (γ t)
  have hct : f (γ t) = c t := hlift t
  have hsolve : Riemannian.Geodesic.SolvesGeodesicODEAt
      (I := I) g (f (γ t)) c t := by
    simpa only [hct] using
      (Riemannian.Geodesic.hasGeodesicEquationAt_iff_solvesGeodesicODEAt.mp (hgeo t))
  obtain ⟨hW_ev, a, hWa, -⟩ := hsolve
  have hW_ev' : ∀ᶠ τ in 𝓝 t, HasDerivAt W (deriv W τ) τ := by
    simpa only [W] using hW_ev
  have hWa' : HasDerivAt (deriv W) a t := by
    simpa only [W] using hWa
  have hS : ContDiffAt ℝ ∞ S (W t) := by
    have h := localInverse_mapReading_contDiffAt hft
    change ContDiffAt ℝ ∞ S (extChartAt I (f (γ t)) (c t))
    rw [← hct]
    exact h
  have hS2 : ContDiffAt ℝ 2 S (W t) :=
    hS.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hWcont : ContinuousAt W t := (hW_ev'.self_of_nhds).continuousAt
  have hS_ev : ∀ᶠ τ in 𝓝 t, ContDiffAt ℝ 2 S (W τ) :=
    hWcont.eventually (hS2.eventually (by norm_num))
  have hrel : u =ᶠ[𝓝 t] fun τ => S (W τ) := by
    have h := chartReading_lift_eventuallyEq_localInverse
      (c := c) (γ := γ) (t := t) hf hc.continuousAt hγ.continuousAt hlift
    simpa only [u, W, S, hct] using h
  have hu_raw : ∀ᶠ τ in 𝓝 t, HasDerivAt u
      (fderiv ℝ S (W τ) (deriv W τ)) τ := by
    filter_upwards [hW_ev', hS_ev, hrel.eventually_nhds] with τ hWτ hSτ hrelτ
    have hcomp := (hSτ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt τ hWτ
    exact hcomp.congr_of_eventuallyEq hrelτ
  have hu_ev : ∀ᶠ τ in 𝓝 t, HasDerivAt u (deriv u τ) τ := by
    filter_upwards [hu_raw] with τ hτ
    rw [hτ.deriv]
    exact hτ
  have hu_deriv_eq : deriv u =ᶠ[𝓝 t]
      fun τ => fderiv ℝ S (W τ) (deriv W τ) := by
    filter_upwards [hu_raw] with τ hτ
    exact hτ.deriv
  have hDS : HasFDerivAt (fderiv ℝ S)
      (fderiv ℝ (fderiv ℝ S) (W t)) (W t) :=
    ((hS2.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hcDS : HasDerivAt (fun τ => fderiv ℝ S (W τ))
      (fderiv ℝ (fderiv ℝ S) (W t) (deriv W t)) t :=
    hDS.comp_hasDerivAt t hW_ev'.self_of_nhds
  have hsecond : HasDerivAt
      (fun τ => fderiv ℝ S (W τ) (deriv W τ))
      (fderiv ℝ (fderiv ℝ S) (W t) (deriv W t) (deriv W t) +
        fderiv ℝ S (W t) a) t :=
    hcDS.clm_apply hWa'
  refine ⟨fderiv ℝ (fderiv ℝ S) (W t) (deriv W t) (deriv W t) +
      fderiv ℝ S (W t) a, ?_, ?_⟩
  · simpa only [u] using hu_ev
  · simpa only [u] using hsecond.congr_of_eventuallyEq hu_deriv_eq

/-- **Math.** A continuous lift of a geodesic through a metric-preserving local diffeomorphism is
a geodesic. The local inverse supplies the lift's second derivative, and the pullback
Christoffel law reflects the geodesic equation. -/
private theorem isGeodesic_lift_of_isLocalDiffeomorph
    {f : Mt → M} (hf : IsLocalDiffeomorph It I ∞ f)
    (gt : Riemannian.RiemannianMetric It Mt) (g : Riemannian.RiemannianMetric I M)
    (hpres : Riemannian.DCPreservesMetric gt g f)
    {c : ℝ → M} {γ : ℝ → Mt} (hc : Continuous c) (hγ : Continuous γ)
    (hlift : ∀ τ, f (γ τ) = c τ)
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g c) :
    Riemannian.Geodesic.IsGeodesic (I := It) gt γ := by
  letI : Bundle.RiemannianBundle (TangentSpace It : Mt → Type _) :=
    ⟨gt.toRiemannianMetric⟩
  have hgt_eq : gt = Riemannian.RiemannianMetric.pullbackOfSmoothImmersion g f
      (Riemannian.dcSmoothImmersion_of_isLocalDiffeomorph hf) := by
    apply Riemannian.RiemannianMetric.eq_of_metricInner_eq
    intro x u v
    rw [Riemannian.RiemannianMetric.pullbackOfSmoothImmersion_metricInner]
    exact hpres x u v
  intro t
  rw [Riemannian.Geodesic.hasGeodesicEquationAt_iff_solvesGeodesicODEAt, hgt_eq]
  obtain ⟨a, hu_ev, ha⟩ := lift_chart_regular_of_isLocalDiffeomorph
    hf hc hγ hlift hgeo t
  apply Riemannian.Geodesic.solvesGeodesicODEAt_of_comp
    hf g hγ.continuousAt hu_ev a ha
  have hfun : (fun τ => f (γ τ)) = c := funext hlift
  rw [hfun]
  simpa only [hlift t] using
    (Riemannian.Geodesic.hasGeodesicEquationAt_iff_solvesGeodesicODEAt.mp (hgeo t))

/-- **Math.** **Lee, Corollary 6.24.** If `π : (M̃, g̃) → (M, g)` is a
Riemannian covering between connected Riemannian manifolds, then `M̃` is complete if and
only if `M` is complete.

The forward implication is Theorem 6.23. For the converse, lift each complete base geodesic
globally through the covering map. The smooth local inverse to `π` makes that continuous lift a
geodesic with the prescribed initial velocity, so Hopf--Rinow gives completeness of the cover. -/
theorem complete_iff_of_riemannianCovering
    (gt : LeeLib.Ch02.RiemannianMetric It Mt)
    (g : LeeLib.Ch02.RiemannianMetric I M)
    (π : C^∞⟮It, Mt; I, M⟯)
    (hπ : LeeLib.Ch02.IsRiemannianCovering gt g π) :
    letI : MetricSpace Mt := gt.toMetricSpace
    letI : MetricSpace M := g.toMetricSpace
    CompleteSpace Mt ↔ CompleteSpace M := by
  letI : MetricSpace Mt := gt.toMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  constructor
  · intro hcomplete
    exact (completeLocalIsometry gt g π hπ.isLocalIsometry hcomplete).1
  · intro hcomplete
    letI : CompleteSpace M := hcomplete
    letI : Bundle.RiemannianBundle (TangentSpace It : Mt → Type _) :=
      ⟨gt.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hgt : Riemannian.RiemannianMetric.IsRiemannianDist gt := ⟨fun _ _ => rfl⟩
    have hg : Riemannian.RiemannianMetric.IsRiemannianDist g := ⟨fun _ _ => rfl⟩
    have hbase : Riemannian.Geodesic.IsGeodesicallyComplete g :=
      Riemannian.Geodesic.isGeodesicallyComplete_of_complete g hg
    have hsource : Riemannian.Geodesic.IsGeodesicallyComplete gt := by
      intro p v
      let v' : TangentSpace I (π p) := mfderiv It I π p v
      obtain ⟨c, hc0, hcv, hccurve⟩ := hbase (π p) v'
      let cc : C(ℝ, M) := ⟨c, hccurve.continuous⟩
      obtain ⟨γc, ⟨hγ0, hγlift⟩, -⟩ :=
        hπ.1.isCoveringMap.existsUnique_continuousMap_lifts cc 0 p (by
          simpa only [cc, ContinuousMap.coe_mk] using hc0.symm)
      let γ : ℝ → Mt := γc
      have hγcont : Continuous γ := γc.continuous
      have hlift : ∀ t, π (γ t) = c t := by
        intro t
        exact congrFun hγlift t
      have hpres : Riemannian.DCPreservesMetric gt g π :=
        fun x u w => (hπ.2.inner_mfderiv x u w).symm
      have hγgeo : Riemannian.Geodesic.IsGeodesic (I := It) gt γ :=
        isGeodesic_lift_of_isLocalDiffeomorph hπ.1.isLocalDiffeomorph
          gt g hpres hccurve.continuous hγcont hlift hccurve.2
      have hγ0' : γ 0 = p := hγ0
      have hγd : HasDerivAt (Riemannian.Geodesic.chartReading (I := It) p γ)
          (deriv (Riemannian.Geodesic.chartReading (I := It) p γ) 0) 0 := by
        have h := (hγgeo 0).hasDerivAt_extChartAt_deriv
          hγcont.continuousAt (show γ 0 ∈ (chartAt Ht p).source by
            rw [hγ0']; exact mem_chart_source Ht p)
        simpa only [Riemannian.Geodesic.chartReading_def] using h
      have hdiff : MDifferentiableAt It I (π : Mt → M) p :=
        hπ.1.isLocalDiffeomorph.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      have hproj := Riemannian.hasDerivAt_extChartAt_comp_of_hasFDerivAt_mapReading
        (Riemannian.hasFDerivAt_mapReading_self hdiff) hγ0'
        hγcont.continuousAt hγd
      have hcurve : (fun t => extChartAt I (π p) (π (γ t))) =
          Riemannian.Geodesic.chartReading (I := I) (π p) c := by
        funext t
        simp only [Riemannian.Geodesic.chartReading_def, hlift]
      rw [hcurve] at hproj
      have hvel : deriv (Riemannian.Geodesic.chartReading (I := It) p γ) 0 =
          (v : E) := hπ.1.injective_mfderiv p (by
        exact hproj.unique (by simpa only [v'] using hcv))
      rw [hvel] at hγd
      exact ⟨γ, hγ0', hγd, hγcont, hγgeo⟩
    exact Riemannian.Geodesic.complete_of_isGeodesicallyComplete gt hgt hsource

end LeeLib.Ch06

end
