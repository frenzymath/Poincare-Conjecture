import LeeLib.AppendixA.CoveringLifting
import LeeLib.Ch02.RiemannianCovering
import LeeLib.Ch06.HopfRinow
import LeeLib.Ch12.MyersIndex
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Lee Chapter 12: Myers' theorem

The diameter and compactness clauses reuse DoCarmoLib's Bonnet--Myers assembly.
MorganTianLib's second-variation theorem supplies the remaining minimizing-index
inequality, yielding a callback-free theorem under the standard positive Ricci,
completeness, connectedness, and dimension assumptions.  Lower-level packaged
index and analytic interfaces are retained for reuse.

For the topological last step, a covering of a compact space has finite fibers
because covering fibers are discrete.  For a connected total space, evaluation
at one point embeds the covering-automorphism group into such a fiber, so that
group is finite as well.

For a simply connected total space, monodromy at one point is injective.  Thus
a compact simply connected cover gives the finite fundamental-group conclusion
directly, without first constructing an equivalence between the fundamental
group and a fiber or the covering-automorphism group.  The latter conditional
forms are retained as useful alternate interfaces.  Finally,
`myers_finiteFundamentalGroup_of_simplyConnected_riemannianCover` combines this
topological step with the callback-free compactness theorem for an explicitly
given simply connected Riemannian cover.
-/

noncomputable section

namespace LeeLib.Ch12

open Set
open scoped Manifold ContDiff Topology

/-- **Math.** Every fiber of a covering map with compact total space and a
`T₁` base is finite.  The fiber is closed in the compact total space and has
the discrete topology supplied by the covering trivialization. -/
theorem finite_fiber_of_compact_covering
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T1Space Y] {p : X → Y}
    (hp : IsCoveringMap p) (y : Y) : Finite (p ⁻¹' {y}) := by
  letI : DiscreteTopology (p ⁻¹' {y}) := (hp y).discreteTopology_fiber
  have hclosed : IsClosed (p ⁻¹' {y}) := isClosed_singleton.preimage hp.continuous
  letI : CompactSpace (p ⁻¹' {y}) := isCompact_iff_compactSpace.mp hclosed.isCompact
  exact finite_of_compact_of_discrete

/-- **Math.** If the total space of a covering is simply connected, monodromy
at any chosen point of a fiber is injective.  Two loops with the same lifted
endpoint give paths in the total space with common endpoints; simple
connectedness makes those paths homotopic, and projecting the homotopy proves
the original loops equal in the fundamental group. -/
theorem monodromy_at_injective
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] {p : E → X} (cov : IsCoveringMap p)
    {x : X} (e : E) (he : p e = x) :
    Function.Injective
      (fun γ : FundamentalGroup X x => cov.monodromy γ ⟨e, he⟩) := by
  intro γ δ h
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    induction δ using Path.Homotopic.Quotient.ind with
    | mk δ =>
      let Γ := cov.liftPath γ e (γ.source.trans he.symm)
      let Δ := cov.liftPath δ e (δ.source.trans he.symm)
      have hΓ0 : Γ 0 = e := cov.liftPath_zero ..
      have hΔ0 : Δ 0 = e := cov.liftPath_zero ..
      have hend : Γ 1 = Δ 1 := congrArg Subtype.val h
      let Γp : Path e (Γ 1) := ⟨Γ, hΓ0, rfl⟩
      let Δp : Path e (Γ 1) := ⟨Δ, hΔ0, hend.symm⟩
      have hup : Path.Homotopic.Quotient.mk Γp =
          Path.Homotopic.Quotient.mk Δp := Subsingleton.elim _ _
      have hdown := congrArg (fun q => q.map ⟨p, cov.continuous⟩) hup
      have hΓmap : HEq
          ((Path.Homotopic.Quotient.mk Γp).map ⟨p, cov.continuous⟩)
          (Path.Homotopic.Quotient.mk γ) := by
        rw [← Path.Homotopic.Quotient.mk_map]
        apply Path.Homotopic.hpath_hext
        intro t
        exact congrFun (cov.liftPath_lifts γ e (γ.source.trans he.symm)) t
      have hΔmap : HEq
          ((Path.Homotopic.Quotient.mk Δp).map ⟨p, cov.continuous⟩)
          (Path.Homotopic.Quotient.mk δ) := by
        rw [← Path.Homotopic.Quotient.mk_map]
        apply Path.Homotopic.hpath_hext
        intro t
        exact congrFun (cov.liftPath_lifts δ e (δ.source.trans he.symm)) t
      exact eq_of_heq (hΓmap.symm.trans ((heq_of_eq hdown).trans hΔmap))

/-- **Math.** A space admitting a compact simply connected covering has finite
fundamental group.  Monodromy embeds the fundamental group into one covering
fiber, and that fiber is finite because it is compact and discrete. -/
theorem finite_fundamentalGroup_of_compact_simplyConnected_cover
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [SimplyConnectedSpace X] [TopologicalSpace Y] [T1Space Y]
    {p : X → Y} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (y : Y) :
    Finite (FundamentalGroup Y y) := by
  obtain ⟨x, hx⟩ := hsurj y
  letI : Finite (p ⁻¹' {y}) := finite_fiber_of_compact_covering hp y
  exact Finite.of_injective
    (fun γ : FundamentalGroup Y y => hp.monodromy γ ⟨x, hx⟩)
    (monodromy_at_injective hp x hx)

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- Smooth-cover specialization of
`finite_fundamentalGroup_of_compact_simplyConnected_cover`, suitable for the
universal Riemannian cover in Myers' theorem. -/
theorem finite_fundamentalGroup_of_compact_simplyConnected_smoothCover
    [CompactSpace M] [SimplyConnectedSpace M] [T1Space M']
    {π : C^∞⟮I, M; I', M'⟯} (hπ : LeeLib.Ch02.IsSmoothCoveringMap π) (p : M') :
    Finite (FundamentalGroup M' p) :=
  finite_fundamentalGroup_of_compact_simplyConnected_cover
    hπ.isCoveringMap hπ.surjective p

/-- **Math.** Evaluate a covering automorphism at a chosen point, regarded as
a point of the fiber over its image. -/
def coveringAutEval (π : C^∞⟮I, M; I', M'⟯) (x : M) :
    LeeLib.Ch02.CoveringAut π → π ⁻¹' {π x} :=
  fun φ => ⟨φ x, by
    change π (φ x) = π x
    exact φ.proj_comp x⟩

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- **Math.** On a connected covering space, a covering automorphism is
determined by its value at one point.  This is unique lifting applied to two
automorphisms over the same projection. -/
theorem coveringAutEval_injective [ConnectedSpace M]
    {π : C^∞⟮I, M; I', M'⟯} (hπ : LeeLib.Ch02.IsSmoothCoveringMap π) (x : M) :
    Function.Injective (coveringAutEval π x) := by
  intro φ ψ hφψ
  apply LeeLib.Ch02.CoveringAut.ext
  intro y
  have hcomp :
      (π : M → M') ∘ (φ : M → M) = (π : M → M') ∘ (ψ : M → M) := by
    funext z
    exact (φ.proj_comp z).trans (ψ.proj_comp z).symm
  have hfun : (φ : M → M) = (ψ : M → M) :=
    LeeLib.AppendixA.coveringMap_unique_lift hπ.isCoveringMap
      φ.toDiffeomorph.continuous ψ.toDiffeomorph.continuous hcomp x
      (congrArg Subtype.val hφψ)
  exact congrFun hfun y

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- **Math.** The covering-automorphism group of a connected compact smooth
covering space is finite: evaluation embeds it into one finite fiber. -/
theorem finite_coveringAut_of_compact [CompactSpace M] [ConnectedSpace M] [T1Space M']
    {π : C^∞⟮I, M; I', M'⟯} (hπ : LeeLib.Ch02.IsSmoothCoveringMap π) (x : M) :
    Finite (LeeLib.Ch02.CoveringAut π) := by
  letI : Finite (π ⁻¹' {π x}) :=
    finite_fiber_of_compact_covering hπ.isCoveringMap (π x)
  exact Finite.of_injective (coveringAutEval π x) (coveringAutEval_injective hπ x)

/-- **Math.** Conditional form of Lee Appendix A.61 followed by compactness:
if a fundamental group is explicitly identified with a fiber of a covering
whose total space is compact, then the fundamental group is finite.

The equivalence is an explicit hypothesis because the universal-cover
fiber/fundamental-group correspondence is the still-unformalized Appendix C
input; the covering-space compactness argument itself is complete. -/
theorem finite_fundamentalGroup_of_fiber_equiv
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T1Space Y] {p : X → Y} (hp : IsCoveringMap p) (y : Y)
    (e : FundamentalGroup Y y ≃ p ⁻¹' {y}) : Finite (FundamentalGroup Y y) := by
  letI : Finite (p ⁻¹' {y}) := finite_fiber_of_compact_covering hp y
  exact Finite.of_injective e e.injective

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- **Math.** Conditional deck-transformation form of the finite fundamental
group step in Myers' theorem.  If the fundamental group is explicitly
identified with the covering-automorphism group of a connected compact smooth
cover, then it is finite. -/
theorem finite_fundamentalGroup_of_coveringAut_equiv
    [CompactSpace M] [ConnectedSpace M] [T1Space M']
    {π : C^∞⟮I, M; I', M'⟯} (hπ : LeeLib.Ch02.IsSmoothCoveringMap π)
    (x : M) (p : M')
    (e : FundamentalGroup M' p ≃ LeeLib.Ch02.CoveringAut π) :
    Finite (FundamentalGroup M' p) := by
  letI : Finite (LeeLib.Ch02.CoveringAut π) := finite_coveringAut_of_compact hπ x
  exact Finite.of_injective e e.injective

/-! ## The diameter and compactness clauses -/

section RiemannianMyers

variable [InnerProductSpace ℝ E] [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T3Space M] [ConnectedSpace M]

omit [InnerProductSpace ℝ E] [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem myersMetric_isRiemannianDist
    (g : LeeLib.Ch02.RiemannianMetric I M) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    Riemannian.RiemannianMetric.IsRiemannianDist g := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ⟨fun _ _ => rfl⟩

set_option linter.unusedVariables false in
/-- **Math.** A low-level packaged-index form of the diameter and compactness
clauses of Lee's Myers theorem.  The global hypothesis
`hRic` is the genuine bound `Ric ≥ (n-1)/r²`.  For every hypothetical
distance-minimizing geodesic longer than `πr`, `hvar` supplies a parallel
orthonormal frame and the nonnegative index forms forced by minimality.
The shared Bonnet--Myers contradiction makes their sum negative, ruling out
the long segment; Hopf--Rinow then gives `diam M ≤ πr` and compactness.

The existence of the packaged index data is explicit because the concrete
exponential-variation/second-variation bridge is still open.  Finiteness of
the fundamental group is the separate covering-space step formalized above. -/
theorem myersPositiveRicci_diameterCompact
    (g : LeeLib.Ch02.RiemannianMetric I M) {r : ℝ} :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    ∀ (hr : 0 < r)
      (hRic : Riemannian.Variation.HasRicciLowerBound (I := I) g r)
      (hvar : ∀ (σ : ℝ → M) (ℓ : ℝ), 0 < ℓ → Real.pi * r < ℓ →
        Riemannian.Geodesic.IsGeodesicOn (I := I) g σ (Set.Icc (0 : ℝ) 1) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist (σ s) (σ t) = |s - t| * ℓ) →
        Riemannian.Variation.BonnetMyersIndexData (I := I) g σ ℓ),
      CompleteSpace M →
        Metric.diam (Set.univ : Set M) ≤ Real.pi * r ∧ CompactSpace M := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hr hRic hvar hcomplete
  letI : CompleteSpace M := hcomplete
  exact Riemannian.Variation.bonnetMyers_diameterBound
    (I := I) g (myersMetric_isRiemannianDist g) hr hRic hvar

set_option linter.unusedVariables false in
/-- **Math.** Lee's diameter and compactness conclusion with the geometric
frame data constructed internally.  The explicit `2 ≤ dim M` assumption
provides a direction perpendicular to the minimizing geodesic.  For the
parallel velocity frame selected by Hopf--Rinow and parallel transport, the
caller supplies only the remaining analytic fact: nonnegativity of the
sine-field index forms.  Curvature-coefficient continuity is derived from the
geodesic and parallel-frame data in the shared DoCarmo assembly.  The frame is
available on `[-1,2]`, providing the endpoint room required by concrete smooth
variations around the segment `[0,1]`. -/
theorem myersPositiveRicci_diameterCompact_of_analytic
    (g : LeeLib.Ch02.RiemannianMetric I M) {r : ℝ} :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    ∀ (hr : 0 < r) (hdim : 2 ≤ Module.finrank ℝ E)
      (hRic : Riemannian.Variation.HasRicciLowerBound (I := I) g r)
      (hanalytic : ∀ (σ : ℝ → M) (ℓ : ℝ), 0 < ℓ → Real.pi * r < ℓ →
        Continuous σ → Riemannian.Geodesic.IsGeodesic (I := I) g σ →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist (σ s) (σ t) = |s - t| * ℓ) →
        ∀ (e : Fin (Module.finrank ℝ E) → ℝ → E)
          (n₀ : Fin (Module.finrank ℝ E)),
          (∀ i, Riemannian.Jacobi.IsParallelFieldAlongOn
            (I := I) g σ (e i) (-1) 2) →
          (∀ t ∈ Set.Icc (-1 : ℝ) 2, ∀ i j,
            Riemannian.RiemannianMetric.metricInner g (σ t)
              (e i t : TangentSpace I (σ t)) (e j t) =
              if i = j then 1 else 0) →
          (∀ t ∈ Set.Icc (-1 : ℝ) 2,
            Riemannian.DCVelocity (I := I) σ t =
              (ℓ • e n₀ t : TangentSpace I (σ t))) →
          Riemannian.Variation.BonnetMyersAnalyticData (I := I) g σ e n₀),
      CompleteSpace M →
        Metric.diam (Set.univ : Set M) ≤ Real.pi * r ∧ CompactSpace M := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hr hdim hRic hanalytic hcomplete
  letI : CompleteSpace M := hcomplete
  exact Riemannian.Variation.bonnetMyers_diameterBound_of_analytic
    (I := I) g (myersMetric_isRiemannianDist g) hr hdim hRic hanalytic

set_option linter.unusedVariables false in
/-- **Math.** Lee's Myers diameter and compactness theorem.  On a complete,
connected Riemannian manifold of dimension at least two, the global bound
`Ric ≥ (n-1)/r²`, with `r > 0`, implies `diam M ≤ pi*r` and compactness.

Unlike `myersPositiveRicci_diameterCompact_of_analytic`, this theorem has no
variation or index-form premise.  The sine-field index inequality follows from
the minimizing-geodesic second variation in `sine_indexForm_nonneg_of_minimizing`;
the shared DoCarmo assembly supplies the parallel frame and the remaining
Bonnet--Myers contradiction. -/
theorem myersPositiveRicci_diameterCompact_of_dim
    (g : LeeLib.Ch02.RiemannianMetric I M) {r : ℝ} :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    ∀ (hr : 0 < r) (hdim : 2 ≤ Module.finrank ℝ E)
      (hRic : Riemannian.Variation.HasRicciLowerBound (I := I) g r),
      CompleteSpace M →
        Metric.diam (Set.univ : Set M) ≤ Real.pi * r ∧ CompactSpace M := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hr hdim hRic hcomplete
  letI : CompleteSpace M := hcomplete
  apply Riemannian.Variation.bonnetMyers_diameterBound_of_analytic
    (I := I) g (myersMetric_isRiemannianDist g) hr hdim hRic
  intro σ ℓ _ _ hσc hσgeo hdist e _ hpar horth _
  refine ⟨fun j _ => ?_⟩
  exact sine_indexForm_nonneg_of_minimizing (I := I) g
    (myersMetric_isRiemannianDist g) hσc hσgeo hdist hpar horth j

end RiemannianMyers

/-! ## The fundamental-group clause on an explicit Riemannian cover -/

section RiemannianCoverMyers

variable
  {Et : Type*} [NormedAddCommGroup Et] [InnerProductSpace ℝ Et]
    [Module.Finite ℝ Et]
  {Ht : Type*} [TopologicalSpace Ht] {It : ModelWithCorners ℝ Et Ht}
    [It.Boundaryless]
  {Mt : Type*} [TopologicalSpace Mt] [ChartedSpace Ht Mt]
    [IsManifold It ∞ Mt] [SigmaCompactSpace Mt] [T3Space Mt]
    [ConnectedSpace Mt] [NeZero (Module.finrank ℝ Et)]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T1Space M]

set_option linter.unusedVariables false in
/-- **Math.** The finite-fundamental-group clause of Myers' theorem for an
explicitly supplied simply connected Riemannian cover.  Positive Ricci
curvature and completeness on the covering manifold make it compact by
`myersPositiveRicci_diameterCompact_of_dim`; monodromy then embeds every
fundamental group of the base into a finite covering fiber.

The geometric hypotheses are stated on the cover because construction of the
universal smooth cover, pullback of the metric and Ricci bound, and transfer of
completeness are separate inputs not yet available in this project. -/
theorem myers_finiteFundamentalGroup_of_simplyConnected_riemannianCover
    (gt : LeeLib.Ch02.RiemannianMetric It Mt)
    (g : LeeLib.Ch02.RiemannianMetric I M)
    (π : C^∞⟮It, Mt; I, M⟯)
    (hπ : LeeLib.Ch02.IsRiemannianCovering gt g π)
    [SimplyConnectedSpace Mt] {r : ℝ} :
    letI : MetricSpace Mt := gt.toMetricSpace
    ∀ (hr : 0 < r) (hdim : 2 ≤ Module.finrank ℝ Et)
      (hRic : Riemannian.Variation.HasRicciLowerBound (I := It) gt r),
      CompleteSpace Mt → ∀ p : M, Finite (FundamentalGroup M p) := by
  letI : MetricSpace Mt := gt.toMetricSpace
  intro hr hdim hRic hcomplete p
  letI : CompleteSpace Mt := hcomplete
  have hmc := myersPositiveRicci_diameterCompact_of_dim
    (M := Mt) gt hr hdim hRic hcomplete
  letI : CompactSpace Mt := hmc.2
  exact finite_fundamentalGroup_of_compact_simplyConnected_smoothCover
    (M := Mt) (M' := M) hπ.1 p

set_option linter.unusedVariables false in
/-- **Math.** The full Myers conclusion on the base of an explicitly supplied
simply connected Riemannian cover.  Positive Ricci curvature and completeness
on the cover give it diameter at most `pi*r` and make it compact.  A Riemannian
covering does not increase distance, so surjectivity transfers the diameter
bound to the base; the base is compact as a continuous image of the cover, and
monodromy gives finiteness of every fundamental group.

This is the strongest assumption-free package currently available without a
general construction of the universal Riemannian cover and the corresponding
completeness and Ricci-curvature transfer theorems. -/
theorem myers_of_simplyConnected_riemannianCover
    [T3Space M] [ConnectedSpace M]
    (gt : LeeLib.Ch02.RiemannianMetric It Mt)
    (g : LeeLib.Ch02.RiemannianMetric I M)
    (π : C^∞⟮It, Mt; I, M⟯)
    (hπ : LeeLib.Ch02.IsRiemannianCovering gt g π)
    [SimplyConnectedSpace Mt] {r : ℝ} :
    letI : MetricSpace Mt := gt.toMetricSpace
    letI : MetricSpace M := g.toMetricSpace
    ∀ (hr : 0 < r) (hdim : 2 ≤ Module.finrank ℝ Et)
      (hRic : Riemannian.Variation.HasRicciLowerBound (I := It) gt r),
      CompleteSpace Mt →
        Metric.diam (Set.univ : Set M) ≤ Real.pi * r ∧
        CompactSpace M ∧ ∀ p : M, Finite (FundamentalGroup M p) := by
  letI : MetricSpace Mt := gt.toMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  intro hr hdim hRic hcomplete
  letI : CompleteSpace Mt := hcomplete
  have hmc := myersPositiveRicci_diameterCompact_of_dim
    (M := Mt) gt hr hdim hRic hcomplete
  letI : CompactSpace Mt := hmc.2
  have hcompact : CompactSpace M := by
    rw [← isCompact_univ_iff]
    simpa only [image_univ, hπ.1.surjective.range_eq] using
      isCompact_univ.image hπ.1.isCoveringMap.continuous
  refine ⟨?_, hcompact, ?_⟩
  · apply Metric.diam_le_of_forall_dist_le
      (mul_nonneg Real.pi_pos.le hr.le)
    intro x _ y _
    obtain ⟨xt, rfl⟩ := hπ.1.surjective x
    obtain ⟨yt, rfl⟩ := hπ.1.surjective y
    calc
      dist (π xt) (π yt) ≤ dist xt yt := by
        rw [dist_edist, dist_edist]
        apply ENNReal.toReal_mono (edist_ne_top _ _)
        exact hπ.isLocalIsometry.riemannianEDist_le xt yt
      _ ≤ Metric.diam (Set.univ : Set Mt) :=
        Metric.dist_le_diam_of_mem isCompact_univ.isBounded (by simp) (by simp)
      _ ≤ Real.pi * r := hmc.1
  · exact myers_finiteFundamentalGroup_of_simplyConnected_riemannianCover
      gt g π hπ hr hdim hRic hcomplete

end RiemannianCoverMyers

end LeeLib.Ch12

end
