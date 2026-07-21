import DoCarmoLib.Riemannian.Variation.BonnetMyers
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Lifting

/-!
# Bonnet--Myers: the finite fundamental-group consequence

The diameter argument makes a complete positive-Ricci universal cover compact.  The
remaining implication is topological: a compact simply connected covering has finite
fibres, and monodromy injects the fundamental group of the base into one such fibre.

Universal-cover existence and transfer of a covering metric are deliberately not hidden
in this file.  The results below accept an explicitly supplied covering map, so their
axiom boundary is visible and they can be reused once that infrastructure is available.
-/

open Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Riemannian.Variation

/-! ## Compact covering fibres and monodromy -/

/-- **Math.** A fibre of a covering map over a `T₁` point is finite when the total
space is compact.  The covering trivialization gives the fibre the discrete topology;
the fibre is closed as the preimage of a singleton. -/
theorem finite_fiber_of_compact_covering
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T1Space Y] {p : X → Y}
    (hp : IsCoveringMap p) (y : Y) : Finite (p ⁻¹' {y}) := by
  letI : DiscreteTopology (p ⁻¹' {y}) := (hp y).discreteTopology_fiber
  have hclosed : IsClosed (p ⁻¹' {y}) := isClosed_singleton.preimage hp.continuous
  letI : CompactSpace (p ⁻¹' {y}) := isCompact_iff_compactSpace.mp hclosed.isCompact
  exact finite_of_compact_of_discrete

/-- **Math.** If the total space of a covering is simply connected, monodromy at
one chosen point of a fibre is injective.  Equal lifted endpoints give paths with
common endpoints upstairs; simple connectedness makes those paths homotopic, and
projection of the homotopy identifies the original fundamental-group elements. -/
theorem monodromy_at_injective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] {p : X → Y} (hp : IsCoveringMap p)
    {y : Y} (x : X) (hx : p x = y) :
    Function.Injective
      (fun γ : FundamentalGroup Y y => hp.monodromy γ ⟨x, hx⟩) := by
  intro γ δ h
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    induction δ using Path.Homotopic.Quotient.ind with
    | mk δ =>
      let Γ := hp.liftPath γ x (γ.source.trans hx.symm)
      let Δ := hp.liftPath δ x (δ.source.trans hx.symm)
      have hΓ0 : Γ 0 = x := hp.liftPath_zero ..
      have hΔ0 : Δ 0 = x := hp.liftPath_zero ..
      have hend : Γ 1 = Δ 1 := congrArg Subtype.val h
      let Γp : Path x (Γ 1) := ⟨Γ, hΓ0, rfl⟩
      let Δp : Path x (Γ 1) := ⟨Δ, hΔ0, hend.symm⟩
      have hup : Path.Homotopic.Quotient.mk Γp =
          Path.Homotopic.Quotient.mk Δp := Subsingleton.elim _ _
      have hdown := congrArg (fun q => q.map ⟨p, hp.continuous⟩) hup
      have hΓmap : HEq
          ((Path.Homotopic.Quotient.mk Γp).map ⟨p, hp.continuous⟩)
          (Path.Homotopic.Quotient.mk γ) := by
        rw [← Path.Homotopic.Quotient.mk_map]
        apply Path.Homotopic.hpath_hext
        intro t
        exact congrFun (hp.liftPath_lifts γ x (γ.source.trans hx.symm)) t
      have hΔmap : HEq
          ((Path.Homotopic.Quotient.mk Δp).map ⟨p, hp.continuous⟩)
          (Path.Homotopic.Quotient.mk δ) := by
        rw [← Path.Homotopic.Quotient.mk_map]
        apply Path.Homotopic.hpath_hext
        intro t
        exact congrFun (hp.liftPath_lifts δ x (δ.source.trans hx.symm)) t
      exact eq_of_heq (hΓmap.symm.trans ((heq_of_eq hdown).trans hΔmap))

/-- **Math.** A compact simply connected surjective covering has finite
fundamental group at every base point. -/
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

/-! ## A Bonnet--Myers package for an explicitly supplied cover -/

/-- **Math.** Bonnet--Myers on an explicitly supplied simply connected cover,
including the finite-fundamental-group conclusion on its base.

The curvature and variation hypotheses are placed on the covering manifold.  The
diameter/compactness part is the callback-free DoCarmo assembly; once compactness
is obtained, the preceding monodromy argument gives finiteness of every base
fundamental group.  Universal-cover existence and curvature transfer remain
separate inputs, rather than being smuggled into this theorem. -/
theorem bonnetMyers_of_explicit_simplyConnected_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [SigmaCompactSpace X] [T2Space X] [ConnectedSpace X] [CompleteSpace X]
    [SimplyConnectedSpace X]
    {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    (g : RiemannianMetric I X) (hg : g.IsRiemannianDist)
    {r : ℝ} (hr : 0 < r) (hdim : 2 ≤ Module.finrank ℝ E)
    (hRic : HasRicciLowerBound (I := I) g r)
    (hanalytic : ∀ (σ : ℝ → X) (ℓ : ℝ), 0 < ℓ → Real.pi * r < ℓ →
      Continuous σ → Riemannian.Geodesic.IsGeodesic (I := I) g σ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (σ s) (σ t) = |s - t| * ℓ) →
      ∀ (e : Fin (Module.finrank ℝ E) → ℝ → E)
        (n₀ : Fin (Module.finrank ℝ E)),
        (∀ i, Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g σ (e i) (-1) 2) →
        (∀ t ∈ Set.Icc (-1 : ℝ) 2, ∀ i j,
          g.metricInner (σ t) (e i t : TangentSpace I (σ t)) (e j t) =
            if i = j then 1 else 0) →
        (∀ t ∈ Set.Icc (-1 : ℝ) 2,
          DCVelocity (I := I) σ t = (ℓ • e n₀ t : TangentSpace I (σ t))) →
        BonnetMyersAnalyticData (I := I) g σ e n₀)
    {p : X → Y} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    Metric.diam (Set.univ : Set X) ≤ Real.pi * r ∧ CompactSpace X ∧
      ∀ y : Y, Finite (FundamentalGroup Y y) := by
  have hmc := bonnetMyers_diameterBound_of_analytic (I := I) g hg hr hdim hRic hanalytic
  letI : CompactSpace X := hmc.2
  refine ⟨hmc.1, inferInstance, ?_⟩
  intro y
  exact finite_fundamentalGroup_of_compact_simplyConnected_cover hp hsurj y

end Riemannian.Variation
