import PetersenLib.Ch06.DiameterBound
import PetersenLib.Ch05.LocalIsometryCovering
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Lifting

/-!
# The covering-space clause of Myers' theorem

The diameter argument in Myers' theorem applies equally to the simply
connected Riemannian universal cover.  Once that cover is compact, the
remaining conclusion that the base has finite fundamental group is purely
topological: monodromy embeds the fundamental group into one discrete compact
covering fiber.

This file proves that final implication for any explicitly supplied compact
simply connected cover.  Construction of the universal Riemannian cover and
transfer of the Ricci bound remain separate geometric inputs; completeness of
an explicit cover is discharged from completeness of the base below.
-/

open Set
open scoped Manifold ContDiff

noncomputable section

namespace PetersenLib

/-- **Math.** Every fiber of a covering map with compact total space and a
`T1` base is finite.  The fiber is closed in the compact total space and its
covering-space topology is discrete. -/
theorem finite_fiber_of_compact_covering
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T1Space Y] {p : X → Y}
    (hp : IsCoveringMap p) (y : Y) : Finite (p ⁻¹' {y}) := by
  letI : DiscreteTopology (p ⁻¹' {y}) := (hp y).discreteTopology_fiber
  have hclosed : IsClosed (p ⁻¹' {y}) := isClosed_singleton.preimage hp.continuous
  letI : CompactSpace (p ⁻¹' {y}) := isCompact_iff_compactSpace.mp hclosed.isCompact
  exact finite_of_compact_of_discrete

/-- **Math.** If the total space of a covering is simply connected, monodromy
at a chosen point of a fiber is injective.  Lift two loops with the same
monodromy endpoint; the lifted paths have common endpoints and are homotopic
upstairs, so their projections represent the same fundamental-group element. -/
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

/-- **Math.** A space admitting a compact simply connected surjective cover
has finite fundamental group at every base point.  Monodromy embeds the group
into a finite covering fiber. -/
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

/-! ## Myers' theorem on an explicitly supplied simply connected cover -/

section RiemannianCover

variable
  {Et : Type*} [NormedAddCommGroup Et] [NormedSpace ℝ Et]
    [InnerProductSpace ℝ Et]
    [FiniteDimensional ℝ Et] [NeZero (Module.finrank ℝ Et)]
    [CompleteSpace Et]
  {Ht : Type*} [TopologicalSpace Ht] {It : ModelWithCorners ℝ Et Ht}
  {Mt : Type*} [MetricSpace Mt] [ChartedSpace Ht Mt] [IsManifold It ∞ Mt]
    [It.Boundaryless] [SigmaCompactSpace Mt] [LocallyCompactSpace Mt]
    [T2Space (TangentBundle It Mt)] [ConnectedSpace Mt]
    [SimplyConnectedSpace Mt]
  {M : Type*} [TopologicalSpace M] [T1Space M]

/-- **Math.** Myers' diameter, compactness, and finite-fundamental-group
conclusions for an explicitly supplied simply connected cover.

The Riemannian metric, completeness, dimension, and Ricci lower bound are
stated on the covering space `Mt`.  Myers makes `Mt` compact; its continuous
surjective image `M` is compact, and monodromy embeds each fundamental group
of `M` into a finite fiber.  No construction of a universal smooth cover, nor
transfer of metric or curvature data across `p`, is assumed here. -/
theorem myersRicci_of_explicit_simplyConnectedCover
    (gt : RiemannianMetric It Mt) (hgt : gt.IsRiemannianDist)
    [CompleteSpace Mt] {k : ℝ} (hk : 0 < k)
    (hdim : 2 ≤ Module.finrank ℝ Et)
    (hRic : HasRicciBoundedBelow gt.leviCivita k)
    {p : Mt → M} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    Metric.diam (Set.univ : Set Mt) ≤ Real.pi / Real.sqrt k ∧
      CompactSpace Mt ∧ CompactSpace M ∧
      ∀ y : M, Finite (FundamentalGroup M y) := by
  have hmc := myersRicciDiameterBound_of_ricciLowerBound (I := It)
    gt hgt hk hdim hRic
  letI : CompactSpace Mt := hmc.2
  have hcompact : CompactSpace M := by
    rw [← isCompact_univ_iff]
    simpa only [image_univ, hsurj.range_eq] using
      isCompact_univ.image hp.continuous
  refine ⟨hmc.1, hmc.2, hcompact, ?_⟩
  intro y
  exact finite_fundamentalGroup_of_compact_simplyConnected_cover hp hsurj y

end RiemannianCover

/-! ## The explicit-cover conclusion from completeness of the base -/

section CompleteBaseRiemannianCover

variable
  {Et : Type*} [NormedAddCommGroup Et] [NormedSpace ℝ Et]
    [InnerProductSpace ℝ Et] [FiniteDimensional ℝ Et]
    [NeZero (Module.finrank ℝ Et)] [CompleteSpace Et]
  {Ht : Type*} [TopologicalSpace Ht] {It : ModelWithCorners ℝ Et Ht}
  {Mt : Type*} [MetricSpace Mt] [ChartedSpace Ht Mt] [IsManifold It ∞ Mt]
    [It.Boundaryless] [SigmaCompactSpace Mt] [LocallyCompactSpace Mt]
    [T2Space (TangentBundle It Mt)] [ConnectedSpace Mt]
    [SimplyConnectedSpace Mt]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space (TangentBundle I M)] [ConnectedSpace M]

/-- **Math.** Myers' conclusions for an explicitly supplied simply connected
Riemannian cover, with completeness stated on the base.  Geodesic completeness
lifts through the covering (`geodesicallyComplete_of_riemannianCovering`), so
Hopf--Rinow makes the cover metrically complete.  The complete local isometry
is then automatically surjective, and the existing compact-cover theorem
gives compactness and finite fundamental groups.

The Ricci lower bound remains an explicit hypothesis on the cover; this theorem
does not assume or conceal curvature transfer from the base. -/
theorem myersRicci_of_explicit_simplyConnectedRiemannianCover_completeBase
    (gt : RiemannianMetric It Mt) (hgt : gt.IsRiemannianDist)
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] {k : ℝ} (hk : 0 < k)
    (hdim : 2 ≤ Module.finrank ℝ Et)
    (hRic : HasRicciBoundedBelow gt.leviCivita k)
    {p : Mt → M} (hp : IsCoveringMap p)
    (hlocal : IsLocalRiemannianIsometry gt g p) :
    Metric.diam (Set.univ : Set Mt) ≤ Real.pi / Real.sqrt k ∧
      CompactSpace Mt ∧ CompactSpace M ∧
      ∀ y : M, Finite (FundamentalGroup M y) := by
  have hbaseGeo : IsGeodesicallyComplete (I := I) g :=
    (isGeodesicallyComplete_iff_geodesic (I := I) g).mpr
      (Geodesic.isGeodesicallyComplete_of_complete (I := I) g hg)
  have hcoverGeo : IsGeodesicallyComplete (I := It) gt :=
    geodesicallyComplete_of_riemannianCovering hlocal hp hbaseGeo
  have hcoverGeo' : Geodesic.IsGeodesicallyComplete (I := It) gt :=
    (isGeodesicallyComplete_iff_geodesic (I := It) gt).mp hcoverGeo
  letI : CompleteSpace Mt :=
    Geodesic.complete_of_isGeodesicallyComplete (I := It) gt hgt hcoverGeo'
  have hsurj : Function.Surjective p :=
    completeLocalIsometry_surjective hlocal hcoverGeo
  exact myersRicci_of_explicit_simplyConnectedCover
    gt hgt hk hdim hRic hp hsurj

end CompleteBaseRiemannianCover

end PetersenLib

end
