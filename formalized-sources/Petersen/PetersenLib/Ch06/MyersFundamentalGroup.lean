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
transfer of completeness and the Ricci bound remain separate geometric inputs.
-/

open Set

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

end PetersenLib

end
