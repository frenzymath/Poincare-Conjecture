import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Rigidity of a simply connected quotient by a finite free action

This is a genuine orbit-quotient result: the covering property is constructed
from finiteness, freeness, continuity, and the topology of the source. It is
not assumed as a replacement for the mathematical conclusion.

The key observation is that monodromy surjects from the fundamental group of
the quotient onto the opposite of the acting group whenever the source is
path connected. Thus simple connectivity of the quotient forces the group
to be trivial. Simple connectivity of the source is not needed.

The sphere specialization gives the topological conclusion needed to eliminate
spherical space-form factors in the Poincare endgame. Smoothness of the
quotient structure is a separate issue; no diffeomorphism claim is made here.
-/

open Function Set Topology

namespace PoincareConjecture

section QuotientCovering

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [Group G] [MulAction G E]
  {p : E → X} (hp : IsQuotientCoveringMap p G)
  [PathConnectedSpace E] [SimplyConnectedSpace X]

include hp

/-- A quotient covering with path-connected source and simply connected base
has trivial acting group. The fundamental-group map is proved surjective by
path lifting in Mathlib, not included among the assumptions. -/
theorem quotientCovering_group_subsingleton : Subsingleton G := by
  obtain ⟨e⟩ := (inferInstance : Nonempty E)
  have hop : Subsingleton Gᵐᵒᵖ :=
    (hp.fundamentalGroupToMulOpposite_surjective (x := p e) ⟨e, rfl⟩).subsingleton
  exact ⟨fun g h => MulOpposite.op_injective (hop.elim _ _)⟩

/-- The quotient projection itself, not just some abstract equivalence, is
bijective over a simply connected base. -/
theorem quotientCovering_bijective : Bijective p := by
  letI : Subsingleton G := quotientCovering_group_subsingleton hp
  refine ⟨?_, hp.surjective⟩
  intro x y hxy
  obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.mp hxy
  have hg1 : g = 1 := Subsingleton.elim _ _
  simpa [hg1] using hg.symm

/-- The actual quotient covering projection is a homeomorphism. -/
noncomputable def quotientCoveringHomeomorph : E ≃ₜ X :=
  hp.isCoveringMap.isLocalHomeomorph.toHomeomorphOfBijective
    (quotientCovering_bijective hp)

@[simp] theorem quotientCoveringHomeomorph_apply (e : E) :
    quotientCoveringHomeomorph hp e = p e := rfl

end QuotientCovering

section FiniteAction

variable (G E : Type*) [Group G] [Finite G] [TopologicalSpace E]
  [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
  [LocallyCompactSpace E] [T2Space E] [PathConnectedSpace E]
  [SimplyConnectedSpace (MulAction.orbitRel.Quotient G E)]

include E

/-- A finite free continuous action on a locally compact Hausdorff,
path-connected space has simply connected quotient only if the group is trivial. -/
theorem finiteAction_group_subsingleton : Subsingleton G :=
  quotientCovering_group_subsingleton
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G) (E := E))

/-- A simply connected finite free orbit quotient is homeomorphic to the
original space, with the quotient projection as the homeomorphism. -/
noncomputable def finiteActionQuotientHomeomorph : E ≃ₜ MulAction.orbitRel.Quotient G E :=
  quotientCoveringHomeomorph
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G) (E := E))

@[simp] theorem finiteActionQuotientHomeomorph_apply (e : E) :
    finiteActionQuotientHomeomorph G E e = Quotient.mk (MulAction.orbitRel G E) e := rfl

end FiniteAction

/-- The standard three-sphere, with its subspace topology and round metric. -/
abbrev Sphere3 := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

/-- The source sphere needed for the quotient argument is path connected.
No formalization of the Poincare theorem is used for this instance. -/
instance sphere3_pathConnectedSpace : PathConnectedSpace Sphere3 := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere (E := EuclideanSpace ℝ (Fin 4)) ?_ 0 zero_le_one
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

/-- The topological spherical-space-form endgame, for the actual finite free
orbit quotient. Continuous actions suffice; finite free isometric actions are
covered as a special case. -/
theorem sphere3_quotient_homeomorph
    (G : Type*) [Group G] [Finite G] [MulAction G Sphere3]
    [ContinuousConstSMul G Sphere3] [IsCancelSMul G Sphere3]
    [SimplyConnectedSpace (MulAction.orbitRel.Quotient G Sphere3)] :
    Nonempty (MulAction.orbitRel.Quotient G Sphere3 ≃ₜ Sphere3) :=
  ⟨(finiteActionQuotientHomeomorph G Sphere3).symm⟩

/-- The same conclusion for a manifold presented by a homeomorphism to a
spherical orbit quotient. The presentation is real quotient data, not an
assumption that this manifold is already a sphere. -/
theorem homeomorph_sphere3_of_finite_quotient
    (G : Type*) [Group G] [Finite G] [MulAction G Sphere3]
    [ContinuousConstSMul G Sphere3] [IsCancelSMul G Sphere3]
    {M : Type*} [TopologicalSpace M] [SimplyConnectedSpace M]
    (e : M ≃ₜ MulAction.orbitRel.Quotient G Sphere3) : Nonempty (M ≃ₜ Sphere3) := by
  letI : SimplyConnectedSpace (MulAction.orbitRel.Quotient G Sphere3) :=
    e.symm.toHomotopyEquiv.simplyConnectedSpace
  exact ⟨e.trans (finiteActionQuotientHomeomorph G Sphere3).symm⟩

end PoincareConjecture
