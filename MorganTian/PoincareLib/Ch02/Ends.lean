import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Constructions
import Mathlib.Data.Set.Inclusion
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.BooleanAlgebra.Set

/-!
# Poincaré Ch. 2, §2.4 — The space of ends

The **space of ends** of a topological space `X` (Morgan–Tian, *Ricci Flow and the
Poincaré Conjecture*, §2.4, `def:space-of-ends`), formalized as the inverse limit of the
inverse system `K ↦ π₀(X \ K)` indexed by compact subsets `K ⊆ X`, directed by inclusion,
with structure maps `endsTransition` induced by the inclusions `X \ K' ⊆ X \ K` for `K ⊆ K'`
(sending a connected component of the smaller complement to the connected component of the
larger complement containing it).

## Main declarations

* `endsTransition`: the structure map `π₀(X \ K') → π₀(X \ K)` of the inverse system, for
  `K ≤ K'` in `TopologicalSpace.Compacts X`.
* `SpaceOfEnds`: the space of ends of `X`, i.e. the inverse limit of the system above.

## Design notes

* The blueprint states the inverse system for a manifold `M`, indexed by compact
  *codimension-0 submanifolds* `K ⊂ M`. The standard topological definition, indexing
  instead over **all** compact subsets `K : TopologicalSpace.Compacts X`, is equivalent by
  cofinality (every compact set lies in a compact codimension-0 submanifold, blueprint
  `lem:compact-set-in-codim-zero-submanifold`) and is the one formalized here, since it
  makes sense for an arbitrary topological space, not just for manifolds.
* `π₀(X \ K)` is represented by `ConnectedComponents ((K : Set X)ᶜ)`, the quotient of the
  subtype `(K : Set X)ᶜ` by its connected components.
* `endsTransition` is built from the continuous inclusion map
  `Set.inclusion : (K' : Set X)ᶜ → (K : Set X)ᶜ` (valid since `K ⊆ K'` gives
  `(K' : Set X)ᶜ ⊆ (K : Set X)ᶜ`) via the functoriality of `ConnectedComponents`,
  `Continuous.connectedComponentsMap`.
* `SpaceOfEnds X` is cut out, inside the product `Π K, ConnectedComponents ((K : Set X)ᶜ)`,
  by the compatibility conditions of an inverse limit; its topology is the one induced from
  the product (subspace) topology.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4.
-/

open TopologicalSpace (Compacts)

namespace PoincareLib

variable {X : Type*} [TopologicalSpace X]

/-! ## The structure maps of the inverse system -/

/-- If `K ≤ K'` then `X \ K'` is contained in `X \ K`; this is the inclusion inducing the
structure map `endsTransition` of the inverse system defining the space of ends. -/
theorem compl_subset_compl_of_le {K K' : Compacts X} (h : K ≤ K') :
    (K' : Set X)ᶜ ⊆ (K : Set X)ᶜ :=
  Set.compl_subset_compl_of_subset (SetLike.coe_subset_coe.mpr h)

/-- For compacts `K ≤ K'`, the map `π₀(X \ K') → π₀(X \ K)` induced by inclusion: it sends the
connected component of a point of `X \ K'` to the connected component (in the possibly larger
set `X \ K`) of the same point. This is the structure map of the inverse system
`K ↦ π₀(X \ K)` whose inverse limit is the space of ends (blueprint `def:space-of-ends`). -/
def endsTransition {K K' : Compacts X} (h : K ≤ K') :
    ConnectedComponents ((K' : Set X)ᶜ : Set X) → ConnectedComponents ((K : Set X)ᶜ : Set X) :=
  (continuous_inclusion (compl_subset_compl_of_le h)).connectedComponentsMap

/-- The transition map sends the class of a point `x ∈ X \ K'` to the class of the same point,
viewed in `X \ K`. -/
@[simp]
theorem endsTransition_mk {K K' : Compacts X} (h : K ≤ K') (x : ((K' : Set X)ᶜ : Set X)) :
    endsTransition h (ConnectedComponents.mk x) =
      ConnectedComponents.mk (Set.inclusion (compl_subset_compl_of_le h) x) :=
  rfl

/-- Each structure map of the inverse system is continuous. -/
@[continuity]
theorem continuous_endsTransition {K K' : Compacts X} (h : K ≤ K') :
    Continuous (endsTransition h) :=
  (continuous_inclusion (compl_subset_compl_of_le h)).connectedComponentsMap_continuous

/-- The structure map for `K ≤ K` (with equal indices) is the identity. -/
@[simp]
theorem endsTransition_refl (K : Compacts X) :
    endsTransition (le_refl K) = id := by
  funext e
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe e
  rfl

/-- The structure maps compose according to the order on `Compacts X`, i.e. they form a genuine
inverse system: transitioning from `K''` to `K'` and then to `K` agrees with transitioning
directly from `K''` to `K`. -/
theorem endsTransition_trans {K K' K'' : Compacts X} (h : K ≤ K') (h' : K' ≤ K'')
    (e : ConnectedComponents ((K'' : Set X)ᶜ : Set X)) :
    endsTransition h (endsTransition h' e) = endsTransition (h.trans h') e := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe e
  rfl

/-! ## The space of ends -/

/-- The **space of ends** of `X`: the inverse limit of `π₀(X \ K)` over compact `K ⊆ X`
(Morgan–Tian §2.4, `def:space-of-ends`, specialized from compact codimension-0 submanifolds of
a manifold to all compact subsets of a general topological space, an equivalent indexing by
cofinality). A point of `SpaceOfEnds X` is a choice, for every compact `K`, of a connected
component of `X \ K`, compatible with the structure maps `endsTransition`. -/
def SpaceOfEnds (X : Type*) [TopologicalSpace X] : Type _ :=
  { e : (K : Compacts X) → ConnectedComponents ((K : Set X)ᶜ : Set X) //
    ∀ ⦃K K' : Compacts X⦄ (h : K ≤ K'), endsTransition h (e K') = e K }

/-- `SpaceOfEnds X` carries the subspace topology induced from the product topology on
`Π K, ConnectedComponents (X \ K)`. -/
instance : TopologicalSpace (SpaceOfEnds X) :=
  inferInstanceAs (TopologicalSpace
    { e : (K : Compacts X) → ConnectedComponents ((K : Set X)ᶜ : Set X) //
      ∀ ⦃K K' : Compacts X⦄ (h : K ≤ K'), endsTransition h (e K') = e K })

end PoincareLib
