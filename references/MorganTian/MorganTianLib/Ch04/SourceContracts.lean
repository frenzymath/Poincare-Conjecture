import MorganTianLib.Ch04.ConvexInvariant
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Morgan--Tian Ch. 4 - source-facing convex-set contracts

The intrinsic tangent-cone predicate in `ConvexInvariant` is deliberately
independent of regularity and carrier hypotheses.  The source definition
bundles those hypotheses with a field defined and smooth on an open
neighborhood.  This file records that packaging explicitly.  For a dependent
fiber family we use an explicit `Sigma` carrier proxy: its topology is the
ordinary sigma/disjoint-union topology, not the total-space topology of a
genuine glued vector bundle.  The missing bundle-topology bridge is therefore
kept visible rather than being inferred from this interface.

These are contract-level definitions.  They do not manufacture a smooth
Levi--Civita trivialization or a parabolic contact identity.
-/

open Set
open scoped Topology ContDiff NNReal

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## A smooth field near a closed convex carrier -/

/-- Hamilton's source-level preservation contract for a finite-dimensional
carrier.  The function is represented on the ambient vector space, while its
smoothness is required only on the specified open neighborhood of the carrier.
The final conjunct is the intrinsic tangent-cone condition from
`vectorFieldPreservesConvexSet`.
-/
def vectorFieldPreservesConvexSetOn
    (Z U : Set V) (ψ : V → V) : Prop :=
  IsClosed Z ∧ Convex ℝ Z ∧ IsOpen U ∧ Z ⊆ U ∧
    ContDiffOn ℝ ∞ ψ U ∧ vectorFieldPreservesConvexSet Z ψ

theorem vectorFieldPreservesConvexSetOn.closed
    {Z U : Set V} {ψ : V → V}
    (h : vectorFieldPreservesConvexSetOn Z U ψ) : IsClosed Z :=
  h.1

theorem vectorFieldPreservesConvexSetOn.convex
    {Z U : Set V} {ψ : V → V}
    (h : vectorFieldPreservesConvexSetOn Z U ψ) : Convex ℝ Z :=
  h.2.1

theorem vectorFieldPreservesConvexSetOn.open_neighborhood
    {Z U : Set V} {ψ : V → V}
    (h : vectorFieldPreservesConvexSetOn Z U ψ) : IsOpen U :=
  h.2.2.1

theorem vectorFieldPreservesConvexSetOn.carrier_subset
    {Z U : Set V} {ψ : V → V}
    (h : vectorFieldPreservesConvexSetOn Z U ψ) : Z ⊆ U :=
  h.2.2.2.1

theorem vectorFieldPreservesConvexSetOn.smooth
    {Z U : Set V} {ψ : V → V}
    (h : vectorFieldPreservesConvexSetOn Z U ψ) : ContDiffOn ℝ ∞ ψ U :=
  h.2.2.2.2.1

theorem vectorFieldPreservesConvexSetOn.tangent
    {Z U : Set V} {ψ : V → V}
    (h : vectorFieldPreservesConvexSetOn Z U ψ) :
    vectorFieldPreservesConvexSet Z ψ :=
  h.2.2.2.2.2

/-- Smoothness on the source neighborhood supplies the local Lipschitz input
needed by the ODE barrier on every compact convex range contained in that
neighborhood.  The statement is deliberately local; it does not turn a
nearby smooth field into a globally Lipschitz field. -/
theorem vectorFieldPreservesConvexSetOn.exists_lipschitzOnWith
    {Z U : Set V} {ψ : V → V}
    (h : vectorFieldPreservesConvexSetOn Z U ψ)
    {K : Set V} (hKsub : K ⊆ U) (hKconv : Convex ℝ K)
    (hKcompact : IsCompact K) :
    ∃ C : ℝ≥0, LipschitzOnWith C ψ K := by
  exact (h.smooth.mono hKsub).exists_lipschitzOnWith
    (by simp) hKconv hKcompact

/-! ## Total-space carriers for dependent fibers -/

variable {M : Type*} {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]

/-- The total-space realization of a dependent fiber family. -/
def totalFiberSet (Z : FiberSet M F) : Set (Sigma F) :=
  {p | p.2 ∈ Z p.1}

omit [(x : M) → NormedAddCommGroup (F x)] [(x : M) → NormedSpace ℝ (F x)] in
@[simp] theorem mem_totalFiberSet_iff
    (Z : FiberSet M F) (p : Sigma F) :
    p ∈ totalFiberSet Z ↔ p.2 ∈ Z p.1 :=
  Iff.rfl

/-- A closed/convex dependent-fiber carrier proxy.

`totalFiberSet Z` lives in the ordinary sigma topology.  Thus this predicate
records closedness of the chosen proxy and fiberwise convexity, but does not
claim closedness in the total-space topology of an actual vector bundle.  A
geometric Ch. 4 producer must supply that bundle-topology compatibility. -/
def closedConvexSubbundle (Z : FiberSet M F) : Prop :=
  IsClosed (totalFiberSet Z) ∧ fiberwiseConvex Z

theorem closedConvexSubbundle.closed
    {Z : FiberSet M F} (hZ : closedConvexSubbundle Z) :
    IsClosed (totalFiberSet Z) :=
  hZ.1

theorem closedConvexSubbundle.convex
    {Z : FiberSet M F} (hZ : closedConvexSubbundle Z) :
    fiberwiseConvex Z :=
  hZ.2

/-- A total-space neighborhood of a fiber family. -/
def totalFiberNeighborhood (Z U : FiberSet M F) : Prop :=
  IsOpen (totalFiberSet U) ∧ totalFiberSet Z ⊆ totalFiberSet U

omit [(x : M) → NormedSpace ℝ (F x)] in
theorem totalFiberNeighborhood.open
    {Z U : FiberSet M F} (hU : totalFiberNeighborhood Z U) :
    IsOpen (totalFiberSet U) :=
  hU.1

omit [(x : M) → NormedSpace ℝ (F x)] in
theorem totalFiberNeighborhood.carrier_subset
    {Z U : FiberSet M F} (hU : totalFiberNeighborhood Z U) :
    totalFiberSet Z ⊆ totalFiberSet U :=
  hU.2

/-- Fiberwise smoothness of an ambient field on the chosen neighborhood.
Regularity in the base variable is kept explicit elsewhere, because the
abstract dependent-fiber interface does not choose a bundle trivialization. -/
def fiberwiseContDiffOn
    (U : FiberSet M F) (ψ : FiberwiseVectorField F) : Prop :=
  ∀ x, ContDiffOn ℝ ∞ (ψ x) (U x)

/-- Source-level fiberwise preservation contract: an open total-space
neighborhood, fiberwise smoothness there, and the tangent-cone condition in
each carrier fiber. -/
def convexSubbundlePreservingVectorFieldOn
    (Z U : FiberSet M F) (ψ : FiberwiseVectorField F) : Prop :=
  totalFiberNeighborhood Z U ∧ fiberwiseContDiffOn U ψ ∧
    convexSubbundlePreservingVectorField Z ψ

theorem convexSubbundlePreservingVectorFieldOn.neighborhood
    {Z U : FiberSet M F} {ψ : FiberwiseVectorField F}
    (h : convexSubbundlePreservingVectorFieldOn Z U ψ) :
    totalFiberNeighborhood Z U :=
  h.1

theorem convexSubbundlePreservingVectorFieldOn.smooth
    {Z U : FiberSet M F} {ψ : FiberwiseVectorField F}
    (h : convexSubbundlePreservingVectorFieldOn Z U ψ) :
    fiberwiseContDiffOn U ψ :=
  h.2.1

theorem convexSubbundlePreservingVectorFieldOn.tangent
    {Z U : FiberSet M F} {ψ : FiberwiseVectorField F}
    (h : convexSubbundlePreservingVectorFieldOn Z U ψ) :
    convexSubbundlePreservingVectorField Z ψ :=
  h.2.2

/-- The complete source carrier package, with a declared transport family.
The transport family is an explicit input so this contract can later be
instantiated by Levi--Civita parallel transport without pretending that an
arbitrary linear equivalence is geometric. -/
def closedConvexParallelInvariantSubbundle
    (Z : FiberSet M F) (P : LinearTransportFamily F) : Prop :=
  closedConvexSubbundle Z ∧ parallelInvariantFiberSet Z P

theorem closedConvexParallelInvariantSubbundle.carrier
    {Z : FiberSet M F} {P : LinearTransportFamily F}
    (hZ : closedConvexParallelInvariantSubbundle Z P) :
    closedConvexSubbundle Z :=
  hZ.1

theorem closedConvexParallelInvariantSubbundle.parallel
    {Z : FiberSet M F} {P : LinearTransportFamily F}
    (hZ : closedConvexParallelInvariantSubbundle Z P) :
    parallelInvariantFiberSet Z P :=
  hZ.2

end MorganTianLib
