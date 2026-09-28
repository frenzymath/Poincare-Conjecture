import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Connected coverings of a simply connected base

The covering need not be presented by a faithful group action. This matters
for spherical quotient data packaged by an orthogonal representation that
may have a kernel. The proof uses path lifting and the actual monodromy of
the covering, so no freeness or group triviality is assumed.
-/

open Function Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

section Covering

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [PathConnectedSpace E] [SimplyConnectedSpace X]
  {p : E → X} (hp : IsCoveringMap p)

include hp

/-- A path-connected covering of a simply connected base is injective.
No local path-connectedness hypothesis is needed for this direction. -/
theorem covering_injective_of_simplyConnected : Injective p := by
  intro x y hxy
  let Γ : Path.Homotopic.Quotient x y := .mk (PathConnectedSpace.somePath x y)
  let ex : p ⁻¹' {p x} := ⟨x, rfl⟩
  let ey : p ⁻¹' {p x} := ⟨y, hxy.symm⟩
  have h := hp.monodromy_eq_of_map_eq (γ := .refl (p x))
    (ex := ex) (ey := ey) Γ (Subsingleton.elim _ _)
  rw [hp.monodromy_refl] at h
  exact congrArg Subtype.val h

/-- A surjective connected covering of a simply connected base is a
homeomorphism whose forward map is the supplied covering projection. -/
noncomputable def simplyConnectedCoverHomeomorph (hsurj : Surjective p) : E ≃ₜ X :=
  hp.isLocalHomeomorph.toHomeomorphOfBijective
    ⟨covering_injective_of_simplyConnected hp, hsurj⟩

@[simp] theorem simplyConnectedCoverHomeomorph_apply (hsurj : Surjective p) (e : E) :
    simplyConnectedCoverHomeomorph hp hsurj e = p e := rfl

end Covering

section Smooth

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W K}
  {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [ChartedSpace H E] [ChartedSpace K X]
  [CompactSpace E] [T2Space E] [T2Space X]
  [PathConnectedSpace E] [SimplyConnectedSpace X] {n : ℕ∞ω}
  {p : E → X}

/-- A surjective local diffeomorphism from a compact path-connected manifold
to a simply connected Hausdorff manifold is a global diffeomorphism. The
covering property follows from compactness, not from extra quotient axioms. -/
noncomputable def compactLocalDiffeomorphToSimplyConnected
    (hp : IsLocalDiffeomorph I J n p) (hsurj : Surjective p) : E ≃ₘ^n⟮I, J⟯ X :=
  hp.diffeomorphOfBijective
    ⟨covering_injective_of_simplyConnected
      (isLocalHomeomorph_iff_isCoveringMap.mp hp.isLocalHomeomorph), hsurj⟩

end Smooth

end PoincareConjecture
