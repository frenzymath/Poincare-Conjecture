import PetersenLib.Ch05.ExponentialMap

/-!
# Petersen Ch. 5, §5.6 — fixed-point sets and totally geodesic submanifolds

* `fixedPointSet S` (`def:pet-ch5-fixed-point-set`) — the common fixed-point set
  `Fix(S) = {x ∈ M | F x = x for all F ∈ S}` of a family `S` of self-maps
  (isometries) of `M`.
* `IsTotallyGeodesic g N TN` (`def:pet-ch5-fixed-point-set`) — a submanifold
  `N ⊂ M`, carried by its tangent distribution `TN p ⊂ T_pM`, is **totally
  geodesic** if for each `p ∈ N` a neighbourhood of `0` in `T_pN` is mapped into
  `N` by `exp_p`: every `M`-geodesic tangent to `N` stays in `N` for a short
  time.  This is the property Prop. 5.6.5 establishes for each component of a
  fixed-point set `Fix(S)`.

Reference: Petersen, *Riemannian Geometry*, 3rd ed., §5.6 (Prop. 5.6.5).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Fixed-point sets -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-fixed-point-set`): the **fixed-point
set** `Fix(S) = {x ∈ M | F x = x for all F ∈ S}` of a set `S` of self-maps
(isometries) of `M`. -/
def fixedPointSet (S : Set (M → M)) : Set M := {x : M | ∀ F ∈ S, F x = x}

@[simp] theorem mem_fixedPointSet {S : Set (M → M)} {x : M} :
    x ∈ fixedPointSet S ↔ ∀ F ∈ S, F x = x := Iff.rfl

/-- **Math.** The fixed-point set of a family is the intersection of the
individual fixed-point sets: `Fix(S) = ⋂_{F ∈ S} {x | F x = x}`. -/
theorem fixedPointSet_eq_iInter (S : Set (M → M)) :
    fixedPointSet S = ⋂ F ∈ S, {x : M | F x = x} := by
  ext x; simp [fixedPointSet]

/-- **Math.** In a Hausdorff space the **fixed-point set of a family of
continuous maps is closed** — the intersection over `F ∈ S` of the closed
equalizers `{x | F x = x}`.  This is the first step of Prop. 5.6.5: each
connected component of `Fix(S)` is then a totally geodesic submanifold. -/
theorem isClosed_fixedPointSet [T2Space M] {S : Set (M → M)}
    (hS : ∀ F ∈ S, Continuous F) : IsClosed (fixedPointSet S) := by
  rw [fixedPointSet_eq_iInter]
  exact isClosed_iInter fun F => isClosed_iInter fun hF =>
    isClosed_eq (hS F hF) continuous_id

/-! ## Totally geodesic submanifolds -/

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-fixed-point-set`): a submanifold
`N ⊂ M`, presented together with its tangent distribution `TN : ∀ p, Submodule ℝ
(T_pM)` (so `TN p = T_pN` for `p ∈ N`), is **totally geodesic** if for each
`p ∈ N` a neighbourhood of `0` in `T_pN` — i.e. eventually along the subspace
`TN p` as `v → 0` — is mapped into `N` by `exp_p`.  Equivalently, `M`-geodesics
tangent to `N` remain in `N` for a short time. -/
def IsTotallyGeodesic (g : RiemannianMetric I M) (N : Set M)
    (TN : ∀ p : M, Submodule ℝ (TangentSpace I p)) : Prop :=
  ∀ p ∈ N, ∀ᶠ v in 𝓝[(TN p : Set (TangentSpace I p))] (0 : TangentSpace I p),
    expMap (I := I) g p v ∈ N

end PetersenLib

end
