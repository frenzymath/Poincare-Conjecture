import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Busemann sublevel sets

This module records the set-theoretic definitions used in Chow--Knopf,
Appendix B.6.
-/

open Set

set_option autoImplicit false

namespace ChowKnopf

/-- **Math.** A metric ray is an isometric path with nonnegative time parameter.
This encodes that every segment is unit-speed and minimizing. -/
structure Ray (M : Type*) [PseudoMetricSpace M] where
  toFun : NNReal → M
  isometry_toFun : Isometry toFun

instance {M : Type*} [PseudoMetricSpace M] : CoeFun (Ray M) (fun _ ↦ NNReal → M) :=
  ⟨Ray.toFun⟩

/-- **Math.** If `γ` is a ray and `s ≥ 0`, its shift is
`γₛ(s') = γ(s + s')`. -/
def shiftedRay {M : Type*} [PseudoMetricSpace M] (γ : Ray M) (s : NNReal) : Ray M where
  toFun := fun s' ↦ γ (s + s')
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro x y
    rw [γ.isometry_toFun.dist_eq]
    simp only [NNReal.dist_eq, NNReal.coe_add]
    congr 1
    ring

@[simp]
theorem shiftedRay_apply {M : Type*} [PseudoMetricSpace M]
    (γ : Ray M) (s s' : NNReal) :
    shiftedRay γ s s' = γ (s + s') := rfl

/-- **Math.** The rays emanating from `O`. -/
def raysFrom {M : Type*} [PseudoMetricSpace M] (O : M) : Set (Ray M) :=
  {γ | γ 0 = O}

/-- **Math.** The closed left half space of a ray, equivalently the complement
of the union of the open balls `B(γ(t), t)` for `t > 0`. -/
def busemannHalfSpace {M : Type*} [PseudoMetricSpace M] (γ : Ray M) : Set M :=
  {x | ∀ t : NNReal, 0 < t → (t : ℝ) ≤ dist x (γ t)}

/-- **Math.** The Busemann sublevel set at height `s` is the intersection of
the half spaces associated to all rays from the origin, shifted by `s`. -/
def busemannSublevelSet {M : Type*} [PseudoMetricSpace M]
    (O : M) (s : NNReal) : Set M :=
  ⋂ γ ∈ raysFrom O, busemannHalfSpace (shiftedRay γ s)

/-- Membership in a Busemann sublevel set is membership in every shifted-ray
half space. -/
theorem mem_busemannSublevelSet_iff {M : Type*} [PseudoMetricSpace M]
    (O x : M) (s : NNReal) :
    x ∈ busemannSublevelSet O s ↔
      ∀ γ : Ray M, γ 0 = O →
        ∀ t : NNReal, 0 < t → (t : ℝ) ≤ dist x (γ (s + t)) := by
  simp [busemannSublevelSet, raysFrom, busemannHalfSpace]

end ChowKnopf
