import PoincareConjecture.Geometry.SmoothQuotient
import PoincareConjecture.Topology.FreeProduct
import PoincareConjecture.Topology.SimplyConnectedCover
import PoincareConjecture.Topology.SphereBundle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Regression examples for the quotient endgame

The main nontrivial example is the antipodal action on the actual standard
three-sphere. We check its action laws, freeness, smoothness, the quotient
manifold construction, and the obstruction to simple connectivity. We also
exercise the connected-covering theorem on the identity of the real line
and the free-product theorem with trivial and nontrivial factors.
-/

open Function Set PoincareConjecture
open scoped Manifold ContDiff

namespace PoincareConjectureTests

abbrev AntipodalGroup := Multiplicative (ZMod 2)

private theorem antipodalGroup_cases (g : AntipodalGroup) :
    g.toAdd = 0 ∨ g.toAdd = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h g.toAdd

noncomputable instance antipodalAction : MulAction AntipodalGroup Sphere3 where
  smul g x := if g.toAdd = 0 then x else -x
  one_smul x := by
    change (if (0 : ZMod 2) = 0 then x else -x) = x
    simp only [if_true]
  mul_smul g h x := by
    change (if (g * h).toAdd = 0 then x else -x) =
      (if g.toAdd = 0 then (if h.toAdd = 0 then x else -x)
        else -(if h.toAdd = 0 then x else -x))
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases antipodalGroup_cases g with hg | hg <;>
      rcases antipodalGroup_cases h with hh | hh <;>
      simp [toAdd_mul, hg, hh, h11]

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

theorem antipodalAction_smooth (g : AntipodalGroup) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : Sphere3 => g • x) := by
  change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : Sphere3 => if g.toAdd = 0 then x else -x)
  by_cases hg : g.toAdd = 0
  · simp only [hg, if_true]
    exact contMDiff_id
  · simp only [hg, if_false]
    exact contMDiff_neg_sphere

noncomputable instance antipodalAction_continuous : ContinuousConstSMul AntipodalGroup Sphere3 :=
  ⟨fun g => (antipodalAction_smooth g).continuous⟩

noncomputable instance antipodalAction_free : IsCancelSMul AntipodalGroup Sphere3 := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  change (if g.toAdd = 0 then x else -x) = x at hx
  by_cases hg : g.toAdd = 0
  · exact Multiplicative.toAdd.injective (by simpa using hg)
  · simp only [hg, if_false] at hx
    exact False.elim ((ne_neg_of_mem_unit_sphere ℝ x) hx.symm)

/-- The new atlas theorem works on the genuine nontrivial antipodal quotient,
not only on a quotient with a trivial acting group. -/
theorem antipodalQuotient_isManifold :
    IsManifold (𝓡 3) ∞ (MulAction.orbitRel.Quotient AntipodalGroup Sphere3) :=
  finiteSmoothAction_isManifold AntipodalGroup antipodalAction_smooth

/-- Its actual projection is a local diffeomorphism. -/
theorem antipodalQuotient_projection_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Quotient.mk (MulAction.orbitRel AntipodalGroup Sphere3)) :=
  finiteSmoothAction_isLocalDiffeomorph AntipodalGroup antipodalAction_smooth

/-- Simple connectivity cannot be dropped: the antipodal quotient fails it.
The proof uses the new monodromy result and the two distinct group elements. -/
theorem antipodalQuotient_not_simplyConnected :
    ¬ SimplyConnectedSpace (MulAction.orbitRel.Quotient AntipodalGroup Sphere3) := by
  intro h
  letI := h
  have hG := finiteAction_group_subsingleton AntipodalGroup Sphere3
  have h01 := congrArg Multiplicative.toAdd
    (hG.elim (Multiplicative.ofAdd (0 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 2)))
  exact zero_ne_one h01

/-- A nonempty instance of the connected-covering theorem with its actual
covering map. This has no assumptions from the theorem being tested. -/
theorem real_identity_cover_injective : Injective (id : ℝ → ℝ) := by
  apply covering_injective_of_simplyConnected
  intro x
  have hc : IsClosedMap (id : ℝ → ℝ) := (Homeomorph.refl ℝ).isClosedMap
  apply hc.isEvenlyCovered_of_openPartialHomeomorph
    (by simpa only [preimage_id] using finite_singleton x)
  intro e _
  exact ⟨(Homeomorph.refl ℝ).toOpenPartialHomeomorph, mem_univ _, rfl⟩

/-- The free product of a finite family of trivial groups is trivial. -/
theorem trivial_freeProduct : Subsingleton (Monoid.CoprodI (fun _ : Fin 3 => Unit)) :=
  freeProduct_subsingleton (fun _ : Fin 3 => Unit)

/-- An infinite cyclic factor prevents a free product from being trivial. -/
theorem integer_freeProduct_not_subsingleton :
    ¬ Subsingleton (Monoid.CoprodI (fun _ : Fin 1 => Multiplicative ℤ)) := by
  intro h
  letI := h
  have hi := freeProduct_no_infiniteCyclic_factor (fun _ : Fin 1 => Multiplicative ℤ) 0
  exact hi.false (MulEquiv.refl (Multiplicative ℤ))

/-- Freeness is essential for group-triviality: a nontrivial group can act
trivially on a point, whose quotient is a point and hence simply connected. -/
theorem freeness_cannot_be_omitted :
    ∃ action : MulAction AntipodalGroup Unit,
      letI := action
      SimplyConnectedSpace (MulAction.orbitRel.Quotient AntipodalGroup Unit) ∧
        ¬ Subsingleton AntipodalGroup := by
  let action : MulAction AntipodalGroup Unit := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
  }
  refine ⟨action, ?_⟩
  letI := action
  refine ⟨inferInstance, ?_⟩
  intro h
  have h01 := congrArg Multiplicative.toAdd
    (h.elim (Multiplicative.ofAdd (0 : ZMod 2)) (Multiplicative.ofAdd (1 : ZMod 2)))
  exact zero_ne_one h01

/-- An explicit point on the actual two-sphere for nonempty bundle tests. -/
noncomputable def sphere2Basepoint : Sphere2 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The identity mapping torus identifies points separated by exactly one
period in its real-coordinate cover. This tests the orbit quotient itself. -/
theorem sphereMappingTorus_period :
    (Quotient.mk (MulAction.orbitRel (Multiplicative ℤ)
      (MappingTorusCover (Homeomorph.refl Sphere2))) (sphere2Basepoint, (0 : ℝ))) =
    Quotient.mk (MulAction.orbitRel (Multiplicative ℤ)
      (MappingTorusCover (Homeomorph.refl Sphere2))) (sphere2Basepoint, (1 : ℝ)) := by
  apply Quotient.sound
  let z : MappingTorusCover (Homeomorph.refl Sphere2) := (sphere2Basepoint, 0)
  let w : MappingTorusCover (Homeomorph.refl Sphere2) := (sphere2Basepoint, 1)
  change ∃ g : Multiplicative ℤ, g • w = z
  refine ⟨Multiplicative.ofAdd (-1), ?_⟩
  change (((Homeomorph.refl Sphere2) ^ (-1 : ℤ)) sphere2Basepoint, 1 + ((-1 : ℤ) : ℝ)) = _
  change (((1 : Sphere2 ≃ₜ Sphere2) ^ (-1 : ℤ)) sphere2Basepoint, 1 + ((-1 : ℤ) : ℝ)) = _
  simp only [one_zpow, Homeomorph.one_apply, Int.cast_neg, Int.cast_one, add_neg_cancel]
  rfl

/-- The full product fundamental-group equivalence has an actual input,
and its inverse sends the generator back correctly. -/
theorem sphereProduct_generator_roundtrip :
    let e := sphere2CircleFundamentalGroupEquiv (sphere2Basepoint, (1 : Circle))
    e (e.symm (Multiplicative.ofAdd (1 : ℤ))) = Multiplicative.ofAdd (1 : ℤ) := by
  exact (sphere2CircleFundamentalGroupEquiv (sphere2Basepoint, (1 : Circle))).apply_symm_apply _

/-- The antipodal mapping torus is nonempty and its fundamental group
contains distinct elements. This tests the twisted monodromy model rather
than assuming a cyclic group description. -/
theorem twistedSphere_fundamentalGroup_nontrivial :
    ∃ q : TwistedSphereMappingTorus, Nontrivial (FundamentalGroup TwistedSphereMappingTorus q) := by
  let q : TwistedSphereMappingTorus := Quotient.mk
    (MulAction.orbitRel (Multiplicative ℤ) (MappingTorusCover sphere2Antipodal))
      (sphere2Basepoint, 0)
  refine ⟨q, ?_⟩
  exact (twistedSphereFundamentalGroupEquiv q).surjective.nontrivial

end PoincareConjectureTests
