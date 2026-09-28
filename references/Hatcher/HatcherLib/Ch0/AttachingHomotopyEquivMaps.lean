import HatcherLib.Ch0.AttachingHomotopyEquiv

/-!
# Homotopic attaching maps in map form

The cylinder proof in `AttachingHomotopyEquiv` is naturally phrased using one
map `F : A × I → X₀`.  Hatcher's propositions quantify instead over two maps
`f,g : A → X₀` together with a homotopy.  This file supplies that small
interface bridge, without adding any hypotheses beyond the HEP used by the
cylinder theorem.
-/

namespace HatcherLib

open scoped unitInterval
open ContinuousMap

universe u

variable {X₀ X₁ : Type u} [TopologicalSpace X₀] [TopologicalSpace X₁]

variable {A : Set X₁}

/-- The HEP-form attaching-space equivalence for two explicitly given homotopic
maps.  The homotopy is reparameterized from mathlib's `I × A` convention to the
`A × I` convention used by `attachEval`.
-/
theorem attachingSpace_homotopyEquiv_rel_of_homotopic
    (hA : IsClosed A) (hHEP : HasHEP.{u, u} A)
    {f g : C(↥A, X₀)} (hfg : f.Homotopic g) :
    ∃ (φ : C(AttachingSpace A f, AttachingSpace A g))
      (ψ : C(AttachingSpace A g, AttachingSpace A f)),
      (∀ x₀ : X₀, φ (attachInclBase A f x₀) = attachInclBase A g x₀) ∧
      (∀ x₀ : X₀, ψ (attachInclBase A g x₀) = attachInclBase A f x₀) ∧
      Nonempty ((ψ.comp φ).HomotopyRel (ContinuousMap.id _)
        (Set.range (attachInclBase A f))) ∧
      Nonempty ((φ.comp ψ).HomotopyRel (ContinuousMap.id _)
        (Set.range (attachInclBase A g))) := by
  obtain ⟨H⟩ := hfg
  let F : C(↥A × I, X₀) :=
    ⟨fun p => H (p.2, p.1),
      (map_continuous H).comp (continuous_snd.prodMk continuous_fst)⟩
  have hF0 : attachEval F 0 = f := by
    ext a
    exact H.map_zero_left a
  have hF1 : attachEval F 1 = g := by
    ext a
    exact H.map_one_left a
  rw [← hF0, ← hF1]
  exact attachingSpace_homotopyEquiv_rel hA hHEP F

/-- The non-relative form of
`attachingSpace_homotopyEquiv_rel_of_homotopic`. -/
theorem attachingSpace_homotopyEquiv_of_homotopic
    (hA : IsClosed A) (hHEP : HasHEP.{u, u} A)
    {f g : C(↥A, X₀)} (hfg : f.Homotopic g) :
    Nonempty (ContinuousMap.HomotopyEquiv (AttachingSpace A f)
      (AttachingSpace A g)) := by
  obtain ⟨φ, ψ, -, -, ⟨Hψφ⟩, ⟨Hφψ⟩⟩ :=
    attachingSpace_homotopyEquiv_rel_of_homotopic hA hHEP hfg
  exact ⟨{ toFun := φ
           invFun := ψ
           left_inv := ⟨Hψφ.toHomotopy⟩
           right_inv := ⟨Hφψ.toHomotopy⟩ }⟩

end HatcherLib
