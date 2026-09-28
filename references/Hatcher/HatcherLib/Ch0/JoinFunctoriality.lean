import HatcherLib.Ch0.SpaceOperations

/-!
# Chapter 0 — Functoriality of joins

The quotient presentation of the join makes its functoriality explicit.  A
pair of continuous maps `f : X → X'` and `g : Y → Y'` induces a continuous map
`X * Y → X' * Y'`; the endpoint identifications are preserved automatically.
This file records the generator formula and the identity/composition laws.
-/

namespace HatcherLib

open scoped unitInterval

universe u v u' v' u'' v''

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- A pair of maps induces a map of joins. -/
def joinMap (f : C(X, X')) (g : C(Y, Y')) : C(Join X Y, Join X' Y') := by
  let F : C(X × Y × I, Join X' Y') :=
    ⟨fun p => joinMk (f p.1, g p.2.1, p.2.2), by fun_prop⟩
  have hwd : ∀ a b : X × Y × I, (joinSetoid (X := X) (Y := Y)).r a b → F a = F b := by
    rintro a b (rfl | ⟨hx, ha, hb⟩ | ⟨hy, ha, hb⟩)
    · rfl
    · dsimp [F, joinMk]
      apply Quotient.sound
      exact Or.inr (Or.inl ⟨congrArg f hx, ha, hb⟩)
    · dsimp [F, joinMk]
      apply Quotient.sound
      exact Or.inr (Or.inr ⟨congrArg g hy, ha, hb⟩)
  exact ⟨Quotient.lift F hwd, (map_continuous F).quotient_lift hwd⟩

@[simp] theorem joinMap_joinMk (f : C(X, X')) (g : C(Y, Y'))
    (x : X) (y : Y) (t : I) :
    joinMap f g (joinMk (x, y, t)) = joinMk (f x, g y, t) := by
  unfold joinMap
  dsimp [joinMk]

@[simp] theorem joinMap_id :
    joinMap (ContinuousMap.id X) (ContinuousMap.id Y) = ContinuousMap.id (Join X Y) := by
  ext z
  induction z using Quotient.ind with
  | _ p =>
    cases p with
    | mk x yi =>
      cases yi with
      | mk y t =>
        change joinMap (ContinuousMap.id X) (ContinuousMap.id Y) (joinMk (x, y, t)) =
          joinMk (x, y, t)
        rw [joinMap_joinMk]
        rfl

theorem joinMap_comp {X'' : Type u''} {Y'' : Type v''}
    [TopologicalSpace X''] [TopologicalSpace Y'']
    (f : C(X, X')) (g : C(Y, Y'))
    (f' : C(X', X'')) (g' : C(Y', Y'')) :
    joinMap (f'.comp f) (g'.comp g) =
      (joinMap f' g').comp (joinMap f g) := by
  ext z
  induction z using Quotient.ind with
  | _ p =>
    cases p with
    | mk x yi =>
      cases yi with
      | mk y t =>
        change joinMap (f'.comp f) (g'.comp g) (joinMk (x, y, t)) =
          joinMap f' g' (joinMap f g (joinMk (x, y, t)))
        rw [joinMap_joinMk, joinMap_joinMk, joinMap_joinMk]
        rfl

end HatcherLib
