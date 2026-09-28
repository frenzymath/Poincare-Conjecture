import HatcherLib.Ch1.BasicConstructions

/-!
# Chapter 1: based homotopies

The chapter distinguishes ordinary homotopies from homotopies that preserve a
chosen basepoint.  `ContinuousMap.HomotopyRel` is exactly the corresponding
mathlib notion; the structures below expose it in chapter-local terminology.
-/

namespace HatcherLib

noncomputable section

open scoped ContinuousMap

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ : X} {y₀ : Y}

/-- A homotopy of maps of pairs: throughout the homotopy, the source
subspace is carried into the target subspace. -/
def PairHomotopy (A : Set X) (B : Set Y) (f g : C(X, Y)) :=
  { H : ContinuousMap.Homotopy f g //
    ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B }

/-- A homotopy of maps that fixes the chosen basepoint. -/
abbrev BasedHomotopy (x₀ : X) (f g : C(X, Y)) :=
  ContinuousMap.HomotopyRel f g {x₀}

/-- A homotopy equivalence that preserves specified basepoints in both directions. -/
structure BasedHomotopyEquiv (x₀ : X) (y₀ : Y) where
  toFun : C(X, Y)
  invFun : C(Y, X)
  map_base : toFun x₀ = y₀
  inv_base : invFun y₀ = x₀
  left_inv : Nonempty (BasedHomotopy x₀ (invFun.comp toFun) (ContinuousMap.id X))
  right_inv : Nonempty (BasedHomotopy y₀ (toFun.comp invFun) (ContinuousMap.id Y))

/-- A parser-visible name for the type of based homotopy equivalences. -/
def basedHomotopyEquivType (x₀ : X) (y₀ : Y) := BasedHomotopyEquiv x₀ y₀

namespace BasedHomotopyEquiv

/-- Forgetting basepoints gives an ordinary homotopy equivalence. -/
def toHomotopyEquiv (e : BasedHomotopyEquiv x₀ y₀) : X ≃ₕ Y where
  toFun := e.toFun
  invFun := e.invFun
  left_inv := e.left_inv.map (fun h => h.toHomotopy)
  right_inv := e.right_inv.map (fun h => h.toHomotopy)

/-- The inverse of a based homotopy equivalence. -/
def symm (e : BasedHomotopyEquiv x₀ y₀) : BasedHomotopyEquiv y₀ x₀ where
  toFun := e.invFun
  invFun := e.toFun
  map_base := e.inv_base
  inv_base := e.map_base
  left_inv := e.right_inv
  right_inv := e.left_inv

end BasedHomotopyEquiv

end
end HatcherLib
