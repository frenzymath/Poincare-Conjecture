import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Chapter 0 - Characteristic maps as quotient maps

A CW characteristic map restricted to its closed model ball is a continuous
surjection onto the closed cell.  Since the model ball is compact and the
ambient CW space is Hausdorff, this restriction is a quotient map.  This is the
local point-set input for presenting a skeleton as an adjunction-space quotient.
-/

namespace HatcherLib

open Metric Set

universe u

open Topology

variable {X : Type u} [TopologicalSpace X]
  {C D : Set X} [RelCWComplex C D]

/-- The characteristic map of a cell, restricted and corestricted from the
closed model ball onto the closed cell. -/
noncomputable def closedCellCharacteristic (n : ℕ) (i : RelCWComplex.cell C n) :
    C(↑(closedBall (0 : Fin n → ℝ) 1), ↑(RelCWComplex.closedCell (C := C) n i)) := by
  let hmaps : MapsTo (RelCWComplex.map (C := C) n i)
      (closedBall (0 : Fin n → ℝ) 1) (RelCWComplex.closedCell (C := C) n i) :=
    fun x hx => ⟨x, hx, rfl⟩
  exact ⟨hmaps.restrict (RelCWComplex.map (C := C) n i)
      (closedBall (0 : Fin n → ℝ) 1) (RelCWComplex.closedCell (C := C) n i),
    (RelCWComplex.continuousOn (C := C) n i).mapsToRestrict hmaps⟩

@[simp]
theorem closedCellCharacteristic_apply (n : ℕ) (i : RelCWComplex.cell C n)
    (x : ↑(closedBall (0 : Fin n → ℝ) 1)) :
    (closedCellCharacteristic n i x : X) = RelCWComplex.map n i x :=
  rfl

theorem closedCellCharacteristic_surjective (n : ℕ) (i : RelCWComplex.cell C n) :
    Function.Surjective (closedCellCharacteristic n i) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The closed-cell characteristic map is a quotient map. -/
theorem isQuotientMap_closedCellCharacteristic [T2Space X] (n : ℕ)
    (i : RelCWComplex.cell C n) :
    IsQuotientMap (closedCellCharacteristic n i) := by
  letI : CompactSpace (↑(closedBall (0 : Fin n → ℝ) 1)) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Fin n → ℝ) 1)
  exact IsQuotientMap.of_surjective_continuous
    (closedCellCharacteristic_surjective n i)
    (map_continuous (closedCellCharacteristic n i))

end HatcherLib
