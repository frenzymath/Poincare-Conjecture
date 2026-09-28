import HatcherLib.Ch1.VanKampenGrid

/-!
# Context closure for van Kampen factorization moves

The elementary factorization moves used in the van Kampen proof may occur
inside a larger word.  This file records the corresponding congruence rules
for `VanKampenWordEquivalent`, so the geometric grid argument can rewrite one
local segment without rebuilding the surrounding factorization.
-/

namespace HatcherLib

noncomputable section

universe u v

variable {X : Type u} [TopologicalSpace X]

namespace VanKampenWordMove

/-- An elementary move remains elementary after adjoining a fixed prefix. -/
theorem append_left {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    {left right : List (VanKampenFactor cover)}
    (move : VanKampenWordMove cover left right)
    (pre : List (VanKampenFactor cover)) :
    VanKampenWordMove cover (pre ++ left) (pre ++ right) := by
  cases move with
  | eraseOne left right i =>
      simpa only [List.append_assoc] using
        VanKampenWordMove.eraseOne (cover := cover) (pre ++ left) right i
  | multiply left right i a b =>
      simpa only [List.append_assoc] using
        VanKampenWordMove.multiply (cover := cover) (pre ++ left) right i a b
  | changeCover left right i j w =>
      simpa only [List.append_assoc] using
        VanKampenWordMove.changeCover (cover := cover)
          (pre ++ left) right i j w

/-- An elementary move remains elementary after adjoining a fixed suffix. -/
theorem append_right {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    {left right : List (VanKampenFactor cover)}
    (move : VanKampenWordMove cover left right)
    (suffix : List (VanKampenFactor cover)) :
    VanKampenWordMove cover (left ++ suffix) (right ++ suffix) := by
  cases move with
  | eraseOne left right i =>
      simpa only [List.append_assoc, List.cons_append] using
        VanKampenWordMove.eraseOne (cover := cover)
          left (right ++ suffix) i
  | multiply left right i a b =>
      simpa only [List.append_assoc, List.cons_append] using
        VanKampenWordMove.multiply (cover := cover)
          left (right ++ suffix) i a b
  | changeCover left right i j w =>
      simpa only [List.append_assoc, List.cons_append] using
        VanKampenWordMove.changeCover (cover := cover)
          left (right ++ suffix) i j w

end VanKampenWordMove

namespace VanKampenWordEquivalent

/-- Factorization equivalence is stable under adjoining a fixed prefix. -/
theorem append_left {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    {left right : List (VanKampenFactor cover)}
    (equiv : VanKampenWordEquivalent cover left right)
    (pre : List (VanKampenFactor cover)) :
    VanKampenWordEquivalent cover (pre ++ left) (pre ++ right) := by
  induction equiv with
  | rel left right move =>
      exact Relation.EqvGen.rel _ _ (move.append_left pre)
  | refl word => exact Relation.EqvGen.refl _
  | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans left middle right _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Factorization equivalence is stable under adjoining a fixed suffix. -/
theorem append_right {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    {left right : List (VanKampenFactor cover)}
    (equiv : VanKampenWordEquivalent cover left right)
    (suffix : List (VanKampenFactor cover)) :
    VanKampenWordEquivalent cover (left ++ suffix) (right ++ suffix) := by
  induction equiv with
  | rel left right move =>
      exact Relation.EqvGen.rel _ _ (move.append_right suffix)
  | refl word => exact Relation.EqvGen.refl _
  | symm left right _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans left middle right _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Equivalent prefixes and suffixes may be concatenated independently. -/
theorem append {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    {left₁ right₁ left₂ right₂ : List (VanKampenFactor cover)}
    (equiv₁ : VanKampenWordEquivalent cover left₁ right₁)
    (equiv₂ : VanKampenWordEquivalent cover left₂ right₂) :
    VanKampenWordEquivalent cover (left₁ ++ left₂) (right₁ ++ right₂) :=
  Relation.EqvGen.trans _ _ _ (equiv₁.append_right left₂)
    (equiv₂.append_left right₁)

/-- A single elementary move can be used as a factorization equivalence. -/
theorem of_move {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    {left right : List (VanKampenFactor cover)}
    (move : VanKampenWordMove cover left right) :
    VanKampenWordEquivalent cover left right :=
  Relation.EqvGen.rel _ _ move

/-- A trivial factor can be inserted at any position. -/
theorem insert_one {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    (left right : List (VanKampenFactor cover)) (i : ι) :
    VanKampenWordEquivalent cover (left ++ right)
      (left ++ ⟨i, 1⟩ :: right) :=
  Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _
      (VanKampenWordMove.eraseOne (cover := cover) left right i))

/-- Two adjacent factors from one cover member can be multiplied. -/
theorem multiply {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    (left right : List (VanKampenFactor cover)) (i : ι)
    (a b : CoverFundamentalGroup cover i) :
    VanKampenWordEquivalent cover
      (left ++ ⟨i, a⟩ :: ⟨i, b⟩ :: right)
      (left ++ ⟨i, a * b⟩ :: right) :=
  Relation.EqvGen.rel _ _
    (VanKampenWordMove.multiply (cover := cover) left right i a b)

/-- A loop in a pairwise overlap can be reinterpreted in either member. -/
theorem change_cover {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    (left right : List (VanKampenFactor cover)) (i j : ι)
    (w : CoverIntersectionFundamentalGroup cover i j) :
    VanKampenWordEquivalent cover
      (left ++ ⟨i, coverIntersectionToLeft cover i j w⟩ :: right)
      (left ++ ⟨j, coverIntersectionToRight cover i j w⟩ :: right) :=
  Relation.EqvGen.rel _ _
    (VanKampenWordMove.changeCover (cover := cover) left right i j w)

end VanKampenWordEquivalent

/-! ## Evaluation and representative paths -/

/-- Evaluating concatenated factor lists agrees with multiplication in the
free product. -/
@[simp] theorem vanKampenWordEvaluation_append {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (left right : List (VanKampenFactor cover)) :
    vanKampenWordEvaluation cover (left ++ right) =
      vanKampenWordEvaluation cover left *
        vanKampenWordEvaluation cover right := by
  simp [vanKampenWordEvaluation]

/-- The chosen loop for a concatenated factor list traverses the right block
before the left block.  This is the path-level form of the categorical
composition convention for `FundamentalGroup` multiplication. -/
theorem vanKampenWordLoop_append {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (left right : List (VanKampenFactor cover)) :
    (vanKampenWordLoop cover (left ++ right)).Homotopic
      ((vanKampenWordLoop cover right).trans
        (vanKampenWordLoop cover left)) := by
  induction left with
  | nil =>
      simpa [vanKampenWordLoop] using
        (Path.Homotopic.trans_refl (vanKampenWordLoop cover right)).symm
  | cons a left ih =>
      have h₁ := Path.Homotopic.hcomp ih
        (Path.Homotopic.refl (vanKampenFactorLoop cover a))
      have h₂ := Path.Homotopic.trans_assoc
        (vanKampenWordLoop cover right) (vanKampenWordLoop cover left)
          (vanKampenFactorLoop cover a)
      simpa [vanKampenWordLoop] using h₁.trans h₂

/-- The loop chosen for a one-factor word is homotopic to that factor's
chosen representative. -/
theorem vanKampenWordLoop_singleton {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (a : VanKampenFactor cover) :
    (vanKampenWordLoop cover [a]).Homotopic
      (vanKampenFactorLoop cover a) := by
  simpa [vanKampenWordLoop] using
    Path.Homotopic.refl_trans (vanKampenFactorLoop cover a)

/-- Equivalent factor words have homotopic chosen representative loops. -/
theorem vanKampenWordLoop_homotopic_of_equivalent {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    {left right : List (VanKampenFactor cover)}
    (equiv : VanKampenWordEquivalent cover left right) :
    (vanKampenWordLoop cover left).Homotopic
      (vanKampenWordLoop cover right) :=
  vanKampenWordLoop_homotopic_of_map_eq cover left right
    (vanKampenWordEquivalent_map_eq cover equiv)

end
end HatcherLib
