import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

/-!
# Chapter 1: algebraic constructions used by van Kampen

Mathlib's indexed coproduct is the free product, implemented by reduced words
and characterized by its universal property.
-/

namespace HatcherLib

open Module

universe u v w

variable {ι : Type u} (G : ι → Type v) [∀ i, Group (G i)]

/-- The free product of an indexed family of groups. -/
abbrev FreeProduct := Monoid.CoprodI G

/-- Reduced words in the factors of a free product. -/
abbrev FreeProductWord := Monoid.CoprodI.Word G

/-- The canonical inclusion of a factor into a free product. -/
def freeProductInclusion (i : ι) : G i →* FreeProduct G :=
  Monoid.CoprodI.of

variable {H : Type w} [Group H]

/-- The homomorphism out of a free product determined by homomorphisms on its factors. -/
def freeProductLift (φ : ∀ i, G i →* H) : FreeProduct G →* H :=
  Monoid.CoprodI.lift φ

/-- The free-product lift restricts to the prescribed homomorphism on each factor. -/
theorem freeProductLift_comp_inclusion (φ : ∀ i, G i →* H) (i : ι) :
    (freeProductLift G φ).comp (freeProductInclusion G i) = φ i :=
  Monoid.CoprodI.lift_comp_of φ i

/-- Uniqueness in the universal property of the free product. -/
theorem freeProductLift_unique (φ : ∀ i, G i →* H) (ψ : FreeProduct G →* H)
    (hψ : ∀ i, ψ.comp (freeProductInclusion G i) = φ i) :
    ψ = freeProductLift G φ := by
  apply Monoid.CoprodI.ext_hom
  intro i
  have hi := hψ i
  change ψ.comp (Monoid.CoprodI.of : G i →* _) = φ i at hi
  change ψ.comp (Monoid.CoprodI.of : G i →* _) =
    (Monoid.CoprodI.lift φ).comp Monoid.CoprodI.of
  rw [hi, Monoid.CoprodI.lift_comp_of]

/-- A free group on a specified type of generators. -/
abbrev FreeGroupOn (S : Type u) := FreeGroup S

/-- A basis of a group indexed by `S`, equivalently an isomorphism with `FreeGroup S`. -/
abbrev FreeBasis (S : Type u) (K : Type v) [Group K] := FreeGroupBasis S K

/-- The property that a group is free on some basis. -/
abbrev IsFree (K : Type u) [Group K] : Prop := IsFreeGroup K

/-- A chosen basis for a group known to be free. -/
noncomputable def chosenFreeBasis (K : Type u) [Group K] [IsFreeGroup K] :
    FreeBasis (IsFreeGroup.Generators K) K :=
  IsFreeGroup.basis K

/-- The rank of a free group, as the cardinality of a chosen free basis. -/
noncomputable def freeGroupRank (K : Type u) [Group K] [IsFreeGroup K] : Cardinal :=
  Cardinal.mk (IsFreeGroup.Generators K)

/-- The index type of any free basis is equivalent to the index type of the
chosen basis. Mathlib obtains this equivalence by passing to abelianizations. -/
noncomputable def freeBasisIndexEquivGenerators
    {S : Type u} {K : Type v} [Group K] [IsFreeGroup K]
    (b : FreeBasis S K) : S ≃ IsFreeGroup.Generators K :=
  Equiv.ofFreeGroupEquiv (b.repr.symm.trans (IsFreeGroup.toFreeGroup K))

/-- The cardinality of a free basis is independent of the chosen basis and is
equal to the rank of the group. -/
theorem freeBasis_cardinalMk_eq_rank
    {S : Type u} {K : Type v} [Group K] [IsFreeGroup K]
    (b : FreeBasis S K) :
    Cardinal.lift.{v} (Cardinal.mk S) =
      Cardinal.lift.{u} (freeGroupRank K) := by
  let e := freeBasisIndexEquivGenerators b
  apply le_antisymm
  · exact Cardinal.lift_mk_le'.2 ⟨e.toEmbedding⟩
  · exact Cardinal.lift_mk_le'.2 ⟨e.symm.toEmbedding⟩

/-- The abelianization of the free group on `S` is free abelian on the same
indexing type. -/
noncomputable def freeGroupAbelianizationBasis (S : Type u) :
    Basis S ℤ (FreeAbelianGroup S) :=
  FreeAbelianGroup.basis S

/-- Nielsen--Schreier: every subgroup of a free group is free. -/
theorem subgroup_of_free_is_free {K : Type u} [Group K] [IsFreeGroup K]
    (L : Subgroup K) : IsFreeGroup L := by
  infer_instance

/-- The Fundamental Theorem of Algebra in polynomial form. -/
theorem fundamentalTheoremOfAlgebra {f : Polynomial ℂ} (hf : 0 < f.degree) :
    ∃ z : ℂ, f.IsRoot z :=
  Complex.exists_root hf

end HatcherLib
