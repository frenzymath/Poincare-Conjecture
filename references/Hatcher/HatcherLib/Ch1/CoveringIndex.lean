import HatcherLib.Ch1.CoveringSpaces
import Mathlib.Algebra.Group.Subgroup.MulOppositeLemmas
import Mathlib.GroupTheory.Index

/-!
# Chapter 1: fibers and subgroup index

This file formalizes Hatcher's sheets/index calculation. A loop class acts on
the fiber by monodromy; two classes have the same endpoint exactly when they
represent the same coset of the image subgroup. For a path-connected total
space this gives an equivalence between the fiber and the coset space, hence
the cardinality formula.
-/

namespace HatcherLib

noncomputable section

open CategoryTheory

universe u v

variable {E : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X} {e₀ : E}

/-- The endpoint in the chosen fiber of the lift of a based loop class. -/
def coveringEndpoint (cov : CoveringMap p) (e₀ : E)
    (g : FundamentalGroup X (p e₀)) : (p ⁻¹' {p e₀}) :=
  cov.monodromy (FundamentalGroup.toPath g) ⟨e₀, rfl⟩

/-- The subgroup of the base fundamental group induced by a covering. -/
def coveringImageSubgroup (cov : CoveringMap p) (e₀ : E) :
    Subgroup (FundamentalGroup X (p e₀)) :=
  (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range

/-- The subgroup induced by a covering in Hatcher's path-product
multiplication convention. -/
def coveringPiOneImageSubgroup (cov : CoveringMap p) (e₀ : E) :
    Subgroup (PiOne (p e₀)) :=
  (inducedPiOne ⟨p, cov.continuous⟩ e₀).range

/-- Hatcher's induced subgroup is the opposite of mathlib's raw fundamental
group image. -/
theorem coveringPiOneImageSubgroup_eq_op (cov : CoveringMap p) (e₀ : E) :
    coveringPiOneImageSubgroup cov e₀ =
      (coveringImageSubgroup cov e₀).op := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.unop, rfl⟩
  · intro hx
    change x.unop ∈ coveringImageSubgroup cov e₀ at hx
    rcases hx with ⟨y, hy⟩
    refine ⟨MulOpposite.op y, ?_⟩
    apply MulOpposite.unop_injective
    exact hy

/-- A simply-connected covering space induces the trivial subgroup of the
raw fundamental group of its base. -/
theorem coveringImageSubgroup_eq_bot_of_simplyConnected
    (cov : CoveringMap p) [SimplyConnectedSpace E] (e₀ : E) :
    coveringImageSubgroup cov e₀ = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨u, rfl⟩
  have hu : u = 1 := by
    change FundamentalGroup.toPath u =
      FundamentalGroup.toPath (1 : FundamentalGroup E e₀)
    exact Subsingleton.elim _ _
  rw [hu]
  exact map_one _

/-- In Hatcher's multiplication convention, a simply-connected cover also
induces the trivial subgroup. -/
theorem coveringPiOneImageSubgroup_eq_bot_of_simplyConnected
    (cov : CoveringMap p) [SimplyConnectedSpace E] (e₀ : E) :
    coveringPiOneImageSubgroup cov e₀ = ⊥ := by
  rw [coveringPiOneImageSubgroup_eq_op,
    coveringImageSubgroup_eq_bot_of_simplyConnected, Subgroup.op_bot]

omit [TopologicalSpace E] in
lemma covering_toPath_mul (g h : FundamentalGroup X (p e₀)) :
    FundamentalGroup.toPath (g * h) =
      (FundamentalGroup.toPath h).trans (FundamentalGroup.toPath g) := by
  change (h : End (FundamentalGroupoid.mk (p e₀))) ≫
      (g : End (FundamentalGroupoid.mk (p e₀))) =
      (FundamentalGroup.toPath h).trans (FundamentalGroup.toPath g)
  exact FundamentalGroupoid.comp_eq _ _ _ _ _

lemma covering_inverse_endpoint (cov : CoveringMap p)
    (g : FundamentalGroup X (p e₀)) :
    cov.monodromy (FundamentalGroup.toPath g⁻¹)
      (coveringEndpoint cov e₀ g) = ⟨e₀, rfl⟩ := by
  have htrans := cov.monodromy_trans_apply
    (FundamentalGroup.toPath g) (FundamentalGroup.toPath g⁻¹) ⟨e₀, rfl⟩
  have hpath :
      (FundamentalGroup.toPath g).trans (FundamentalGroup.toPath g⁻¹) =
        Path.Homotopic.Quotient.refl (p e₀) := by
    rw [← covering_toPath_mul g⁻¹ g]
    rw [inv_mul_cancel]
    rfl
  rw [hpath] at htrans
  rw [cov.monodromy_refl] at htrans
  exact htrans.symm

/-- A loop in the image subgroup fixes the chosen point of the fiber. -/
lemma covering_fixed_of_range (cov : CoveringMap p) (u : FundamentalGroup E e₀) :
    cov.monodromy
      (FundamentalGroup.toPath ((FundamentalGroup.map
        ⟨p, cov.continuous⟩ e₀) u)) ⟨e₀, rfl⟩ = ⟨e₀, rfl⟩ := by
  have hmap :
      FundamentalGroup.toPath ((FundamentalGroup.map
        ⟨p, cov.continuous⟩ e₀) u) =
        (FundamentalGroup.toPath u).map ⟨p, cov.continuous⟩ := by
    rw [FundamentalGroup.map_apply]
  rw [hmap]
  exact cov.monodromy_map (FundamentalGroup.toPath u)

/-- A fixed point of monodromy determines a loop upstairs. -/
lemma covering_range_of_fixed (cov : CoveringMap p)
    (g : FundamentalGroup X (p e₀))
    (hfix : cov.monodromy (FundamentalGroup.toPath g) ⟨e₀, rfl⟩ = ⟨e₀, rfl⟩) :
    g ∈ coveringImageSubgroup cov e₀ := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective
    (FundamentalGroup.toPath g)
  have hmono :
      cov.monodromy (Path.Homotopic.Quotient.mk γ) ⟨e₀, rfl⟩ =
        ⟨cov.liftPath γ e₀ (by simp) 1,
          (congrFun (cov.liftPath_lifts γ e₀ (by simp)) 1).trans γ.target⟩ := by
    unfold IsCoveringMap.monodromy
    rfl
  have hfix' := hfix
  rw [← hγ, hmono] at hfix'
  have hΓend : (cov.liftPath γ e₀ (by simp)) 1 = e₀ :=
    congrArg Subtype.val hfix'
  let Γ : C(↑unitInterval, E) := cov.liftPath γ e₀ (by simp)
  let Γpath : Path e₀ e₀ :=
    Path.mk Γ (cov.liftPath_zero γ e₀ (by simp)) hΓend
  refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Γpath), ?_⟩
  have hmap :
      FundamentalGroup.map ⟨p, cov.continuous⟩ e₀
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Γpath)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) := by
    rw [FundamentalGroup.map_apply]
    rw [← Path.Homotopic.Quotient.mk_map]
    congr 1
    ext t
    exact congrFun (cov.liftPath_lifts γ e₀ (by simp)) t
  rw [hmap]
  exact congrArg FundamentalGroup.fromPath hγ

/-- The image subgroup consists exactly of loop classes whose lift from the
chosen point closes up. -/
theorem mem_coveringImageSubgroup_iff_monodromy_fixed
    (cov : CoveringMap p) (g : FundamentalGroup X (p e₀)) :
    g ∈ coveringImageSubgroup cov e₀ ↔
      cov.monodromy (FundamentalGroup.toPath g) ⟨e₀, rfl⟩ = ⟨e₀, rfl⟩ := by
  constructor
  · rintro ⟨u, rfl⟩
    exact covering_fixed_of_range cov u
  · exact covering_range_of_fixed cov g

/-- Endpoint equality is exactly the left-coset relation for the image subgroup. -/
lemma coveringEndpoint_eq_iff (cov : CoveringMap p) (e₀ : E)
    (g h : FundamentalGroup X (p e₀)) :
    coveringEndpoint cov e₀ g = coveringEndpoint cov e₀ h ↔
      g⁻¹ * h ∈ coveringImageSubgroup cov e₀ := by
  constructor
  · intro heq
    apply covering_range_of_fixed cov (g⁻¹ * h)
    rw [covering_toPath_mul]
    rw [cov.monodromy_trans_apply]
    change cov.monodromy (FundamentalGroup.toPath g⁻¹)
      (coveringEndpoint cov e₀ h) = ⟨e₀, rfl⟩
    rw [← heq]
    exact covering_inverse_endpoint cov g
  · intro hmem
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
    have hfix :
        cov.monodromy (FundamentalGroup.toPath (g⁻¹ * h)) ⟨e₀, rfl⟩ =
          ⟨e₀, rfl⟩ := by
      rw [← hu]
      exact covering_fixed_of_range cov u
    have hfix' :
        cov.monodromy (FundamentalGroup.toPath g⁻¹)
          (coveringEndpoint cov e₀ h) = ⟨e₀, rfl⟩ := by
      rw [covering_toPath_mul] at hfix
      rw [cov.monodromy_trans_apply] at hfix
      exact hfix
    apply (cov.monodromy_bijective (FundamentalGroup.toPath g⁻¹)).1
    rw [covering_inverse_endpoint cov g, hfix']

/-- The endpoint map descends to the quotient by the image subgroup. -/
def coveringEndpointQuotient (cov : CoveringMap p) (e₀ : E) :
    (FundamentalGroup X (p e₀) ⧸ coveringImageSubgroup cov e₀) →
      (p ⁻¹' {p e₀}) := by
  let f : FundamentalGroup X (p e₀) → (p ⁻¹' {p e₀}) :=
    coveringEndpoint cov e₀
  let hf : ∀ a b, QuotientGroup.leftRel (coveringImageSubgroup cov e₀) a b →
      f a = f b := by
    intro a b hab
    apply (coveringEndpoint_eq_iff cov e₀ a b).2
    exact QuotientGroup.leftRel_apply.mp hab
  exact Quotient.lift f hf

theorem coveringEndpointQuotient_injective (cov : CoveringMap p) (e₀ : E) :
    Function.Injective (coveringEndpointQuotient cov e₀) := by
  intro a b hab
  induction a using QuotientGroup.induction_on with
  | _ ga =>
    induction b using QuotientGroup.induction_on with
    | _ gb =>
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      apply (coveringEndpoint_eq_iff cov e₀ ga gb).1
      simpa [coveringEndpointQuotient] using hab

/-- Path-connectedness of the total space makes the endpoint map onto the
chosen fiber. -/
theorem coveringEndpointQuotient_surjective [PathConnectedSpace E]
    (cov : CoveringMap p) (e₀ : E) :
    Function.Surjective (coveringEndpointQuotient cov e₀) := by
  intro z
  let γ : Path e₀ z.1 := PathConnectedSpace.somePath e₀ z.1
  have hz : p z.1 = p e₀ := by
    have hz0 := z.2
    change p z.1 ∈ ({p e₀} : Set X) at hz0
    exact Set.mem_singleton_iff.mp hz0
  let q : Path (p e₀) (p e₀) :=
    (γ.map cov.continuous).cast rfl hz.symm
  let g : FundamentalGroup X (p e₀) :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)
  refine ⟨(g : FundamentalGroup X (p e₀) ⧸ coveringImageSubgroup cov e₀), ?_⟩
  change coveringEndpoint cov e₀ g = z
  apply Subtype.ext
  change (cov.monodromy (FundamentalGroup.toPath g) ⟨e₀, rfl⟩).1 = z
  have heq : (Path.Homotopic.Quotient.mk γ).map ⟨p, cov.continuous⟩ =
      (Path.Homotopic.Quotient.mk q).cast rfl z.2 := by
    simp [q, Path.Homotopic.Quotient.mk_cast,
      Path.Homotopic.Quotient.cast_cast]
    exact (Path.Homotopic.Quotient.mk_map γ ⟨p, cov.continuous⟩).symm
  have hm : cov.monodromy (Path.Homotopic.Quotient.mk q) ⟨e₀, rfl⟩ = z :=
    cov.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk γ) heq
  exact congrArg Subtype.val hm

/-- The fiber of a connected covering is equivalent to the left cosets of
the image subgroup. -/
def coveringFiberCosetEquiv [PathConnectedSpace E]
    (cov : CoveringMap p) (e₀ : E) :
    (FundamentalGroup X (p e₀) ⧸ coveringImageSubgroup cov e₀) ≃
      (p ⁻¹' {p e₀}) :=
  Equiv.ofBijective (coveringEndpointQuotient cov e₀)
    ⟨coveringEndpointQuotient_injective cov e₀,
      coveringEndpointQuotient_surjective cov e₀⟩

/-- The exact sheets/index formula as a cardinal equality. Unlike `Nat.card`,
this retains the size of infinite covering fibers. -/
theorem coveringFiber_cardinal_eq_coset_cardinal [PathConnectedSpace E]
    (cov : CoveringMap p) (e₀ : E) :
    Cardinal.lift.{v} (Cardinal.mk (p ⁻¹' {p e₀})) =
      Cardinal.lift.{u} (Cardinal.mk
        (FundamentalGroup X (p e₀) ⧸ coveringImageSubgroup cov e₀)) :=
  (Cardinal.lift_mk_eq'.2 ⟨coveringFiberCosetEquiv cov e₀⟩).symm

/-- Hatcher's sheets/index formula, with the sheet count represented by the
cardinality of a fiber. -/
theorem coveringSheets_eq_subgroup_index [PathConnectedSpace E]
    (cov : CoveringMap p) (e₀ : E) :
    Nat.card (p ⁻¹' {p e₀}) = (coveringImageSubgroup cov e₀).index := by
  rw [Subgroup.index_eq_card]
  exact (Nat.card_congr (coveringFiberCosetEquiv cov e₀)).symm

end
end HatcherLib
