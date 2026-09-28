import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Homotopy.Product

/-!
# Chapter 1: paths and the fundamental group

Hatcher's first constructions are already implemented in mathlib's path
homotopy groupoid.  This file gives them names in the `HatcherLib` namespace,
and records the small bridges used by the chapter blueprint.  The endpoint
indices on `Path` make the endpoint conditions explicit in every definition.
-/

namespace HatcherLib

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ x₂ : X}

/-! ## Paths and path homotopies -/

/-- A path from `x₀` to `x₁` (Hatcher's path definition, with endpoints indexed). -/
abbrev Path (x₀ x₁ : X) := _root_.Path x₀ x₁

namespace Path

/-- A homotopy of paths relative to both endpoints. -/
abbrev Homotopy (p q : HatcherLib.Path x₀ x₁) := _root_.Path.Homotopy p q

/-- The relation of homotopy of paths with fixed endpoints. -/
abbrev Homotopic (p q : HatcherLib.Path x₀ x₁) : Prop := _root_.Path.Homotopic p q

/-- The homotopy class of a path. -/
abbrev HomotopyClass (x₀ x₁ : X) := _root_.Path.Homotopic.Quotient x₀ x₁

end Path

/-- A loop at `x₀`. -/
abbrev Loop (x₀ : X) := HatcherLib.Path x₀ x₀

/-- Composition of paths, traversing the first path and then the second. -/
def pathProduct (p : HatcherLib.Path x₀ x₁) (q : HatcherLib.Path x₁ x₂) :
    HatcherLib.Path x₀ x₂ :=
  p.trans q

/-- The reverse of a path. -/
def pathReverse (p : HatcherLib.Path x₀ x₁) : HatcherLib.Path x₁ x₀ :=
  p.symm

/-- Homotopies of paths form an equivalence relation. -/
theorem pathHomotopic_equivalence (x₀ x₁ : X) :
    Equivalence (@_root_.Path.Homotopic X _ x₀ x₁) :=
  _root_.Path.Homotopic.equivalence

/-- Path composition respects homotopy in both factors. -/
theorem pathProduct_homotopic
    {p p' : HatcherLib.Path x₀ x₁} {q q' : HatcherLib.Path x₁ x₂}
    (hp : _root_.Path.Homotopic p p') (hq : _root_.Path.Homotopic q q') :
    _root_.Path.Homotopic (pathProduct p q) (pathProduct p' q') :=
  hp.hcomp hq

/-! ## The affine example -/

/-- The straight-line homotopy between paths in a topological real vector space. -/
def affinePathHomotopy
    {E : Type u} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E]
    {a b : E} (p q : _root_.Path a b) : _root_.Path.Homotopy p q where
  toFun := ContinuousMap.Homotopy.affine p.toContinuousMap q.toContinuousMap
  continuous_toFun :=
    (ContinuousMap.Homotopy.affine p.toContinuousMap q.toContinuousMap).continuous
  map_zero_left s := by simp
  map_one_left s := by simp
  prop' t s hs := by
    rcases hs with hs | hs
    · subst s
      simp
    · rw [Set.mem_singleton_iff] at hs
      subst s
      simp

/-- Any two paths with the same endpoints in a topological real vector space are homotopic. -/
theorem affine_paths_homotopic
    {E : Type u} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E]
    {a b : E} (p q : _root_.Path a b) : _root_.Path.Homotopic p q :=
  ⟨affinePathHomotopy p q⟩

/-! ## The fundamental group -/

/-- Hatcher's set of loop homotopy classes. -/
abbrev PiOneSet (x₀ : X) := _root_.Path.Homotopic.Quotient x₀ x₀

/-- The fundamental group at a basepoint, with Hatcher's path-product
convention. Mathlib's endomorphism multiplication traverses the right factor
first, so the opposite group traverses `p` and then `q` in the product
`[p] * [q]`. -/
abbrev PiOne (x₀ : X) := MulOpposite (_root_.FundamentalGroup X x₀)

/-- A loop class regarded as an element of Hatcher's fundamental group. -/
abbrev piOneClass (p : _root_.Path x₀ x₀) : PiOne x₀ :=
  MulOpposite.op (_root_.FundamentalGroup.fromPath (.mk p))

/-- Multiplication in `PiOne` is represented by traversing the first path and
then the second, exactly as in Hatcher's definition. -/
@[simp] theorem piOneClass_pathProduct (p q : _root_.Path x₀ x₀) :
    piOneClass (pathProduct p q) = piOneClass p * piOneClass q := by
  apply MulOpposite.unop_injective
  change _root_.FundamentalGroup.fromPath (.mk (p.trans q)) =
    _root_.FundamentalGroup.fromPath (.mk q) *
      _root_.FundamentalGroup.fromPath (.mk p)
  rfl

/-- Change of basepoint along a path, in Hatcher's direction. -/
def changeBasepoint (h : HatcherLib.Path x₀ x₁) : PiOne x₁ ≃* PiOne x₀ :=
  MulEquiv.op (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath h.symm)

/-- The change-of-basepoint map is a multiplicative equivalence. -/
theorem changeBasepoint_bijective (h : HatcherLib.Path x₀ x₁) :
    Function.Bijective (changeBasepoint h) :=
  (changeBasepoint h).bijective

/-- The homomorphism on fundamental groups induced by a continuous map. -/
def inducedPiOne (f : C(X, Y)) (x₀ : X) : PiOne x₀ →* PiOne (f x₀) :=
  MonoidHom.op (_root_.FundamentalGroup.map f x₀)

/-- The induced map with a separately specified target basepoint. -/
def inducedPiOneOfEq (f : C(X, Y)) {x₀ : X} {y₀ : Y} (h : f x₀ = y₀) :
    PiOne x₀ →* PiOne y₀ :=
  MonoidHom.op (_root_.FundamentalGroup.mapOfEq f h)

/-- Transporting an induced fundamental-group map along reflexivity does not
change the map. -/
@[simp] theorem fundamentalGroup_mapOfEq_rfl (f : C(X, Y)) (x : X) :
    _root_.FundamentalGroup.mapOfEq f (rfl : f x = f x) =
      _root_.FundamentalGroup.map f x := by
  ext u
  obtain ⟨γ, rfl⟩ :=
    _root_.Path.Homotopic.Quotient.mk_surjective (_root_.FundamentalGroup.toPath u)
  rw [_root_.FundamentalGroup.mapOfEq_apply, _root_.FundamentalGroup.map_apply,
    ← _root_.Path.Homotopic.Quotient.mk_map]
  apply congrArg _root_.Path.Homotopic.Quotient.mk
  apply _root_.Path.ext
  rfl

/-- Changing the target basepoint after applying an induced map is the same as
using `mapOfEq` directly. -/
theorem fundamentalGroup_basepointTransport_comp_map
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) :
    (_root_.FundamentalGroup.mapOfEq (ContinuousMap.id Y) h).comp
        (_root_.FundamentalGroup.map f x) =
      _root_.FundamentalGroup.mapOfEq f h := by
  ext u
  obtain ⟨γ, rfl⟩ :=
    _root_.Path.Homotopic.Quotient.mk_surjective (_root_.FundamentalGroup.toPath u)
  rw [MonoidHom.comp_apply, _root_.FundamentalGroup.map_apply,
    ← _root_.Path.Homotopic.Quotient.mk_map, _root_.FundamentalGroup.mapOfEq_apply,
    _root_.FundamentalGroup.mapOfEq_apply]
  apply congrArg _root_.Path.Homotopic.Quotient.mk
  apply _root_.Path.ext
  rfl

/-- Basepoint transport along an equality cancels transport along its inverse. -/
theorem fundamentalGroup_basepointTransport_comp_mapOfEq_symm
    (f : C(X, Y)) {x : X} {y : Y} (h : y = f x) :
    (_root_.FundamentalGroup.mapOfEq (ContinuousMap.id Y) h).comp
        (_root_.FundamentalGroup.mapOfEq f h.symm) =
      _root_.FundamentalGroup.map f x := by
  ext u
  obtain ⟨γ, rfl⟩ :=
    _root_.Path.Homotopic.Quotient.mk_surjective (_root_.FundamentalGroup.toPath u)
  rw [MonoidHom.comp_apply, _root_.FundamentalGroup.mapOfEq_apply,
    _root_.FundamentalGroup.mapOfEq_apply, _root_.FundamentalGroup.map_apply,
    ← _root_.Path.Homotopic.Quotient.mk_map]
  apply congrArg _root_.Path.Homotopic.Quotient.mk
  apply _root_.Path.ext
  rfl

/-- The raw mathlib product equivalence, using its endomorphism-composition
convention. -/
def fundamentalGroupProdMulEquiv (x₀ : X) (y₀ : Y) :
    _root_.FundamentalGroup X x₀ × _root_.FundamentalGroup Y y₀ ≃*
      _root_.FundamentalGroup (X × Y) (x₀, y₀) where
  toFun p := _root_.Path.Homotopic.prod p.1 p.2
  invFun p := (_root_.Path.Homotopic.projLeft p, _root_.Path.Homotopic.projRight p)
  left_inv p := by
    ext
    · exact _root_.Path.Homotopic.projLeft_prod p.1 p.2
    · exact _root_.Path.Homotopic.projRight_prod p.1 p.2
  right_inv := _root_.Path.Homotopic.prod_projLeft_projRight
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul]
    exact (_root_.Path.Homotopic.comp_prod_eq_prod_comp q.1 q.2 p.1 p.2).symm

/-- Opposite groups commute with binary products. -/
def mulOppositeProdMulEquiv (G H : Type*) [Group G] [Group H] :
    MulOpposite G × MulOpposite H ≃* MulOpposite (G × H) where
  toFun x := MulOpposite.op (x.1.unop, x.2.unop)
  invFun x := (MulOpposite.op x.unop.1, MulOpposite.op x.unop.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The product formula for fundamental groups in Hatcher's path-product
convention. -/
def piOneProdMulEquiv (x₀ : X) (y₀ : Y) :
    PiOne x₀ × PiOne y₀ ≃* PiOne (x₀, y₀) :=
  (mulOppositeProdMulEquiv
    (_root_.FundamentalGroup X x₀) (_root_.FundamentalGroup Y y₀)).trans
      (MulEquiv.op (fundamentalGroupProdMulEquiv x₀ y₀))

/-! ## Simply connected spaces -/

/-- Hatcher's notion of a simply-connected space. -/
abbrev SimplyConnected (X : Type u) [TopologicalSpace X] : Prop :=
  _root_.SimplyConnectedSpace X

/-- Simply-connectedness is equivalent to existence and uniqueness of path classes. -/
theorem simplyConnected_iff_unique_path_class (X : Type u) [TopologicalSpace X] :
    SimplyConnected X ↔
      Nonempty X ∧ ∀ x y : X,
        Nonempty (Unique (_root_.Path.Homotopic.Quotient x y)) :=
  _root_.simply_connected_iff_unique_homotopic X

/-- In a simply-connected space all paths with fixed endpoints are homotopic. -/
theorem simplyConnected_paths_homotopic [SimplyConnected X]
    (p q : _root_.Path x₀ x₁) : _root_.Path.Homotopic p q :=
  _root_.SimplyConnectedSpace.paths_homotopic p q

end
end HatcherLib
