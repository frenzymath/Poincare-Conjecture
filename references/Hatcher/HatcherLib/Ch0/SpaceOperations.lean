import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Logic.Relation
import Mathlib.Topology.UnitInterval
import HatcherLib.Ch0.QuotientContractible

/-!
# Chapter 0 — Standard operations on spaces

This file gives the point-set constructions used in the middle of Hatcher's
Chapter 0.  The definitions are deliberately quotient-based: this keeps the
identifications visible in the type and gives every construction its canonical
quotient map.  The later CW-theoretic statements can therefore use these
objects without introducing an unbundled ``quotient space'' parameter.
-/

namespace HatcherLib

open scoped unitInterval

universe u v w

variable {X : Type u} [TopologicalSpace X]

/-! ## Cone and suspension -/

/-- The subset collapsed to the vertex in the cone on `X`. -/
def coneBase (X : Type u) : Set (X × I) := Set.univ ×ˢ ({(0 : I)} : Set I)

/-- The (topological) cone on `X`, namely `(X × I)/(X × {0})`. -/
abbrev Cone (X : Type u) [TopologicalSpace X] : Type u :=
  collapseQuotient (coneBase X)

/-- The canonical quotient map into the cone. -/
def coneMk : C(X × I, Cone X) := collapseMk (coneBase X)

@[simp] theorem coneMk_apply (x : X) (t : I) : coneMk (x, t) = collapseMk (coneBase X) (x, t) :=
  rfl

/-- Every point in the collapsed base of a cone is the vertex. -/
theorem coneMk_base_eq (x y : X) : coneMk (x, 0) = coneMk (y, 0) := by
  apply collapseMk_eq_of_mem
  · exact ⟨Set.mem_univ _, rfl⟩
  · exact ⟨Set.mem_univ _, rfl⟩

/-- The vertex of the cone (independent of the choice of `x`). -/
noncomputable def coneVertex (x : X) : Cone X := coneMk (x, 0)

theorem coneVertex_eq (x y : X) : coneVertex x = coneVertex y := coneMk_base_eq x y

/-- A map induces a map of cones. -/
def coneMap {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) : C(Cone X, Cone Y) := by
  let F : C(X × I, Cone Y) :=
    (coneMk (X := Y)).comp (f.prodMap (ContinuousMap.id I))
  have hwd : ∀ a b : X × I, (collapseSetoid (coneBase X)).r a b → F a = F b := by
    rintro a b (rfl | ⟨ha, hb⟩)
    · rfl
    · have ha0 : a.2 = (0 : I) := by simpa [coneBase] using ha.2
      have hb0 : b.2 = (0 : I) := by simpa [coneBase] using hb.2
      dsimp [F, coneMk]
      apply collapseMk_eq_of_mem (A := coneBase Y)
      · change (f a.1, a.2) ∈ coneBase Y
        exact ⟨Set.mem_univ _, ha0⟩
      · change (f b.1, b.2) ∈ coneBase Y
        exact ⟨Set.mem_univ _, hb0⟩
  exact ⟨Quotient.lift F hwd, (map_continuous F).quotient_lift hwd⟩

@[simp] theorem coneMap_coneMk {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    (x : X) (t : I) : coneMap f (coneMk (x, t)) = coneMk (f x, t) := by
  unfold coneMap
  dsimp [coneMk, collapseMk]
  rw [ContinuousMap.prodMap_apply]
  rfl

@[simp] theorem coneMap_id : coneMap (ContinuousMap.id X) = ContinuousMap.id (Cone X) := by
  ext z
  induction z using Quotient.ind with
  | _ p =>
    cases p with
    | mk x t =>
      change coneMap (ContinuousMap.id X) (coneMk (x, t)) = coneMk (x, t)
      rw [coneMap_coneMk]
      rfl

theorem coneMap_comp {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    coneMap (g.comp f) = (coneMap g).comp (coneMap f) := by
  ext z
  induction z using Quotient.ind with
  | _ p =>
    cases p with
    | mk x t =>
      change coneMap (g.comp f) (coneMk (x, t)) =
        coneMap g (coneMap f (coneMk (x, t)))
      rw [coneMap_coneMk, coneMap_coneMk, coneMap_coneMk]
      rfl

/-- The cone is contractible whenever its base is nonempty. -/
theorem cone_contractible [Nonempty X] : ContractibleSpace (Cone X) := by
  classical
  let scale : C(I × I, I) :=
    ⟨fun p => ⟨(1 - (p.1 : ℝ)) * (p.2 : ℝ), by
        have h₁ : 0 ≤ (1 - (p.1 : ℝ)) := by
          linarith [unitInterval.le_one p.1]
        have h₁' : 0 ≤ (p.1 : ℝ) := unitInterval.nonneg p.1
        have h₂ : 0 ≤ (p.2 : ℝ) := unitInterval.nonneg p.2
        have h₂' : (p.2 : ℝ) ≤ 1 := unitInterval.le_one p.2
        constructor
        · exact mul_nonneg h₁ h₂
        · have hprod : (1 - (p.1 : ℝ)) * (p.2 : ℝ) ≤ (1 - (p.1 : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left h₂' h₁
          nlinarith⟩,
      by fun_prop⟩
  let Hraw : C(I × (X × I), Cone X) :=
    ⟨fun p => coneMk (p.2.1, scale (p.1, p.2.2)), by fun_prop⟩
  have hwd : ∀ (t : I) (a b : X × I),
      (collapseSetoid (coneBase X)).r a b → Hraw (t, a) = Hraw (t, b) := by
    intro t a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · have ha0 : a.2 = (0 : I) := by simpa [coneBase] using ha.2
      have hb0 : b.2 = (0 : I) := by simpa [coneBase] using hb.2
      dsimp [Hraw]
      have hs : scale (t, (0 : I)) = (0 : I) := by
        apply Subtype.ext
        dsimp [scale]
        ring
      rw [ha0, hb0, hs]
      exact coneMk_base_eq _ _
  let Hfun : I × Cone X → Cone X := fun p =>
    Quotient.lift (fun q : X × I => Hraw (p.1, q)) (hwd p.1) p.2
  have hHcont : Continuous Hfun := by
    refine (isQuotientMap_quotient_mk'.continuous_lift_prod_right ?_)
    exact (map_continuous Hraw).comp (by fun_prop)
  let x₀ : X := Classical.arbitrary X
  let H : ContinuousMap.Homotopy (ContinuousMap.id (Cone X))
      (ContinuousMap.const (Cone X) (coneVertex x₀)) :=
    { toContinuousMap := ⟨Hfun, hHcont⟩
      map_zero_left := by
        intro z
        induction z using Quotient.ind with
        | _ p =>
          cases p with
          | mk x t =>
            change Hfun (0, coneMk (x, t)) = coneMk (x, t)
            dsimp [Hfun, Hraw, scale, collapseMk]
            have hs : (⟨(1 - (0 : ℝ)) * (t : ℝ), by
                rw [sub_zero, one_mul]
                exact t.property⟩ : I) = t := by
              apply Subtype.ext
              simp
            rw [hs]
      map_one_left := by
        intro z
        induction z using Quotient.ind with
        | _ p =>
          cases p with
          | mk x t =>
            change Hfun (1, coneMk (x, t)) = coneVertex x₀
            dsimp [Hfun, Hraw, scale, coneVertex, collapseMk]
            have hs : (⟨(1 - (1 : ℝ)) * (t : ℝ), by norm_num⟩ : I) = 0 := by
              apply Subtype.ext
              norm_num
            rw [hs]
            exact coneMk_base_eq _ _ }
  refine ⟨⟨?_, ?_, ?_, ?_⟩⟩
  · exact ContinuousMap.const (Cone X) ()
  · exact ContinuousMap.const Unit (coneVertex x₀)
  · exact ⟨H.symm⟩
  · exact ⟨ContinuousMap.Homotopy.refl _⟩

/-- The relation identifying the two ends of `X × I` in the suspension. -/
def suspensionSetoid : Setoid (X × I) where
  r a b := a = b ∨ (a.2 = 0 ∧ b.2 = 0) ∨ (a.2 = 1 ∧ b.2 = 1)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a; exact Or.inl rfl
    · intro a b h
      rcases h with rfl | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hb, ha⟩)
      · exact Or.inr (Or.inr ⟨hb, ha⟩)
    · intro a b c hab hbc
      rcases hab with rfl | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hbc
      · rcases hbc with rfl | ⟨hb', hc⟩ | ⟨hb', hc⟩
        · exact Or.inr (Or.inl ⟨ha, hb⟩)
        · exact Or.inr (Or.inl ⟨ha, hc⟩)
        · exact False.elim (zero_ne_one (hb.symm.trans hb'))
      · rcases hbc with rfl | ⟨hb', hc⟩ | ⟨hb', hc⟩
        · exact Or.inr (Or.inr ⟨ha, hb⟩)
        · exact False.elim (one_ne_zero (hb.symm.trans hb'))
        · exact Or.inr (Or.inr ⟨ha, hc⟩)

/-- The suspension `SX`, obtained by collapsing the bottom and top ends separately. -/
abbrev Suspension (X : Type u) [TopologicalSpace X] : Type u := Quotient (suspensionSetoid (X := X))

/-- The quotient map into the suspension. -/
def suspensionMk : C(X × I, Suspension X) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

theorem suspensionMk_bottom_eq (x y : X) : suspensionMk (x, 0) = suspensionMk (y, 0) :=
  Quotient.sound (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem suspensionMk_top_eq (x y : X) : suspensionMk (x, 1) = suspensionMk (y, 1) :=
  Quotient.sound (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- A map induces a map of suspensions. -/
def suspensionMap {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) :
    C(Suspension X, Suspension Y) := by
  let F : C(X × I, Suspension Y) :=
    suspensionMk.comp (f.prodMap (ContinuousMap.id I))
  have hwd : ∀ a b : X × I, suspensionSetoid.r a b → F a = F b := by
    rintro a b (rfl | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · rfl
    · dsimp [F, suspensionMk]
      apply Quotient.sound
      exact Or.inr (Or.inl ⟨ha, hb⟩)
    · dsimp [F, suspensionMk]
      apply Quotient.sound
      exact Or.inr (Or.inr ⟨ha, hb⟩)
  exact ⟨Quotient.lift F hwd, (map_continuous F).quotient_lift hwd⟩

@[simp] theorem suspensionMap_suspensionMk {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    (x : X) (t : I) : suspensionMap f (suspensionMk (x, t)) = suspensionMk (f x, t) := by
  unfold suspensionMap
  dsimp [suspensionMk]
  rw [ContinuousMap.prodMap_apply]
  rfl

@[simp] theorem suspensionMap_id :
    suspensionMap (ContinuousMap.id X) = ContinuousMap.id (Suspension X) := by
  ext z
  induction z using Quotient.ind with
  | _ p =>
    cases p with
    | mk x t =>
      change suspensionMap (ContinuousMap.id X) (suspensionMk (x, t)) = suspensionMk (x, t)
      rw [suspensionMap_suspensionMk]
      rfl

theorem suspensionMap_comp {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    suspensionMap (g.comp f) = (suspensionMap g).comp (suspensionMap f) := by
  ext z
  induction z using Quotient.ind with
  | _ p =>
    cases p with
    | mk x t =>
      change suspensionMap (g.comp f) (suspensionMk (x, t)) =
        suspensionMap g (suspensionMap f (suspensionMk (x, t)))
      rw [suspensionMap_suspensionMk, suspensionMap_suspensionMk,
        suspensionMap_suspensionMk]
      rfl

/-! ## Mapping cones -/

/-- The elementary identifications used to form the mapping cone of `f`:
collapse the bottom of the cylinder and attach its top to `Y` along `f`. -/
def mappingConeStep {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    (p q : Y ⊕ (X × I)) : Prop :=
  (∃ x₁ x₂ : X, p = Sum.inr (x₁, 0) ∧ q = Sum.inr (x₂, 0)) ∨
  (∃ x : X, p = Sum.inr (x, 1) ∧ q = Sum.inl (f x))

/-- The setoid generated by the mapping-cone identifications. -/
abbrev mappingConeSetoid {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) :
    Setoid (Y ⊕ (X × I)) := Relation.EqvGen.setoid (mappingConeStep f)

/-- The mapping cone `Y ∪_f CX`, represented as a quotient of `Y ⊕ (X × I)`. -/
abbrev MappingCone {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) : Type (max u v) :=
  Quotient (mappingConeSetoid f)

/-- The quotient map into a mapping cone. -/
def mappingConeMk {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) :
    C(Y ⊕ (X × I), MappingCone f) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

/-- The copy of the target in a mapping cone. -/
def mappingConeInclY {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) :
    C(Y, MappingCone f) :=
  (mappingConeMk f).comp ⟨Sum.inl, continuous_inl⟩

/-- The cylinder part of a mapping cone. -/
def mappingConeInclCylinder {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) :
    C(X × I, MappingCone f) :=
  (mappingConeMk f).comp ⟨Sum.inr, continuous_inr⟩

theorem mappingCone_bottom_eq {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    (x₁ x₂ : X) : mappingConeInclCylinder f (x₁, 0) = mappingConeInclCylinder f (x₂, 0) := by
  unfold mappingConeInclCylinder mappingConeMk
  dsimp
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (Or.inl ⟨x₁, x₂, rfl, rfl⟩)

theorem mappingCone_attach_eq {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    mappingConeInclCylinder f (x, 1) = mappingConeInclY f (f x) := by
  unfold mappingConeInclCylinder mappingConeInclY mappingConeMk
  dsimp
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (Or.inr ⟨x, rfl, rfl⟩)

/-! ## Joins -/

/-- The equivalence relation for the join `X * Y`: at the bottom retain `x`, and
at the top retain `y`. -/
def joinSetoid {Y : Type v} [TopologicalSpace Y] : Setoid (X × Y × I) where
  r a b := a = b ∨ (a.1 = b.1 ∧ a.2.2 = 0 ∧ b.2.2 = 0) ∨
    (a.2.1 = b.2.1 ∧ a.2.2 = 1 ∧ b.2.2 = 1)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a; exact Or.inl rfl
    · intro a b h
      rcases h with rfl | ⟨hx, ha, hb⟩ | ⟨hy, ha, hb⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hx.symm, hb, ha⟩)
      · exact Or.inr (Or.inr ⟨hy.symm, hb, ha⟩)
    · intro a b c hab hbc
      rcases hab with rfl | ⟨hxa, ha, hb⟩ | ⟨hya, ha, hb⟩
      · exact hbc
      · rcases hbc with rfl | ⟨hxb, hb', hc⟩ | ⟨hyb, hb', hc⟩
        · exact Or.inr (Or.inl ⟨hxa, ha, hb⟩)
        · exact Or.inr (Or.inl ⟨hxa.trans hxb, ha, hc⟩)
        · exact False.elim (zero_ne_one (hb.symm.trans hb'))
      · rcases hbc with rfl | ⟨hxb, hb', hc⟩ | ⟨hyb, hb', hc⟩
        · exact Or.inr (Or.inr ⟨hya, ha, hb⟩)
        · exact False.elim (one_ne_zero (hb.symm.trans hb'))
        · exact Or.inr (Or.inr ⟨hya.trans hyb, ha, hc⟩)

/-- The join of two spaces. -/
abbrev Join (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    Type (max u v) := Quotient (joinSetoid (X := X) (Y := Y))

def joinMk {Y : Type v} [TopologicalSpace Y] : C(X × Y × I, Join X Y) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

theorem joinMk_bottom_eq {Y : Type v} [TopologicalSpace Y] (x : X) (y₁ y₂ : Y) :
    joinMk (x, y₁, 0) = joinMk (x, y₂, 0) :=
  Quotient.sound (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))

theorem joinMk_top_eq {Y : Type v} [TopologicalSpace Y] (x₁ x₂ : X) (y : Y) :
    joinMk (x₁, y, 1) = joinMk (x₂, y, 1) :=
  Quotient.sound (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))

/-! ## Wedges and smash products -/

/-- The wedge sum of pointed spaces, formed by identifying their basepoints. -/
abbrev WedgeSum (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y) :
    Type (max u v) := collapseQuotient ({Sum.inl x₀, Sum.inr y₀} : Set (X ⊕ Y))

def wedgeMk (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y) :
    C(X ⊕ Y, WedgeSum x₀ y₀) := collapseMk _

/-- The two canonical maps into a wedge sum. -/
def wedgeInclLeft (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y) :
    C(X, WedgeSum x₀ y₀) :=
  (wedgeMk x₀ y₀).comp ⟨Sum.inl, continuous_inl⟩

def wedgeInclRight (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y) :
    C(Y, WedgeSum x₀ y₀) :=
  (wedgeMk x₀ y₀).comp ⟨Sum.inr, continuous_inr⟩

@[simp] theorem wedgeInclLeft_apply (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y)
    (x : X) : wedgeInclLeft x₀ y₀ x = wedgeMk x₀ y₀ (Sum.inl x) := rfl

@[simp] theorem wedgeInclRight_apply (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y)
    (y : Y) : wedgeInclRight x₀ y₀ y = wedgeMk x₀ y₀ (Sum.inr y) := rfl

theorem wedgeMk_glue (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y) :
    wedgeMk x₀ y₀ (Sum.inl x₀) = wedgeMk x₀ y₀ (Sum.inr y₀) := by
  apply collapseMk_eq_of_mem
  · simp
  · simp

/-- The smash product of pointed spaces, obtained by collapsing the wedge in the product. -/
def smashBase (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y) : Set (X × Y) :=
  {p | p.1 = x₀ ∨ p.2 = y₀}

abbrev SmashProduct (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y) :
    Type (max u v) := collapseQuotient (smashBase x₀ y₀)

def smashMk (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y) :
    C(X × Y, SmashProduct x₀ y₀) := collapseMk _

theorem smashMk_base_eq_left (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y)
    (y : Y) : smashMk x₀ y₀ (x₀, y) = smashMk x₀ y₀ (x₀, y₀) := by
  apply collapseMk_eq_of_mem <;> simp [smashBase]

theorem smashMk_base_eq_right (x₀ : X) {Y : Type v} [TopologicalSpace Y] (y₀ : Y)
    (x : X) : smashMk x₀ y₀ (x, y₀) = smashMk x₀ y₀ (x₀, y₀) := by
  apply collapseMk_eq_of_mem <;> simp [smashBase]

/-- A pair of basepoint-preserving maps induces a map of smash products. -/
def smashMap {Y : Type v} {Z : Type v} {W : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    [TopologicalSpace W] (x₀ : X) (y₀ : Y) (z₀ : Z) (w₀ : W)
    (f : C(X, Z)) (g : C(Y, W)) (hf : f x₀ = z₀) (hg : g y₀ = w₀) :
    C(SmashProduct x₀ y₀, SmashProduct z₀ w₀) := by
  let F : C(X × Y, SmashProduct z₀ w₀) :=
    (smashMk z₀ w₀).comp (f.prodMap g)
  have hwd : ∀ a b : X × Y, (collapseSetoid (smashBase x₀ y₀)).r a b → F a = F b := by
    rintro a b (rfl | ⟨ha, hb⟩)
    · rfl
    · apply collapseMk_eq_of_mem (A := smashBase z₀ w₀)
      · change f a.1 = z₀ ∨ g a.2 = w₀
        rcases ha with ha | ha
        · exact Or.inl (hf ▸ congrArg f ha)
        · exact Or.inr (hg ▸ congrArg g ha)
      · change f b.1 = z₀ ∨ g b.2 = w₀
        rcases hb with hb | hb
        · exact Or.inl (hf ▸ congrArg f hb)
        · exact Or.inr (hg ▸ congrArg g hb)
  exact ⟨Quotient.lift F hwd, (map_continuous F).quotient_lift hwd⟩

@[simp] theorem smashMap_smashMk {Y : Type v} {Z : Type v} {W : Type w} [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace W] (x₀ : X) (y₀ : Y) (z₀ : Z) (w₀ : W)
    (f : C(X, Z)) (g : C(Y, W)) (hf : f x₀ = z₀) (hg : g y₀ = w₀)
    (x : X) (y : Y) :
    smashMap x₀ y₀ z₀ w₀ f g hf hg (smashMk x₀ y₀ (x, y)) =
      smashMk z₀ w₀ (f x, g y) := by
  unfold smashMap
  dsimp [smashMk, collapseMk]
  rw [ContinuousMap.prodMap_apply]
  rfl

/-! ## Simplices and CW vocabulary -/

/-- Hatcher's standard `(n-1)`-simplex, using mathlib's canonical definition. -/
abbrev Simplex (n : ℕ) : Type := (stdSimplex ℝ (Fin n))

instance simplex_nonempty (n : ℕ) [NeZero n] : Nonempty (Simplex n) := by
  classical
  exact ⟨⟨Pi.single (default : Fin n) 1, single_mem_stdSimplex ℝ default⟩⟩

end HatcherLib
