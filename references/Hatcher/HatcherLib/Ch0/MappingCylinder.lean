import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import HatcherLib.Ch0.HomotopyExtension

/-!
# Chapter 0 — The mapping cylinder

Hatcher's Chapter 0 introduces, for a map `f : X → Y`, the **mapping cylinder**
`M_f`: the quotient of the disjoint union `(X × I) ⊔ Y` obtained by identifying
each `(x, 1)` with `f x ∈ Y`. mathlib has no mapping cylinder, so we build it here
as project-local infrastructure.

Main constructions:

* `HatcherLib.MappingCylinder f` — the mapping cylinder `M_f`, the quotient of
  `(X × I) ⊕ Y` by the identification `(x, 1) ∼ f x`;
* `mcylInclX`, `mcylInclY` — the inclusions `X → M_f` (`x ↦ (x, 0)`) and
  `Y → M_f` (`y ↦ y`);
* `mcylProj` — the canonical retraction `r : M_f → Y` collapsing the cylinder
  (`(x, t) ↦ f x`, `y ↦ y`), so `r ∘ j = 𝟙` and `r ∘ i = f`;
* `mcylDeformationRetract` — **`M_f` deformation retracts onto `Y`** (Hatcher's
  "a mapping cylinder `M_f` deformation retracts to the subspace `Y` by sliding
  each `(x, t)` along `{x} × I` to `f x`"). The sliding homotopy is
  `(x, t) ↦ (x, t + s(1 - t))`, continuous because `M_f × I` is a quotient of
  `((X × I) ⊕ Y) × I` (`I` locally compact);
* `mcylHomotopyEquiv` — hence `r : M_f → Y` and `j : Y → M_f` are inverse
  **homotopy equivalences** `M_f ≃ₕ Y`.
-/

namespace HatcherLib

open scoped unitInterval
open ContinuousMap

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The normalisation function on `(X × I) ⊕ Y` sending each top point `(x, 1)` of
the cylinder to `f x ∈ Y` and fixing everything else. The mapping-cylinder
identification is exactly its kernel. -/
noncomputable def mcylNorm (f : C(X, Y)) (p : (X × I) ⊕ Y) : (X × I) ⊕ Y :=
  p.elim (fun q => if (q.2 : ℝ) = 1 then Sum.inr (f q.1) else Sum.inl q) Sum.inr

@[simp] theorem mcylNorm_inr (f : C(X, Y)) (y : Y) : mcylNorm f (Sum.inr y) = Sum.inr y := rfl

theorem mcylNorm_inl (f : C(X, Y)) (x : X) (t : I) :
    mcylNorm f (Sum.inl (x, t)) = if (t : ℝ) = 1 then Sum.inr (f x) else Sum.inl (x, t) := rfl

@[simp] theorem mcylNorm_inl_top (f : C(X, Y)) (x : X) :
    mcylNorm f (Sum.inl (x, 1)) = Sum.inr (f x) := by
  rw [mcylNorm_inl]; simp

theorem mcylNorm_inl_of_ne (f : C(X, Y)) (x : X) (t : I) (ht : (t : ℝ) ≠ 1) :
    mcylNorm f (Sum.inl (x, t)) = Sum.inl (x, t) := by
  rw [mcylNorm_inl]; simp [ht]

/-- The setoid identifying `(x, 1)` with `f x`: two points are equivalent when
`mcylNorm` sends them to the same point. -/
noncomputable def mcylSetoid (f : C(X, Y)) : Setoid ((X × I) ⊕ Y) := Setoid.ker (mcylNorm f)

/-- The **mapping cylinder** `M_f` of a map `f : X → Y`: the quotient of
`(X × I) ⊕ Y` by the identification `(x, 1) ∼ f x`, carrying the quotient topology
(Hatcher, Def. of the mapping cylinder). -/
abbrev MappingCylinder (f : C(X, Y)) : Type u := Quotient (mcylSetoid f)

/-- The quotient map `(X × I) ⊕ Y → M_f`. -/
noncomputable def mcylMk (f : C(X, Y)) : C((X × I) ⊕ Y, MappingCylinder f) :=
  ⟨Quotient.mk (mcylSetoid f), continuous_quotient_mk'⟩

theorem mcylMk_eq {f : C(X, Y)} {a b : (X × I) ⊕ Y} (h : mcylNorm f a = mcylNorm f b) :
    mcylMk f a = mcylMk f b := Quotient.sound h

/-- The top of the cylinder `(x, 1)` is glued to `f x ∈ Y`. -/
theorem mcylMk_top (f : C(X, Y)) (x : X) :
    mcylMk f (Sum.inl (x, 1)) = mcylMk f (Sum.inr (f x)) :=
  mcylMk_eq (by simp)

/-- The inclusion `i : X → M_f`, `x ↦ (x, 0)`. -/
noncomputable def mcylInclX (f : C(X, Y)) : C(X, MappingCylinder f) :=
  (mcylMk f).comp ⟨fun x => Sum.inl (x, 0), by fun_prop⟩

/-- The inclusion `j : Y → M_f`, `y ↦ y`. -/
noncomputable def mcylInclY (f : C(X, Y)) : C(Y, MappingCylinder f) :=
  (mcylMk f).comp ⟨Sum.inr, by fun_prop⟩

@[simp] theorem mcylInclX_apply (f : C(X, Y)) (x : X) :
    mcylInclX f x = mcylMk f (Sum.inl (x, 0)) := rfl

@[simp] theorem mcylInclY_apply (f : C(X, Y)) (y : Y) :
    mcylInclY f y = mcylMk f (Sum.inr y) := rfl

/-- The underlying map `(X × I) ⊕ Y → Y` of the canonical retraction:
`(x, t) ↦ f x`, `y ↦ y`. -/
def mcylProjFun (f : C(X, Y)) : C((X × I) ⊕ Y, Y) :=
  ⟨Sum.elim (fun q => f q.1) id, ((map_continuous f).comp continuous_fst).sumElim continuous_id⟩

@[simp] theorem mcylProjFun_inl (f : C(X, Y)) (x : X) (t : I) :
    mcylProjFun f (Sum.inl (x, t)) = f x := rfl

@[simp] theorem mcylProjFun_inr (f : C(X, Y)) (y : Y) : mcylProjFun f (Sum.inr y) = y := rfl

theorem mcylProjFun_norm (f : C(X, Y)) (p : (X × I) ⊕ Y) :
    mcylProjFun f (mcylNorm f p) = mcylProjFun f p := by
  cases p with
  | inr y => rfl
  | inl q =>
    obtain ⟨x, t⟩ := q
    rw [mcylNorm_inl]
    by_cases ht : (t : ℝ) = 1 <;> simp [ht]

theorem mcylProj_wd (f : C(X, Y)) (a b : (X × I) ⊕ Y) (h : mcylNorm f a = mcylNorm f b) :
    mcylProjFun f a = mcylProjFun f b := by
  rw [← mcylProjFun_norm f a, ← mcylProjFun_norm f b, h]

/-- The **canonical retraction** `r : M_f → Y` collapsing the cylinder to its base:
`(x, t) ↦ f x` and `y ↦ y` (Hatcher's retraction of `M_f` onto `Y`). -/
noncomputable def mcylProj (f : C(X, Y)) : C(MappingCylinder f, Y) where
  toFun := Quotient.lift (mcylProjFun f) (mcylProj_wd f)
  continuous_toFun := (map_continuous (mcylProjFun f)).quotient_lift (mcylProj_wd f)

@[simp] theorem mcylProj_mk (f : C(X, Y)) (p : (X × I) ⊕ Y) :
    mcylProj f (mcylMk f p) = mcylProjFun f p := rfl

@[simp] theorem mcylProj_comp_inclY (f : C(X, Y)) :
    (mcylProj f).comp (mcylInclY f) = ContinuousMap.id Y := by
  ext y; rfl

@[simp] theorem mcylProj_inclY (f : C(X, Y)) (y : Y) : mcylProj f (mcylInclY f y) = y := rfl

@[simp] theorem mcylProj_inclX (f : C(X, Y)) (x : X) : mcylProj f (mcylInclX f x) = f x := rfl

/-! ## The deformation retraction of `M_f` onto `Y` -/

/-- The sliding parameter `slide (t, s) = t + s(1 - t) ∈ I`. As `s` runs `0 → 1` it
slides `t` up to `1`; `slide (t, 0) = t`, `slide (t, 1) = 1`, `slide (1, s) = 1`. -/
def mcylSlide : C(I × I, I) where
  toFun ts := ⟨(ts.1 : ℝ) + (ts.2 : ℝ) * (1 - (ts.1 : ℝ)), by
    rw [Set.mem_Icc]
    have h0t : (0 : ℝ) ≤ (ts.1 : ℝ) := unitInterval.nonneg _
    have ht1 : (ts.1 : ℝ) ≤ 1 := unitInterval.le_one _
    have h0s : (0 : ℝ) ≤ (ts.2 : ℝ) := unitInterval.nonneg _
    have hs1 : (ts.2 : ℝ) ≤ 1 := unitInterval.le_one _
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg h0s (by linarith : (0 : ℝ) ≤ 1 - (ts.1 : ℝ))]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (ts.2 : ℝ))
        (by linarith : (0 : ℝ) ≤ 1 - (ts.1 : ℝ))]⟩
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop

@[simp] theorem mcylSlide_coe (t s : I) :
    (mcylSlide (t, s) : ℝ) = (t : ℝ) + (s : ℝ) * (1 - (t : ℝ)) := rfl

@[simp] theorem mcylSlide_zero (t : I) : mcylSlide (t, 0) = t := by
  apply Subtype.ext; simp

@[simp] theorem mcylSlide_one (t : I) : mcylSlide (t, 1) = 1 := by
  apply Subtype.ext; simp

@[simp] theorem mcylSlide_top (s : I) : mcylSlide (1, s) = 1 := by
  apply Subtype.ext; simp

/-- The underlying sliding map `((X × I) ⊕ Y) × I → (X × I) ⊕ Y`, packaged with `I`
as the *first* coordinate so it can be fed to
`IsQuotientMap.continuous_lift_prod_right`: `(x, t) ↦ (x, slide (t, s))`, `y ↦ y`. -/
def mcylDtilMap (_f : C(X, Y)) : C(I × ((X × I) ⊕ Y), (X × I) ⊕ Y) where
  toFun p := p.2.elim (fun q => Sum.inl (q.1, mcylSlide (q.2, p.1))) Sum.inr
  continuous_toFun := by
    have key : Continuous (fun w : ((X × I) ⊕ Y) × I =>
        (w.1.elim (fun q => Sum.inl (q.1, mcylSlide (q.2, w.2))) Sum.inr : (X × I) ⊕ Y)) := by
      rw [← Homeomorph.comp_continuous_iff'
        (Homeomorph.sumProdDistrib (X := X × I) (Y := Y) (Z := I)).symm]
      refine continuous_sum_dom.mpr ⟨?_, ?_⟩
      · have h : ((fun w : ((X × I) ⊕ Y) × I =>
            w.1.elim (fun q => Sum.inl (q.1, mcylSlide (q.2, w.2))) Sum.inr) ∘
            ⇑(Homeomorph.sumProdDistrib (X := X × I) (Y := Y) (Z := I)).symm) ∘ Sum.inl =
            fun w : (X × I) × I => (Sum.inl (w.1.1, mcylSlide (w.1.2, w.2)) : (X × I) ⊕ Y) := by
          funext w; simp [Homeomorph.sumProdDistrib]
        rw [h]; fun_prop
      · have h : ((fun w : ((X × I) ⊕ Y) × I =>
            w.1.elim (fun q => Sum.inl (q.1, mcylSlide (q.2, w.2))) Sum.inr) ∘
            ⇑(Homeomorph.sumProdDistrib (X := X × I) (Y := Y) (Z := I)).symm) ∘ Sum.inr =
            fun w : Y × I => (Sum.inr w.1 : (X × I) ⊕ Y) := by
          funext w; simp [Homeomorph.sumProdDistrib]
        rw [h]; fun_prop
    exact key.comp (by fun_prop : Continuous (fun p : I × ((X × I) ⊕ Y) => (p.2, p.1)))

@[simp] theorem mcylDtilMap_inl (f : C(X, Y)) (s : I) (x : X) (t : I) :
    mcylDtilMap f (s, Sum.inl (x, t)) = Sum.inl (x, mcylSlide (t, s)) := rfl

@[simp] theorem mcylDtilMap_inr (f : C(X, Y)) (s : I) (y : Y) :
    mcylDtilMap f (s, Sum.inr y) = Sum.inr y := rfl

/-- Sliding descends to `M_f`: applying `mcylNorm` after one step of sliding
depends only on the class of the input. -/
theorem mcylNorm_dtil (f : C(X, Y)) (s : I) (p : (X × I) ⊕ Y) :
    mcylNorm f (mcylDtilMap f (s, p)) = mcylNorm f (mcylDtilMap f (s, mcylNorm f p)) := by
  cases p with
  | inr y => rfl
  | inl q =>
    obtain ⟨x, t⟩ := q
    by_cases ht : (t : ℝ) = 1
    · have h1 : t = 1 := Subtype.ext ht
      subst h1; simp
    · rw [mcylNorm_inl_of_ne f x t ht]

theorem mcylDtil_wd (f : C(X, Y)) (s : I) {a b : (X × I) ⊕ Y}
    (h : mcylNorm f a = mcylNorm f b) :
    mcylMk f (mcylDtilMap f (s, a)) = mcylMk f (mcylDtilMap f (s, b)) :=
  mcylMk_eq (by rw [mcylNorm_dtil f s a, mcylNorm_dtil f s b, h])

/-- **`M_f` deformation retracts onto `Y`.** The homotopy slides each cylinder
point `(x, t)` up its fibre `{x} × I` to the top `(x, 1) = f x`, fixing `Y`
throughout; at time `1` it is the retraction `j ∘ r`. -/
noncomputable def mcylDeformationRetract (f : C(X, Y)) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (MappingCylinder f))
      ((mcylInclY f).comp (mcylProj f)) (Set.range (mcylInclY f)) where
  toContinuousMap :=
    { toFun := fun p => Quotient.liftOn p.2 (fun a => mcylMk f (mcylDtilMap f (p.1, a)))
        (fun a b hab => mcylDtil_wd f p.1 hab)
      continuous_toFun := by
        apply (isQuotientMap_quotient_mk').continuous_lift_prod_right
        exact continuous_quotient_mk'.comp (map_continuous (mcylDtilMap f)) }
  map_zero_left := by
    intro z
    induction z using Quotient.ind with
    | _ p =>
      show mcylMk f (mcylDtilMap f (0, p)) = mcylMk f p
      cases p with
      | inr y => rfl
      | inl q => obtain ⟨x, t⟩ := q; show mcylMk f (Sum.inl (x, mcylSlide (t, 0))) = _; simp
  map_one_left := by
    intro z
    induction z using Quotient.ind with
    | _ p =>
      show mcylMk f (mcylDtilMap f (1, p)) = (mcylInclY f) (mcylProj f (mcylMk f p))
      cases p with
      | inr y => rfl
      | inl q =>
        obtain ⟨x, t⟩ := q
        show mcylMk f (Sum.inl (x, mcylSlide (t, 1))) = mcylInclY f (mcylProj f (mcylMk f (Sum.inl (x, t))))
        rw [mcylSlide_one]; exact mcylMk_top f x
  prop' := by
    rintro s z ⟨y, rfl⟩
    show mcylMk f (mcylDtilMap f (s, Sum.inr y)) = mcylInclY f y
    rfl

/-- **`Y` and `M_f` are homotopy equivalent** via the canonical retraction
`r : M_f → Y` and the inclusion `j : Y → M_f`: `r ∘ j = 𝟙_Y` on the nose and
`j ∘ r ≃ 𝟙_{M_f}` via the deformation retraction of `M_f` onto `Y`. -/
noncomputable def mcylHomotopyEquiv (f : C(X, Y)) :
    ContinuousMap.HomotopyEquiv (MappingCylinder f) Y where
  toFun := mcylProj f
  invFun := mcylInclY f
  left_inv := ContinuousMap.Homotopic.symm ⟨(mcylDeformationRetract f).toHomotopy⟩
  right_inv := by
    rw [mcylProj_comp_inclY]

end HatcherLib
