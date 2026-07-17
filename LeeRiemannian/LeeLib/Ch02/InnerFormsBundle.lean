/-
Chapter 2, "Riemannian Metrics", Problem 2-16, second half: towards the *fibre metric* on
`Λ^k T^*M`.

`LeeLib.Ch02.InnerForms` builds the fibrewise algebra -- the inner product `⟨·,·⟩` on
`V [⋀^ι]→L[ℝ] ℝ` for an inner product space `V`, Lee's characterization (2.26), positive
definiteness, uniqueness, and independence of the orthonormal basis used to define it.  What is
missing there, and what Lee's Problem 2-16 actually asks for, is that the pointwise family
assembles into a **smooth** fibre metric on the bundle `Λ^k T^*M` that
`LeeLib.AppendixA.AlternatingBundle` builds over `M`.  This file supplies the two ingredients that
step needs, both of which are absent from mathlib.

## 1. The bilinear form, built from evaluation maps (`innerFormsCLM`)

`LeeLib.Ch02.innerFormsₗ` is a bare `LinearMap`, while any fibre-metric structure wants a
`ContinuousLinearMap`.  Upgrading it would need continuity of a linear form on
`(TangentSpace I x) [⋀^ι]→L[ℝ] ℝ`, and `TangentSpace I x` carries **no norm**, so the usual
"linear on a finite-dimensional space is continuous" route is unavailable.  Instead `innerFormsCLM`
is *assembled* from mathlib's `ContinuousAlternatingMap.apply` -- evaluation at a fixed tuple,
already bundled as a continuous linear map for a bare topological module -- via
`ContinuousLinearMap.smulRight`:

  `⟨·,·⟩ = (k!)⁻¹ • ∑_{s : ι → ι'} (eval at e ∘ s) ⊗ (eval at e ∘ s)`.

Continuity is then free and, in particular, no norm on `V` is used anywhere in that section, which
is exactly what lets it be instantiated at a tangent space.  `innerFormsCLM_eq_innerForms` bridges
it to `innerForms`, so the whole pointwise theory -- (2.26), positive definiteness, uniqueness,
frame independence -- transfers verbatim.

## 2. Joint evaluation is `C^∞` (`evalCMM`, `contDiff_evalCMM`)

Smoothness of the fibre metric rests on "a smooth `k`-form field applied to `k` smooth vector fields
is a smooth function", i.e. on `(ξ, v) ↦ ξ v` being `C^∞` **jointly**.  Mathlib has only first-order
statements (`HasFDerivAt.continuousAlternatingMap_apply`); `ContinuousMultilinearMap.contDiff`
covers a *fixed* map applied to varying vectors, which is not enough.

## The mathlib instance bug this file is shaped around

The natural formulation of §2 -- `v ↦ (ξ ↦ ξ v)` valued in the dual `(F [⋀^ι]→L[ℝ] ℝ) →L[ℝ] ℝ` --
is **unusable**, and so, for the same reason, is `Bundle.ContMDiffRiemannianMetric IB n F E` at
`F := E [⋀^Fin k]→L[ℝ] ℝ` (its `contMDiff` field mentions the model space `F →L[ℝ] F →L[ℝ] ℝ`).

`ContinuousAlternatingMap.addCommMonoid` (`Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`,
around line 226) is declared with `fast_instance%`.  That makes it defeq to
`ContinuousAlternatingMap.instSeminormedAddCommGroup.toAddCommMonoid` at *default* transparency but
**not at reducible transparency** -- checked directly: `rfl` proves them equal, `with_reducible rfl`
fails.  Instance search and unification work reducibly, so once `F [⋀^ι]→L[ℝ] ℝ` sits in the
*domain* of a `ContinuousLinearMap`, the elaborated type carries `ContinuousLinearMap.addCommMonoid`
while every normed-analysis lemma (`MultilinearMap.mkContinuous`,
`ContinuousLinearMap.toSeminormedAddCommGroup`, ...) supplies
`SeminormedAddCommGroup.toAddCommMonoid`, and the two never match.  Symptoms:

* `#synth NormedAddCommGroup ((F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (F [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)` fails,
  after diverging into unrelated (C*-algebra) branches -- although the instance *term*
  `ContinuousLinearMap.toNormedAddCommGroup (E := …) (F := …) (σ₁₂ := RingHom.id ℝ)` elaborates
  fine once the implicits are given by hand.
* the same statements with a plain normed space in place of `F [⋀^Fin k]→L[ℝ] ℝ` all work.

Raising `synthInstance.maxHeartbeats`/`maxSize`, `backward.isDefEq.respectTransparency false`,
instance-priority changes and `attribute [-instance]` were all tried and none helps.

**The workaround is structural, not a hack**: make the form an extra *slot* of a single multilinear
map rather than the codomain.  Indexing slots by `Option ι` (`none` the form, `some i` the `i`-th
vector), `(ξ, v) ↦ ξ v` is multilinear in all slots at once with codomain `ℝ` -- a plain normed
space, so nothing is poisoned -- and `ContinuousMultilinearMap.contDiff` applies directly.
-/
import LeeLib.Ch02.InnerForms
import LeeLib.Ch02.FormProduct
import LeeLib.Ch02.OrthonormalFrame
import LeeLib.AppendixA.AlternatingBundle

namespace LeeLib.Ch02

open Bundle ContinuousLinearMap Finset Module InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

/-! ### The pointwise bilinear form, built from evaluation maps

Everything here is for a bare topological `ℝ`-module `V`: no norm is used, which is what lets the
construction be applied to `TangentSpace I x`. -/

section PointwiseCLM

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {ι' : Type*} [Fintype ι'] [DecidableEq ι']

/-- **The inner product on `k`-covectors, as a continuous bilinear form**, built from a family
`e : ι' → V` (in practice an orthonormal basis):

  `⟨w, θ⟩ = (k!)⁻¹ ∑_{s : ι → ι'} w(e ∘ s) · θ(e ∘ s)`.

This is `LeeLib.Ch02.innerForms` (`innerFormsCLM_apply`), but assembled from
`ContinuousAlternatingMap.apply` -- evaluation at a fixed tuple, already continuous and linear --
rather than from the bare `LinearMap` `innerFormsₗ`.  Continuity therefore comes for free and, in
particular, does not need a norm on `V`: `TangentSpace I x` has none. -/
def innerFormsCLM (e : ι' → V) :
    (V [⋀^ι]→L[ℝ] ℝ) →L[ℝ] (V [⋀^ι]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  ((Fintype.card ι).factorial : ℝ)⁻¹ •
    ∑ s : ι → ι', (ContinuousAlternatingMap.apply ℝ V ℝ fun i => e (s i)).smulRight
      (ContinuousAlternatingMap.apply ℝ V ℝ fun i => e (s i))

omit [IsTopologicalAddGroup V] [DecidableEq ι'] in
@[simp] theorem innerFormsCLM_apply (e : ι' → V) (w θ : V [⋀^ι]→L[ℝ] ℝ) :
    innerFormsCLM e w θ
      = ((Fintype.card ι).factorial : ℝ)⁻¹ * ∑ s : ι → ι', w (fun i => e (s i)) * θ (fun i => e (s i)) := by
  simp [innerFormsCLM, Finset.sum_apply, Finset.mul_sum]

end PointwiseCLM

/-! ### The bridge to `innerForms`

`innerFormsCLM` is the continuous bilinear form; `LeeLib.Ch02.innerForms` is the function the
pointwise theory of `LeeLib.Ch02.InnerForms` is stated about.  They agree, so the whole of that
theory -- (2.26), positive definiteness, uniqueness, frame independence -- transfers. -/

section Bridge

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {ι' : Type*} [Fintype ι'] [DecidableEq ι']

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
@[simp] theorem innerFormsCLM_eq_innerForms (e : OrthonormalBasis ι' ℝ V) (w θ : V [⋀^ι]→L[ℝ] ℝ) :
    innerFormsCLM (⇑e) w θ = innerForms e w θ := by
  rw [innerFormsCLM_apply, innerForms, div_eq_inv_mul]

end Bridge

/-! ### Joint evaluation `(ξ, v) ↦ ξ v` is `C^∞`

To prove the fibre metric smooth we need that `x ↦ (ω x)(Y_1 x, …, Y_k x)` is smooth when the form
field `ω` and the vector fields `Y_i` all vary.  Mathlib has only first-order statements for this
(`HasFDerivAt.continuousAlternatingMap_apply`); `ContinuousMultilinearMap.contDiff` covers a *fixed*
map applied to varying vectors, which is not enough.

The obvious formulation -- `v ↦ (ξ ↦ ξ v)` as a map into the dual `(F [⋀^ι]→L[ℝ] ℝ) →L[ℝ] ℝ` -- is
**unusable**, for the reason in the module docstring: no normed-analysis lemma can be applied at that
type.  Concretely, `MultilinearMap.mkContinuous` cannot produce a
`ContinuousMultilinearMap ℝ (fun _ : ι => F) ((F [⋀^ι]→L[ℝ] ℝ) →L[ℝ] ℝ)`: elaborating that type
picks `ContinuousLinearMap.addCommMonoid` for the codomain, `mkContinuous` supplies
`SeminormedAddCommGroup.toAddCommMonoid`, and unification -- which is *reducible* -- fails, because
it recurses into the alternating domain where `ContinuousAlternatingMap.addCommMonoid` is a
`fast_instance%` and so is defeq to its normed counterpart only at default transparency.  (Verified:
the same statement with a plain normed space in place of `F [⋀^ι]→L[ℝ] ℝ` elaborates fine.)

The fix is to make the form one more *slot* of a single multilinear map, rather than the codomain.
Indexing the slots by `Option ι` -- `none` carrying the form, `some i` the `i`-th vector -- the
evaluation `(ξ, v) ↦ ξ v` is multilinear in all slots at once, with codomain `ℝ`.  **`ℝ` is a plain
normed space, so nothing is poisoned**, and `ContinuousMultilinearMap.contDiff` applies directly. -/

section EvalSmooth

-- `ι` is restricted to `Type` (rather than `Type*`) so that the two slot types of `evalDom` --
-- `F [⋀^ι]→L[ℝ] ℝ` and `F` -- land in the *same* universe.  This costs nothing: the only `ι` this
-- is ever used at is `Fin k`.
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

variable (F ι) in
/-- The slot types of the joint evaluation map: `none` carries the alternating form, `some i` the
`i`-th vector it is applied to. -/
abbrev evalDom : Option ι → Type _
  | none => F [⋀^ι]→L[ℝ] ℝ
  | some _ => F

/-- The slot types are normed spaces.  The instance has to be given by hand: instance search will
not case-split on the `Option ι` index to reduce `evalDom`. -/
instance instNormedAddCommGroupEvalDom : ∀ i : Option ι, NormedAddCommGroup (evalDom F ι i)
  | none => inferInstanceAs (NormedAddCommGroup (F [⋀^ι]→L[ℝ] ℝ))
  | some _ => inferInstanceAs (NormedAddCommGroup F)

instance instNormedSpaceEvalDom : ∀ i : Option ι, NormedSpace ℝ (evalDom F ι i)
  | none => inferInstanceAs (NormedSpace ℝ (F [⋀^ι]→L[ℝ] ℝ))
  | some _ => inferInstanceAs (NormedSpace ℝ F)

/-- Reading the vector slots off a point of the joint domain.

A `def`, not an `abbrev`: an `abbrev` is reducible, so `simp` unfolds it and the rewrite lemmas
below (whose left-hand sides mention it) never match. -/
def evalVec (m : ∀ i : Option ι, evalDom F ι i) : ι → F := fun i => m (some i)

omit [Fintype ι] in
/-- Updating a vector slot updates the vector tuple, and leaves the form slot alone. -/
theorem evalVec_update_some [DecidableEq (Option ι)]
    (m : ∀ i : Option ι, evalDom F ι i) (i₀ : ι) (z : F) :
    evalVec (Function.update m (some i₀) z) = Function.update (evalVec m) i₀ z := by
  funext j
  show Function.update m (some i₀) z (some j) = Function.update (evalVec m) i₀ z j
  rcases eq_or_ne j i₀ with rfl | h
  · rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne ((Option.some_injective ι).ne h), Function.update_of_ne h]
    rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Updating the form slot leaves the vector tuple alone. -/
@[simp] theorem evalVec_update_none [DecidableEq (Option ι)]
    (m : ∀ i : Option ι, evalDom F ι i)
    (z : evalDom F ι none) : evalVec (Function.update m none z) = evalVec m := by
  funext j
  show Function.update m none z (some j) = m (some j)
  rw [Function.update_of_ne (Option.some_ne_none j)]

omit [Fintype ι] [DecidableEq ι] in
/-- Updating a vector slot leaves the form slot alone. -/
@[simp] theorem update_some_none [DecidableEq (Option ι)]
    (m : ∀ i : Option ι, evalDom F ι i) (i₀ : ι) (z : F) :
    Function.update m (some i₀) z none = m none :=
  Function.update_of_ne (Option.some_ne_none i₀).symm ..

omit [Fintype ι] [DecidableEq ι] in
/-- The form slot of an updated form slot. -/
@[simp] theorem update_none_none [DecidableEq (Option ι)]
    (m : ∀ i : Option ι, evalDom F ι i)
    (z : evalDom F ι none) : Function.update m none z none = z := Function.update_self ..

/-- **Joint evaluation `(ξ, v) ↦ ξ v`, as a multilinear map in all slots at once.**

Linearity in the `none` slot is linearity of `ξ ↦ ξ v`; linearity in a `some i` slot is
multilinearity of the alternating map `ξ`. -/
def evalMultilinear : MultilinearMap ℝ (evalDom F ι) ℝ where
  toFun m := (m none) (evalVec m)
  map_update_add' := by
    rintro _ m (_ | i₀) x y
    · simp [evalVec_update_none]
    · simp only [evalVec_update_some, update_some_none]
      exact (m none).map_update_add _ _ _ _
  map_update_smul' := by
    rintro _ m (_ | i₀) c x
    · simp [evalVec_update_none]
    · simp only [evalVec_update_some, update_some_none]
      exact (m none).map_update_smul _ _ _ _

@[simp] theorem evalMultilinear_apply (m : ∀ i : Option ι, evalDom F ι i) :
    evalMultilinear (F := F) (ι := ι) m = (m none) (evalVec m) := rfl

/-- The joint evaluation map is bounded with constant `1`: `|ξ v| ≤ ‖ξ‖ ∏ ‖v i‖` is exactly
`ContinuousAlternatingMap.le_opNorm`, and `‖ξ‖ ∏ ‖v i‖` is the product over all of `Option ι`. -/
theorem norm_evalMultilinear_le (m : ∀ i : Option ι, evalDom F ι i) :
    ‖evalMultilinear (F := F) (ι := ι) m‖ ≤ 1 * ∏ i, ‖m i‖ := by
  rw [one_mul, Fintype.prod_option, evalMultilinear_apply]
  exact (m none).le_opNorm _

variable (F ι) in
/-- **Joint evaluation, bundled as a continuous multilinear map.**  The codomain is `ℝ`, which is
why this works where the dual-valued formulation does not. -/
def evalCMM :=
  (evalMultilinear (F := F) (ι := ι)).mkContinuous 1 (norm_evalMultilinear_le (F := F) (ι := ι))

/-- **`(ξ, v) ↦ ξ v` is `C^∞` jointly.**  This is the analytic content behind "a smooth `k`-form
field applied to `k` smooth vector fields is a smooth function", which mathlib does not have in any
form. -/
theorem contDiff_evalCMM (n : ℕ∞ω) :
    ContDiff ℝ n fun m : ∀ i : Option ι, evalDom F ι i => (m none) (evalVec m) :=
  (evalCMM F ι).contDiff

end EvalSmooth


/-! ### A smooth `k`-form field applied to smooth vector fields

This is the manifold-level consequence of `contDiff_evalCMM`, and the shape every downstream use
wants.  Mathlib has nothing like it: its bundle API *consumes* hom-bundle sections
(`clm_bundle_apply`) but has no alternating-bundle analogue, and the `volumeForm_apply_eq_det`
route used elsewhere in this development works only in top degree. -/

section ManifoldApply

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {k : ℕ}

/-- **A smooth `k`-form field applied to `k` smooth vector fields is a smooth function.**

Read in a trivialization, `w x (Y_1 x, …, Y_k x)` becomes `W x (u_1 x, …, u_k x)` with everything
in the model space -- the alternating bundle's trivialization is precomposition with the tangent
bundle's, so the two coordinate changes cancel -- and that is `C^∞` by `contDiff_evalCMM`. -/
theorem contMDiffAt_apply_section
    {w : ∀ x : M, (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ}
    {Y : Fin k → ∀ x : M, TangentSpace I x} {x₀ : M}
    (hw : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) x (w x)) x₀)
    (hY : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := TangentSpace I) x (Y i x)) x₀) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => w x (fun i => Y i x)) x₀ := by
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set aT := trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
    (fun x => (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ) x₀ with haT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  -- coordinate representations of the form field and of the vector fields
  have hW : ContMDiffAt I 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ) ∞ (fun x => (aT ⟨x, w x⟩).2) x₀ :=
    (Bundle.contMDiffAt_section _).mp hw
  have hu : ∀ i, ContMDiffAt I 𝓘(ℝ, E) ∞ (fun x => (sT ⟨x, Y i x⟩).2) x₀ := fun i =>
    (Bundle.contMDiffAt_section _).mp (hY i)
  -- bundle them into one `Option (Fin k)`-indexed tuple
  set m : M → ∀ i : Option (Fin k), evalDom E (Fin k) i := fun x i =>
    Option.rec ((aT ⟨x, w x⟩).2) (fun j => (sT ⟨x, Y j x⟩).2) i with hm
  have hmsmooth : ContMDiffAt I 𝓘(ℝ, ∀ i : Option (Fin k), evalDom E (Fin k) i) ∞ m x₀ :=
    contMDiffAt_pi_space.mpr fun i => by
      cases i with
      | none => exact hW
      | some j => exact hu j
  have hcand : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => (m x none) (evalVec (m x))) x₀ :=
    (contDiff_evalCMM (F := E) (ι := Fin k) ∞).contDiffAt.comp_contMDiffAt hmsmooth
  refine hcand.congr_of_eventuallyEq ?_
  filter_upwards [sT.open_baseSet.mem_nhds hx₀] with x hx
  show w x (fun i => Y i x) = (m x none) (evalVec (m x))
  have hcoord : (m x none) = (w x).compContinuousLinearMap (sT.symmL ℝ x) := rfl
  rw [hcoord]
  refine (congrArg (w x) (funext fun i => ?_)).symm
  show sT.symmL ℝ x ((sT ⟨x, Y i x⟩).2) = Y i x
  rw [Trivialization.symmL_apply, Trivialization.symm_apply_apply_mk sT hx]

end ManifoldApply

end

end LeeLib.Ch02
