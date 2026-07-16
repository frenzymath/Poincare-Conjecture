import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# `C^∞` smoothness of a parametric Bochner integral over a compact parameter space

This file supplies a piece of analysis that Mathlib does not currently package: if a family
of maps `F a : E → G` (`a` ranging over a **compact** parameter space `α` carrying a finite
measure `μ`) is jointly nice — each `F a` is `C^∞`, and every order-`m` iterated `x`-derivative
`(a, x) ↦ D_x^m(F a)(x)` is **jointly continuous** — then the averaged map

  `x ↦ ∫_α F a x dμ(a)`

is itself `C^∞`, and its `m`-th derivative is obtained by differentiating under the integral,
`D^m(∫ F) = ∫ D^m F`.

Mathlib provides the *first* derivative under the integral sign
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`) and a `C^∞` version **specialised to
convolutions** (`contDiffOn_convolution_right_with_param`), but no general `C^∞`
parametric-integral theorem.  The proof here follows the classical route:

* the candidate Taylor series is `parametricIntegralSeries F x m = ∫_α D_x^m(F a)(x) dμ` (a
  `FormalMultilinearSeries` with a **fixed** codomain `G`, which avoids the universe bump that
  forces the convolution proof through `ULift`);
* the derivative step `D(∫ D^m F) = ∫ D^{m+1} F` is `hasFDerivAt_parametricIntegral_iteratedFDeriv`,
  an application of the first-derivative theorem whose domination bound is a genuine constant
  supplied by continuity on the compact `α ×ˢ closedBall`;
* continuity of each series term is `continuous_parametric_integral_of_continuous`.

Assembling these into a `HasFTaylorSeriesUpTo ∞` yields `contDiff_parametricIntegral`.

The intended client is Petersen Exercise 1.6.26 (`avgMetricCompact.contMDiff`): smoothness in the
base point of the Haar average of the pullback metric over a compact-group action.

Reference: e.g. Lang, *Real and Functional Analysis*, differentiation under the integral sign.
-/

open MeasureTheory Filter Metric Set
open scoped Topology ContDiff Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace PetersenLib

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [SecondCountableTopology α] [CompactSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → E → G}

/-! ## Joint continuity of partial iterated derivatives of a jointly smooth family

A reusable analytic fact underlying the `hcont` hypothesis of the parametric-integral theorems
below: if `f : F × E → G` is jointly `C^∞`, then each order-`m` iterated derivative **in the
second variable only**, `(a, x) ↦ D_x^m (f(a, ·))(x)`, is jointly continuous in `(a, x)`.  The
partial derivative is a fixed continuous-linear reindexing of the joint iterated derivative
(`iteratedFDeriv ℝ m f`), via the affine slice `y ↦ (a, y) = (a,0) + inr y`. -/
section PartialIteratedFDeriv

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]

/-- The order-`m` partial iterated derivative in the second variable of a jointly smooth `f` is a
fixed continuous-linear reindexing of the joint iterated derivative:
`D_x^m (f(a, ·))(x) = (D^m f (a,x)).compContinuousLinearMap (fun _ => inr)`. -/
theorem iteratedFDeriv_partial_eq {f : F₁ × E₁ → G₁} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (a : F₁) (x : E₁) :
    iteratedFDeriv ℝ m (fun y => f (a, y)) x
      = (iteratedFDeriv ℝ m f (a, x)).compContinuousLinearMap
          (fun _ : Fin m => ContinuousLinearMap.inr ℝ F₁ E₁) := by
  have hc0 : ContDiff ℝ ∞ (fun _ : F₁ × E₁ => (a, (0 : E₁))) := contDiff_const
  have haff : ContDiff ℝ ∞ (fun z : F₁ × E₁ => (a, (0 : E₁)) + z) := hc0.add contDiff_id
  have hcd : ContDiff ℝ ∞ (fun z : F₁ × E₁ => f ((a, 0) + z)) := hf.comp haff
  have h1 : iteratedFDeriv ℝ m (fun y : E₁ => f (a, y)) x
      = iteratedFDeriv ℝ m ((fun z : F₁ × E₁ => f ((a, 0) + z)) ∘
          (ContinuousLinearMap.inr ℝ F₁ E₁)) x := by
    congr 1; ext y; simp
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hcd _ (by exact_mod_cast le_top)]
  congr 1
  rw [iteratedFDeriv_comp_add_left]
  congr 1
  simp

/-- **Joint continuity of the partial iterated derivative.**  For a jointly `C^∞` map
`f : F × E → G`, the order-`m` iterated derivative in the second variable,
`(a, x) ↦ D_x^m (f(a, ·))(x)`, is continuous in the pair `(a, x)`. -/
theorem continuous_iteratedFDeriv_partial {f : F₁ × E₁ → G₁} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    Continuous (fun p : F₁ × E₁ => iteratedFDeriv ℝ m (fun y => f (p.1, y)) p.2) := by
  have hrw : (fun p : F₁ × E₁ => iteratedFDeriv ℝ m (fun y => f (p.1, y)) p.2)
      = fun p => ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin m => ContinuousLinearMap.inr ℝ F₁ E₁) (iteratedFDeriv ℝ m f p) := by
    funext p
    rw [iteratedFDeriv_partial_eq hf m p.1 p.2,
      ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  rw [hrw]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin m => ContinuousLinearMap.inr ℝ F₁ E₁)).continuous.comp
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))

/-- `Set.univ ×ˢ s` is invariant under translating the first coordinate: adding a constant
`(a, 0)` moves each point within `Set.univ ×ˢ s`. -/
theorem vadd_univ_prod_eq {s : Set E₁} (a : F₁) :
    (a, (0 : E₁)) +ᵥ ((Set.univ : Set F₁) ×ˢ s) = (Set.univ : Set F₁) ×ˢ s := by
  ext ⟨u, v⟩
  simp only [Set.mem_vadd_set, Set.mem_prod, Set.mem_univ, true_and, Prod.exists,
    vadd_eq_add, Prod.mk_add_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨p, q, hq, -, hqv⟩
    rwa [← hqv, zero_add]
  · intro hv
    exact ⟨u - a, v, hv, by abel, by rw [zero_add]⟩

/-- **Open-set analogue of `iteratedFDeriv_partial_eq`.**  On the open slab `Set.univ ×ˢ s`
(with `s ⊆ E₁` open), the order-`m` iterated derivative of the partial map `y ↦ f (a, y)`
computed *within* `s` is the fixed continuous-linear reindexing of the joint iterated derivative
computed *within* `Set.univ ×ˢ s`. -/
theorem iteratedFDerivWithin_partial_eq {f : F₁ × E₁ → G₁} {s : Set E₁} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f (Set.univ ×ˢ s)) (m : ℕ) (a : F₁) {x : E₁} (hx : x ∈ s) :
    iteratedFDerivWithin ℝ m (fun y => f (a, y)) s x
      = (iteratedFDerivWithin ℝ m f (Set.univ ×ˢ s) (a, x)).compContinuousLinearMap
          (fun _ : Fin m => ContinuousLinearMap.inr ℝ F₁ E₁) := by
  have hS : IsOpen ((Set.univ : Set F₁) ×ˢ s) := isOpen_univ.prod hs
  set g : E₁ →L[ℝ] F₁ × E₁ := ContinuousLinearMap.inr ℝ F₁ E₁ with hg
  -- the translated integrand, `C^∞` on the (translation-invariant) slab
  have hmapsTo : Set.MapsTo (fun z : F₁ × E₁ => (a, (0 : E₁)) + z)
      (Set.univ ×ˢ s) (Set.univ ×ˢ s) := by
    rintro ⟨u, v⟩ hz
    simp only [Set.mem_prod, Set.mem_univ, true_and] at hz ⊢
    rwa [Prod.mk_add_mk, zero_add]
  have hcd : ContDiffOn ℝ ∞ (fun z : F₁ × E₁ => f ((a, (0 : E₁)) + z)) (Set.univ ×ˢ s) :=
    hf.comp ((contDiff_const.add contDiff_id).contDiffOn) hmapsTo
  -- the preimage of the slab under `inr` is `s`
  have hpre : g ⁻¹' (Set.univ ×ˢ s) = s := by
    ext y; simp [hg]
  have hgx : g x ∈ Set.univ ×ˢ s := by simp [hg, hx]
  have hpt : (a, (0 : E₁)) + g x = (a, x) := by simp [hg]
  -- rewrite the partial derivative as the composition with `inr`, then apply the comp-right rule
  have hcomp : (fun y : E₁ => f (a, y))
      = (fun z : F₁ × E₁ => f ((a, (0 : E₁)) + z)) ∘ g := by
    funext y; simp [hg]
  have hcr := ContinuousLinearMap.iteratedFDerivWithin_comp_right (i := m) g hcd hS.uniqueDiffOn
      (by rw [hpre]; exact hs.uniqueDiffOn) hgx (by exact_mod_cast le_top)
  rw [hpre] at hcr
  rw [hcomp, hcr]
  -- shift the base point back through the translation; the slab is translation-invariant
  rw [iteratedFDerivWithin_comp_add_left m (a, (0 : E₁)) (g x), hpt, vadd_univ_prod_eq]

/-- **Open-set analogue of `continuous_iteratedFDeriv_partial`.**  For a jointly `C^∞` map on the
open slab `Set.univ ×ˢ s`, the order-`m` iterated derivative in the second variable,
`(a, x) ↦ D_x^m (f (a, ·))(x)`, is jointly continuous on `Set.univ ×ˢ s`.  This is exactly the
`hcont` hypothesis of `contDiffOn_parametricIntegral` when the parameter derivative is only known
to be smooth on the image of a chart. -/
theorem continuousOn_iteratedFDeriv_partial {f : F₁ × E₁ → G₁} {s : Set E₁} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f (Set.univ ×ˢ s)) (m : ℕ) :
    ContinuousOn (fun p : F₁ × E₁ => iteratedFDeriv ℝ m (fun y => f (p.1, y)) p.2)
      (Set.univ ×ˢ s) := by
  have hS : IsOpen ((Set.univ : Set F₁) ×ˢ s) := isOpen_univ.prod hs
  have hinner : ContinuousOn (iteratedFDerivWithin ℝ m f (Set.univ ×ˢ s)) (Set.univ ×ˢ s) :=
    hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hS.uniqueDiffOn
  -- the joint within-derivative on the slab, reindexed by the fixed CLM `compContinuousLinearMapL`
  have hbase : ContinuousOn
      (fun p : F₁ × E₁ => ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ F₁ E₁)
        (iteratedFDerivWithin ℝ m f (Set.univ ×ˢ s) p)) (Set.univ ×ˢ s) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin m => ContinuousLinearMap.inr ℝ F₁ E₁)).continuous.comp_continuousOn hinner
  -- on the slab it agrees with the partial within-derivative, and (open `s`) with `iteratedFDeriv`
  refine hbase.congr fun p hp => ?_
  obtain ⟨a, x⟩ := p
  have hx : x ∈ s := hp.2
  rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    ← iteratedFDerivWithin_partial_eq hs hf m a hx,
    iteratedFDerivWithin_of_isOpen m hs hx]

/-- Translating the first coordinate by a constant `a` carries the **recentred slab**
`((a + ·) ⁻¹' u) ×ˢ s` onto `u ×ˢ s`.  The open-set analogue of `vadd_univ_prod_eq`, used to
transport a partial iterated derivative computed on the recentred slab back to `u ×ˢ s`. -/
theorem vadd_preimage_prod_eq {u : Set F₁} {s : Set E₁} (a : F₁) :
    (a, (0 : E₁)) +ᵥ (((fun w => a + w) ⁻¹' u) ×ˢ s) = u ×ˢ s := by
  ext ⟨p, q⟩
  simp only [Set.mem_vadd_set, Set.mem_prod, Set.mem_preimage, Prod.exists,
    vadd_eq_add, Prod.mk_add_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨w, y, ⟨hw, hy⟩, hp, hq⟩
    refine ⟨hp ▸ hw, ?_⟩
    rw [← hq, zero_add]; exact hy
  · rintro ⟨hp, hq⟩
    exact ⟨p - a, q, ⟨by rwa [add_sub_cancel], hq⟩, by abel, by rw [zero_add]⟩

/-- **Open-set analogue of `iteratedFDeriv_partial_eq` with *both* coordinates restricted.**  On
the open slab `u ×ˢ s` (both `u ⊆ F₁` and `s ⊆ E₁` open), for `a ∈ u` and `x ∈ s` the order-`m`
iterated derivative of the partial map `y ↦ f (a, y)` computed *within* `s` is the fixed
continuous-linear reindexing of the joint iterated derivative computed *within* `u ×ˢ s`.  This
generalises `iteratedFDerivWithin_partial_eq` (which fixes `u = univ`): now the parameter varies
inside an honest chart image, not all of `F₁`. -/
theorem iteratedFDerivWithin_partial_prod_eq {f : F₁ × E₁ → G₁} {u : Set F₁} {s : Set E₁}
    (hu : IsOpen u) (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f (u ×ˢ s)) (m : ℕ)
    {a : F₁} (ha : a ∈ u) {x : E₁} (hx : x ∈ s) :
    iteratedFDerivWithin ℝ m (fun y => f (a, y)) s x
      = (iteratedFDerivWithin ℝ m f (u ×ˢ s) (a, x)).compContinuousLinearMap
          (fun _ : Fin m => ContinuousLinearMap.inr ℝ F₁ E₁) := by
  set g : E₁ →L[ℝ] F₁ × E₁ := ContinuousLinearMap.inr ℝ F₁ E₁ with hg
  have hu' : IsOpen ((fun w => a + w) ⁻¹' u) := hu.preimage (continuous_const.add continuous_id)
  have hT : IsOpen (((fun w => a + w) ⁻¹' u) ×ˢ s) := hu'.prod hs
  -- the translated integrand, `C^∞` on the (recentred) slab
  have hmapsTo : Set.MapsTo (fun z : F₁ × E₁ => (a, (0 : E₁)) + z)
      (((fun w => a + w) ⁻¹' u) ×ˢ s) (u ×ˢ s) := by
    rintro ⟨w, y⟩ hz
    simp only [Set.mem_prod, Set.mem_preimage, Prod.mk_add_mk, zero_add] at hz ⊢
    exact hz
  have hcd : ContDiffOn ℝ ∞ (fun z : F₁ × E₁ => f ((a, (0 : E₁)) + z))
      (((fun w => a + w) ⁻¹' u) ×ˢ s) :=
    hf.comp ((contDiff_const.add contDiff_id).contDiffOn) hmapsTo
  -- the preimage of the recentred slab under `inr` is `s` (using `a ∈ u`, i.e. `0` is in the
  -- recentred first factor)
  have hpre : (g : E₁ → F₁ × E₁) ⁻¹' (((fun w => a + w) ⁻¹' u) ×ˢ s) = s := by
    ext y
    simp only [hg, ContinuousLinearMap.inr_apply, Set.mem_preimage, Set.mem_prod, add_zero]
    exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have hgx : g x ∈ ((fun w => a + w) ⁻¹' u) ×ˢ s := by
    simp only [hg, ContinuousLinearMap.inr_apply, Set.mem_prod, Set.mem_preimage, add_zero]
    exact ⟨ha, hx⟩
  have hpt : (a, (0 : E₁)) + g x = (a, x) := by
    simp only [hg, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  have hcomp : (fun y : E₁ => f (a, y))
      = (fun z : F₁ × E₁ => f ((a, (0 : E₁)) + z)) ∘ g := by
    funext y
    simp only [hg, Function.comp_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
      add_zero, zero_add]
  have hcr := ContinuousLinearMap.iteratedFDerivWithin_comp_right (i := m) g hcd hT.uniqueDiffOn
      (by rw [hpre]; exact hs.uniqueDiffOn) hgx (by exact_mod_cast le_top)
  rw [hpre] at hcr
  rw [hcomp, hcr,
    iteratedFDerivWithin_comp_add_left m (a, (0 : E₁)) (g x), hpt, vadd_preimage_prod_eq]

/-- **Open-set analogue of `continuousOn_iteratedFDeriv_partial` with *both* coordinates
restricted.**  For a jointly `C^∞` map on the open slab `u ×ˢ s` (both `u ⊆ F₁` and `s ⊆ E₁`
open), the order-`m` iterated derivative in the second variable, `(a, x) ↦ D_x^m (f (a, ·))(x)`,
is jointly continuous on `u ×ˢ s`.  This is the version the manifold client (Ex 1.6.26) needs:
the group parameter is only smooth on a *chart image* `u`, not on the whole model space, so the
`hcont` input of `contDiffOn_parametricIntegral` must be assembled over such a slab (then glued
across the group's chart cover, since continuity within `univ ×ˢ s` is a local property). -/
theorem continuousOn_iteratedFDeriv_partial_prod {f : F₁ × E₁ → G₁} {u : Set F₁} {s : Set E₁}
    (hu : IsOpen u) (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f (u ×ˢ s)) (m : ℕ) :
    ContinuousOn (fun p : F₁ × E₁ => iteratedFDeriv ℝ m (fun y => f (p.1, y)) p.2) (u ×ˢ s) := by
  have hS : IsOpen (u ×ˢ s) := hu.prod hs
  have hinner : ContinuousOn (iteratedFDerivWithin ℝ m f (u ×ˢ s)) (u ×ˢ s) :=
    hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hS.uniqueDiffOn
  have hbase : ContinuousOn
      (fun p : F₁ × E₁ => ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ F₁ E₁)
        (iteratedFDerivWithin ℝ m f (u ×ˢ s) p)) (u ×ˢ s) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin m => ContinuousLinearMap.inr ℝ F₁ E₁)).continuous.comp_continuousOn hinner
  refine hbase.congr fun p hp => ?_
  obtain ⟨a, x⟩ := p
  have ha : a ∈ u := hp.1
  have hx : x ∈ s := hp.2
  rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    ← iteratedFDerivWithin_partial_prod_eq hu hs hf m ha hx,
    iteratedFDerivWithin_of_isOpen m hs hx]

end PartialIteratedFDeriv

/-- The candidate formal Taylor series of the parametric integral `x ↦ ∫_α F a x dμ`: its
`m`-th term is the Bochner integral over the parameter of the order-`m` iterated derivative of
the integrand. -/
def parametricIntegralSeries (F : α → E → G) (x : E) : FormalMultilinearSeries ℝ E G :=
  fun m => ∫ a, iteratedFDeriv ℝ m (F a) x ∂μ

/-- For a fixed base point, the order-`m` derivative integrand is integrable: it is continuous
on the compact parameter space against the finite measure `μ`. -/
theorem integrable_iteratedFDeriv_apply {m : ℕ}
    (hcm : Continuous (fun p : α × E => iteratedFDeriv ℝ m (F p.1) p.2)) (x : E) :
    Integrable (fun a => iteratedFDeriv ℝ m (F a) x) μ := by
  have hc : Continuous (fun a : α => iteratedFDeriv ℝ m (F a) x) :=
    hcm.comp (continuous_id.prodMk continuous_const)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Each term of the candidate Taylor series is continuous in the base point, by continuity of
the parametric integral of a jointly continuous integrand over the compact `α`. -/
theorem continuous_parametricIntegralSeries {m : ℕ}
    (hcm : Continuous (fun p : α × E => iteratedFDeriv ℝ m (F p.1) p.2)) :
    Continuous (fun x => ∫ a, iteratedFDeriv ℝ m (F a) x ∂μ) := by
  have huncurry : Continuous (Function.uncurry (fun (x : E) (a : α) => iteratedFDeriv ℝ m (F a) x)) :=
    hcm.comp continuous_swap
  have h := continuous_parametric_integral_of_continuous (μ := μ) huncurry isCompact_univ
  simpa only [setIntegral_univ] using h

/-- **The order-`m` derivative-under-the-integral step.**  Under joint continuity of the
order-`m` and order-`(m+1)` iterated derivatives (and `C^∞`-ness of each `F a`), the parametric
integral of the order-`m` derivative is differentiable in the base point, with derivative the
`curryLeft` of the parametric integral of the order-`(m+1)` derivative — i.e. `D(∫ D^m F) =
∫ D^{m+1} F`, up to the canonical `curryLeft` identification.

**The `curryLeft`/integral commutation, done in the good instance.**  The heart of the step is
`fderiv (∫ D^m F) x = (∫ D^{m+1} F x).curryLeft`.  The naive route — pulling `curryLeft` out of a
Bochner integral `∫ (g a).curryLeft` — is blocked: on the 2-level codomain `E →L[ℝ] (E [×m]→L[ℝ] G)`,
the inner `ContinuousMultilinearMap` carries the *seminormed* instance that `.curryLeft` forces, for
which `ContinuousENorm` does not synthesize, so `Integrable (fun a => (g a).curryLeft)` cannot even
be *stated* (the "2-level CLM Bochner gotcha", verified run 0111 s0018).  We sidestep it entirely:
`hasFDerivAt_integral_of_dominated_loc_of_lip` hands back the fibre derivative `∫ a, D_x(D^m F a) x`
**together with its integrability** `hInt`, both in the *default* (`normedAddCommGroup'`) instance
path — the one place a 2-level integrand is well-formed.  The identification with the `curryLeft` is
then discharged **pointwise**: `((∫ D_x(D^m F)) v) w = ∫ D^{m+1} F x (v ::ᵥ w) = ((∫ D^{m+1} F).curryLeft v) w`,
using only `ContinuousLinearMap.integral_apply hInt` / `ContinuousMultilinearMap.integral_apply`
(evaluation past the integral in the good instance) and `hfderiv_eq` / `curryLeft_apply`, never
integrating a freshly-stated `curryLeft`-valued family. -/
theorem hasFDerivAt_parametricIntegral_iteratedFDeriv {m : ℕ}
    (hdiff : ∀ a, ContDiff ℝ ∞ (F a))
    (hcm : Continuous (fun p : α × E => iteratedFDeriv ℝ m (F p.1) p.2))
    (hcm1 : Continuous (fun p : α × E => iteratedFDeriv ℝ (m + 1) (F p.1) p.2))
    (x : E) :
    HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ m (F a) y ∂μ)
      ((∫ a, iteratedFDeriv ℝ (m + 1) (F a) x ∂μ).curryLeft) x := by
  -- per-parameter: `iteratedFDeriv^m (F a)` is differentiable with derivative the `curryLeft` of
  -- the next iterate, from the finite Taylor expansion of the smooth `F a`.
  have htaylor : ∀ a : α, ∀ y : E,
      HasFDerivAt (fun z => iteratedFDeriv ℝ m (F a) z)
        ((iteratedFDeriv ℝ (m + 1) (F a) y).curryLeft) y := by
    intro a y
    have hcd : ContDiff ℝ (m + 1 : ℕ) (F a) := (hdiff a).of_le (by exact_mod_cast le_top)
    have h := hcd.ftaylorSeries.fderiv m (by exact_mod_cast Nat.lt_succ_self m) y
    simpa only [ftaylorSeries] using h
  have hfderiv_eq : ∀ a : α, ∀ y : E,
      fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y
        = (iteratedFDeriv ℝ (m + 1) (F a) y).curryLeft :=
    fun a y => (htaylor a y).fderiv
  -- the fibre derivative's norm equals the next iterate's norm (`curryLeft` is an isometry).
  have hnorm : ∀ a : α, ∀ y : E,
      ‖fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y‖
        = ‖iteratedFDeriv ℝ (m + 1) (F a) y‖ := fun a y => by
    rw [hfderiv_eq a y]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) G).norm_map _
  -- a uniform bound on the order-`(m+1)` derivative over the compact `α ×ˢ closedBall x 1`
  obtain ⟨C, hC⟩ : ∃ C, ∀ a : α, ∀ y ∈ closedBall x 1,
      ‖iteratedFDeriv ℝ (m + 1) (F a) y‖ ≤ C := by
    have hK : IsCompact ((univ : Set α) ×ˢ closedBall x 1) :=
      isCompact_univ.prod (isCompact_closedBall x 1)
    obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn hcm1.continuousOn
    exact ⟨C, fun a y hy => hCb (a, y) ⟨mem_univ a, hy⟩⟩
  -- assemble the hypotheses of `hasFDerivAt_integral_of_dominated_loc_of_lip`
  have hF_meas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ m (F a) y) μ := by
    filter_upwards with y
    exact (hcm.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hF_int : Integrable (fun a => iteratedFDeriv ℝ m (F a) x) μ :=
    integrable_iteratedFDeriv_apply hcm x
  have hF'_meas : AEStronglyMeasurable
      (fun a => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x) μ := by
    rw [show (fun a => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x)
          = (fun a => (iteratedFDeriv ℝ (m + 1) (F a) x).curryLeft) from
        funext fun a => hfderiv_eq a x]
    exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) G).isometry.continuous.comp
      (hcm1.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  -- local Lipschitz bound (radius `1`), from the fderiv bound via convexity.
  have h_lip : ∀ᵐ a ∂μ,
      LipschitzOnWith (Real.nnabs C) (fun z => iteratedFDeriv ℝ m (F a) z) (ball x 1) := by
    filter_upwards with a
    refine (convex_ball x 1).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := fun y => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y)
      (fun y _ => (htaylor a y).differentiableAt.hasFDerivAt.hasFDerivWithinAt) fun y hy => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, hnorm a y]
    exact (hC a y (ball_subset_closedBall hy)).trans (le_abs_self C)
  have h_diff_at : ∀ᵐ a ∂μ, HasFDerivAt (fun z => iteratedFDeriv ℝ m (F a) z)
      (fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x) x := by
    filter_upwards with a
    exact (htaylor a x).differentiableAt.hasFDerivAt
  -- `hasFDerivAt_integral_of_dominated_loc_of_lip` gives BOTH integrability of the fibre derivative
  -- (`hInt`, in the good instance) and the derivative-under-integral (`hFD`).
  obtain ⟨hInt, hFD⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (F := fun y a => iteratedFDeriv ℝ m (F a) y)
    (F' := fun a => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x)
    (bound := fun _ => C) (x₀ := x) (s := ball x 1)
    (ball_mem_nhds x one_pos) hF_meas hF_int hF'_meas h_lip (integrable_const C) h_diff_at
  have hint : Integrable (fun a => iteratedFDeriv ℝ (m + 1) (F a) x) μ :=
    integrable_iteratedFDeriv_apply hcm1 x
  -- pointwise identification `∫ D_x(D^m F) = (∫ D^{m+1} F).curryLeft`, all in the good instance.
  have hEq : (∫ a, fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x ∂μ)
      = (∫ a, iteratedFDeriv ℝ (m + 1) (F a) x ∂μ).curryLeft := by
    refine ContinuousLinearMap.ext fun v => ContinuousMultilinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.integral_apply hInt,
      ContinuousMultilinearMap.integral_apply (hInt.apply_continuousLinearMap v),
      ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.integral_apply hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hfderiv_eq a x, ContinuousMultilinearMap.curryLeft_apply]
  rw [hEq] at hFD
  exact hFD

/-- **`C^∞` parametric Bochner integral (compact parameter space).**  If each `F a : E → G` is
`C^∞` and every order-`m` iterated `x`-derivative `(a, x) ↦ D_x^m(F a)(x)` is jointly continuous
over the compact parameter space `α`, then the average `x ↦ ∫_α F a x dμ(a)` is `C^∞`.

This is the general parametric-integral smoothness theorem Mathlib is missing (it has only the
first derivative and a convolution-specific `C^∞` version). -/
theorem contDiff_parametricIntegral
    (hdiff : ∀ a, ContDiff ℝ ∞ (F a))
    (hcont : ∀ m : ℕ, Continuous (fun p : α × E => iteratedFDeriv ℝ m (F p.1) p.2)) :
    ContDiff ℝ ∞ (fun x => ∫ a, F a x ∂μ) := by
  have htaylor : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, F a x ∂μ)
      (parametricIntegralSeries (μ := μ) F) := by
    refine ⟨?_, ?_, ?_⟩
    · -- `zero_eq`: the 0-th term evaluates (curry0) to the integral itself.  Evaluation of a
      -- continuous multilinear map commutes with the Bochner integral.
      intro x
      show (∫ a, iteratedFDeriv ℝ 0 (F a) x ∂μ).curry0 = ∫ a, F a x ∂μ
      rw [ContinuousMultilinearMap.curry0_apply,
        ContinuousMultilinearMap.integral_apply (integrable_iteratedFDeriv_apply (hcont 0) x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      simp only [iteratedFDeriv_zero_apply]
    · -- `fderiv`: the derivative step
      intro m _ x
      exact hasFDerivAt_parametricIntegral_iteratedFDeriv hdiff (hcont m) (hcont (m + 1)) x
    · -- `cont`: continuity of each term
      intro m _
      exact continuous_parametricIntegralSeries (hcont m)
  exact htaylor.contDiff

/-! ## Local (open-set) version

The manifold client (Ex 1.6.26) can only produce the smoothness/joint-continuity hypotheses on
the image of a chart — an **open subset** `s ⊆ E`, not all of `E` — because the coordinate
representation of a bundle section is only honest inside the trivialisation's base set.  The
following open-set version of the theorem is what applies there: on an open `s`, `ContDiffOn`
smoothness of each `F a` plus joint continuity of the iterated derivatives over `α ×ˢ s` gives
`ContDiffOn` smoothness of the average.  On the open `s` all the `iteratedFDerivWithin` reduce to
plain `iteratedFDeriv`, so the proof reuses the global derivative-under-the-integral step almost
verbatim, only shrinking the domination ball to a `closedBall x r ⊆ s`. -/

/-- **The order-`m` derivative-under-the-integral step, on an open set.**  Local analogue of
`hasFDerivAt_parametricIntegral_iteratedFDeriv`: for `x` in the open set `s`, under `C^∞`-ness of
each `F a` on `s` and joint continuity of the order-`m`/`(m+1)` iterated `x`-derivatives over
`α ×ˢ s`, the parametric integral of the order-`m` derivative is differentiable at `x`, with
derivative `(∫ D^{m+1} F x).curryLeft`.  The finite Taylor expansion is read off `ftaylorSeriesWithin`
(`iteratedFDerivWithin` collapses to `iteratedFDeriv` on the open `s`) and the domination bound is a
constant on a `closedBall x r ⊆ s`. -/
theorem hasFDerivAt_parametricIntegral_iteratedFDeriv_on {s : Set E} (hs : IsOpen s) {m : ℕ}
    (hdiff : ∀ a, ContDiffOn ℝ ∞ (F a) s)
    (hcm : ContinuousOn (fun p : α × E => iteratedFDeriv ℝ m (F p.1) p.2) (univ ×ˢ s))
    (hcm1 : ContinuousOn (fun p : α × E => iteratedFDeriv ℝ (m + 1) (F p.1) p.2) (univ ×ˢ s))
    {x : E} (hx : x ∈ s) :
    HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ m (F a) y ∂μ)
      ((∫ a, iteratedFDeriv ℝ (m + 1) (F a) x ∂μ).curryLeft) x := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  set r := ε / 2 with hr
  have hrpos : 0 < r := by positivity
  have hcball : closedBall x r ⊆ s :=
    (Metric.closedBall_subset_ball (by rw [hr]; linarith)).trans hball
  have hballr : ball x r ⊆ s := ball_subset_closedBall.trans hcball
  -- per-parameter finite Taylor expansion, valid at every `y ∈ s`.
  have htaylor : ∀ a : α, ∀ y ∈ s, HasFDerivAt (fun z => iteratedFDeriv ℝ m (F a) z)
        ((iteratedFDeriv ℝ (m + 1) (F a) y).curryLeft) y := by
    intro a y hy
    have hcd : ContDiffOn ℝ (m + 1 : ℕ) (F a) s := (hdiff a).of_le (by exact_mod_cast le_top)
    have hft := hcd.ftaylorSeriesWithin hs.uniqueDiffOn
    have hfw := hft.fderivWithin m (by exact_mod_cast Nat.lt_succ_self m) y hy
    have hEqOn : Set.EqOn (fun z => ftaylorSeriesWithin ℝ (F a) s z m)
        (fun z => iteratedFDeriv ℝ m (F a) z) s :=
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := F a) m hs
    have hval : (ftaylorSeriesWithin ℝ (F a) s y (m + 1)).curryLeft
        = (iteratedFDeriv ℝ (m + 1) (F a) y).curryLeft := by
      rw [show ftaylorSeriesWithin ℝ (F a) s y (m + 1) = iteratedFDerivWithin ℝ (m + 1) (F a) s y
            from rfl, iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := F a) (m + 1) hs hy]
    rw [hval] at hfw
    exact (hfw.hasFDerivAt (hs.mem_nhds hy)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hs.mem_nhds hy) hEqOn.symm)
  have hfderiv_eq : ∀ a : α, ∀ y ∈ s,
      fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y
        = (iteratedFDeriv ℝ (m + 1) (F a) y).curryLeft :=
    fun a y hy => (htaylor a y hy).fderiv
  have hnorm : ∀ a : α, ∀ y ∈ s,
      ‖fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y‖
        = ‖iteratedFDeriv ℝ (m + 1) (F a) y‖ := fun a y hy => by
    rw [hfderiv_eq a y hy]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) G).norm_map _
  -- a uniform bound on the order-`(m+1)` derivative over the compact `α ×ˢ closedBall x r ⊆ s`.
  obtain ⟨C, hC⟩ : ∃ C, ∀ a : α, ∀ y ∈ closedBall x r,
      ‖iteratedFDeriv ℝ (m + 1) (F a) y‖ ≤ C := by
    have hK : IsCompact ((univ : Set α) ×ˢ closedBall x r) :=
      isCompact_univ.prod (isCompact_closedBall x r)
    have hmono : (univ : Set α) ×ˢ closedBall x r ⊆ univ ×ˢ s := prod_mono subset_rfl hcball
    obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn (hcm1.mono hmono)
    exact ⟨C, fun a y hy => hCb (a, y) ⟨mem_univ a, hy⟩⟩
  -- continuity in the parameter at a fixed base point `y ∈ s`.
  have hcont_a : ∀ y ∈ s, Continuous (fun a : α => iteratedFDeriv ℝ m (F a) y) := fun y hy =>
    hcm.comp_continuous (continuous_id.prodMk continuous_const) (fun a => ⟨mem_univ a, hy⟩)
  have hcont_a1 : ∀ y ∈ s, Continuous (fun a : α => iteratedFDeriv ℝ (m + 1) (F a) y) := fun y hy =>
    hcm1.comp_continuous (continuous_id.prodMk continuous_const) (fun a => ⟨mem_univ a, hy⟩)
  have hF_meas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ m (F a) y) μ := by
    filter_upwards [ball_mem_nhds x hrpos] with y hy
    exact (hcont_a y (hballr hy)).aestronglyMeasurable
  have hF_int : Integrable (fun a => iteratedFDeriv ℝ m (F a) x) μ :=
    (hcont_a x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hF'_meas : AEStronglyMeasurable
      (fun a => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x) μ := by
    rw [show (fun a => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x)
          = (fun a => (iteratedFDeriv ℝ (m + 1) (F a) x).curryLeft) from
        funext fun a => hfderiv_eq a x hx]
    exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) G).isometry.continuous.comp
      (hcont_a1 x hx)).aestronglyMeasurable
  have h_lip : ∀ᵐ a ∂μ,
      LipschitzOnWith (Real.nnabs C) (fun z => iteratedFDeriv ℝ m (F a) z) (ball x r) := by
    filter_upwards with a
    refine (convex_ball x r).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := fun y => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y)
      (fun y hy => (htaylor a y (hballr hy)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
      fun y hy => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, hnorm a y (hballr hy)]
    exact (hC a y (ball_subset_closedBall hy)).trans (le_abs_self C)
  have h_diff_at : ∀ᵐ a ∂μ, HasFDerivAt (fun z => iteratedFDeriv ℝ m (F a) z)
      (fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x) x := by
    filter_upwards with a
    exact (htaylor a x hx).differentiableAt.hasFDerivAt
  obtain ⟨hInt, hFD⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip (μ := μ)
    (F := fun y a => iteratedFDeriv ℝ m (F a) y)
    (F' := fun a => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x)
    (bound := fun _ => C) (x₀ := x) (s := ball x r)
    (ball_mem_nhds x hrpos) hF_meas hF_int hF'_meas h_lip (integrable_const C) h_diff_at
  have hint : Integrable (fun a => iteratedFDeriv ℝ (m + 1) (F a) x) μ :=
    (hcont_a1 x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hEq : (∫ a, fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x ∂μ)
      = (∫ a, iteratedFDeriv ℝ (m + 1) (F a) x ∂μ).curryLeft := by
    refine ContinuousLinearMap.ext fun v => ContinuousMultilinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.integral_apply hInt,
      ContinuousMultilinearMap.integral_apply (hInt.apply_continuousLinearMap v),
      ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.integral_apply hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hfderiv_eq a x hx, ContinuousMultilinearMap.curryLeft_apply]
  rw [hEq] at hFD
  exact hFD

/-- **`C^∞` parametric Bochner integral over an open set (compact parameter space).**  If each
`F a : E → G` is `C^∞` on the open set `s` and every order-`m` iterated `x`-derivative
`(a, x) ↦ D_x^m(F a)(x)` is jointly continuous over `α ×ˢ s`, then `x ↦ ∫_α F a x dμ(a)` is `C^∞`
on `s`.  This is the version the manifold client applies on a chart's (open) image; the
`fderivWithin` and `cont` fields of the Taylor series both come from the single derivative-step
lemma `hasFDerivAt_parametricIntegral_iteratedFDeriv_on`. -/
theorem contDiffOn_parametricIntegral {s : Set E} (hs : IsOpen s)
    (hdiff : ∀ a, ContDiffOn ℝ ∞ (F a) s)
    (hcont : ∀ m : ℕ, ContinuousOn (fun p : α × E => iteratedFDeriv ℝ m (F p.1) p.2) (univ ×ˢ s)) :
    ContDiffOn ℝ ∞ (fun x => ∫ a, F a x ∂μ) s := by
  have hintg : ∀ (m : ℕ), ∀ x ∈ s, Integrable (fun a => iteratedFDeriv ℝ m (F a) x) μ := by
    intro m x hx
    have hc : Continuous (fun a : α => iteratedFDeriv ℝ m (F a) x) :=
      (hcont m).comp_continuous (continuous_id.prodMk continuous_const) (fun a => ⟨mem_univ a, hx⟩)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have htaylor : HasFTaylorSeriesUpToOn ∞ (fun x => ∫ a, F a x ∂μ)
      (parametricIntegralSeries (μ := μ) F) s := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      show (∫ a, iteratedFDeriv ℝ 0 (F a) x ∂μ).curry0 = ∫ a, F a x ∂μ
      rw [ContinuousMultilinearMap.curry0_apply,
        ContinuousMultilinearMap.integral_apply (hintg 0 x hx)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun a => by
        simp only [iteratedFDeriv_zero_apply])
    · intro m _ x hx
      exact (hasFDerivAt_parametricIntegral_iteratedFDeriv_on hs hdiff (hcont m)
        (hcont (m + 1)) hx).hasFDerivWithinAt
    · intro m _ x hx
      exact (hasFDerivAt_parametricIntegral_iteratedFDeriv_on hs hdiff (hcont m)
        (hcont (m + 1)) hx).continuousAt.continuousWithinAt
  exact htaylor.contDiffOn

end PetersenLib
