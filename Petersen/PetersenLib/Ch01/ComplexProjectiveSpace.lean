import PetersenLib.Ch01.HomogeneousMetrics
import PetersenLib.Ch01.SphereRadialProjection
import PetersenLib.Ch01.SphereCodRestrictLocal
import PetersenLib.Foundations.LocalSection

/-!
# Complex projective space as a smooth manifold, and the Fubini–Study metric

Petersen's Example 1.3.4 introduces the Fubini–Study metric as the unique metric on
`ℂPⁿ = S^{2n+1}/S¹` making the Hopf projection a Riemannian submersion.  The statement
`PetersenLib.fubiniStudyMetric` (`PetersenLib.Ch01.HomogeneousMetrics`) proves this, but it
takes the quotient manifold and the projection as *hypotheses*, because Mathlib's
`Projectivization` carries no smooth structure and Mathlib has no quotient-manifold theorem.

This file removes that hypothesis: it **constructs** `ℂPⁿ` as a smooth manifold and discharges
all four hypotheses of `fubiniStudyMetric` for the genuine Hopf projection.

## Main definitions

* `ComplexProjectiveSpace n` — `ℂPⁿ`, the orbit space of the unit sphere `S^{2n+1} ⊆ ℂ^{n+1}`
  under the scalar action of `Circle`, with the quotient topology.  The quotient map is open
  (`MulAction.isOpenQuotientMap_quotientMk`), which is what makes the charts continuous.
* `projSphere : S^{2n+1} → ℂPⁿ` — the Hopf projection.
* `affineCoord i` / `chartInv i` — the `i`-th affine coordinate map `[z] ↦ (z_{σ j}/z_i)_j` and
  its inverse `w ↦ [1 : w]` (normalized to the sphere), for `i : Fin (n+1)`.
* `chartCP i : OpenPartialHomeomorph (ℂPⁿ) (Fin n → ℂ)` — the resulting chart, with source the
  open set `{[z] | z_i ≠ 0}` and target all of `ℂⁿ`.

## Main results

* `instChartedSpaceComplexProjectiveSpace` — the `n+1` affine charts cover `ℂPⁿ`.
* `instIsManifoldComplexProjectiveSpace` — `ℂPⁿ` is a `C^∞` real manifold: the transition maps
  `w ↦ (v_{σ k}/v_j)_k` with `v = insertNth i 1 w` are rational with nonvanishing denominator.
* `contMDiff_projSphere`, `surjective_projSphere`, `surjective_mfderiv_projSphere`,
  `projSphere_eq_iff` — the Hopf projection is a smooth surjective submersion whose fibres are
  exactly the circle orbits.  Surjectivity of the differential comes from an **explicit smooth
  local section** through each point (`localSection`), fed to
  `PetersenLib.mfderiv_localSection_eq_symm`.
* `fubiniStudyMetricComplexProjectiveSpace` — Petersen Example 1.3.4 on the genuine `ℂPⁿ`:
  there is a *unique* Riemannian metric on `ℂPⁿ` making `S^{2n+1} → ℂPⁿ` a Riemannian
  submersion.

The computation that makes the charts work is `coe_unitSphereProj_smul`: for `c ≠ 0` the radial
projections of `c • v` and of `v` differ by the unit scalar `c/‖c‖ ∈ S¹`, hence agree in `ℂPⁿ`.
Everything is done *coordinatewise* to avoid the `Module ℝ (EuclideanSpace ℂ (Fin m))` diamond
documented in `PetersenLib.Ch01.HopfSphereSubmersion`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Example 1.3.4 and Example 1.4.14.
-/

open Metric Module Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace PetersenLib

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin (n + 1))

/-! ## The circle action and the orbit space -/

instance instContinuousConstSMulCircleSphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] : ContinuousConstSMul Circle (sphere (0 : E) 1) :=
  inferInstanceAs <| ContinuousConstSMul (sphere (0 : ℂ) 1) (sphere (0 : E) 1)

/-- **Math.** Complex projective space `ℂPⁿ`, realized as the orbit space `S^{2n+1}/S¹` of the
unit sphere of `ℂ^{n+1}` under the scalar action of the circle (Petersen, Example 1.3.4). -/
abbrev ComplexProjectiveSpace (n : ℕ) : Type :=
  Quotient (MulAction.orbitRel Circle (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1))

/-- **Math.** The Hopf projection `S^{2n+1} → ℂPⁿ`, `z ↦ [z]`. -/
def projSphere (z : sphere (0 : 𝔼) 1) : ComplexProjectiveSpace n :=
  Quotient.mk (MulAction.orbitRel Circle (sphere (0 : 𝔼) 1)) z

theorem isOpenQuotientMap_projSphere :
    IsOpenQuotientMap (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem isQuotientMap_projSphere :
    Topology.IsQuotientMap (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) :=
  isOpenQuotientMap_projSphere.isOpenMap.isQuotientMap
    isOpenQuotientMap_projSphere.continuous isOpenQuotientMap_projSphere.surjective

theorem continuous_projSphere :
    Continuous (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) :=
  isOpenQuotientMap_projSphere.continuous

theorem surjective_projSphere :
    Function.Surjective (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) :=
  isOpenQuotientMap_projSphere.surjective

/-- **Math.** The fibres of the Hopf projection are exactly the circle orbits. -/
theorem projSphere_eq_iff (z z' : sphere (0 : 𝔼) 1) :
    projSphere z = projSphere z' ↔ ∃ a : Circle, a • z = z' := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
    exact ⟨a⁻¹, by rw [← ha, inv_smul_smul]⟩
  · rintro ⟨a, rfl⟩
    exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨a⁻¹, inv_smul_smul a z⟩)

theorem projSphere_circle_smul (a : Circle) (z : sphere (0 : 𝔼) 1) :
    projSphere (a • z) = projSphere z :=
  (projSphere_eq_iff _ _).mpr ⟨a⁻¹, inv_smul_smul a z⟩

/-! ## Homogeneous coordinates -/

theorem coe_circle_smul_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : Circle) (z : sphere (0 : E) 1) :
    ((a • z : sphere (0 : E) 1) : E) = (a : ℂ) • (z : E) := rfl

theorem circle_coe_ne_zero (a : Circle) : (a : ℂ) ≠ 0 := by
  intro h
  have h1 := Circle.norm_coe a
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-! ### Coordinatewise scalar multiplication

The `ℝ`-action on `EuclideanSpace ℂ (Fin m)` is the restriction-of-scalars one, *not* the
`PiLp` one, so `PiLp.smul_apply` does **not** apply to a real scalar there (this is the diamond
recorded in `PetersenLib.Ch01.HopfSphereSubmersion`).  These two lemmas are the only interface
we use. -/

theorem euclidean_complex_smul_apply (c : ℂ) (v : 𝔼) (k : Fin (n + 1)) :
    (c • v) k = c * v k := by simp

theorem euclidean_real_smul_apply (r : ℝ) (v : 𝔼) (k : Fin (n + 1)) :
    (r • v) k = (r : ℂ) * v k := by
  simp only [WithLp.ofLp_smul, Pi.smul_apply]
  exact Complex.real_smul

/-! ### Complex-valued division is real-smooth

`ContDiff*.div` in Mathlib requires the codomain to *be* the base field; here the base field is
`ℝ` and the codomain is `ℂ`, so we go through `inv` and `mul`, which do allow a normed algebra
codomain. -/

theorem ContDiffAt.div_complex {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : F → ℂ} {x : F} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (hx : g x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => f y / g y) x := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hx)

theorem ContDiffOn.div_complex {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : F → ℂ} {s : Set F} (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s)
    (hx : ∀ y ∈ s, g y ≠ 0) : ContDiffOn ℝ ∞ (fun y => f y / g y) s := fun y hy => by
  simpa only [div_eq_mul_inv] using (hf y hy).mul ((hg y hy).inv (hx y hy))

/-- The `i`-th affine coordinate of a representative: `z ↦ (z_{σ j}/z_i)_j`. -/
def affineCoordAux (i : Fin (n + 1)) (z : sphere (0 : 𝔼) 1) : Fin n → ℂ :=
  fun j => (z : 𝔼) (i.succAbove j) / (z : 𝔼) i

theorem affineCoordAux_circle_smul (i : Fin (n + 1)) (a : Circle) (z : sphere (0 : 𝔼) 1) :
    affineCoordAux i (a • z) = affineCoordAux i z := by
  funext j
  simp only [affineCoordAux, coe_circle_smul_sphere, euclidean_complex_smul_apply]
  exact mul_div_mul_left _ _ (circle_coe_ne_zero a)

/-- **Math.** The `i`-th affine coordinate map on `ℂPⁿ`, `[z] ↦ (z_{σ j}/z_i)_j`.  It is
scale-invariant, hence well defined on the quotient (off the source it returns junk zeros,
which is harmless: the chart only uses it on `{z_i ≠ 0}`). -/
def affineCoord (i : Fin (n + 1)) : ComplexProjectiveSpace n → Fin n → ℂ :=
  Quotient.lift (affineCoordAux i) <| by
    intro z z' h
    obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.mp h
    rw [← ha, affineCoordAux_circle_smul]

@[simp] theorem affineCoord_projSphere (i : Fin (n + 1)) (z : sphere (0 : 𝔼) 1) :
    affineCoord i (projSphere z) = affineCoordAux i z := rfl

/-- The scale-invariant predicate "the `i`-th homogeneous coordinate is nonzero". -/
def CoordNe (i : Fin (n + 1)) : ComplexProjectiveSpace n → Prop :=
  Quotient.lift (fun z : sphere (0 : 𝔼) 1 => (z : 𝔼) i ≠ 0) <| by
    intro z z' h
    obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.mp h
    rw [← ha]
    simp only [coe_circle_smul_sphere, euclidean_complex_smul_apply, eq_iff_iff]
    exact ⟨fun hne => fun hz' => hne (by rw [hz', mul_zero]),
      fun hne => mul_ne_zero (circle_coe_ne_zero a) hne⟩

/-- The source of the `i`-th affine chart: `{[z] | z_i ≠ 0}`. -/
def chartSource (i : Fin (n + 1)) : Set (ComplexProjectiveSpace n) := {p | CoordNe i p}

theorem mem_chartSource_projSphere {i : Fin (n + 1)} {z : sphere (0 : 𝔼) 1} :
    projSphere z ∈ chartSource i ↔ (z : 𝔼) i ≠ 0 := Iff.rfl

theorem continuous_sphere_coord (i : Fin (n + 1)) :
    Continuous fun z : sphere (0 : 𝔼) 1 => (z : 𝔼) i :=
  (EuclideanSpace.proj i).continuous.comp continuous_subtype_val

theorem isOpen_sphere_coord_ne (i : Fin (n + 1)) :
    IsOpen {z : sphere (0 : 𝔼) 1 | (z : 𝔼) i ≠ 0} :=
  isOpen_compl_singleton.preimage (continuous_sphere_coord i)

theorem preimage_chartSource (i : Fin (n + 1)) :
    (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) ⁻¹' chartSource i
      = {z : sphere (0 : 𝔼) 1 | (z : 𝔼) i ≠ 0} := rfl

theorem isOpen_chartSource (i : Fin (n + 1)) :
    IsOpen (chartSource i : Set (ComplexProjectiveSpace n)) := by
  rw [← isQuotientMap_projSphere.isOpen_preimage, preimage_chartSource]
  exact isOpen_sphere_coord_ne i

/-! ## The chart inverse -/

instance instNontrivialEuclideanComplex : Nontrivial 𝔼 := by
  refine ⟨0, WithLp.toLp 2 (fun _ => 1), fun h => ?_⟩
  have := congrArg (fun v : 𝔼 => v 0) h
  simp at this

/-- The affine lift `ℂⁿ → ℂ^{n+1}`, `w ↦ [1 : w]` with the `1` in slot `i`. -/
def affineLift (i : Fin (n + 1)) (w : Fin n → ℂ) : 𝔼 := WithLp.toLp 2 (Fin.insertNth i 1 w)

@[simp] theorem affineLift_apply_same (i : Fin (n + 1)) (w : Fin n → ℂ) :
    affineLift i w i = 1 := by
  simp [affineLift, Fin.insertNth_apply_same]

@[simp] theorem affineLift_apply_succAbove (i : Fin (n + 1)) (w : Fin n → ℂ) (j : Fin n) :
    affineLift i w (i.succAbove j) = w j := by
  simp [affineLift, Fin.insertNth_apply_succAbove]

theorem affineLift_ne_zero (i : Fin (n + 1)) (w : Fin n → ℂ) : affineLift i w ≠ 0 := by
  intro h
  have h1 : affineLift i w i = 0 := by rw [h]; simp
  rw [affineLift_apply_same] at h1
  exact one_ne_zero h1

theorem norm_affineLift_ne_zero (i : Fin (n + 1)) (w : Fin n → ℂ) :
    ((‖affineLift i w‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
  have h : ‖affineLift i w‖ ≠ 0 := norm_ne_zero_iff.mpr (affineLift_ne_zero i w)
  simpa using inv_ne_zero h

/-- Coordinates of the radial projection.  Stated separately because the `ℝ`-action used by
`unitSphereProj` comes from the `InnerProductSpace ℝ 𝔼` instance, whose `SMul ℝ 𝔼` is *not*
syntactically the `PiLp` one — so `rw` with a coordinate lemma fails and we let `simp` bridge. -/
theorem coe_unitSphereProj_apply (v : 𝔼) (hv : v ≠ 0) (k : Fin (n + 1)) :
    ((unitSphereProj v : sphere (0 : 𝔼) 1) : 𝔼) k = ((‖v‖⁻¹ : ℝ) : ℂ) * v k := by
  rw [coe_unitSphereProj hv]
  simp only [WithLp.ofLp_smul, Pi.smul_apply]
  exact Complex.real_smul

/-- **Math.** The radial projections of `c • v` and of `v` differ by the unit scalar `c/‖c‖`. -/
theorem coe_unitSphereProj_smul (c : ℂ) (hc : c ≠ 0) (v : 𝔼) (hv : v ≠ 0) (k : Fin (n + 1)) :
    ((unitSphereProj (c • v) : sphere (0 : 𝔼) 1) : 𝔼) k
      = (c / (‖c‖ : ℂ)) * (((unitSphereProj v : sphere (0 : 𝔼) 1) : 𝔼) k) := by
  have hcv : c • v ≠ 0 := smul_ne_zero hc hv
  have hcn' : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hc)
  have hvn' : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hv)
  rw [coe_unitSphereProj_apply _ hcv, coe_unitSphereProj_apply _ hv,
    euclidean_complex_smul_apply, norm_smul]
  push_cast
  field_simp

/-- **Math.** `ℂ`-collinear nonzero vectors define the same point of `ℂPⁿ`. -/
theorem projSphere_unitSphereProj_smul (c : ℂ) (hc : c ≠ 0) (v : 𝔼) (hv : v ≠ 0) :
    projSphere (unitSphereProj (c • v)) = projSphere (unitSphereProj v) := by
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have ha : ‖c / (‖c‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg c),
      div_self hcn]
  refine ((projSphere_eq_iff _ _).mpr
    ⟨(⟨c / (‖c‖ : ℂ), mem_sphere_zero_iff_norm.mpr ha⟩ : Circle), ?_⟩).symm
  apply Subtype.ext
  rw [coe_circle_smul_sphere]
  refine PiLp.ext fun k => ?_
  rw [euclidean_complex_smul_apply]
  exact (coe_unitSphereProj_smul c hc v hv k).symm

theorem unitSphereProj_coe (z : sphere (0 : 𝔼) 1) : unitSphereProj (z : 𝔼) = z := by
  have hn : ‖(z : 𝔼)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have hz : (z : 𝔼) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  apply Subtype.ext
  rw [coe_unitSphereProj hz, hn]
  simp

/-- The chart inverse, at the level of the sphere: `w ↦ [1 : w]/‖[1 : w]‖`. -/
def chartInvSphere (i : Fin (n + 1)) (w : Fin n → ℂ) : sphere (0 : 𝔼) 1 :=
  unitSphereProj (affineLift i w)

/-- **Math.** The inverse of the `i`-th affine chart: `w ↦ [1 : w]`. -/
def chartInv (i : Fin (n + 1)) (w : Fin n → ℂ) : ComplexProjectiveSpace n :=
  projSphere (chartInvSphere i w)

theorem coe_chartInvSphere (i : Fin (n + 1)) (w : Fin n → ℂ) (k : Fin (n + 1)) :
    ((chartInvSphere i w : sphere (0 : 𝔼) 1) : 𝔼) k
      = ((‖affineLift i w‖⁻¹ : ℝ) : ℂ) * affineLift i w k := by
  rw [chartInvSphere, coe_unitSphereProj_apply _ (affineLift_ne_zero i w)]

theorem chartInvSphere_coord_ne_zero (i : Fin (n + 1)) (w : Fin n → ℂ) :
    ((chartInvSphere i w : sphere (0 : 𝔼) 1) : 𝔼) i ≠ 0 := by
  rw [coe_chartInvSphere, affineLift_apply_same, mul_one]
  exact norm_affineLift_ne_zero i w

theorem chartInv_mem_chartSource (i : Fin (n + 1)) (w : Fin n → ℂ) :
    chartInv i w ∈ chartSource i :=
  chartInvSphere_coord_ne_zero i w

theorem chartInvSphere_coord_ne_zero_iff (i j : Fin (n + 1)) (w : Fin n → ℂ) :
    ((chartInvSphere i w : sphere (0 : 𝔼) 1) : 𝔼) j ≠ 0 ↔ affineLift i w j ≠ 0 := by
  rw [coe_chartInvSphere]
  exact mul_ne_zero_iff.trans
    ⟨fun h => h.2, fun h => ⟨norm_affineLift_ne_zero i w, h⟩⟩

theorem chartInv_mem_chartSource_iff (i j : Fin (n + 1)) (w : Fin n → ℂ) :
    chartInv i w ∈ chartSource j ↔ affineLift i w j ≠ 0 :=
  chartInvSphere_coord_ne_zero_iff i j w

/-- The `j`-th affine coordinates of `[1 : w]` form a rational function of `w`. -/
theorem affineCoord_chartInv (i j : Fin (n + 1)) (w : Fin n → ℂ) :
    affineCoord j (chartInv i w)
      = fun k => affineLift i w (j.succAbove k) / affineLift i w j := by
  funext k
  simp only [chartInv, affineCoord_projSphere, affineCoordAux, coe_chartInvSphere]
  exact mul_div_mul_left _ _ (norm_affineLift_ne_zero i w)

/-- Right inverse: the `i`-th affine chart recovers `w` from `[1 : w]`. -/
theorem affineCoord_chartInv_self (i : Fin (n + 1)) (w : Fin n → ℂ) :
    affineCoord i (chartInv i w) = w := by
  rw [affineCoord_chartInv]
  funext k
  rw [affineLift_apply_same, affineLift_apply_succAbove, div_one]

/-- The affine lift of the affine coordinates of `z` is `z_i⁻¹ • z`. -/
theorem affineLift_affineCoordAux (i : Fin (n + 1)) (z : sphere (0 : 𝔼) 1)
    (hz : (z : 𝔼) i ≠ 0) :
    affineLift i (affineCoordAux i z) = ((z : 𝔼) i)⁻¹ • (z : 𝔼) := by
  refine PiLp.ext fun k => ?_
  rw [euclidean_complex_smul_apply]
  refine Fin.succAboveCases (α := fun k => affineLift i (affineCoordAux i z) k
      = ((z : 𝔼) i)⁻¹ * (z : 𝔼) k) i ?_ (fun j => ?_) k
  · show affineLift i (affineCoordAux i z) i = ((z : 𝔼) i)⁻¹ * (z : 𝔼) i
    rw [affineLift_apply_same, inv_mul_cancel₀ hz]
  · show affineLift i (affineCoordAux i z) (i.succAbove j)
        = ((z : 𝔼) i)⁻¹ * (z : 𝔼) (i.succAbove j)
    rw [affineLift_apply_succAbove]
    simp only [affineCoordAux]
    rw [div_eq_inv_mul]

theorem coe_sphere_ne_zero (z : sphere (0 : 𝔼) 1) : (z : 𝔼) ≠ 0 := by
  intro h
  have hn : ‖(z : 𝔼)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

/-- Left inverse: `[1 : (z_{σ j}/z_i)] = [z]` whenever `z_i ≠ 0`. -/
theorem chartInv_affineCoord (i : Fin (n + 1)) (p : ComplexProjectiveSpace n)
    (hp : p ∈ chartSource i) : chartInv i (affineCoord i p) = p := by
  induction p using Quotient.inductionOn with
  | h z =>
    have hz : (z : 𝔼) i ≠ 0 := hp
    show projSphere (unitSphereProj (affineLift i (affineCoordAux i z))) = projSphere z
    rw [affineLift_affineCoordAux i z hz,
      projSphere_unitSphereProj_smul _ (inv_ne_zero hz) _ (coe_sphere_ne_zero z),
      unitSphereProj_coe]

/-! ## Smoothness of the affine lift and of the chart inverse -/

/-- The `k`-th coordinate of `ℂ^{n+1}`, as a **real**-linear continuous map.  Built by hand:
`ContinuousLinearMap.restrictScalars` needs an `IsScalarTower ℝ ℂ 𝔼` that does not synthesize
here (the `Module ℝ (EuclideanSpace ℂ _)` diamond), whereas the `PiLp` scalar actions are
coordinatewise, so `map_add'`/`map_smul'` hold definitionally. -/
def euclideanCoord (k : Fin (n + 1)) : 𝔼 →L[ℝ] ℂ where
  toFun v := v k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (EuclideanSpace.proj k).continuous

/-- `WithLp.toLp`, as a real-linear continuous map `ℂ^{n+1} → EuclideanSpace ℂ (Fin (n+1))`. -/
def euclideanToLp : (Fin (n + 1) → ℂ) →L[ℝ] 𝔼 where
  toFun := WithLp.toLp 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := PiLp.continuous_toLp 2 _

theorem contDiff_euclidean_coord (k : Fin (n + 1)) : ContDiff ℝ ∞ fun v : 𝔼 => v k :=
  (euclideanCoord k).contDiff

theorem contDiff_insertNth (i : Fin (n + 1)) :
    ContDiff ℝ ∞ fun w : Fin n → ℂ =>
      (Fin.insertNth (α := fun _ : Fin (n + 1) => ℂ) i (1 : ℂ) w) := by
  refine contDiff_pi.mpr fun k => ?_
  refine Fin.succAboveCases (α := fun k => ContDiff ℝ ∞ fun w : Fin n → ℂ =>
      (Fin.insertNth (α := fun _ : Fin (n + 1) => ℂ) i (1 : ℂ) w) k) i ?_ (fun j => ?_) k
  · have h1 : ContDiff ℝ ∞ fun _ : Fin n → ℂ => (1 : ℂ) := contDiff_const
    simpa only [Fin.insertNth_apply_same] using h1
  · have hj : ContDiff ℝ ∞ fun w : Fin n → ℂ => w j := contDiff_apply ℝ ℂ j
    simpa only [Fin.insertNth_apply_succAbove] using hj

theorem contDiff_affineLiftEuclidean (i : Fin (n + 1)) :
    ContDiff ℝ ∞ (affineLift i : (Fin n → ℂ) → 𝔼) :=
  euclideanToLp.contDiff.comp (contDiff_insertNth i)

theorem contDiff_affineLift_apply (i k : Fin (n + 1)) :
    ContDiff ℝ ∞ fun w : Fin n → ℂ => affineLift i w k :=
  (euclideanCoord k).contDiff.comp (contDiff_affineLiftEuclidean i)

theorem contMDiff_chartInvSphere (i : Fin (n + 1)) :
    ContMDiff 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) ∞
      (chartInvSphere i : (Fin n → ℂ) → sphere (0 : 𝔼) 1) := by
  intro w
  exact (contMDiffAt_unitSphereProj (E := 𝔼) (n := 2 * n + 1)
    (affineLift_ne_zero i w)).comp w (contDiff_affineLiftEuclidean i).contMDiff.contMDiffAt

theorem continuous_chartInv (i : Fin (n + 1)) :
    Continuous (chartInv i : (Fin n → ℂ) → ComplexProjectiveSpace n) :=
  continuous_projSphere.comp (contMDiff_chartInvSphere i).continuous

/-! ## Continuity of the affine coordinate map -/

theorem continuousOn_affineCoordAux (i : Fin (n + 1)) :
    ContinuousOn (affineCoordAux i) {z : sphere (0 : 𝔼) 1 | (z : 𝔼) i ≠ 0} := by
  refine continuousOn_pi.mpr fun j => ?_
  exact ContinuousOn.div (continuous_sphere_coord (i.succAbove j)).continuousOn
    (continuous_sphere_coord i).continuousOn fun z hz => hz

theorem continuousOn_affineCoord (i : Fin (n + 1)) :
    ContinuousOn (affineCoord i) (chartSource i : Set (ComplexProjectiveSpace n)) := by
  rw [continuousOn_open_iff (isOpen_chartSource i)]
  intro V hV
  rw [← isQuotientMap_projSphere.isOpen_preimage]
  have hpre : (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) ⁻¹'
      ((chartSource i : Set (ComplexProjectiveSpace n)) ∩ affineCoord i ⁻¹' V)
      = {z : sphere (0 : 𝔼) 1 | (z : 𝔼) i ≠ 0} ∩ affineCoordAux i ⁻¹' V := rfl
  rw [hpre]
  exact (continuousOn_open_iff (isOpen_sphere_coord_ne i)).mp (continuousOn_affineCoordAux i) V hV

/-! ## The atlas -/

/-- **Math.** The `i`-th affine chart of `ℂPⁿ`, with source `{[z] | z_i ≠ 0}` and target `ℂⁿ`. -/
def chartCP (i : Fin (n + 1)) :
    OpenPartialHomeomorph (ComplexProjectiveSpace n) (Fin n → ℂ) where
  toFun := affineCoord i
  invFun := chartInv i
  source := chartSource i
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' w _ := chartInv_mem_chartSource i w
  left_inv' p hp := chartInv_affineCoord i p hp
  right_inv' w _ := affineCoord_chartInv_self i w
  open_source := isOpen_chartSource i
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_affineCoord i
  continuousOn_invFun := (continuous_chartInv i).continuousOn

@[simp] theorem chartCP_apply (i : Fin (n + 1)) : ⇑(chartCP i) = affineCoord (n := n) i := rfl

@[simp] theorem chartCP_source (i : Fin (n + 1)) :
    (chartCP i).source = (chartSource i : Set (ComplexProjectiveSpace n)) := rfl

@[simp] theorem chartCP_symm_apply (i : Fin (n + 1)) :
    ⇑(chartCP i).symm = chartInv (n := n) i := rfl

@[simp] theorem chartCP_target (i : Fin (n + 1)) :
    (chartCP (n := n) i).target = Set.univ := rfl

theorem exists_mem_chartSource (p : ComplexProjectiveSpace n) : ∃ i, p ∈ chartSource i := by
  induction p using Quotient.inductionOn with
  | h z =>
    by_contra hcon
    have hzero : ∀ i, (z : 𝔼) i = 0 := by
      intro i
      by_contra hi
      exact hcon ⟨i, mem_chartSource_projSphere.mpr hi⟩
    have hn : ‖(z : 𝔼)‖ = 0 := by
      rw [EuclideanSpace.norm_eq]
      simp [hzero]
    rw [mem_sphere_zero_iff_norm.mp z.2] at hn
    exact one_ne_zero hn

/-- A choice of affine chart containing a given point of `ℂPⁿ`. -/
def chartIndex (p : ComplexProjectiveSpace n) : Fin (n + 1) := (exists_mem_chartSource p).choose

theorem mem_chartSource_chartIndex (p : ComplexProjectiveSpace n) :
    p ∈ chartSource (chartIndex p) := (exists_mem_chartSource p).choose_spec

instance instChartedSpaceComplexProjectiveSpace :
    ChartedSpace (Fin n → ℂ) (ComplexProjectiveSpace n) where
  atlas := Set.range chartCP
  chartAt p := chartCP (chartIndex p)
  mem_chart_source p := mem_chartSource_chartIndex p
  chart_mem_atlas p := ⟨chartIndex p, rfl⟩

theorem chartAt_complexProjectiveSpace (p : ComplexProjectiveSpace n) :
    chartAt (Fin n → ℂ) p = chartCP (chartIndex p) := rfl

/-! ## The smooth structure -/

instance instIsManifoldComplexProjectiveSpace :
    IsManifold 𝓘(ℝ, Fin n → ℂ) ∞ (ComplexProjectiveSpace n) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨i, rfl⟩ ⟨j, rfl⟩
  have hsource : ((chartCP (n := n) i).symm ≫ₕ chartCP j).source
      = {w : Fin n → ℂ | affineLift i w j ≠ 0} := by
    ext w
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      chartCP_target, chartCP_symm_apply, chartCP_source, Set.mem_inter_iff, Set.mem_univ,
      Set.mem_preimage, true_and, Set.mem_setOf_eq]
    exact chartInv_mem_chartSource_iff i j w
  have hfun : ∀ w : Fin n → ℂ, (𝓘(ℝ, Fin n → ℂ) ∘ (chartCP (n := n) i).symm ≫ₕ chartCP j ∘
      𝓘(ℝ, Fin n → ℂ).symm) w
      = fun k => affineLift i w (j.succAbove k) / affineLift i w j := by
    intro w
    simp only [Function.comp_apply, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_eq,
      OpenPartialHomeomorph.coe_trans, chartCP_symm_apply, chartCP_apply]
    exact affineCoord_chartInv i j w
  have hset : 𝓘(ℝ, Fin n → ℂ).symm ⁻¹' ((chartCP (n := n) i).symm ≫ₕ chartCP j).source ∩
      Set.range 𝓘(ℝ, Fin n → ℂ) ⊆ {w : Fin n → ℂ | affineLift i w j ≠ 0} := by
    intro w hw
    have := hw.1
    simp only [modelWithCornersSelf_coe_symm, Set.preimage_id_eq, id_eq, hsource] at this
    exact this
  refine ContDiffOn.mono ?_ hset
  refine ContDiffOn.congr ?_ fun w hw => hfun w
  refine contDiffOn_pi.mpr fun k => ?_
  exact ContDiffOn.div_complex (contDiff_affineLift_apply i (j.succAbove k)).contDiffOn
    (contDiff_affineLift_apply i j).contDiffOn fun w hw => hw

/-! ## The Hopf projection is a smooth submersion -/

theorem contDiffAt_ambientAffineCoord (i : Fin (n + 1)) (v₀ : 𝔼) (hv : v₀ i ≠ 0) :
    ContDiffAt ℝ ∞ (fun v : 𝔼 => (fun j => v (i.succAbove j) / v i : Fin n → ℂ)) v₀ := by
  refine contDiffAt_pi.mpr fun j => ?_
  exact ContDiffAt.div_complex (contDiff_euclidean_coord (i.succAbove j)).contDiffAt
    (contDiff_euclidean_coord i).contDiffAt hv

theorem contMDiff_projSphere :
    ContMDiff (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) ∞
      (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) := by
  intro z
  rw [contMDiffAt_iff_target]
  refine ⟨continuous_projSphere.continuousAt, ?_⟩
  have hzi : (z : 𝔼) (chartIndex (projSphere z)) ≠ 0 :=
    mem_chartSource_chartIndex (projSphere z)
  have hfun : (extChartAt 𝓘(ℝ, Fin n → ℂ) (projSphere z)) ∘
      (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n)
      = (fun v : 𝔼 => (fun j => v ((chartIndex (projSphere z)).succAbove j) /
          v (chartIndex (projSphere z)) : Fin n → ℂ)) ∘ ((↑) : sphere (0 : 𝔼) 1 → 𝔼) := by
    funext y
    simp only [Function.comp_apply, extChartAt, OpenPartialHomeomorph.extend_coe,
      modelWithCornersSelf_coe, id_eq, chartAt_complexProjectiveSpace, chartCP_apply,
      affineCoord_projSphere]
    rfl
  rw [hfun]
  exact (contDiffAt_ambientAffineCoord _ (z : 𝔼) hzi).comp_contMDiffAt
    contMDiff_coe_sphere.contMDiffAt

/-! ### An explicit smooth local section through each point -/

/-- The unit scalar `‖z_i‖ / z_i`, which turns `z` into the normalized representative
`[1 : w]/‖[1 : w]‖` picked out by the `i`-th chart. -/
def hopfPhase (i : Fin (n + 1)) (z : sphere (0 : 𝔼) 1) (hz : (z : 𝔼) i ≠ 0) : Circle :=
  ⟨((‖(z : 𝔼) i‖ : ℝ) : ℂ) / (z : 𝔼) i, by
    have h : ‖((‖(z : 𝔼) i‖ : ℝ) : ℂ) / (z : 𝔼) i‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hz)]
    exact mem_sphere_zero_iff_norm.mpr h⟩

theorem chartInvSphere_affineCoordAux (i : Fin (n + 1)) (z : sphere (0 : 𝔼) 1)
    (hz : (z : 𝔼) i ≠ 0) :
    chartInvSphere i (affineCoordAux i z) = hopfPhase i z hz • z := by
  have hzc : (z : 𝔼) ≠ 0 := coe_sphere_ne_zero z
  have hn : ‖(z : 𝔼) i‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hn' : ((‖(z : 𝔼) i‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hscal : ((z : 𝔼) i)⁻¹ / ((‖((z : 𝔼) i)⁻¹‖ : ℝ) : ℂ)
      = ((‖(z : 𝔼) i‖ : ℝ) : ℂ) / (z : 𝔼) i := by
    rw [norm_inv]
    push_cast
    field_simp
  apply Subtype.ext
  rw [coe_circle_smul_sphere]
  refine PiLp.ext fun k => ?_
  rw [euclidean_complex_smul_apply]
  have hkey := coe_unitSphereProj_smul ((z : 𝔼) i)⁻¹ (inv_ne_zero hz) (z : 𝔼) hzc k
  rw [unitSphereProj_coe] at hkey
  show ((unitSphereProj (affineLift i (affineCoordAux i z)) : sphere (0 : 𝔼) 1) : 𝔼) k = _
  rw [affineLift_affineCoordAux i z hz, hkey, hscal]
  rfl

/-- **Math.** An explicit smooth local section of the Hopf projection through `z`: read the
`i`-th affine coordinates, rebuild the normalized representative, and rotate it back onto `z`
by the phase `hopfPhase`. -/
def localSection (i : Fin (n + 1)) (a : Circle) (p : ComplexProjectiveSpace n) :
    sphere (0 : 𝔼) 1 :=
  a • chartInvSphere i (affineCoord i p)

theorem projSphere_localSection (i : Fin (n + 1)) (a : Circle) (p : ComplexProjectiveSpace n)
    (hp : p ∈ chartSource i) : projSphere (localSection i a p) = p := by
  rw [localSection, projSphere_circle_smul]
  exact chartInv_affineCoord i p hp

theorem localSection_projSphere (i : Fin (n + 1)) (z : sphere (0 : 𝔼) 1)
    (hz : (z : 𝔼) i ≠ 0) :
    localSection i (hopfPhase i z hz)⁻¹ (projSphere z) = z := by
  rw [localSection, affineCoord_projSphere, chartInvSphere_affineCoordAux i z hz, inv_smul_smul]

theorem contMDiffAt_localSection (i : Fin (n + 1)) (a : Circle) (p : ComplexProjectiveSpace n)
    (hp : p ∈ chartSource i) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) ∞ (localSection i a) p := by
  have hchart : ContMDiffAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) ∞ (affineCoord (n := n) i) p := by
    have hmem : chartCP (n := n) i ∈
        IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℂ) ∞ (ComplexProjectiveSpace n) :=
      IsManifold.subset_maximalAtlas ⟨i, rfl⟩
    exact (contMDiffOn_of_mem_maximalAtlas hmem).contMDiffAt
      ((isOpen_chartSource i).mem_nhds hp)
  exact ((contMDiff_circle_smul_sphere (n := n) a).contMDiffAt).comp p
    (((contMDiff_chartInvSphere i).contMDiffAt).comp p hchart)

theorem surjective_mfderiv_projSphere (z : sphere (0 : 𝔼) 1) :
    Function.Surjective
      (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
        (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z) := by
  set i := chartIndex (projSphere z) with hi
  have hzi : (z : 𝔼) i ≠ 0 := mem_chartSource_chartIndex (projSphere z)
  set a : Circle := (hopfPhase i z hzi)⁻¹ with ha
  set s : ComplexProjectiveSpace n → sphere (0 : 𝔼) 1 := localSection i a with hs
  have hsz : s (projSphere z) = z := localSection_projSphere i z hzi
  have hpmem : projSphere z ∈ chartSource i := hzi
  have hs_smooth : ContMDiffAt 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) ∞ s (projSphere z) :=
    contMDiffAt_localSection i a (projSphere z) hpmem
  have hs_diff : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) s (projSphere z) :=
    hs_smooth.mdifferentiableAt (by simp)
  have hsec : ∀ᶠ y in 𝓝 (projSphere z), projSphere (s y) = y := by
    filter_upwards [(isOpen_chartSource i).mem_nhds hpmem] with y hy
    exact projSphere_localSection i a y hy
  have hq : MDifferentiableAt (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) projSphere (s (projSphere z)) := by
    rw [hsz]
    exact (contMDiff_projSphere z).mdifferentiableAt (by simp)
  intro u
  refine ⟨mfderiv 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) s (projSphere z) u, ?_⟩
  have hkey := mfderiv_localSection_eq_symm hs_diff hq hsec u
  rw [hsz] at hkey
  exact hkey

/-! ## The Fubini–Study metric on `ℂPⁿ` -/

/-- **Math.** Petersen, Example 1.3.4, on the genuine `ℂPⁿ`: there is a **unique** Riemannian
metric on complex projective space making the Hopf projection `S^{2n+1} → ℂPⁿ` a Riemannian
submersion — the **Fubini–Study metric**.  Unlike `PetersenLib.fubiniStudyMetric`, which takes
the quotient manifold and the projection as hypotheses, here `ℂPⁿ` and the projection are
*constructed*, and all four hypotheses are discharged by proof. -/
theorem fubiniStudyMetricComplexProjectiveSpace :
    ∃! gFS : RiemannianMetric 𝓘(ℝ, Fin n → ℂ) (ComplexProjectiveSpace n),
      IsRiemannianSubmersion (sphereMetricUnit (n := 2 * n + 1) 𝔼) gFS projSphere :=
  fubiniStudyMetric projSphere contMDiff_projSphere surjective_projSphere
    surjective_mfderiv_projSphere projSphere_eq_iff

end PetersenLib
