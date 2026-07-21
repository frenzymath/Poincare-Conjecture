import PetersenLib.Ch01.RiemannianManifolds
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Petersen Ch. 1, Example 1.1.3 — the Euclidean sphere

The **canonical metric** on the Euclidean sphere `Sⁿ(R) ⊆ ℝⁿ⁺¹`: the metric
induced from the embedding `Sⁿ(R) ↪ ℝⁿ⁺¹` via the pullback construction
(`PetersenLib.pullbackMetric`).

Mathlib (at this pin) equips only the *unit* sphere `Metric.sphere (0 : E) 1`
with a charted-space and (analytic) manifold structure, via stereographic
charts (`Mathlib.Geometry.Manifold.Instances.Sphere`). We therefore:

1. define `sphereMetricUnit`, the canonical metric of the unit sphere
   `Sⁿ = Sⁿ(1)`, directly over Mathlib's structure, pulling the ambient
   inner-product metric back along the inclusion (which is a smooth
   immersion by `contMDiff_coe_sphere` and `mfderiv_coe_sphere_injective`);
2. transport the charted-space and analytic-manifold structure to the sphere
   of an arbitrary radius `r > 0` along the scaling homeomorphism
   `x ↦ r⁻¹ • x` (`sphereHomeomorphUnitSphere`), prove that the inclusion
   `Sⁿ(r) ↪ E` is a smooth immersion for this structure, and define the
   blueprint's `sphereMetric` for every radius.

The radius hypothesis `0 < r` enters through a `[Fact (0 < r)]` instance so
that the transported charted-space/manifold structures are found by instance
resolution — the same idiom as Mathlib's `[Fact (finrank ℝ E = n + 1)]` for
the sphere's dimension. The transported instances are declared with priority
`100`, so at the literal radius `1` (where `Fact ((0 : ℝ) < 1)` holds
globally) Mathlib's own unit-sphere instances always take precedence.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Example 1.1.3.
-/

open Metric Module Function Bundle
open scoped ContDiff Manifold Topology

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Scaling a sphere to the unit sphere -/

private theorem inv_smul_mem_unitSphere {r : ℝ} (hr : 0 < r) (x : sphere (0 : E) r) :
    r⁻¹ • (x : E) ∈ sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, mem_sphere_zero_iff_norm.mp x.2,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']

private theorem smul_mem_sphere_of_mem_unitSphere {r : ℝ} (hr : 0 < r)
    (y : sphere (0 : E) 1) : r • (y : E) ∈ sphere (0 : E) r := by
  rw [mem_sphere_zero_iff_norm, norm_smul, mem_sphere_zero_iff_norm.mp y.2,
    Real.norm_eq_abs, abs_of_pos hr, mul_one]

/-- **Math.** Petersen Example 1.1.3 (auxiliary): the scaling map
`x ↦ (1/R) x` is a homeomorphism from the Euclidean sphere `Sⁿ(R) ⊆ E` of
radius `R > 0` onto the unit sphere `Sⁿ = Sⁿ(1) ⊆ E`, with inverse
`y ↦ R y`. -/
def sphereHomeomorphUnitSphere (r : ℝ) [Fact (0 < r)] :
    sphere (0 : E) r ≃ₜ sphere (0 : E) 1 where
  toFun x := ⟨r⁻¹ • (x : E), inv_smul_mem_unitSphere (Fact.out : 0 < r) x⟩
  invFun y := ⟨r • (y : E), smul_mem_sphere_of_mem_unitSphere (Fact.out : 0 < r) y⟩
  left_inv x := Subtype.ext (by
    show r • (r⁻¹ • (x : E)) = (x : E)
    rw [smul_smul, mul_inv_cancel₀ (Fact.out : 0 < r).ne', one_smul])
  right_inv y := Subtype.ext (by
    show r⁻¹ • (r • (y : E)) = (y : E)
    rw [smul_smul, inv_mul_cancel₀ (Fact.out : 0 < r).ne', one_smul])
  continuous_toFun := (continuous_subtype_val.const_smul r⁻¹).subtype_mk _
  continuous_invFun := (continuous_subtype_val.const_smul r).subtype_mk _

@[simp]
theorem sphereHomeomorphUnitSphere_apply_coe (r : ℝ) [Fact (0 < r)]
    (x : sphere (0 : E) r) :
    ((sphereHomeomorphUnitSphere r x : sphere (0 : E) 1) : E) = r⁻¹ • (x : E) :=
  rfl

@[simp]
theorem sphereHomeomorphUnitSphere_symm_apply_coe (r : ℝ) [Fact (0 < r)]
    (y : sphere (0 : E) 1) :
    (((sphereHomeomorphUnitSphere r).symm y : sphere (0 : E) r) : E) = r • (y : E) :=
  rfl

/-! ## The manifold structure on a sphere of arbitrary radius

Mathlib's stereographic-chart development covers the unit sphere only; we
transport its structure to `Sⁿ(R)` along `sphereHomeomorphUnitSphere`. -/

section SphereManifold

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- **Eng.** The charted-space structure on the sphere `Sⁿ(R) ⊆ E` of radius
`R > 0`: Mathlib's stereographic charts of the unit sphere, precomposed with
the scaling homeomorphism `Sⁿ(R) ≃ₜ Sⁿ(1)`. Priority `100`, so that at the
literal radius `1` Mathlib's `EuclideanSpace.instChartedSpaceSphere` wins. -/
instance (priority := 100) sphereChartedSpace (r : ℝ) [Fact (0 < r)] :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : E) r) where
  atlas := (sphereHomeomorphUnitSphere r).transOpenPartialHomeomorph ''
    atlas (EuclideanSpace ℝ (Fin n)) (sphere (0 : E) 1)
  chartAt x := (sphereHomeomorphUnitSphere r).transOpenPartialHomeomorph
    (chartAt (EuclideanSpace ℝ (Fin n)) (sphereHomeomorphUnitSphere r x))
  mem_chart_source x :=
    mem_chart_source (EuclideanSpace ℝ (Fin n)) (sphereHomeomorphUnitSphere r x)
  chart_mem_atlas _ := Set.mem_image_of_mem _ (chart_mem_atlas _ _)

theorem sphere_chartAt_eq (r : ℝ) [Fact (0 < r)] (x : sphere (0 : E) r) :
    chartAt (EuclideanSpace ℝ (Fin n)) x
      = (sphereHomeomorphUnitSphere r).transOpenPartialHomeomorph
          (chartAt (EuclideanSpace ℝ (Fin n)) (sphereHomeomorphUnitSphere r x)) :=
  rfl

/-- **Math.** The sphere `Sⁿ(R) ⊆ E` of radius `R > 0` is an analytic
manifold modelled on `EuclideanSpace ℝ (Fin n)`: the transition maps of the
transported atlas are literally the transition maps of the unit sphere's
stereographic atlas. -/
instance (priority := 100) sphereIsManifold (r : ℝ) [Fact (0 < r)] :
    IsManifold (𝓡 n) ω (sphere (0 : E) r) where
  compatible := by
    rintro e e' ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    rw [Homeomorph.transOpenPartialHomeomorph_eq_trans,
      Homeomorph.transOpenPartialHomeomorph_eq_trans,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc
        (sphereHomeomorphUnitSphere r).toOpenPartialHomeomorph.symm,
      ← Homeomorph.symm_toOpenPartialHomeomorph,
      ← Homeomorph.trans_toOpenPartialHomeomorph,
      Homeomorph.symm_trans_self,
      Homeomorph.refl_toOpenPartialHomeomorph,
      OpenPartialHomeomorph.refl_trans]
    exact StructureGroupoid.compatible _ hc hc'

/-- **Math.** The scaling map `Sⁿ(R) → Sⁿ(1)`, `x ↦ (1/R) x`, is `C^m` for
the transported manifold structure on `Sⁿ(R)` — indeed, read in the
transported charts it is the identity. -/
theorem contMDiff_sphereHomeomorphUnitSphere {m : ℕ∞ω} (r : ℝ) [Fact (0 < r)] :
    ContMDiff (𝓡 n) (𝓡 n) m (⇑(sphereHomeomorphUnitSphere (E := E) r)) := by
  set ψ := sphereHomeomorphUnitSphere (E := E) r with hψ
  intro x
  rw [contMDiffAt_iff]
  refine ⟨ψ.continuous.continuousAt, ?_⟩
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ]
  refine contDiffAt_id.congr_of_eventuallyEq ?_
  have hmem : extChartAt (𝓡 n) x x
      ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (ψ x)).target := by
    show chartAt (EuclideanSpace ℝ (Fin n)) (ψ x) (ψ x) ∈ _
    exact (chartAt _ (ψ x)).map_source (mem_chart_source _ _)
  filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) (ψ x)).open_target.mem_nhds hmem]
    with z hz
  show chartAt (EuclideanSpace ℝ (Fin n)) (ψ x)
      (ψ (ψ.symm ((chartAt (EuclideanSpace ℝ (Fin n)) (ψ x)).symm z))) = z
  rw [ψ.apply_symm_apply]
  exact (chartAt _ (ψ x)).right_inv hz

/-- **Math.** The inverse scaling map `Sⁿ(1) → Sⁿ(R)`, `y ↦ R y`, is `C^m`
for the transported manifold structure on `Sⁿ(R)`. -/
theorem contMDiff_sphereHomeomorphUnitSphere_symm {m : ℕ∞ω} (r : ℝ) [Fact (0 < r)] :
    ContMDiff (𝓡 n) (𝓡 n) m (⇑(sphereHomeomorphUnitSphere (E := E) r).symm) := by
  set ψ := sphereHomeomorphUnitSphere (E := E) r with hψ
  intro y
  rw [contMDiffAt_iff]
  refine ⟨ψ.symm.continuous.continuousAt, ?_⟩
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ]
  refine contDiffAt_id.congr_of_eventuallyEq ?_
  have hmem : extChartAt (𝓡 n) y y
      ∈ (chartAt (EuclideanSpace ℝ (Fin n)) y).target := by
    show chartAt (EuclideanSpace ℝ (Fin n)) y y ∈ _
    exact (chartAt _ y).map_source (mem_chart_source _ _)
  filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) y).open_target.mem_nhds hmem]
    with z hz
  show chartAt (EuclideanSpace ℝ (Fin n)) (ψ (ψ.symm y))
      (ψ (ψ.symm ((chartAt (EuclideanSpace ℝ (Fin n)) y).symm z))) = z
  simp only [Homeomorph.apply_symm_apply]
  exact (chartAt _ y).right_inv hz

/-- **Math.** Petersen Example 1.1.3: the inclusion `Sⁿ(R) ↪ E` of the
sphere of radius `R > 0` is `C^m` (indeed analytic): it factors as the
scaling `Sⁿ(R) → Sⁿ(1)`, followed by the unit-sphere inclusion, followed by
the linear map `y ↦ R y` of `E`. -/
theorem contMDiff_coe_sphere_radius {m : ℕ∞ω} (r : ℝ) [Fact (0 < r)] :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) m ((↑) : sphere (0 : E) r → E) := by
  have hr : (0 : ℝ) < r := Fact.out
  have hval : (((↑) : sphere (0 : E) r → E))
      = ((fun y : E => r • y) ∘ ((↑) : sphere (0 : E) 1 → E))
        ∘ ⇑(sphereHomeomorphUnitSphere r) := by
    funext z
    show (z : E) = r • (r⁻¹ • (z : E))
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [hval]
  exact ((contDiff_const_smul r).contMDiff.comp contMDiff_coe_sphere).comp
    (contMDiff_sphereHomeomorphUnitSphere r)

/-- **Math.** Petersen Example 1.1.3: the differential of the inclusion
`Sⁿ(R) ↪ E` is injective at every point, i.e. the inclusion is an immersion.
The differential factors through the differential of the scaling
diffeomorphism onto the unit sphere (injective, having the inverse scaling
as a smooth left inverse), the differential of the unit-sphere inclusion
(injective by `mfderiv_coe_sphere_injective`), and the invertible linear map
`y ↦ R y`. -/
theorem mfderiv_coe_sphere_radius_injective (r : ℝ) [Fact (0 < r)]
    (x : sphere (0 : E) r) :
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) r → E) x) := by
  have hr : (0 : ℝ) < r := Fact.out
  set ψ := sphereHomeomorphUnitSphere (E := E) r with hψ
  have hψd : MDifferentiableAt (𝓡 n) (𝓡 n) (⇑ψ) x :=
    (contMDiff_sphereHomeomorphUnitSphere (m := 1) r x).mdifferentiableAt one_ne_zero
  have hψsd : MDifferentiableAt (𝓡 n) (𝓡 n) (⇑ψ.symm) (ψ x) :=
    (contMDiff_sphereHomeomorphUnitSphere_symm (m := 1) r (ψ x)).mdifferentiableAt
      one_ne_zero
  -- the differential of the scaling map is injective
  have hinjψ : Function.Injective (mfderiv (𝓡 n) (𝓡 n) (⇑ψ) x) := by
    have hid : (⇑ψ.symm ∘ ⇑ψ : sphere (0 : E) r → sphere (0 : E) r) = id :=
      funext fun z => ψ.symm_apply_apply z
    refine Function.LeftInverse.injective
      (g := mfderiv (𝓡 n) (𝓡 n) (⇑ψ.symm) (ψ x)) fun u => ?_
    have h1 : mfderiv (𝓡 n) (𝓡 n) (⇑ψ.symm ∘ ⇑ψ) x u = u := by
      rw [hid, mfderiv_id]; rfl
    have h2 : mfderiv (𝓡 n) (𝓡 n) (⇑ψ.symm) (ψ x) (mfderiv (𝓡 n) (𝓡 n) (⇑ψ) x u)
        = mfderiv (𝓡 n) (𝓡 n) (⇑ψ.symm ∘ ⇑ψ) x u := by
      rw [mfderiv_comp x hψsd hψd]; rfl
    exact h2.trans h1
  -- factor the inclusion through the unit sphere
  have hval : (((↑) : sphere (0 : E) r → E))
      = ((fun y : E => r • y) ∘ ((↑) : sphere (0 : E) 1 → E)) ∘ ⇑ψ := by
    funext z
    show (z : E) = r • (r⁻¹ • (z : E))
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hval1 : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (ψ x) :=
    (contMDiff_coe_sphere (m := 1) (ψ x)).mdifferentiableAt one_ne_zero
  have hsmul : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : E => r • y) ((ψ x : E)) :=
    ((contDiff_const_smul (n := (1 : ℕ∞ω)) r).contMDiff.contMDiffAt).mdifferentiableAt
      one_ne_zero
  have hg : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E)
      ((fun y : E => r • y) ∘ ((↑) : sphere (0 : E) 1 → E)) (ψ x) :=
    hsmul.comp (ψ x) hval1
  -- the differential of `y ↦ r • y` on `E` is `r • id`, injective since `r ≠ 0`
  have hsmul_inj : Function.Injective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : E => r • y) ((ψ x : E))) := by
    have hf : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y : E => r • y) ((ψ x : E))
        = r • ContinuousLinearMap.id ℝ E := by
      rw [mfderiv_eq_fderiv]
      exact ((hasFDerivAt_id _).const_smul r).fderiv
    rw [hf]
    intro a b hab
    refine smul_right_injective E hr.ne' ?_
    simpa using hab
  -- injectivity of the differential of `(r • ·) ∘ (unit-sphere inclusion)`
  have hg_inj : Function.Injective
      (mfderiv (𝓡 n) 𝓘(ℝ, E)
        ((fun y : E => r • y) ∘ ((↑) : sphere (0 : E) 1 → E)) (ψ x)) := by
    rw [mfderiv_comp (ψ x) hsmul hval1]
    intro a b hab
    exact mfderiv_coe_sphere_injective (ψ x) (hsmul_inj hab)
  rw [hval, mfderiv_comp x hg hψd]
  intro a b hab
  exact hinjψ (hg_inj hab)

/-- **Math.** Petersen Example 1.1.3: the inclusion `Sⁿ(R) ↪ E` is a smooth
immersion. -/
theorem isSmoothImmersion_coe_sphere_radius (r : ℝ) [Fact (0 < r)] :
    IsSmoothImmersion (I := 𝓡 n) (I' := 𝓘(ℝ, E)) ((↑) : sphere (0 : E) r → E) :=
  ⟨contMDiff_coe_sphere_radius r, fun x => mfderiv_coe_sphere_radius_injective r x⟩

/-- **Math.** Petersen Example 1.1.3: the inclusion `Sⁿ = Sⁿ(1) ↪ E` of the
unit sphere is a smooth immersion (Mathlib's `contMDiff_coe_sphere` and
`mfderiv_coe_sphere_injective`). -/
theorem isSmoothImmersion_coe_sphere :
    IsSmoothImmersion (I := 𝓡 n) (I' := 𝓘(ℝ, E)) ((↑) : sphere (0 : E) 1 → E) :=
  ⟨contMDiff_coe_sphere, fun x => mfderiv_coe_sphere_injective x⟩

/-! ## The canonical metric on the sphere -/

variable (E) in
/-- **Math.** Petersen Example 1.1.3: the **canonical metric** on the
Euclidean sphere `Sⁿ(R) = {x ∈ ℝⁿ⁺¹ | |x| = R}` of radius `R > 0`, induced
from the embedding `Sⁿ(R) ↪ ℝⁿ⁺¹` via the pullback metric:
`g(u, v) = ⟨Dι(u), Dι(v)⟩` for the inclusion `ι : Sⁿ(R) → ℝⁿ⁺¹`. -/
def sphereMetric (r : ℝ) [Fact (0 < r)] :
    RiemannianMetric (𝓡 n) (sphere (0 : E) r) :=
  pullbackMetric (innerProductSpaceMetric E) ((↑) : sphere (0 : E) r → E)
    (isSmoothImmersion_coe_sphere_radius r)

@[simp]
theorem sphereMetric_apply (r : ℝ) [Fact (0 < r)] (x : sphere (0 : E) r)
    (u v : TangentSpace (𝓡 n) x) :
    (sphereMetric E r).metricInner x u v
      = @inner ℝ E _ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) r → E) x u)
          (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) r → E) x v) :=
  rfl

/-- Companion to `sphereMetric_apply` in terms of the raw `inner` field, so
that the `simp` set stays confluent with `metricInner_apply`. -/
@[simp]
theorem sphereMetric_inner_apply (r : ℝ) [Fact (0 < r)] (x : sphere (0 : E) r)
    (u v : TangentSpace (𝓡 n) x) :
    (sphereMetric E r).inner x u v
      = @inner ℝ E _ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) r → E) x u)
          (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) r → E) x v) :=
  rfl

variable (E) in
/-- **Math.** Petersen Example 1.1.3: the canonical metric on the **unit
sphere** (the *standard sphere*) `Sⁿ = Sⁿ(1) ⊆ ℝⁿ⁺¹`, induced from the
embedding `Sⁿ ↪ ℝⁿ⁺¹`. Stated over Mathlib's stereographic charted-space
structure on `Metric.sphere (0 : E) 1`. -/
def sphereMetricUnit : RiemannianMetric (𝓡 n) (sphere (0 : E) 1) :=
  pullbackMetric (innerProductSpaceMetric E) ((↑) : sphere (0 : E) 1 → E)
    isSmoothImmersion_coe_sphere

@[simp]
theorem sphereMetricUnit_apply (x : sphere (0 : E) 1)
    (u v : TangentSpace (𝓡 n) x) :
    (sphereMetricUnit E).metricInner x u v
      = @inner ℝ E _ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x u)
          (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v) :=
  rfl

/-- Companion to `sphereMetricUnit_apply` in terms of the raw `inner` field,
so that the `simp` set stays confluent with `metricInner_apply`. -/
@[simp]
theorem sphereMetricUnit_inner_apply (x : sphere (0 : E) 1)
    (u v : TangentSpace (𝓡 n) x) :
    (sphereMetricUnit E).inner x u v
      = @inner ℝ E _ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x u)
          (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v) :=
  rfl

/-- **Math.** Petersen Example 1.1.3: with the canonical metric, the
inclusion `Sⁿ(R) ↪ ℝⁿ⁺¹` is a Riemannian (isometric) immersion. -/
theorem sphereMetric_isRiemannianImmersion (r : ℝ) [Fact (0 < r)] :
    IsRiemannianImmersion (sphereMetric (n := n) E r) (innerProductSpaceMetric E)
      ((↑) : sphere (0 : E) r → E) :=
  pullbackMetric_isRiemannianImmersion _ _ _

/-- **Math.** Petersen Example 1.1.3: with the canonical metric, the
inclusion `Sⁿ ↪ ℝⁿ⁺¹` of the unit sphere is a Riemannian (isometric)
immersion. -/
theorem sphereMetricUnit_isRiemannianImmersion :
    IsRiemannianImmersion (sphereMetricUnit (n := n) E) (innerProductSpaceMetric E)
      ((↑) : sphere (0 : E) 1 → E) :=
  pullbackMetric_isRiemannianImmersion _ _ _

end SphereManifold

end PetersenLib
