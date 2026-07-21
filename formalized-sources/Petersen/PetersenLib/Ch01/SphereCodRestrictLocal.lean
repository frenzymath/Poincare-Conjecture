import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Local codomain restriction to the unit sphere

`ContMDiff.codRestrict_sphere` in mathlib restricts a globally smooth map
into a smooth map to the sphere. This file provides the pointwise (`At`)
version: a map `f : M → sphere (0 : E) 1` is `C^m` at `x` as soon as its
ambient composition `y ↦ (f y : E)` is `C^m` at `x` — the sphere carries
the subspace topology and the stereographic charts are smooth on their
domains, so smoothness is a local matter. This serves maps (e.g. radial
projections) that are only smooth away from a bad set.
-/

open Metric
open scoped Manifold ContDiff RealInnerProductSpace

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Eng.** Pointwise version of `ContMDiff.codRestrict_sphere`: a
sphere-valued map is `C^m` at `x` iff its ambient composition is. -/
theorem contMDiffAt_sphere_iff_ambient {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    {m : ℕ∞ω} {f : M → sphere (0 : E) 1} {x : M} :
    ContMDiffAt I (𝓡 n) m f x ↔ ContMDiffAt I 𝓘(ℝ, E) m (fun y => (f y : E)) x := by
  constructor
  · intro h
    exact contMDiff_coe_sphere.contMDiffAt.comp x h
  · intro h
    rw [contMDiffAt_iff_target]
    refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr h.continuousAt, ?_⟩
    set v : sphere (0 : E) 1 := f x with hv
    -- The chart at `v` is the stereographic projection from `-v`, followed by the
    -- linear isometry `U` onto Euclidean space; both are smooth near `(v : E)`.
    let U : (ℝ ∙ ((-v : sphere (0 : E) 1) : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
      (OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere (-v))).repr
    have hmem : (v : E) ∈ {y : E | innerSL ℝ ((-v : sphere (0 : E) 1) : E) y ≠ (1 : ℝ)} := by
      simp only [Set.mem_setOf_eq, innerSL_apply_apply, coe_neg_sphere, inner_neg_left,
        real_inner_self_eq_norm_mul_norm, norm_eq_of_mem_sphere]
      norm_num
    have hopen : IsOpen {y : E | innerSL ℝ ((-v : sphere (0 : E) 1) : E) y ≠ (1 : ℝ)} :=
      isOpen_ne_fun (innerSL ℝ _).continuous continuous_const
    have hst : ContDiffAt ℝ m (stereoToFun ((-v : sphere (0 : E) 1) : E)) (v : E) :=
      contDiffOn_stereoToFun.contDiffAt (hopen.mem_nhds hmem)
    have hU : ContDiffAt ℝ m (⇑U) (stereoToFun ((-v : sphere (0 : E) 1) : E) (v : E)) :=
      (U.contDiff.of_le le_top).contDiffAt
    exact ContDiffAt.comp_contMDiffAt (f := fun y => ((f y : E))) (hU.comp _ hst) h
