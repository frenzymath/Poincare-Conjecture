/-
Chapter 2, Example 2.24(c) and Problem 2-4: **polar coordinates exhibit
`ℝⁿ ∖ {0}` as a warped product**.

Lee's statement (Problem 2-4).  Let `ρ : ℝ⁺ → ℝ` be the standard coordinate, and
let `ℝ⁺ ×_ρ S^{n-1}` be the resulting warped product.  Then
`Φ(ρ, ω) = ρ ω` is an isometry from `ℝ⁺ ×_ρ S^{n-1}` onto `ℝⁿ ∖ {0}` with its
Euclidean metric.  Lee flags it "(Used on p. 293.)": it is the flat model that
geodesic polar coordinates are compared against, so `dρ² + ρ² g̊` is the shape every
later normal-coordinate computation reduces to.

**The computation.**  Everything rests on one orthogonality fact.  At `(r, ω)` the
differential of `Φ` sends `(a, w)` to

  `dΦ(a, w) = a ω + r · dι(w)`,

`ι : S^{n-1} ↪ ℝⁿ` being the inclusion.  Hence

  `⟪dΦ(a,w), dΦ(a',w')⟫ = a a' ‖ω‖² + a r ⟪ω, dι w'⟫ + a' r ⟪dι w, ω⟫ + r² ⟪dι w, dι w'⟫`.

Now `‖ω‖ = 1` because `ω ∈ S^{n-1}`, and the two cross terms **vanish**, because
the tangent space to the sphere at `ω` is exactly `ω^⊥`
(`range_mfderiv_coe_sphere`: the range of `dι_ω` is `(ℝ ∙ ω)ᗮ`).  So the whole
thing collapses to

  `a a' + r² ⟪dι w, dι w'⟫ = a a' + r² g̊_ω(w, w')`,

which is precisely `(g_{ℝ⁺} ⊕ ρ² g̊)` at `(r, ω)` — the warped product metric with
warping function `ρ`.  The radial and spherical directions being orthogonal is
what makes the metric a *warped product* rather than a general block form; that is
the geometric content of the problem.

**What had to be built.**  The radial factor is the open submanifold
`ℝ⁺ = (0, ∞) ⊆ ℝ`, and the warped product needs a *Riemannian metric* on it, hence
the differential of the inclusion `ℝ⁺ ↪ ℝ` — which mathlib does not compute for an
open subset.  That gap is filled in `OpenSubmanifold.lean`; here it is used twice,
once to build `posRealsMetric` and once inside the differential computation.

`polarMap` is stated into `E` rather than into `↥(E ∖ {0})`: the metric identity is
about `Φ^* ḡ`, and the Euclidean metric on the punctured space is the restriction of
the one on `E`, so nothing is lost.  That `Φ` really is a bijection onto `E ∖ {0}`
— the rest of Lee's assertion — is `polarMap_ne_zero`, `polarMap_injective` and
`polarMap_surjOn`, proved separately below.
-/
import LeeLib.Ch02.OpenSubmanifold
import LeeLib.Ch02.ProductMetric
import LeeLib.Ch02.Sphere
import LeeLib.Ch02.Isometry

namespace LeeLib.Ch02

open Manifold Metric Module TopologicalSpace
open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

/-! ### The radial factor `ℝ⁺` -/

/-- **`ℝ⁺ = (0, ∞)`**, Lee's parameter domain for the radial factor of the warped
product, as an open submanifold of `ℝ`. -/
def posReals : Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩

@[simp] theorem mem_posReals {r : ℝ} : r ∈ posReals ↔ 0 < r := Iff.rfl

theorem posReals_pos (r : posReals) : 0 < (r : ℝ) := r.2

theorem posReals_ne_zero (r : posReals) : (r : ℝ) ≠ 0 := ne_of_gt (posReals_pos r)

/-- **Lee's coordinate function `ρ`** on `ℝ⁺`: the restriction of the standard
coordinate of `ℝ`.  It is the warping function of the polar warped product. -/
def rho : posReals → ℝ := fun r => (r : ℝ)

@[simp] theorem rho_apply (r : posReals) : rho r = (r : ℝ) := rfl

theorem contMDiff_rho : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ rho :=
  contMDiff_subtype_val

theorem rho_ne_zero (r : posReals) : rho r ≠ 0 := posReals_ne_zero r

/-- The metric on `ℝ⁺` induced from `ℝ`: the radial factor of the warped product. -/
def posRealsMetric : RiemannianMetric 𝓘(ℝ, ℝ) posReals :=
  openSubmanifoldMetric (euclideanMetric ℝ) posReals

/-- On `ℝ⁺` the induced metric is `dρ²`: it multiplies the two components. -/
@[simp] theorem posRealsMetric_innerAt (r : posReals) (a b : TangentSpace 𝓘(ℝ, ℝ) r) :
    posRealsMetric.innerAt r a b = (show ℝ from a) * (show ℝ from b) := by
  rw [posRealsMetric, openSubmanifoldMetric_innerAt, euclideanMetric_innerAt]
  exact real_inner_comm _ _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The polar map -/

variable (E) in
/-- **Lee's `Φ(ρ, ω) = ρ ω`**, the polar coordinate map `ℝ⁺ × S^{n-1} → ℝⁿ`. -/
def polarMap : posReals × sphere (0 : E) 1 → E := fun p => ((p.1 : ℝ)) • ((p.2 : E))

@[simp] theorem polarMap_apply (p : posReals × sphere (0 : E) 1) :
    polarMap E p = ((p.1 : ℝ)) • ((p.2 : E)) := rfl

/-- `‖Φ(r, ω)‖ = r`: the radial coordinate is recovered as the norm.  This is what
makes `Φ` injective and its image the punctured space. -/
theorem norm_polarMap (p : posReals × sphere (0 : E) 1) : ‖polarMap E p‖ = (p.1 : ℝ) := by
  rw [polarMap_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (posReals_pos p.1),
    mem_sphere_zero_iff_norm.1 p.2.2, mul_one]

/-- `Φ` lands in the punctured space `ℝⁿ ∖ {0}`, since `‖Φ(r,ω)‖ = r > 0`. -/
theorem polarMap_ne_zero (p : posReals × sphere (0 : E) 1) : polarMap E p ≠ 0 := by
  intro h
  have := norm_polarMap p
  rw [h, norm_zero] at this
  exact absurd this.symm (posReals_ne_zero p.1)

/-- `Φ` is injective: the norm recovers `r`, and then dividing recovers `ω`. -/
theorem polarMap_injective : Function.Injective (polarMap E) := by
  rintro ⟨r, s1⟩ ⟨r', s2⟩ h
  have hr : (r : ℝ) = (r' : ℝ) := by
    rw [← norm_polarMap (E := E) (r, s1), ← norm_polarMap (E := E) (r', s2), h]
  have hs : (s1 : E) = (s2 : E) := by
    have h' : (r : ℝ) • (s1 : E) = (r : ℝ) • (s2 : E) := by
      simpa [hr] using h
    exact smul_right_injective E (posReals_ne_zero r) h'
  exact Prod.ext (Subtype.ext hr) (Subtype.ext hs)

/-- **`Φ` maps onto `ℝⁿ ∖ {0}`**: every nonzero `x` is `‖x‖ · (x/‖x‖)`.  Together
with `polarMap_ne_zero` and `polarMap_injective` this is Lee's assertion that `Φ`
is a bijection `ℝ⁺ × S^{n-1} → ℝⁿ ∖ {0}`. -/
theorem polarMap_surjOn : Set.SurjOn (polarMap E) Set.univ {0}ᶜ := by
  rintro x (hx : x ≠ 0)
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  refine ⟨(⟨‖x‖, norm_pos_iff.2 hx⟩, ⟨‖x‖⁻¹ • x, ?_⟩), Set.mem_univ _, ?_⟩
  · simp [norm_smul, inv_mul_cancel₀ hnorm]
  · show ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]

theorem contMDiff_polarMap {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) ∞ (polarMap E) :=
  (contMDiff_subtype_val.comp contMDiff_fst).smul (contMDiff_coe_sphere.comp contMDiff_snd)

/-! ### The differential of `Φ` -/

/-- The **radial partial derivative** of `Φ`: `d/dr (r ω₀) = ω₀`, so a radial
tangent vector `a` is sent to `a ω₀`.

The inclusion `ℝ⁺ ↪ ℝ` appears here, which is why `mfderiv_opens_subtypeVal` is
needed: without it this differential is stuck. -/
theorem mfderiv_polarMap_fst (ω₀ : E) (r₀ : posReals) (a : TangentSpace 𝓘(ℝ, ℝ) r₀) :
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun z : posReals => (z : ℝ) • ω₀) r₀) a = (show ℝ from a) • ω₀ := by
  have hsmul : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => t • ω₀) (r₀ : ℝ) :=
    (differentiableAt_id.smul_const ω₀).mdifferentiableAt
  have hval : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z : posReals => (z : ℝ)) r₀ :=
    (contMDiff_subtype_val (I := 𝓘(ℝ, ℝ)) (n := ∞) (U := posReals)).mdifferentiableAt (by simp)
  have h1 : (fun z : posReals => (z : ℝ) • ω₀)
      = (fun t : ℝ => t • ω₀) ∘ (fun z : posReals => (z : ℝ)) := rfl
  have h2 : HasFDerivAt (fun t : ℝ => t • ω₀) ((ContinuousLinearMap.id ℝ ℝ).smulRight ω₀) (r₀ : ℝ) :=
    (hasFDerivAt_id (r₀ : ℝ)).smul_const ω₀
  rw [h1, mfderiv_comp (I' := 𝓘(ℝ, ℝ)) r₀ hsmul hval]
  simp only [mfderiv_eq_fderiv, h2.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply,
    mfderiv_opens_subtypeVal_apply]
  rfl

/-- The **spherical partial derivative** of `Φ`: `d/dω (r₀ ω) = r₀ · dι`, since
`ω ↦ r₀ ω` is the inclusion followed by a fixed scaling. -/
theorem mfderiv_polarMap_snd {n : ℕ} [Fact (finrank ℝ E = n + 1)] (r₀ : ℝ)
    (ω₀ : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) ω₀) :
    (mfderiv (𝓡 n) 𝓘(ℝ, E) (fun z : sphere (0 : E) 1 => r₀ • (z : E)) ω₀) w =
      r₀ • (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) ω₀ w) := by
  have hincl : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) ω₀ :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
  have hsmul : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun u : E => r₀ • u) ((ω₀ : E)) :=
    ((differentiableAt_id).const_smul r₀).mdifferentiableAt
  have h1 : (fun z : sphere (0 : E) 1 => r₀ • (z : E))
      = (fun u : E => r₀ • u) ∘ ((↑) : sphere (0 : E) 1 → E) := rfl
  have h2 : HasFDerivAt (fun u : E => r₀ • u) (r₀ • (ContinuousLinearMap.id ℝ E)) ((ω₀ : E)) :=
    (hasFDerivAt_id (ω₀ : E)).const_smul r₀
  rw [h1, mfderiv_comp (I' := 𝓘(ℝ, E)) ω₀ hsmul hincl]
  simp only [mfderiv_eq_fderiv, h2.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
  rfl

/-- **`dΦ_{(r,ω)}(a, w) = a ω + r · dι(w)`.**

Obtained from the two partial derivatives by `mfderiv_prod_eq_add_apply`, which is
the product rule on a product manifold. -/
theorem mfderiv_polarMap_apply {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (p : posReals × sphere (0 : E) 1) (v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p) :
    (show E from (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (polarMap E) p) v) =
      (show ℝ from v.1) • ((p.2 : E))
        + (p.1 : ℝ) • (show E from mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 v.2) := by
  have hsplit := mfderiv_prod_eq_add_apply (v := v)
    ((contMDiff_polarMap (E := E) (n := n)).mdifferentiableAt (by simp))
  -- The two partial maps of `Φ` are literally the two maps computed above.
  have e1 : (fun z : posReals => polarMap E (z, p.2))
      = fun z : posReals => (z : ℝ) • ((p.2 : E)) := rfl
  have e2 : (fun z : sphere (0 : E) 1 => polarMap E (p.1, z))
      = fun z : sphere (0 : E) 1 => (p.1 : ℝ) • ((z : E)) := rfl
  rw [show (show E from (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (polarMap E) p) v) = _ from hsplit,
    e1, e2]
  congr 1
  · exact mfderiv_polarMap_fst (p.2 : E) p.1 v.1
  · exact mfderiv_polarMap_snd (p.1 : ℝ) p.2 v.2

/-! ### Orthogonality of the radial and spherical directions -/

/-- **The tangent directions to the sphere are orthogonal to the radius.**

`range_mfderiv_coe_sphere` says the image of `dι_ω` is `(ℝ ∙ ω)ᗮ`; this is that
statement read as the vanishing of an inner product.  It is the one fact that makes
the polar metric a *warped product*: it kills the cross terms `⟪ω, dι w⟫`. -/
theorem inner_coe_sphere_mfderiv_eq_zero {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (ω₀ : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) ω₀) :
    ⟪(ω₀ : E), (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) ω₀ w : E)⟫ = 0 := by
  have hmem : (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) ω₀ w : E) ∈ (ℝ ∙ (ω₀ : E))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := n) ω₀]
    exact ⟨w, rfl⟩
  exact hmem (ω₀ : E) (Submodule.mem_span_singleton_self _)

/-- `inner_coe_sphere_mfderiv_eq_zero` with the arguments in the other order; both
orders occur, one for each slot of the symmetric form. -/
theorem inner_mfderiv_coe_sphere_eq_zero {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (ω₀ : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) ω₀) :
    ⟪(show E from mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) ω₀ w), (ω₀ : E)⟫ = 0 :=
  (real_inner_comm _ _).trans (inner_coe_sphere_mfderiv_eq_zero ω₀ w)

/-! ### The polar warped product and Lee's Problem 2-4 -/

variable (E) in
/-- **The warped product `ℝ⁺ ×_ρ S^{n-1}`** (Lee, Example 2.24(c)): the product
`ℝ⁺ × S^{n-1}` carrying `dρ² + ρ² g̊`. -/
def polarWarpedMetric (n : ℕ) [Fact (finrank ℝ E = n + 1)] :
    RiemannianMetric (𝓘(ℝ, ℝ).prod (𝓡 n)) (posReals × sphere (0 : E) 1) :=
  warpedProductMetric posRealsMetric (roundMetric E n) contMDiff_rho rho_ne_zero

/-- **Lee's Problem 2-4**: `Φ(ρ, ω) = ρ ω` pulls the Euclidean metric back to the
warped product metric of `ℝ⁺ ×_ρ S^{n-1}`, i.e. `Φ^* ḡ = dρ² + ρ² g̊`.

Together with `polarMap_ne_zero`, `polarMap_injective` and `polarMap_surjOn` (which
say `Φ` is a bijection onto `ℝⁿ ∖ {0}`), this is Lee's assertion that `Φ` is an
isometry from `ℝ⁺ ×_ρ S^{n-1}` onto `ℝⁿ ∖ {0}` with its Euclidean metric. -/
theorem isMetricPreserving_polarMap {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    IsMetricPreserving (polarWarpedMetric E n) (euclideanMetric E) (polarMap E) := by
  intro p
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  rw [pullbackForm_apply]
  show (euclideanMetric E).innerAt (polarMap E p)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (polarMap E) p v)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (polarMap E) p w)
    = (polarWarpedMetric E n).innerAt p v w
  rw [euclideanMetric_innerAt]
  -- Expand `dΦ` on both slots.
  rw [show (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (polarMap E) p) v = _ from
        mfderiv_polarMap_apply p v,
      show (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (polarMap E) p) w = _ from
        mfderiv_polarMap_apply p w]
  -- Expand the four terms of the inner product.
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  -- The cross terms vanish: sphere directions are orthogonal to the radius.
  rw [inner_coe_sphere_mfderiv_eq_zero p.2 w.2, inner_mfderiv_coe_sphere_eq_zero p.2 v.2]
  -- `‖ω‖ = 1`, and the surviving spherical term is the round metric.
  have hunit : ⟪(p.2 : E), (p.2 : E)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.1 p.2.2, one_pow]
  rw [hunit, polarWarpedMetric, warpedProductMetric_innerAt, posRealsMetric_innerAt,
    roundMetric_innerAt, rho_apply]
  ring

/-- **`Φ` is an immersion**, read off Problem 2-4 via Lee's Lemma 2.11.

This is a sanity check on `isMetricPreserving_polarMap` as much as a result: a
metric-preserving map is automatically an immersion, so a *vacuous* or degenerate
metric identity could not have been proved. -/
theorem injective_mfderiv_polarMap {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (p : posReals × sphere (0 : E) 1) :
    Function.Injective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) (polarMap E) p) :=
  isMetricPreserving_polarMap.injective_mfderiv p

/-! ### Lee's literal `ℝⁿ ∖ {0}`

The results above are stated for an abstract real inner product space `E` with
`[Fact (finrank ℝ E = n + 1)]`, following mathlib's sphere development.  These
specialisations put them in Lee's own notation, and — more to the point — *test*
that the `Fact` hypothesis is dischargeable, so that Problem 2-4 is not a statement
about an empty class of spaces. -/

/-- **Lee's warped product `ℝ⁺ ×_ρ S^{n-1}`** with `S^{n-1} ⊆ ℝⁿ` literally. -/
def polarWarpedMetricEuclidean (n : ℕ) :
    RiemannianMetric (𝓘(ℝ, ℝ).prod (𝓡 n)) (posReals × sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  polarWarpedMetric (EuclideanSpace ℝ (Fin (n + 1))) n

/-- **Lee's Problem 2-4 for `ℝⁿ`**: `Φ(ρ, ω) = ρ ω` carries the warped product
metric of `ℝ⁺ ×_ρ S^{n-1}` to the Euclidean metric of `ℝⁿ ∖ {0}`.

That this instantiates at all is the non-vacuity check for
`isMetricPreserving_polarMap`: the `Fact (finrank ℝ E = n + 1)` hypothesis is
discharged here by a genuine space, for every `n`. -/
theorem isMetricPreserving_polarMap_euclidean (n : ℕ) :
    haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
    IsMetricPreserving (polarWarpedMetricEuclidean n)
      (euclideanMetric (EuclideanSpace ℝ (Fin (n + 1))))
      (polarMap (EuclideanSpace ℝ (Fin (n + 1)))) := by
  haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  exact isMetricPreserving_polarMap

end

end LeeLib.Ch02
