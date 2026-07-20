import PetersenLib.Ch06.RiccatiEstimate
import PetersenLib.Ch01.SpaceForms

/-!
# Petersen Ch. 6, Example 6.4.5 — conjugate points in the space form `Sⁿ_K`

Petersen's Example 6.4.5 (p. 273, blueprint node
`ex:pet-ch6-conjugate-point-space-form`): on `Sⁿ_K` with `K > 0`, polar
coordinates around `p` present the metric as `dr² + sn_K²(r) dσ²_{n-1}`, and
at distance `π/√K` from `p` *every* direction hits a conjugate point.

## What is proved here (the analytic core)

The content that every downstream result actually consumes (Thm 6.4.6
`conjugateRadiusLowerBound`, Klingenberg, the sphere theorems) is the zero set
of the warping function `sn_K`, which is exactly the metric coefficient of the
polar form:

* `snFunction_pi_div_sqrt_eq_zero` : `sn_K(π/√K) = 0` for `K > 0` — the polar
  coefficient degenerates exactly there, which *is* the conjugate point;
* `snFunction_eq_zero_iff_of_pos` : for `K > 0` the full zero set of `sn_K` is
  `{n·π/√K : n ∈ ℤ}`;
* `isLeast_positive_zero_snFunction` : `π/√K` is the **first** positive zero
  (so `sn_K > 0` on `(0, π/√K)`, reusing `snFunction_pos_of_pos`);
* `snFunction_ne_zero_of_nonpos` : for `K ≤ 0`, `sn_K` has **no** zero on
  `(0, ∞)` — no conjugate points in nonpositive curvature. This is the analytic
  content of the blueprint's `rem:pet-ch6-injectivity-radius-nonpositive`;
* `spaceFormJacobiField` / `spaceFormJacobiField_ode` : the Jacobi-field link.
  Along a unit-speed geodesic in the `K`-space form, with `e` a parallel field
  orthogonal to the geodesic, `J(t) = sn_K(t) • e` solves the Jacobi equation
  `J'' + K·J = 0` (in the parallel trivialization, where the curvature operator
  of the constant-curvature space acts as `K · id` on the normal bundle), and
  `spaceFormJacobiField_eq_zero_iff` says it vanishes at `0` and at `π/√K` and
  nowhere in between — i.e. `c(π/√K)` is conjugate to `c(0)` along `c`, in
  every direction `e`.

The link to the polar form itself is `spaceForm_eq_zero_on_sphere_directions`:
at `r = π/√K` the space-form tensor `dr² + sn_K²(r) dσ²_{n-1}` of
`PetersenLib.spaceForm` (Ch01, Example 1.4.6) annihilates the whole spherical
factor and collapses to `dr²` — the geometric statement that all of `Sⁿ⁻¹`
worth of directions focuses to a single point at distance `π/√K`.

The headline `conjugatePointSpaceFormExample` bundles the three facts the
blueprint's downstream nodes cite.

## What is deferred

The *synthetic* reading of Example 6.4.5 — "`exp_p(π/√K · v)` is a critical
point of `exp_p` for every unit `v`", phrased with `Ch03`'s
`curvatureTensor`/`sectionalCurvature` and an honest `IsJacobiField` predicate
along a geodesic of `Sⁿ_K` — is **not** proved here. It is blocked on the
Ch02↔Ch05 bridge: `PetersenLib.spaceForm` (Ch01) is a metric *tensor* on
`ℝ × Sⁿ⁻¹` built by hand, and its Levi-Civita connection is not yet connected
to the abstract Koszul `RiemannianMetric.leviCivita` of Ch02 (where
`curvatureTensor` lives), nor to the chart-Christoffel `expMap` of Ch05. Once
that bridge exists, `spaceFormJacobiField` below is literally the Jacobi field
one needs, and `spaceForm_eq_zero_on_sphere_directions` the degeneracy; no new
analysis is required.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §6.4, Example 6.4.5,
p. 273.
-/

open Set Filter Metric Module Bundle
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## The zero set of `sn_K` -/

/-- **Math.** Petersen Example 6.4.5 (p. 273): for `K > 0`,
`sn_K(π/√K) = sin(π)/√K = 0`. In the polar presentation
`dr² + sn_K²(r) dσ²_{n-1}` of `Sⁿ_K` this is exactly the degeneration of the
metric coefficient at distance `π/√K` from the pole: the conjugate point. -/
theorem snFunction_pi_div_sqrt_eq_zero {K : ℝ} (hK : 0 < K) :
    snFunction K (Real.pi / Real.sqrt K) = 0 := by
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  rw [snFunction_of_pos hK, mul_div_cancel₀ _ hs.ne']
  simp

/-- **Math.** Petersen Example 6.4.5 (p. 273): for `K > 0` the zero set of
`sn_K` is exactly the arithmetic progression `{n·π/√K : n ∈ ℤ}`, since
`sn_K(t) = sin(√K·t)/√K`. The conjugate points along a geodesic of `Sⁿ_K`
therefore occur precisely at the multiples of `π/√K`. -/
theorem snFunction_eq_zero_iff_of_pos {K : ℝ} (hK : 0 < K) (t : ℝ) :
    snFunction K t = 0 ↔ ∃ n : ℤ, t = n * (Real.pi / Real.sqrt K) := by
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  rw [snFunction_of_pos hK, div_eq_zero_iff]
  simp only [hs.ne', or_false]
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by field_simp at hn ⊢; linarith⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    field_simp

/-- **Math.** Petersen Example 6.4.5 (p. 273): for `K > 0`, `π/√K` is the
**first** positive zero of `sn_K` — it is a zero, and every positive zero is
`≥ π/√K`. Equivalently `sn_K > 0` on `(0, π/√K)`
(`snFunction_pos_of_pos`). -/
theorem isLeast_positive_zero_snFunction {K : ℝ} (hK : 0 < K) :
    IsLeast {t : ℝ | 0 < t ∧ snFunction K t = 0} (Real.pi / Real.sqrt K) := by
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hRpos : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos hs
  refine ⟨⟨hRpos, snFunction_pi_div_sqrt_eq_zero hK⟩, ?_⟩
  rintro t ⟨ht, ht0⟩
  by_contra hlt
  exact absurd ht0 (snFunction_pos_of_pos hK ht (not_le.mp hlt)).ne'

/-- **Math.** Petersen §6.4 (p. 273), the `K ≤ 0` counterpart (blueprint
`rem:pet-ch6-injectivity-radius-nonpositive`): for `K ≤ 0` the function `sn_K`
has **no** zero on `(0, ∞)` — `sn_K(t) = t` for `K = 0` and
`sinh(√(-K)·t)/√(-K)` for `K < 0`, both positive. Analytically this is why
there are no conjugate points in nonpositive curvature. -/
theorem snFunction_ne_zero_of_nonpos {K : ℝ} (hK : K ≤ 0) {t : ℝ} (ht : 0 < t) :
    snFunction K t ≠ 0 :=
  (snFunction_pos_of_nonpos hK ht).ne'

/-! ## The Jacobi field `sn_K · e` -/

section JacobiField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Math.** Petersen Example 6.4.5 (p. 273): the Jacobi field of the space
form `Sⁿ_K` along a unit-speed geodesic `c`, written in a parallel
trivialization of the normal bundle: for `e` a parallel field along `c` with
`e ⊥ ċ`, `J(t) = sn_K(t) • e`. It vanishes at `t = 0` with `J'(0) = e`, and
(for `K > 0`) vanishes again exactly at `t = π/√K`. -/
def spaceFormJacobiField (K : ℝ) (e : E) : ℝ → E := fun t => snFunction K t • e

/-- **Math.** `J(t) = sn_K(t) • e` has derivative `cs_K(t) • e`. -/
theorem hasDerivAt_spaceFormJacobiField (K : ℝ) (e : E) (t : ℝ) :
    HasDerivAt (spaceFormJacobiField K e) (csFunction K t • e) t :=
  (hasDerivAt_snFunction K t).smul_const e

/-- **Math.** Petersen Example 6.4.5 (p. 273): `J = sn_K · e` solves the
**Jacobi equation** `J̈ + K·J = 0`. In a space form of constant curvature `K`
the Jacobi operator `R(·, ċ)ċ` acts on the normal bundle as `K · id`, so the
Jacobi equation along a unit-speed geodesic reduces, in a parallel frame, to
the scalar ODE `ẍ + K·x = 0` of `snFunction_ode`. -/
theorem spaceFormJacobiField_ode (K : ℝ) (e : E) (t : ℝ) :
    deriv (deriv (spaceFormJacobiField K e)) t + K • spaceFormJacobiField K e t = 0 := by
  have h1 : deriv (spaceFormJacobiField K e) = fun s => csFunction K s • e :=
    funext fun s => (hasDerivAt_spaceFormJacobiField K e s).deriv
  rw [h1, ((hasDerivAt_csFunction K t).smul_const e).deriv, spaceFormJacobiField,
    smul_smul, ← add_smul]
  simp

/-- **Math.** Petersen Example 6.4.5 (p. 273): the initial conditions of the
space-form Jacobi field: `J(0) = 0` and `J'(0) = e`. -/
theorem spaceFormJacobiField_zero (K : ℝ) (e : E) :
    spaceFormJacobiField K e 0 = 0 ∧ deriv (spaceFormJacobiField K e) 0 = e := by
  refine ⟨by simp [spaceFormJacobiField], ?_⟩
  rw [(hasDerivAt_spaceFormJacobiField K e 0).deriv, csFunction_zero, one_smul]

/-- **Math.** Petersen Example 6.4.5 (p. 273): for `e ≠ 0` the Jacobi field
`J = sn_K · e` vanishes exactly on the zero set of `sn_K`. Combined with
`isLeast_positive_zero_snFunction`: for `K > 0` it vanishes at `0`, is nonzero
throughout `(0, π/√K)`, and vanishes again at `π/√K` — so `c(π/√K)` is
conjugate to `c(0)` along `c`, and this holds for **every** direction `e`
(the "every direction hits a conjugate point" of the example). -/
theorem spaceFormJacobiField_eq_zero_iff {K : ℝ} {e : E} (he : e ≠ 0) (t : ℝ) :
    spaceFormJacobiField K e t = 0 ↔ snFunction K t = 0 := by
  rw [spaceFormJacobiField, smul_eq_zero]
  simp [he]

end JacobiField

/-! ## The link to the polar form `dr² + sn_K²(r) dσ²_{n-1}` -/

section PolarForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- **Math.** Petersen Example 6.4.5 (p. 273): the polar form degenerates at
`r = π/√K`. The space-form tensor `PetersenLib.spaceForm K` of Ch01
(Example 1.4.6) is the polar presentation `dr² + sn_K²(r) dσ²_{n-1}` of `Sⁿ_K`
on `ℝ × Sⁿ⁻¹`; at `r = π/√K` its warping coefficient `sn_K(r)` vanishes
(`snFunction_pi_div_sqrt_eq_zero`), so the tensor annihilates the entire
spherical factor and collapses to `dr²`:
`spaceForm K p u v = u₁ v₁`. Geometrically: the whole sphere `{π/√K} × Sⁿ⁻¹`
of directions is crushed to a single point — the conjugate point antipodal
to `p`. -/
theorem spaceForm_eq_radial_at_pi_div_sqrt {K : ℝ} (hK : 0 < K)
    {p : ℝ × Metric.sphere (0 : E) 1} (hp : p.1 = Real.pi / Real.sqrt K)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p) :
    spaceForm K p u v = u.1 * v.1 := by
  rw [spaceForm_apply, hp, snFunction_pi_div_sqrt_eq_zero hK]
  simp

/-- **Math.** Petersen Example 6.4.5 (p. 273): at `r = π/√K` the space-form
tensor kills every vector tangent to the spherical factor — the failure of
positive definiteness that `spaceForm_pos` (Ch01) excludes precisely by
assuming `sn_K(r) ≠ 0`. Every purely spherical direction `u` (i.e. `u₁ = 0`)
has `spaceForm K p u u = 0` even when `u ≠ 0`. -/
theorem spaceForm_eq_zero_on_sphere_directions {K : ℝ} (hK : 0 < K)
    {p : ℝ × Metric.sphere (0 : E) 1} (hp : p.1 = Real.pi / Real.sqrt K)
    (u : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p) (hu : u.1 = 0) :
    spaceForm K p u u = 0 := by
  rw [spaceForm_eq_radial_at_pi_div_sqrt hK hp, hu, mul_zero]

end PolarForm

/-! ## The headline statement -/

/-- **Math.** Petersen Example 6.4.5 (p. 273), the analytic core: on `Sⁿ_K`
with `K > 0`, polar coordinates around `p` give `dr² + sn_K²(r) dσ²_{n-1}`, and
at distance `π/√K` from `p` every direction hits a conjugate point.

The three facts stated, which are what the downstream nodes (Thm 6.4.6
`conjugateRadiusLowerBound`, Klingenberg, the sphere theorems) consume:

1. `sn_K(π/√K) = 0` — the polar metric coefficient degenerates exactly at
   distance `π/√K`, which *is* the conjugate point;
2. `sn_K > 0` on `(0, π/√K)` — so `π/√K` is the *first* such distance, i.e.
   the conjugate radius of `Sⁿ_K` is exactly `π/√K` and not less;
3. `sn_K` solves the Jacobi equation `ẍ + K·x = 0` — so `t ↦ sn_K(t)·e`, for a
   parallel normal field `e` along a unit-speed geodesic, is literally the
   Jacobi field vanishing at `0` and at `π/√K` (`spaceFormJacobiField`,
   `spaceFormJacobiField_ode`), in *every* direction `e`.

That `π/√K` is the least positive zero is `isLeast_positive_zero_snFunction`;
the full zero set is `snFunction_eq_zero_iff_of_pos`; the degeneration of the
Ch01 polar tensor itself is `spaceForm_eq_radial_at_pi_div_sqrt`. See the
module docstring for what the synthetic reading additionally needs. -/
theorem conjugatePointSpaceFormExample {K : ℝ} (hK : 0 < K) :
    snFunction K (Real.pi / Real.sqrt K) = 0 ∧
      (∀ t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt K), 0 < snFunction K t) ∧
      (∀ t : ℝ, deriv (deriv (snFunction K)) t + K * snFunction K t = 0) :=
  ⟨snFunction_pi_div_sqrt_eq_zero hK,
    fun _ ht => snFunction_pos_of_pos hK ht.1 ht.2,
    fun t => by rw [snFunction_ode]; ring⟩

end PetersenLib
