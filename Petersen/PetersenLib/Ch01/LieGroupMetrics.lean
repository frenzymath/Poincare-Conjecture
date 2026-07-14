import PetersenLib.Ch01.MetricConstructions
import PetersenLib.Ch01.CoordinateRepresentations
import PetersenLib.Ch01.HopfFibration
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Petersen Ch. 1, Examples 1.3.5 & 1.4.3 — SU(2), Berger spheres, and
left-invariant coframes

Two Lie-group examples of Petersen §1.3.2 and §1.4.3:

* **Example 1.4.3** (`leftInvariantCoframeMetric`): on a Lie group `G` with a
  left-invariant metric induced by an inner product `b` on the Lie algebra
  `T_eG`, the left-invariant frame `X_i = dL_x(e_i)` obtained from a basis
  `e_i` of `T_eG` has a dual coframe `σ^i`, and `g = g_{ij} σ^i σ^j` where
  `g_{ij} = b(e_i, e_j)` is a *constant* positive-definite symmetric matrix —
  the metric depends only on its values on `T_eG`
  (`frameRepresentation_leftInvariantFrame`). If the `e_i` are orthonormal,
  `g = (σ^1)² + ⋯ + (σ^n)²` (`leftInvariantCoframeMetric_orthonormal`).

* **Example 1.3.5** (`suTwoMetric`, `bergerSphereMetric`):
  `SU(2) = {A ∈ M₂(ℂ) | det A = 1, A* = A⁻¹} = {[[z, w], [-w̄, z̄]]} = S³(1)`
  (`mem_specialUnitaryGroup_fin_two_iff`, `suTwoEquivSphere`). The Lie-algebra
  frame `X₁ = diag(i, -i)`, `X₂ = [[0,1],[-1,0]]`, `X₃ = [[0,i],[i,0]]`,
  transported along the orbits of the flows `g ↦ exp(tX_i) · g`, becomes on
  `S³(1) ⊆ ℂ²` the frame `X₁(x) = ix`, `X₂(x) = jx`, `X₃(x) = kx` (quaternion
  notation) — in the coordinates of `PetersenLib.HopfFibration` these are
  `hopfVertical` and `hopfHorizontal · 1`, `hopfHorizontal · i`. Declaring
  them orthonormal recovers the round metric `S³(1)` (`suTwoMetric`,
  `suTwoMetric_coframe`); declaring them orthogonal with `|X₁| = ε` and
  `X₂, X₃` unit gives the **Berger spheres** (`bergerSphereMetric`,
  `bergerSphereMetric_coframe`), obtained from the canonical metric by
  scaling the Hopf-fibre direction `X₁` (tangent to the scalar-multiplication
  circle action, Petersen's displayed computation) by `ε²`.

## Implementation

* `S³(1)` is `Metric.sphere (0 : WithLp 2 (ℂ × ℂ)) 1`, the ambient `ℂ²` and
  frame vectors being those of `PetersenLib.Ch01.HopfFibration`; the group
  structure is carried by `Matrix.specialUnitaryGroup (Fin 2) ℂ` and
  identified with the sphere via `suTwoEquivSphere` (Mathlib has no
  Lie-group structure on `specialUnitaryGroup` at this pin, so the metric
  lives on the sphere and the identification is recorded separately).
* The Berger metric is the pullback along `S³ ↪ ℂ²` of an ambient metric
  `bergerAmbientMetric` on all of `ℂ²` which restricts on the unit sphere to
  `⟨u,v⟩ + (ε² - 1)⟨u, ix⟩⟨v, ix⟩`; the interpolation factor
  `(ε² - 1)/(‖y‖⁴ - ‖y‖² + 1)` keeps the ambient form positive definite for
  every `ε ≠ 0` (`bergerAmbientForm_self_pos`), so the general
  `pullbackMetric` machinery applies verbatim.
* On which side the translations act: Petersen calls `g_ε` left-invariant and
  simultaneously identifies the Hopf circle through `g` with the orbit
  `θ ↦ diag(e^{iθ}, e^{-iθ}) · g` of *left* translations. With the (row)
  identification `[[z,w],[-w̄,z̄]] ↔ (z,w)` used here and in the literature
  on this example, the frame `X_i(x) = X_i · x` is tangent to flows of left
  translations and is equivariant under *right* translations
  `R_q : x ↦ x · q` — concretely the complex-linear unitary maps
  `suTwoTranslation`, under which `g_ε` is invariant
  (`bergerAmbientForm_suTwoTranslation`). The two conventions are exchanged
  by the group anti-automorphism `g ↦ g⁻¹`, which carries left-invariant
  metrics to right-invariant ones with the same value at `e`; the resulting
  Riemannian manifolds are isometric, and we record the invariance on the
  side that matches Petersen's Hopf-circle computation.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Examples 1.3.5, 1.4.3.
-/

open Metric Module Function Bundle ComplexConjugate
open scoped ContDiff Manifold Topology InnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-! ## Petersen Example 1.4.3 — left-invariant metrics via a coframe

A frame of left-invariant vector fields `X_i(x) = dL_x(e_i)` on a Lie group,
its dual coframe `σ^i`, and the representation `g = g_{ij} σ^i σ^j` of a
left-invariant metric with *constant* coefficients `g_{ij} = b(e_i, e_j)`. -/

section LeftInvariantCoframe

variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G]

/-- **Math.** Chain rule on a Lie group: `d(L_{x⁻¹})_x ∘ d(L_x)_e = id` on
`T_eG`, since `L_{x⁻¹} ∘ L_x = id`. -/
theorem mfderiv_mul_left_inv_mfderiv_mul_left (x : G) (u : TangentSpace I (1 : G)) :
    mfderiv I I (x⁻¹ * ·) x (mfderiv I I (x * ·) (1 : G) u) = u := by
  have h1 : mfderiv I I ((x⁻¹ * ·) ∘ (x * ·)) (1 : G) u
      = mfderiv I I (x⁻¹ * ·) (x * 1) (mfderiv I I (x * ·) (1 : G) u) :=
    mfderiv_comp_apply (1 : G)
      (mdifferentiableAt_mul_left (I := I) (a := x⁻¹) (b := x * 1))
      (mdifferentiableAt_mul_left (I := I) (a := x) (b := (1 : G))) u
  have hpt : (mfderiv I I (x⁻¹ * ·) (x * 1) : E →L[ℝ] E) = mfderiv I I (x⁻¹ * ·) x := by
    rw [mul_one]
  have h2 := congrArg (fun T : E →L[ℝ] E => T (mfderiv I I (x * ·) (1 : G) u)) hpt
  simp only at h2
  have h3 : mfderiv I I ((x⁻¹ * ·) ∘ (x * ·)) (1 : G) u = u := by
    have hcomp : ((x⁻¹ * ·) ∘ (x * ·) : G → G) = id := by
      funext z; simp
    rw [hcomp, mfderiv_id]
    rfl
  exact h2.symm.trans (h1.symm.trans h3)

/-- **Math.** Chain rule on a Lie group: `d(L_x)_e ∘ d(L_{x⁻¹})_x = id` on
`T_xG`, since `L_x ∘ L_{x⁻¹} = id`. -/
theorem mfderiv_mul_left_mfderiv_mul_left_inv (x : G) (u : TangentSpace I x) :
    mfderiv I I (x * ·) (1 : G) (mfderiv I I (x⁻¹ * ·) x u) = u := by
  have h1 : mfderiv I I ((x * ·) ∘ (x⁻¹ * ·)) x u
      = mfderiv I I (x * ·) (x⁻¹ * x) (mfderiv I I (x⁻¹ * ·) x u) :=
    mfderiv_comp_apply x
      (mdifferentiableAt_mul_left (I := I) (a := x) (b := x⁻¹ * x))
      (mdifferentiableAt_mul_left (I := I) (a := x⁻¹) (b := x)) u
  have hpt : (mfderiv I I (x * ·) (x⁻¹ * x) : E →L[ℝ] E) = mfderiv I I (x * ·) (1 : G) := by
    rw [inv_mul_cancel]
  have h2 := congrArg (fun T : E →L[ℝ] E => T (mfderiv I I (x⁻¹ * ·) x u)) hpt
  simp only at h2
  have h3 : mfderiv I I ((x * ·) ∘ (x⁻¹ * ·)) x u = u := by
    have hcomp : ((x * ·) ∘ (x⁻¹ * ·) : G → G) = id := by
      funext z; simp
    rw [hcomp, mfderiv_id]
    rfl
  exact h2.symm.trans (h1.symm.trans h3)

/-- **Math.** Petersen §1.3.2/§1.4.3: the differential of left translation
`d(L_x)_e : T_eG ≃ T_xG` as a linear equivalence, with inverse
`d(L_{x⁻¹})_x`. This is the trivialization `TG ≃ G × T_eG` at the point `x`. -/
def mulLeftTangentEquiv (x : G) : TangentSpace I (1 : G) ≃ₗ[ℝ] TangentSpace I x :=
  let f : E →L[ℝ] E := mfderiv I I (x * ·) (1 : G)
  let g : E →L[ℝ] E := mfderiv I I (x⁻¹ * ·) x
  LinearEquiv.ofLinear (f : E →ₗ[ℝ] E) (g : E →ₗ[ℝ] E)
    (LinearMap.ext fun u => mfderiv_mul_left_mfderiv_mul_left_inv x u)
    (LinearMap.ext fun u => mfderiv_mul_left_inv_mfderiv_mul_left x u)

@[simp]
theorem mulLeftTangentEquiv_apply (x : G) (u : TangentSpace I (1 : G)) :
    mulLeftTangentEquiv (I := I) x u = mfderiv I I (x * ·) (1 : G) u :=
  rfl

@[simp]
theorem mulLeftTangentEquiv_symm_apply (x : G) (u : TangentSpace I x) :
    (mulLeftTangentEquiv (I := I) x).symm u = mfderiv I I (x⁻¹ * ·) x u :=
  rfl

/-- **Math.** Petersen Example 1.4.3: the **left-invariant frame**
`X_1, …, X_n` on `G` determined by a basis `e_1, …, e_n` of the Lie algebra
`T_eG`: at `x` the basis `X_i(x) = d(L_x)_e(e_i)` of `T_xG`. -/
def leftInvariantFrame {n : ℕ} (e : Module.Basis (Fin n) ℝ E) (x : G) :
    Module.Basis (Fin n) ℝ (TangentSpace I x) :=
  e.map (mulLeftTangentEquiv (I := I) x)

@[simp]
theorem leftInvariantFrame_apply {n : ℕ} (e : Module.Basis (Fin n) ℝ E) (x : G)
    (i : Fin n) :
    leftInvariantFrame (I := I) e x i = mfderiv I I (x * ·) (1 : G) (e i) :=
  rfl

/-- **Math.** Petersen Example 1.4.3: the **dual coframe** `σ^i` of the
left-invariant frame evaluates through the inverse differential:
`σ^i(v) = e^i(d(L_{x⁻¹})_x v)`, the `i`-th Lie-algebra coordinate of `v`
translated back to `T_eG`. -/
theorem leftInvariantFrame_repr_apply {n : ℕ} (e : Module.Basis (Fin n) ℝ E)
    (x : G) (v : TangentSpace I x) (i : Fin n) :
    (leftInvariantFrame (I := I) e x).repr v i
      = e.repr (mfderiv I I (x⁻¹ * ·) x v) i :=
  rfl

/-- **Math.** Coframe duality `σ^i(X_j) = δ^i_j` for the left-invariant frame
and its coframe. -/
theorem leftInvariantFrame_repr_self {n : ℕ} (e : Module.Basis (Fin n) ℝ E)
    (x : G) (i j : Fin n) :
    (leftInvariantFrame (I := I) e x).repr (leftInvariantFrame (I := I) e x j) i
      = if j = i then 1 else 0 :=
  Module.Basis.repr_self_apply _ _ _

/-- **Math.** Petersen Example 1.4.3, the heart of the example: in the
left-invariant frame, the frame representation `g_{ij} = g(X_i, X_j)` of the
left-invariant metric induced by `b` is the **constant** matrix
`g_{ij} = b(e_i, e_j)` — a left-invariant metric depends only on its values
on `T_eG`. It is symmetric and positive definite because `b` is. -/
theorem frameRepresentation_leftInvariantFrame [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < b u u) {n : ℕ}
    (e : Module.Basis (Fin n) ℝ E) (x : G) (i j : Fin n) :
    frameRepresentation (leftInvariantMetric (I := I) b hsymm hpos)
      (leftInvariantFrame (I := I) e x) i j = b (e i) (e j) := by
  show leftInvariantForm (I := I) b x
      (leftInvariantFrame (I := I) e x i) (leftInvariantFrame (I := I) e x j) = _
  rw [leftInvariantForm_apply, leftInvariantFrame_apply, leftInvariantFrame_apply,
    mfderiv_mul_left_inv_mfderiv_mul_left, mfderiv_mul_left_inv_mfderiv_mul_left]

/-- **Math.** Petersen Example 1.4.3: a left-invariant metric written in a
left-invariant coframe, `g = g_{ij} σ^i σ^j` with `g_{ij} = b(e_i, e_j)` a
positive-definite symmetric **constant** matrix: for all `v, w ∈ T_xG`,
`g(v, w) = ∑_{ij} σ^i(v) σ^j(w) b(e_i, e_j)`. -/
theorem leftInvariantCoframeMetric [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < b u u) {n : ℕ}
    (e : Module.Basis (Fin n) ℝ E) (x : G) (v w : TangentSpace I x) :
    (leftInvariantMetric (I := I) b hsymm hpos).metricInner x v w
      = ∑ i, ∑ j,
          ((leftInvariantFrame (I := I) e x).repr v i) *
            ((leftInvariantFrame (I := I) e x).repr w j) * b (e i) (e j) := by
  rw [frameRepresentation_expansion (leftInvariantMetric (I := I) b hsymm hpos)
    (leftInvariantFrame (I := I) e x) v w]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [frameRepresentation_leftInvariantFrame]

/-- **Math.** Petersen Example 1.4.3, first display: if the `X_i` form an
orthonormal basis for the Lie algebra (`b(e_i, e_j) = δ_{ij}`), the
left-invariant metric is `g = (σ^1)² + ⋯ + (σ^n)²`. -/
theorem leftInvariantCoframeMetric_orthonormal [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < b u u) {n : ℕ}
    (e : Module.Basis (Fin n) ℝ E)
    (hb : ∀ i j, b (e i) (e j) = if i = j then 1 else 0)
    (x : G) (v w : TangentSpace I x) :
    (leftInvariantMetric (I := I) b hsymm hpos).metricInner x v w
      = ∑ i,
          ((leftInvariantFrame (I := I) e x).repr v i) *
            ((leftInvariantFrame (I := I) e x).repr w i) := by
  refine frameRepresentation_orthonormal _ (leftInvariantFrame (I := I) e x)
    (fun i j => ?_) v w
  show frameRepresentation (leftInvariantMetric (I := I) b hsymm hpos)
      (leftInvariantFrame (I := I) e x) i j = _
  exact (frameRepresentation_leftInvariantFrame b hsymm hpos e x i j).trans (hb i j)

end LeftInvariantCoframe

/-! ## Smooth families of bilinear forms on a vector space

The variable-coefficient generalization of `constantForm_contMDiff`
(`PetersenLib.Ch01.Minkowski`): on a vector space viewed as a manifold over
itself the tangent trivializations are the identity, so a `ContDiff` family
of bilinear forms is a smooth section of the bundle of bilinear forms. -/

section ContDiffForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** On a vector space `F` viewed as a manifold over itself, a
`C^∞` family of bilinear forms `x ↦ B x` is a smooth section of the bundle
of bilinear forms on the tangent spaces: in the canonical trivialization
`TF ≃ F × F` the section is literally the map `B`. This supplies the
smoothness field of variable-coefficient metrics on `F` such as the ambient
Berger form `bergerAmbientForm`. -/
theorem contDiffForm_contMDiff {B : F → F →L[ℝ] F →L[ℝ] ℝ}
    (hB : ContDiff ℝ ∞ B) :
    ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, B x⟩ : Bundle.TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ))) := by
  intro x
  rw [contMDiffAt_section]
  have heq : (fun x' : F => (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
      (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ) x
        ⟨x', B x'⟩).2) = B := by
    funext x'
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]
  rw [heq]
  exact hB.contMDiff.contMDiffAt

end ContDiffForm

/-! ## The ambient Berger form on `ℂ²`

The bilinear form on `ℂ² = WithLp 2 (ℂ × ℂ)` which restricts on the unit
sphere `S³(1)` to the Berger form `⟨u,v⟩ + (ε² − 1)⟨u, ix⟩⟨v, ix⟩`. Away from
the sphere the correction is damped by `q(y) = ‖y‖⁴ − ‖y‖² + 1` (which equals
`1` on the sphere and is bounded below by `3/4`), keeping the ambient form
positive definite for every `ε ≠ 0`, so that the pullback machinery for
metrics applies directly. -/

section BergerAmbient

/-- **Math.** The tangent field of the Hopf circle action, `y ↦ iy`, as a
continuous linear map of `ℂ²`: complex-scalar multiplication by `i` in both
coordinates. Its value at `y` is `hopfVertical y.fst y.snd`
(`hopfVerticalCLM_apply`) — Petersen's left-invariant field `X₁` on
`SU(2) = S³`. -/
def hopfVerticalCLM : WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm :
      ℂ × ℂ →L[ℝ] WithLp 2 (ℂ × ℂ)).comp
    (((ContinuousLinearMap.mul ℝ ℂ Complex.I).prodMap
        (ContinuousLinearMap.mul ℝ ℂ Complex.I)).comp
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ) :
        WithLp 2 (ℂ × ℂ) →L[ℝ] ℂ × ℂ))

@[simp]
theorem hopfVerticalCLM_apply (y : WithLp 2 (ℂ × ℂ)) :
    hopfVerticalCLM y = hopfVertical y.fst y.snd :=
  rfl

/-- **Math.** The **ambient Berger form** on `ℂ²`:
`B_y(u, v) = ⟨u, v⟩ + ((ε² − 1)/q(y)) ⟨iy, u⟩⟨iy, v⟩` with
`q(y) = ‖y‖⁴ − ‖y‖² + 1`. On the unit sphere `q ≡ 1` and the form restricts
to the Berger metric `ε²(σ¹)² + (σ²)² + (σ³)²` of Petersen Example 1.3.5. -/
def bergerAmbientForm (ε : ℝ) (y : WithLp 2 (ℂ × ℂ)) :
    WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) →L[ℝ] ℝ :=
  letI base : WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) →L[ℝ] ℝ := innerSL ℝ
  base + ((ε ^ 2 - 1) / (‖y‖ ^ 2 * ‖y‖ ^ 2 - ‖y‖ ^ 2 + 1)) •
      (innerSL ℝ (hopfVerticalCLM y)).smulRight (innerSL ℝ (hopfVerticalCLM y))

@[simp]
theorem bergerAmbientForm_apply (ε : ℝ) (y u v : WithLp 2 (ℂ × ℂ)) :
    bergerAmbientForm ε y u v
      = ⟪u, v⟫_ℝ + (ε ^ 2 - 1) / (‖y‖ ^ 2 * ‖y‖ ^ 2 - ‖y‖ ^ 2 + 1) *
          (⟪hopfVertical y.fst y.snd, u⟫_ℝ * ⟪hopfVertical y.fst y.snd, v⟫_ℝ) :=
  rfl

/-- **Math.** The ambient Berger form is symmetric. -/
theorem bergerAmbientForm_symm (ε : ℝ) (y u v : WithLp 2 (ℂ × ℂ)) :
    bergerAmbientForm ε y u v = bergerAmbientForm ε y v u := by
  rw [bergerAmbientForm_apply, bergerAmbientForm_apply, real_inner_comm u v]
  ring

/-- **Math.** The squared norm of the Hopf vertical field: `‖iy‖² = ‖y‖²`
(multiplication by `i` is a linear isometry). -/
theorem norm_sq_hopfVertical (y : WithLp 2 (ℂ × ℂ)) :
    ‖hopfVertical y.fst y.snd‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2 y,
    hopfVertical_fst, hopfVertical_snd, norm_mul, norm_mul, Complex.norm_I,
    one_mul, one_mul]

/-- **Math.** Positive definiteness of the ambient Berger form for every
`ε ≠ 0`. With `t = ‖y‖²`, `s = ⟨iy, u⟩` and `q = t² − t + 1 ≥ 3/4`,
Cauchy–Schwarz gives `s² ≤ t⟨u,u⟩`, so for `ε² ≤ 1`

  `q⟨u,u⟩ + (ε² − 1)s² ≥ ⟨u,u⟩(q − (1 − ε²)t) = ⟨u,u⟩((t−1)² + ε²t) > 0`,

while for `ε² > 1` both summands are already nonnegative with the first
positive. -/
theorem bergerAmbientForm_self_pos {ε : ℝ} (hε : ε ≠ 0)
    (y u : WithLp 2 (ℂ × ℂ)) (hu : u ≠ 0) :
    0 < bergerAmbientForm ε y u u := by
  rw [bergerAmbientForm_apply]
  set t : ℝ := ‖y‖ ^ 2 with ht_def
  set s : ℝ := ⟪hopfVertical y.fst y.snd, u⟫_ℝ with hs_def
  have ht : 0 ≤ t := sq_nonneg ‖y‖
  have hu2 : 0 < ⟪u, u⟫_ℝ := real_inner_self_pos.mpr hu
  have hε2 : 0 < ε ^ 2 := by positivity
  have hq : 0 < t * t - t + 1 := by nlinarith [sq_nonneg (2 * t - 1)]
  have hcs : s * s ≤ t * ⟪u, u⟫_ℝ := by
    have h := real_inner_mul_inner_self_le (hopfVertical y.fst y.snd) u
    have hXX : ⟪hopfVertical y.fst y.snd, hopfVertical y.fst y.snd⟫_ℝ = t := by
      rw [real_inner_self_eq_norm_sq, norm_sq_hopfVertical]
    rwa [hXX] at h
  have key : 0 < (t * t - t + 1) * ⟪u, u⟫_ℝ + (ε ^ 2 - 1) * (s * s) := by
    rcases le_or_gt (ε ^ 2) 1 with h1 | h1
    · rcases eq_or_lt_of_le ht with h0 | h0
      · have hs0 : s * s ≤ 0 := by rw [← h0] at hcs; simpa using hcs
        nlinarith [mul_self_nonneg s]
      · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hcs),
          mul_pos (mul_pos hε2 h0) hu2, mul_nonneg hu2.le (sq_nonneg (t - 1))]
    · nlinarith [mul_pos hq hu2,
        mul_nonneg (sub_nonneg.mpr h1.le) (mul_self_nonneg s)]
  have hsplit : ⟪u, u⟫_ℝ + (ε ^ 2 - 1) / (t * t - t + 1) * (s * s)
      = ((t * t - t + 1) * ⟪u, u⟫_ℝ + (ε ^ 2 - 1) * (s * s)) / (t * t - t + 1) := by
    rw [add_div, mul_div_cancel_left₀ _ hq.ne', div_mul_eq_mul_div]
  rw [hsplit]
  exact div_pos key hq

/-- The real inner product on `ℂ²` bundled as a continuous *bilinear* map:
`innerSL ℝ` with its star-semilinear type unfolded (over `ℝ` the two types
are definitionally equal). -/
private def innerCLM : WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) →L[ℝ] ℝ :=
  innerSL ℝ

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxSynthPendingDepth 3 in
/-- **Math.** The ambient Berger form varies smoothly with the base point:
the correction term is the product of the smooth scalar
`(ε² − 1)/(‖y‖⁴ − ‖y‖² + 1)` (the denominator is bounded below by `3/4`)
and the rank-one form `⟨iy, ·⟩⟨iy, ·⟩`, which depends on `y` through the
continuous linear map `hopfVerticalCLM`. -/
theorem contDiff_bergerAmbientForm (ε : ℝ) :
    ContDiff ℝ ∞ (bergerAmbientForm ε) := by
  have hG : ContDiff ℝ ∞
      (fun y : WithLp 2 (ℂ × ℂ) => innerSL ℝ (hopfVerticalCLM y)) :=
    (innerCLM.comp hopfVerticalCLM).contDiff
  have hrank : ContDiff ℝ ∞
      (fun y : WithLp 2 (ℂ × ℂ) =>
        (innerSL ℝ (hopfVerticalCLM y)).smulRight (innerSL ℝ (hopfVerticalCLM y))) := by
    have h1 : ContDiff ℝ ∞
        (fun y : WithLp 2 (ℂ × ℂ) =>
          ContinuousLinearMap.smulRightL ℝ (WithLp 2 (ℂ × ℂ))
            (WithLp 2 (ℂ × ℂ) →L[ℝ] ℝ) (innerSL ℝ (hopfVerticalCLM y))) :=
      ((ContinuousLinearMap.smulRightL ℝ (WithLp 2 (ℂ × ℂ))
        (WithLp 2 (ℂ × ℂ) →L[ℝ] ℝ)).comp (innerCLM.comp hopfVerticalCLM)).contDiff
    exact h1.clm_apply hG
  have hden : ∀ y : WithLp 2 (ℂ × ℂ), ‖y‖ ^ 2 * ‖y‖ ^ 2 - ‖y‖ ^ 2 + 1 ≠ 0 := by
    intro y
    have ht : (0 : ℝ) ≤ ‖y‖ ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (2 * ‖y‖ ^ 2 - 1)]
  have hnormsq : ContDiff ℝ ∞ (fun y : WithLp 2 (ℂ × ℂ) => ‖y‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hc : ContDiff ℝ ∞
      (fun y : WithLp 2 (ℂ × ℂ) =>
        (ε ^ 2 - 1) / (‖y‖ ^ 2 * ‖y‖ ^ 2 - ‖y‖ ^ 2 + 1)) :=
    contDiff_const.div (((hnormsq.mul hnormsq).sub hnormsq).add contDiff_const) hden
  exact contDiff_const.add (hc.smul hrank)

/-- **Math.** The **ambient Berger metric** on `ℂ²`: the Riemannian metric
with form `bergerAmbientForm ε`, positive definite for every `ε ≠ 0`
(`bergerAmbientForm_self_pos`) and smooth (`contDiff_bergerAmbientForm`).
Its restriction to the unit sphere is the Berger sphere `bergerSphereMetric`. -/
def bergerAmbientMetric (ε : ℝ) (hε : ε ≠ 0) :
    RiemannianMetric 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) (WithLp 2 (ℂ × ℂ)) where
  inner y := bergerAmbientForm ε y
  symm y u v := bergerAmbientForm_symm ε y u v
  pos y u hu := bergerAmbientForm_self_pos hε y u hu
  isVonNBounded y := isVonNBounded_of_posDef (bergerAmbientForm ε y)
    fun u hu => bergerAmbientForm_self_pos hε y u hu
  contMDiff := contDiffForm_contMDiff (contDiff_bergerAmbientForm ε)

end BergerAmbient

/-! ## The Berger sphere metrics on `S³` (Petersen Example 1.3.5)

The pullback of the ambient Berger metric along the inclusion
`S³(1) ↪ ℂ²`. On the sphere the damping factor `q ≡ 1`, so
`g_ε(u, v) = ⟨u, v⟩ + (ε² − 1)⟨ix, u⟩⟨ix, v⟩` — the round metric with the
Hopf-fibre direction scaled by `ε²`; `ε = 1` recovers the round metric. -/

section BergerSphere

/-- **Math.** Petersen Example 1.3.5: the **Berger sphere** `(S³, g_ε)`,
`ε ≠ 0`: the metric on `S³(1) ⊆ ℂ²` induced from the ambient Berger metric
by the inclusion (a smooth immersion). In the left-invariant coframe
`σ¹, σ², σ³` dual to `X₁(x) = ix`, `X₂(x) = jx`, `X₃(x) = kx` it reads
`g_ε = ε²(σ¹)² + (σ²)² + (σ³)²` (`bergerSphereMetric_coframe`): the round
metric rescaled by `ε²` along the Hopf fibre. -/
def bergerSphereMetric (ε : ℝ) (hε : ε ≠ 0) :
    RiemannianMetric (𝓡 3) (sphere (0 : WithLp 2 (ℂ × ℂ)) 1) :=
  pullbackMetric (bergerAmbientMetric ε hε)
    ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ))
    isSmoothImmersion_coe_sphere

@[simp]
theorem bergerSphereMetric_apply (ε : ℝ) (hε : ε ≠ 0)
    (x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1) (u v : TangentSpace (𝓡 3) x) :
    (bergerSphereMetric ε hε).metricInner x u v
      = bergerAmbientForm ε (x : WithLp 2 (ℂ × ℂ))
          (mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
            ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) x u)
          (mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
            ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) x v) :=
  rfl

/-- **Math.** The inclusion `(S³, g_ε) ↪ (ℂ², bergerAmbientMetric)` is a
Riemannian (isometric) immersion — the Berger sphere is a metric
submanifold of the ambient Berger metric by construction. -/
theorem bergerSphereMetric_isRiemannianImmersion (ε : ℝ) (hε : ε ≠ 0) :
    IsRiemannianImmersion (bergerSphereMetric ε hε) (bergerAmbientMetric ε hε)
      ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) :=
  pullbackMetric_isRiemannianImmersion _ _ _

/-- **Math.** Petersen Example 1.3.5: the left-invariant metric on
`SU(2) = S³(1)` making `X₁, X₂, X₃` orthonormal — the Berger metric at
`ε = 1`, which is the round metric of `S³(1)`
(`suTwoMetric_eq_sphereMetricUnit`). -/
def suTwoMetric : RiemannianMetric (𝓡 3) (sphere (0 : WithLp 2 (ℂ × ℂ)) 1) :=
  bergerSphereMetric 1 one_ne_zero

/-- **Math.** Petersen Example 1.3.5: at `ε = 1` the Berger correction
vanishes and `suTwoMetric` is the canonical (round) metric of the unit
sphere `S³(1)`: declaring the left-invariant frame `X₁, X₂, X₃`
orthonormal gives back the metric induced from `ℂ²`. -/
theorem suTwoMetric_eq_sphereMetricUnit (x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1)
    (u v : TangentSpace (𝓡 3) x) :
    suTwoMetric.metricInner x u v
      = (sphereMetricUnit (WithLp 2 (ℂ × ℂ))).metricInner x u v := by
  rw [suTwoMetric, bergerSphereMetric_apply, bergerAmbientForm_apply,
    sphereMetricUnit_apply]
  norm_num

/-! ### The left-invariant frame of `SU(2)` on the sphere

Petersen's Lie-algebra frame `X₁ = diag(i, −i)`, `X₂ = [[0,1],[−1,0]]`,
`X₃ = [[0,i],[i,0]]` of left-invariant fields, read on `S³ ⊆ ℂ²` through the
row identification `[[z,w],[−w̄,z̄]] ↔ (z,w)`: `X₁(x) = ix` (the Hopf
vertical field) and `X₂(x), X₃(x)` the horizontal fields `hopfHorizontal`
at `λ = 1, i` (quaternionically, `ix, jx, kx`). -/

/-- **Math.** Petersen Example 1.3.5: the left-invariant frame of
`SU(2) = S³` in ambient coordinates: `X₁(x) = ix` (tangent to the Hopf
circle action), `X₂(x) = jx`, `X₃(x) = kx` (the horizontal plane). -/
def suTwoFrame (x : WithLp 2 (ℂ × ℂ)) : Fin 3 → WithLp 2 (ℂ × ℂ) :=
  ![hopfVertical x.fst x.snd,
    hopfHorizontal x.fst x.snd 1,
    hopfHorizontal x.fst x.snd Complex.I]

@[simp]
theorem suTwoFrame_zero (x : WithLp 2 (ℂ × ℂ)) :
    suTwoFrame x 0 = hopfVertical x.fst x.snd :=
  rfl

@[simp]
theorem suTwoFrame_one (x : WithLp 2 (ℂ × ℂ)) :
    suTwoFrame x 1 = hopfHorizontal x.fst x.snd 1 :=
  rfl

@[simp]
theorem suTwoFrame_two (x : WithLp 2 (ℂ × ℂ)) :
    suTwoFrame x 2 = hopfHorizontal x.fst x.snd Complex.I :=
  rfl

/-- **Math.** The vertical and horizontal frame fields are orthogonal:
`⟪i(z,w), λ(−w̄, z̄)⟫_ℝ = Re(−λw̄ · conj(iz)) + Re(λz̄ · conj(iw)) = 0`. -/
theorem real_inner_hopfVertical_hopfHorizontal (z w l : ℂ) :
    ⟪hopfVertical z w, hopfHorizontal z w l⟫_ℝ = 0 := by
  simp only [hopfVertical, hopfHorizontal, WithLp.prod_inner_apply, Complex.inner]
  simp only [map_mul, Complex.conj_I, Complex.neg_re, Complex.mul_re,
    Complex.mul_im, Complex.neg_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im]
  ring

/-- **Math.** The squared length of the vertical field:
`⟪i(z,w), i(z,w)⟫_ℝ = |z|² + |w|²` — unit on the unit sphere. -/
theorem real_inner_hopfVertical_self (z w : ℂ) :
    ⟪hopfVertical z w, hopfVertical z w⟫_ℝ = ‖z‖ ^ 2 + ‖w‖ ^ 2 :=
  calc ⟪hopfVertical z w, hopfVertical z w⟫_ℝ
      = ‖hopfVertical z w‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = ‖WithLp.toLp 2 (z, w)‖ ^ 2 := norm_sq_hopfVertical (WithLp.toLp 2 (z, w))
    _ = ‖z‖ ^ 2 + ‖w‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _

/-- **Math.** Petersen Example 1.3.5, the frame computation: on the unit
sphere the Berger form is **diagonal** in the frame `X₁, X₂, X₃`, with
entries `ε², 1, 1` — the coframe representation
`g_ε = ε²(σ¹)² + (σ²)² + (σ³)²`. The correction term `(ε² − 1)⟨ix, ·⟩⟨ix, ·⟩`
contributes `ε² − 1` on `(X₁, X₁)` (as `⟨ix, ix⟩ = 1` on the sphere) and
kills nothing else, the horizontal fields being orthogonal to `ix`. -/
theorem bergerAmbientForm_suTwoFrame (ε : ℝ) {x : WithLp 2 (ℂ × ℂ)}
    (hx : ‖x‖ = 1) (i j : Fin 3) :
    bergerAmbientForm ε x (suTwoFrame x i) (suTwoFrame x j)
      = if i = j then (if i = 0 then ε ^ 2 else 1) else 0 := by
  have h1 : ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1 := by
    rw [← WithLp.prod_norm_sq_eq_of_L2, hx, one_pow]
  have key : ∀ u v : WithLp 2 (ℂ × ℂ),
      bergerAmbientForm ε x u v
        = ⟪u, v⟫_ℝ + (ε ^ 2 - 1) *
            (⟪hopfVertical x.fst x.snd, u⟫_ℝ * ⟪hopfVertical x.fst x.snd, v⟫_ℝ) := by
    intro u v
    rw [bergerAmbientForm_apply, hx]
    norm_num
  have hVV : ⟪hopfVertical x.fst x.snd, hopfVertical x.fst x.snd⟫_ℝ = 1 := by
    rw [real_inner_hopfVertical_self, h1]
  have hVH : ∀ l : ℂ, ⟪hopfVertical x.fst x.snd, hopfHorizontal x.fst x.snd l⟫_ℝ = 0 :=
    fun l => real_inner_hopfVertical_hopfHorizontal x.fst x.snd l
  have hHV : ∀ l : ℂ, ⟪hopfHorizontal x.fst x.snd l, hopfVertical x.fst x.snd⟫_ℝ = 0 :=
    fun l => (real_inner_comm _ _).trans (hVH l)
  have hHH : ∀ l m : ℂ,
      ⟪hopfHorizontal x.fst x.snd l, hopfHorizontal x.fst x.snd m⟫_ℝ = (m * conj l).re := by
    intro l m
    rw [real_inner_hopfHorizontal, h1, mul_one]
  fin_cases i <;> fin_cases j
  · show bergerAmbientForm ε x (hopfVertical x.fst x.snd) (hopfVertical x.fst x.snd) = ε ^ 2
    rw [key, hVV]; ring
  · show bergerAmbientForm ε x (hopfVertical x.fst x.snd)
      (hopfHorizontal x.fst x.snd 1) = 0
    rw [key, hVV, hVH]; ring
  · show bergerAmbientForm ε x (hopfVertical x.fst x.snd)
      (hopfHorizontal x.fst x.snd Complex.I) = 0
    rw [key, hVV, hVH]; ring
  · show bergerAmbientForm ε x (hopfHorizontal x.fst x.snd 1)
      (hopfVertical x.fst x.snd) = 0
    rw [key, hHV, hVH]; ring
  · show bergerAmbientForm ε x (hopfHorizontal x.fst x.snd 1)
      (hopfHorizontal x.fst x.snd 1) = 1
    rw [key, hHH, hVH]; simp
  · show bergerAmbientForm ε x (hopfHorizontal x.fst x.snd 1)
      (hopfHorizontal x.fst x.snd Complex.I) = 0
    rw [key, hHH, hVH]; simp
  · show bergerAmbientForm ε x (hopfHorizontal x.fst x.snd Complex.I)
      (hopfVertical x.fst x.snd) = 0
    rw [key, hHV, hVH]; ring
  · show bergerAmbientForm ε x (hopfHorizontal x.fst x.snd Complex.I)
      (hopfHorizontal x.fst x.snd 1) = 0
    rw [key, hHH, hVH]; simp
  · show bergerAmbientForm ε x (hopfHorizontal x.fst x.snd Complex.I)
      (hopfHorizontal x.fst x.snd Complex.I) = 1
    rw [key, hHH, hVH]; simp

/-- **Math.** Every frame field is tangent to the sphere (orthogonal to the
base point), hence lifts through the differential of the inclusion
`S³ ↪ ℂ²`: the frame hypotheses of `bergerSphereMetric_coframe` are
realizable at every point and every index. -/
theorem exists_mfderiv_coe_eq_suTwoFrame (x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1)
    (i : Fin 3) :
    ∃ u : TangentSpace (𝓡 3) x,
      mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
          ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) x u
        = suTwoFrame (x : WithLp 2 (ℂ × ℂ)) i := by
  fin_cases i
  · exact exists_mfderiv_coe_sphere_eq x
      (real_inner_toLp_hopfVertical (x : WithLp 2 (ℂ × ℂ)).fst (x : WithLp 2 (ℂ × ℂ)).snd)
  · exact exists_mfderiv_coe_sphere_eq x
      (real_inner_toLp_hopfHorizontal (x : WithLp 2 (ℂ × ℂ)).fst (x : WithLp 2 (ℂ × ℂ)).snd 1)
  · exact exists_mfderiv_coe_sphere_eq x
      (real_inner_toLp_hopfHorizontal (x : WithLp 2 (ℂ × ℂ)).fst (x : WithLp 2 (ℂ × ℂ)).snd
        Complex.I)

/-- **Math.** Petersen Example 1.3.5, coframe form of the Berger metric:
in the left-invariant frame `X₁, X₂, X₃` (read through the sphere
inclusion) the Berger metric is diagonal with entries `ε², 1, 1`, i.e.
`g_ε = ε²(σ¹)² + (σ²)² + (σ³)²` in the dual coframe — the metric of
`S³(1)` rescaled by `ε²` along the Hopf fibre `X₁`. Stated for tangent
vectors `u, v` whose ambient images are the frame fields `X_i, X_j`
(such lifts exist: `exists_mfderiv_coe_eq_suTwoFrame`). -/
theorem bergerSphereMetric_coframe (ε : ℝ) (hε : ε ≠ 0)
    (x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1) (i j : Fin 3)
    (u v : TangentSpace (𝓡 3) x)
    (hu : mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) x u
      = suTwoFrame (x : WithLp 2 (ℂ × ℂ)) i)
    (hv : mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) x v
      = suTwoFrame (x : WithLp 2 (ℂ × ℂ)) j) :
    (bergerSphereMetric ε hε).metricInner x u v
      = if i = j then (if i = 0 then ε ^ 2 else 1) else 0 := by
  rw [bergerSphereMetric_apply, hu, hv,
    bergerAmbientForm_suTwoFrame ε (mem_sphere_zero_iff_norm.mp x.2) i j]

/-- **Math.** Petersen Example 1.3.5, coframe form of the round metric on
`SU(2) = S³(1)`: the left-invariant frame `X₁, X₂, X₃` is **orthonormal**
for `suTwoMetric`, i.e. `g = (σ¹)² + (σ²)² + (σ³)²` in the dual coframe
(Petersen Example 1.4.3, first display, for the round `S³`). -/
theorem suTwoMetric_coframe (x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1) (i j : Fin 3)
    (u v : TangentSpace (𝓡 3) x)
    (hu : mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) x u
      = suTwoFrame (x : WithLp 2 (ℂ × ℂ)) i)
    (hv : mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) x v
      = suTwoFrame (x : WithLp 2 (ℂ × ℂ)) j) :
    suTwoMetric.metricInner x u v = if i = j then 1 else 0 := by
  rw [suTwoMetric, bergerSphereMetric_coframe 1 one_ne_zero x i j u v hu hv]
  simp

end BergerSphere

/-! ## `SU(2) = S³` (Petersen Example 1.3.5)

The matrix description: `A ∈ SU(2)` iff `A = [[z, w], [−w̄, z̄]]` with
`|z|² + |w|² = 1`, so the first row identifies `SU(2)` with the unit sphere
`S³(1) ⊆ ℂ²`. -/

section SUTwo

open Matrix

/-- **Math.** Petersen Example 1.3.5: the matrix form of `SU(2)`. A `2 × 2`
complex matrix is special unitary iff it is `[[z, w], [−w̄, z̄]]` with
`|z|² + |w|² = 1`: unitarity with `det A = 1` forces `A* = A⁻¹ = adj A`,
whose entries pin the second row to `(−w̄, z̄)`, and `det A = |z|² + |w|² = 1`
is the sphere equation. -/
theorem mem_specialUnitaryGroup_fin_two_iff {A : Matrix (Fin 2) (Fin 2) ℂ} :
    A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔
      ∃ z w : ℂ, ‖z‖ ^ 2 + ‖w‖ ^ 2 = 1 ∧ A = !![z, w; -conj w, conj z] := by
  constructor
  · intro hA
    obtain ⟨hu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
    -- `A* = A⁻¹ = adj A` (since `det A = 1`)
    have hstar : star A = Matrix.adjugate A := by
      rw [← Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu),
        Matrix.inv_def, hdet]
      simp
    have h10 : A 1 0 = -conj (A 0 1) := by
      have h := congrFun (congrFun hstar 1) 0
      rw [Matrix.star_apply, Matrix.adjugate_fin_two] at h
      have h' : conj (A 0 1) = -A 1 0 := h
      linear_combination h'
    have h11 : A 1 1 = conj (A 0 0) := by
      have h := congrFun (congrFun hstar 1) 1
      rw [Matrix.star_apply, Matrix.adjugate_fin_two] at h
      have h' : conj (A 1 1) = A 0 0 := h
      rw [← h', Complex.conj_conj]
    refine ⟨A 0 0, A 0 1, ?_, ?_⟩
    · -- `det A = 1` is the sphere equation
      rw [Matrix.det_fin_two, h10, h11] at hdet
      have h' : ((‖A 0 0‖ ^ 2 : ℝ) : ℂ) + ((‖A 0 1‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
          ← Complex.mul_conj, ← Complex.mul_conj]
        linear_combination hdet
      exact_mod_cast h'
    · conv_lhs => rw [Matrix.eta_fin_two A, h10, h11]
  · rintro ⟨z, w, h1, rfl⟩
    -- the complexified sphere equation
    have hzw : z * conj z + w * conj w = 1 := by
      rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add,
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h1, Complex.ofReal_one]
    refine Matrix.mem_specialUnitaryGroup_iff.mpr
      ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
    · -- unitarity: `A A* = 1` entrywise
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j
      · show z * conj z + w * conj w = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0
        rw [Matrix.one_apply_eq]; exact hzw
      · show z * conj (-conj w) + w * conj (conj z)
          = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1
        rw [Matrix.one_apply_ne (by decide), map_neg, Complex.conj_conj,
          Complex.conj_conj]
        ring
      · show -conj w * conj z + conj z * conj w
          = (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0
        rw [Matrix.one_apply_ne (by decide)]
        ring
      · show -conj w * conj (-conj w) + conj z * conj (conj z)
          = (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1
        rw [Matrix.one_apply_eq, map_neg, Complex.conj_conj, Complex.conj_conj]
        linear_combination hzw
    · -- `det A = 1`
      rw [Matrix.det_fin_two_of]
      linear_combination hzw

/-- **Math.** Petersen Example 1.3.5: `SU(2) = S³(1)`. The identification
sends `A = [[z, w], [−w̄, z̄]]` to its first row `(z, w) ∈ S³(1) ⊆ ℂ²`,
with inverse `(z, w) ↦ [[z, w], [−w̄, z̄]]`. -/
def suTwoEquivSphere :
    Matrix.specialUnitaryGroup (Fin 2) ℂ ≃ sphere (0 : WithLp 2 (ℂ × ℂ)) 1 where
  toFun A := ⟨WithLp.toLp 2 (A.1 0 0, A.1 0 1), by
    obtain ⟨z, w, h1, hA⟩ := mem_specialUnitaryGroup_fin_two_iff.mp A.2
    have h00 : A.1 0 0 = z := by simp [hA]
    have h01 : A.1 0 1 = w := by simp [hA]
    rw [mem_sphere_zero_iff_norm, h00, h01,
      ← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 (z, w))),
      WithLp.prod_norm_sq_eq_of_L2]
    show Real.sqrt (‖z‖ ^ 2 + ‖w‖ ^ 2) = 1
    rw [h1, Real.sqrt_one]⟩
  invFun x := ⟨!![(x : WithLp 2 (ℂ × ℂ)).fst, (x : WithLp 2 (ℂ × ℂ)).snd;
      -conj (x : WithLp 2 (ℂ × ℂ)).snd, conj (x : WithLp 2 (ℂ × ℂ)).fst],
    mem_specialUnitaryGroup_fin_two_iff.mpr
      ⟨(x : WithLp 2 (ℂ × ℂ)).fst, (x : WithLp 2 (ℂ × ℂ)).snd,
        norm_fst_sq_add_norm_snd_sq_coe_unitSphere x, rfl⟩⟩
  left_inv A := by
    obtain ⟨z, w, h1, hA⟩ := mem_specialUnitaryGroup_fin_two_iff.mp A.2
    have h00 : A.1 0 0 = z := by simp [hA]
    have h01 : A.1 0 1 = w := by simp [hA]
    refine Subtype.ext ?_
    show !![A.1 0 0, A.1 0 1; -conj (A.1 0 1), conj (A.1 0 0)] = A.1
    rw [h00, h01, hA]
  right_inv x := rfl

end SUTwo

end PetersenLib
