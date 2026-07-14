import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import OpenGALib.Riemannian.Manifold.DoCarmoCh4Sectional

/-!
# do Carmo Chapter 4 §4 — Ricci and scalar curvature (algebraic core)

do Carmo §4 introduces, from an algebraic curvature form `B` (the role of
`⟨R·,·⟩`) on a finite-dimensional real inner product space `T_pM`, two averaged
curvatures:

* the **Ricci form** `Q(x,y) = trace of z ↦ R(x,z)y`, which in an orthonormal
  basis `{e_i}` is `Q(x,y) = ∑_i ⟨R(x,e_i)y,e_i⟩ = ∑_i B x e_i y e_i`, and
* the **scalar curvature** `∑_{ij} ⟨R(e_i,e_j)e_i,e_j⟩ = ∑_{ij} B e_i e_j e_i e_j`.

do Carmo's whole point is that these sums do **not** depend on the chosen
orthonormal basis — because each is a *trace*. This file makes that precise
over an arbitrary finite-dimensional real inner product space `V`:

* `bilinTrace` — for any bilinear form `β : V →ₗ V →ₗ ℝ`, its trace via the
  Riesz identification, with `bilinTrace_eq_sum`: `bilinTrace β = ∑_i β(e_i,e_i)`
  for *every* orthonormal basis (basis independence, from
  `LinearMap.trace_eq_sum_inner`).
* `ricciForm B x y` — do Carmo's `Q(x,y)`, defined basis-free as the trace of the
  Riesz endomorphism of `z,w ↦ B x z y w`; `ricciForm_eq_sum` gives the
  orthonormal-basis formula and `ricciForm_symm` its symmetry `Q(x,y)=Q(y,x)`
  (from the pair-swap symmetry of `B`), so `Ric_p(x) = Q(x,x)/(n-1)` is
  intrinsically defined.
* `ricciBilin B` — `Q` packaged as a genuine bilinear form (`Q` is bilinear in
  `x,y`), so that its own trace makes sense.
* `scalarCurvature B` — do Carmo's scalar curvature, the trace of `ricciBilin B`,
  with `scalarCurvature_eq_sum_ricci` and `scalarCurvature_eq_sum` the two
  orthonormal-basis formulas.

Reference: do Carmo, *Riemannian Geometry*, Ch. 4 §4.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Riemannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The trace of a bilinear form via the Riesz identification -/

/-- **Math.** In a finite-dimensional real inner product space the Riesz
representation gives a linear isomorphism between the algebraic dual `V →ₗ[ℝ] ℝ`
and `V`: to a functional `f` it associates the unique vector `v` with
`⟨v, w⟩ = f w`. -/
def rieszInvEquiv (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] V :=
  ((InnerProductSpace.toDual ℝ V).toLinearEquiv ≪≫ₗ LinearMap.toContinuousLinearMap.symm).symm

/-- The defining property of `rieszInvEquiv`: `⟨rieszInvEquiv f, w⟩ = f w`. -/
theorem rieszInvEquiv_inner (f : V →ₗ[ℝ] ℝ) (w : V) :
    inner ℝ (rieszInvEquiv V f) w = f w := by
  have hsymm : (rieszInvEquiv V).symm (rieszInvEquiv V f) = f :=
    (rieszInvEquiv V).symm_apply_apply f
  set v := rieszInvEquiv V f with hv
  have h2 : ((InnerProductSpace.toDual ℝ V) v) w = f w := by
    have := congrArg (fun g => g w) hsymm
    simpa [rieszInvEquiv, LinearEquiv.trans_apply] using this
  rw [← h2, InnerProductSpace.toDual_apply_apply]

/-- **Math.** The **trace of a bilinear form** `β` on a finite-dimensional real
inner product space: the trace of the endomorphism `z ↦ (Riesz vector of
`w ↦ β z w`)`. This is basis-free by construction; `bilinTrace_eq_sum` recovers
the diagonal-sum formula `∑_i β(e_i,e_i)` in every orthonormal basis. -/
def bilinTrace (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : ℝ :=
  LinearMap.trace ℝ V ((rieszInvEquiv V).toLinearMap ∘ₗ β)

/-- **Math.** The trace of a bilinear form equals the diagonal sum over any
orthonormal basis, hence is independent of the basis. This is do Carmo's key
observation (a sum `∑_i β(e_i,e_i)` is a trace). -/
theorem bilinTrace_eq_sum (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ V) :
    bilinTrace β = ∑ i, β (e i) (e i) := by
  rw [bilinTrace, LinearMap.trace_eq_sum_inner _ e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ((rieszInvEquiv V).toLinearMap ∘ₗ β) (e i) = rieszInvEquiv V (β (e i)) := by
    simp [LinearMap.comp_apply]
  rw [this, real_inner_comm, rieszInvEquiv_inner]

/-! ### The Ricci form `Q(x,y)` -/

/-- The bilinear form `z, w ↦ B x z y w` for fixed `x, y`, packaged from the
multilinearity of an algebraic curvature form. -/
def ricciBilinAux {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) (x y : V) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => B x z y w)
    (fun z₁ z₂ w => hB.add_two x z₁ z₂ y w)
    (fun c z w => by simp only [smul_eq_mul]; exact hB.smul_two c x z y w)
    (fun z w₁ w₂ => hB.add_four x z y w₁ w₂)
    (fun c z w => by simp only [smul_eq_mul]; exact hB.smul_four c x z y w)

/-- **Math.** do Carmo Ch. 4 §4: the **Ricci form** `Q(x,y) = trace of
z ↦ R(x,z)y`, defined abstractly as the trace of the bilinear form
`z, w ↦ B x z y w`. It is basis-free; `ricciForm_eq_sum` gives do Carmo's
orthonormal-basis expression `∑_i ⟨R(x,e_i)y,e_i⟩`. -/
def ricciForm {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) (x y : V) : ℝ :=
  bilinTrace (ricciBilinAux hB x y)

/-- **Math.** do Carmo Ch. 4 §4: the orthonormal-basis formula for the Ricci form,
`Q(x,y) = ∑_i B x e_i y e_i`. Independent of the orthonormal basis (both sides
equal the trace). -/
theorem ricciForm_eq_sum {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (x y : V) {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V) :
    ricciForm hB x y = ∑ i, B x (e i) y (e i) :=
  bilinTrace_eq_sum _ e

/-- **Math.** do Carmo Ch. 4 §4: the Ricci form is **symmetric**, `Q(x,y)=Q(y,x)`.
Term by term over an orthonormal basis this is the pair-swap symmetry of `B`:
`B x e_i y e_i = B y e_i x e_i`. This is do Carmo's proof that `Ric_p(x)` is
intrinsically defined. -/
theorem ricciForm_symm {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (x y : V) : ricciForm hB x y = ricciForm hB y x := by
  let e := stdOrthonormalBasis ℝ V
  rw [ricciForm_eq_sum hB x y e, ricciForm_eq_sum hB y x e]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hB.pairSwap x (e i) y (e i)

/-! ### The Ricci form as a genuine bilinear form -/

/-- Additivity of the Ricci form in its first slot. -/
theorem ricciForm_add_left {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (x₁ x₂ y : V) : ricciForm hB (x₁ + x₂) y = ricciForm hB x₁ y + ricciForm hB x₂ y := by
  let e := stdOrthonormalBasis ℝ V
  rw [ricciForm_eq_sum hB _ y e, ricciForm_eq_sum hB x₁ y e, ricciForm_eq_sum hB x₂ y e,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hB.add_left x₁ x₂ (e i) y (e i)

/-- Homogeneity of the Ricci form in its first slot. -/
theorem ricciForm_smul_left {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (c : ℝ) (x y : V) : ricciForm hB (c • x) y = c * ricciForm hB x y := by
  let e := stdOrthonormalBasis ℝ V
  rw [ricciForm_eq_sum hB _ y e, ricciForm_eq_sum hB x y e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hB.smul_left c x (e i) y (e i)

/-- Additivity of the Ricci form in its second slot. -/
theorem ricciForm_add_right {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (x y₁ y₂ : V) : ricciForm hB x (y₁ + y₂) = ricciForm hB x y₁ + ricciForm hB x y₂ := by
  rw [ricciForm_symm hB x (y₁ + y₂), ricciForm_add_left hB y₁ y₂ x,
    ricciForm_symm hB y₁ x, ricciForm_symm hB y₂ x]

/-- Homogeneity of the Ricci form in its second slot. -/
theorem ricciForm_smul_right {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (c : ℝ) (x y : V) : ricciForm hB x (c • y) = c * ricciForm hB x y := by
  rw [ricciForm_symm hB x (c • y), ricciForm_smul_left hB c y x, ricciForm_symm hB y x]

/-- **Math.** do Carmo Ch. 4 §4: the Ricci form `Q` packaged as a genuine bilinear
form on `T_pM`; `ricciBilin B x y = Q(x,y)`. Bilinearity comes from the
multilinearity of `B` (`ricciForm_add_left`, `ricciForm_smul_left`, and their
right-hand versions via symmetry). -/
def ricciBilin {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ricciForm hB x y)
    (fun x₁ x₂ y => ricciForm_add_left hB x₁ x₂ y)
    (fun c x y => by simp only [smul_eq_mul]; exact ricciForm_smul_left hB c x y)
    (fun x y₁ y₂ => ricciForm_add_right hB x y₁ y₂)
    (fun c x y => by simp only [smul_eq_mul]; exact ricciForm_smul_right hB c x y)

@[simp] theorem ricciBilin_apply {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (x y : V) : ricciBilin hB x y = ricciForm hB x y := rfl

/-! ### Scalar curvature -/

/-- **Math.** do Carmo Ch. 4 §4: the (unnormalized) **scalar curvature**, the
trace of the Ricci form `Q`. Basis-free; `scalarCurvature_eq_sum` gives do Carmo's
double-sum `∑_{ij} ⟨R(e_i,e_j)e_i,e_j⟩`. (do Carmo's `K(p)` is this divided by
`n(n-1)`.) -/
def scalarCurvature {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) : ℝ :=
  bilinTrace (ricciBilin hB)

/-- **Math.** Scalar curvature as the sum of Ricci diagonal entries over an
orthonormal basis: `∑_j Q(e_j,e_j)`. Independent of the basis. -/
theorem scalarCurvature_eq_sum_ricci {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V) :
    scalarCurvature hB = ∑ j, ricciForm hB (e j) (e j) := by
  rw [scalarCurvature, bilinTrace_eq_sum _ e]
  simp [ricciBilin_apply]

/-- **Math.** do Carmo Ch. 4 §4: the scalar curvature as the full double sum over
an orthonormal basis, `∑_{ij} B e_i e_j e_i e_j`. Independent of the basis. -/
theorem scalarCurvature_eq_sum {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V) :
    scalarCurvature hB = ∑ i, ∑ j, B (e i) (e j) (e i) (e j) := by
  rw [scalarCurvature_eq_sum_ricci hB e]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ricciForm_eq_sum hB (e j) (e j) e]

end Riemannian
