/-
Chapter 2, "Riemannian Metrics", §"Pseudo-Riemannian Metrics": the pointwise
construction behind **Theorem 2.69** (existence of Lorentz metrics).

Lee's Theorem 2.69 says a smooth manifold admits a Lorentz metric if and only if
it admits a rank-1 tangent distribution.  The *sufficiency* half is constructive,
and this file is its linear-algebra core, done on a single inner product space.

Given a Riemannian inner product `⟪·,·⟫` on `V` and a unit vector `u`, set

  `B(v, w) = ⟪v, w⟫ - 2 ⟪v, u⟫ ⟪w, u⟫`.

`B` is the metric with the sign flipped along `span{u}`: it is `-⟪·,·⟫` on
`span{u}` and agrees with `⟪·,·⟫` on `u^⊥`.  So in an orthonormal basis whose
first member is `u` it is `diag(-1, 1, …, 1)` — a Lorentz scalar product of
signature `(n-1, 1)`.

The key point for the manifold-level construction (not done here) is that `B`
depends on `u` **only through `span{u}`**: it is unchanged by `u ↦ -u`, because
`u` occurs twice.  That is `lorentzForm_neg` below, and it is what will make the
bundle-level form globally well defined from a distribution that admits only
*local* unit sections.
-/
import LeeLib.Ch02.ScalarProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LeeLib.Ch02

open Module Set
open QuadraticMap QuadraticForm
open scoped RealInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The sign-flipped form -/

variable (u : V) in
/-- **The metric with its sign flipped along `span{u}`**:
`B(v, w) = ⟪v, w⟫ - 2 ⟪v, u⟫ ⟪w, u⟫`.

For a *unit* vector `u` this is `-⟪·,·⟫` on `span{u}` and `⟪·,·⟫` on `u^⊥`; it is
the reflection of the metric in the hyperplane `u^⊥`, viewed as a bilinear form. -/
def lorentzForm : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun v w => ⟪v, w⟫ - 2 * ⟪v, u⟫ * ⟪w, u⟫)
    (fun v₁ v₂ w => by simp [inner_add_left]; ring)
    (fun c v w => by simp [inner_smul_left]; ring)
    (fun v w₁ w₂ => by simp [inner_add_left, inner_add_right]; ring)
    (fun c v w => by simp [inner_smul_left, inner_smul_right]; ring)

@[simp] theorem lorentzForm_apply (u v w : V) :
    lorentzForm u v w = ⟪v, w⟫ - 2 * ⟪v, u⟫ * ⟪w, u⟫ := rfl

/-- **The form depends on `u` only up to sign.**  `u` occurs twice, so replacing it
by `-u` changes nothing.  A rank-1 distribution has local unit sections determined
only up to sign, so this is what makes the bundle-level construction well defined. -/
@[simp] theorem lorentzForm_neg (u : V) : lorentzForm (-u) = lorentzForm u := by
  ext v w
  simp [inner_neg_right]

/-- The form is symmetric. -/
theorem lorentzForm_isSymm (u : V) : (lorentzForm u).IsSymm := by
  refine ⟨fun v w => ?_⟩
  simp only [lorentzForm_apply, real_inner_comm v w]
  ring

/-! ### The value on an orthonormal basis whose first member is `u` -/

/-! ### Nondegeneracy, via the reflection in `u^⊥` -/

section Reflect

variable (u : V) in
/-- The reflection of `V` in the hyperplane `u^⊥`, written out: `R w = w - 2⟪w,u⟫u`.
Hand-rolled rather than taken from mathlib's `Submodule.reflection` because all that
is needed is that it is an involution, and because the bundle-level construction will
have to transport it along trivializations, where an explicit formula is what carries. -/
def reflect (w : V) : V := w - (2 * ⟪w, u⟫) • u

/-- The flipped form is the metric with one slot reflected: `B(v,w) = ⟪v, R w⟫`.
This is the identity that makes symmetry and nondegeneracy transparent. -/
theorem lorentzForm_eq_inner_reflect (u v w : V) : lorentzForm u v w = ⟪v, reflect u w⟫ := by
  rw [reflect, inner_sub_right, real_inner_smul_right, lorentzForm_apply]
  ring

/-- **The reflection is an involution** — this is where `‖u‖ = 1` is used. -/
theorem reflect_reflect {u : V} (hu : ‖u‖ = 1) (w : V) : reflect u (reflect u w) = w := by
  have huu : ⟪u, u⟫ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  simp only [reflect, inner_sub_left, real_inner_smul_left, huu]
  module

/-- **The flipped form is nondegenerate.**  If `v` is `B`-orthogonal to everything then
in particular to `R v`, and `B(v, R v) = ⟪v, R(R v)⟫ = ⟪v, v⟫`, forcing `v = 0`.  Note
this argument needs no positivity beyond `⟪v,v⟫ = 0 → v = 0`; it is the reflection's
bijectivity that does the work. -/
theorem lorentzForm_separatingLeft {u : V} (hu : ‖u‖ = 1) :
    (lorentzForm u).SeparatingLeft := by
  intro v hv
  have h := hv (reflect u v)
  rw [lorentzForm_eq_inner_reflect, reflect_reflect hu] at h
  exact inner_self_eq_zero.mp h

end Reflect

section Basis

variable {n : ℕ} {u : V} {b : OrthonormalBasis (Fin (n + 1)) ℝ V}

/-- On an orthonormal basis starting at `u`, the flipped form is `diag(-1, 1, …, 1)`.
This is the whole content of the signature computation. -/
theorem lorentzForm_basis_apply (hb : b 0 = u) (i j : Fin (n + 1)) :
    lorentzForm u (b i) (b j) =
      (if i = j then (1 : ℝ) else 0) - 2 * (if i = 0 then (1 : ℝ) else 0) *
        (if j = 0 then (1 : ℝ) else 0) := by
  have hbi : ∀ k : Fin (n + 1), ⟪b k, u⟫ = if k = 0 then (1 : ℝ) else 0 := by
    intro k
    rw [← hb, b.inner_eq_ite]
  rw [lorentzForm_apply, b.inner_eq_ite, hbi i, hbi j]

/-- The basis is orthonormal *for the flipped form* in Lee's indefinite sense
(`⟪e_i, e_i⟫ = ±1`, off-diagonal entries zero) — with the single `-1` at `u`. -/
theorem isOrthonormal_lorentzForm (hb : b 0 = u) :
    IsOrthonormal (lorentzForm u) (b : Fin (n + 1) → V) := by
  constructor
  · intro i j hij
    rw [lorentzForm_basis_apply hb i j, if_neg hij]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [if_neg (fun h : j = 0 => hij h.symm)]; ring
    · rw [if_neg hi]; ring
  · intro i
    rw [lorentzForm_basis_apply hb i i, if_pos rfl]
    rcases eq_or_ne i 0 with rfl | hi
    · right; norm_num
    · left; rw [if_neg hi]; ring

/-- The `-1` entries of the flipped form on this basis are exactly the index `0`. -/
theorem setOf_lorentzForm_basis_eq_neg_one (hb : b 0 = u) :
    {i : Fin (n + 1) | lorentzForm u (b i) (b i) = -1} = {0} := by
  ext i
  rw [Set.mem_setOf_eq, Set.mem_singleton_iff, lorentzForm_basis_apply hb i i, if_pos rfl]
  rcases eq_or_ne i 0 with rfl | hi
  · norm_num
  · rw [if_neg hi]; norm_num [hi]

/-- **The flipped form has index 1** — Lee's defining property of a Lorentz scalar
product.  Sylvester's law (`IsOrthonormal.sigNeg_eq_ncard`) reads the index off the
adapted basis, where exactly one diagonal entry is `-1`. -/
theorem sigNeg_lorentzForm (hb : b 0 = u) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap (lorentzForm u)) = 1 := by
  have h' : IsOrthonormal (lorentzForm u) (b.toBasis : Fin (n + 1) → V) := by
    rw [OrthonormalBasis.coe_toBasis]; exact isOrthonormal_lorentzForm hb
  rw [h'.sigNeg_eq_ncard]
  simp only [OrthonormalBasis.coe_toBasis]
  rw [setOf_lorentzForm_basis_eq_neg_one hb, Set.ncard_singleton]

variable [FiniteDimensional ℝ V]

/-- **The flipped form has signature `(n, 1)`.**  The positive count follows from the
index and `r + s = dim V` (`sigPos_add_sigNeg_eq_finrank`), which holds because a
nondegenerate form has trivial radical. -/
theorem sigPos_lorentzForm (hu : ‖u‖ = 1) (hb : b 0 = u) (hdim : finrank ℝ V = n + 1) :
    sigPos (LinearMap.BilinMap.toQuadraticMap (lorentzForm u)) = n := by
  have hnd : (lorentzForm u).Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (lorentzForm_separatingLeft hu)
  have hsum := sigPos_add_sigNeg_eq_finrank (lorentzForm_isSymm u) hnd
  rw [sigNeg_lorentzForm hb, hdim] at hsum
  omega

end Basis

/-! ### The signature, without reference to a basis -/

section Signature

variable {n : ℕ} {u : V} [FiniteDimensional ℝ V]

/-- **A unit vector extends to an orthonormal basis starting at it.**  This is
mathlib's `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` with the
one-element set `{0}`; the only content is that a single unit vector is an
orthonormal family. -/
theorem exists_orthonormalBasis_head (hu : ‖u‖ = 1) (hdim : finrank ℝ V = n + 1) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ V, b 0 = u := by
  have hcard : finrank ℝ V = Fintype.card (Fin (n + 1)) := by simpa using hdim
  have hv : Orthonormal ℝ (({0} : Set (Fin (n + 1))).restrict fun _ => u) := by
    constructor
    · intro i; simpa using hu
    · intro i j hij
      exact absurd (Subtype.ext (i.2.trans j.2.symm)) hij
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨b, hb 0 rfl⟩

/-- **The sign flip along a unit vector turns a Riemannian scalar product into a
Lorentz one of signature `(n, 1)`** — the pointwise content of the sufficiency half
of Lee's Theorem 2.69.

Given the metric `⟪·,·⟫` on an `(n+1)`-dimensional space and any unit vector `u`, the
form `⟪v,w⟫ - 2⟪v,u⟫⟪w,u⟫` is symmetric, nondegenerate, and of index 1.  On a manifold
`u` will be a local unit section of a rank-1 distribution; `lorentzForm_neg` is what
makes the resulting form independent of the sign ambiguity in that choice. -/
theorem lorentzForm_isSymm_nondegenerate_signature (hu : ‖u‖ = 1)
    (hdim : finrank ℝ V = n + 1) :
    (lorentzForm u).IsSymm ∧ (lorentzForm u).Nondegenerate ∧
      sigPos (LinearMap.BilinMap.toQuadraticMap (lorentzForm u)) = n ∧
      sigNeg (LinearMap.BilinMap.toQuadraticMap (lorentzForm u)) = 1 := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_head hu hdim
  exact ⟨lorentzForm_isSymm u,
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (lorentzForm_separatingLeft hu),
    sigPos_lorentzForm hu hb hdim, sigNeg_lorentzForm hb⟩

end Signature

end

end LeeLib.Ch02
