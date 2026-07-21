/-
Chapter 2, "Riemannian Metrics", §2.5 "The Riemannian volume form".

Lee's Proposition 2.41 asserts that an *oriented* Riemannian `n`-manifold `(M, g)`
carries a unique `n`-form `dV_g` with `dV_g(E_1, …, E_n) = 1` for every local
oriented orthonormal frame.  Two ingredients are needed, and mathlib supplies only
the first:

* **Fibrewise.**  `Orientation.volumeForm` is exactly Lee's `dV_g|_x`: the unique
  top-degree alternating form taking the value `1` on an oriented orthonormal
  basis.  Its whole API (`volumeForm_robust`, `abs_volumeForm_apply_le`, …) is in
  `Mathlib.Analysis.InnerProductSpace.Orientation`.

* **Globally.**  Mathlib has *no orientation of a manifold or of a vector bundle*
  (verified by grep over `Mathlib/Geometry/` and `Mathlib/Topology/VectorBundle/`:
  the only `orient` hits are unoriented bordism and Euclidean angles), and so no
  way to say that `x ↦ dV_g|_x` varies smoothly.  This file supplies that missing
  layer.

The gap is real rather than cosmetic.  Without a smoothness condition on the
orientation, `x ↦ dV_g|_x` is merely a pointwise family: it is a *section* of no
bundle, and every analytic statement about it has to be re-parametrized by a local
frame.  `IsSmoothOrientation` below is the missing hypothesis, and it is stated so
that it is *dischargeable*: it asks for exactly what `exists_orthonormalFrame_nhds`
(Lee's Proposition 2.8) already produces, a smooth local frame, plus the positivity
of its orientation.

## Main definitions

* `Orientation.volumeFormL`: `Orientation.volumeForm` as a *continuous* alternating
  map.  Mathlib's `volumeForm` is a bare `AlternatingMap`, but the fibres of the
  bundle of differential forms are `ContinuousAlternatingMap`s, so the two cannot
  be connected without this bridge.  The bound needed by `mkContinuous` is mathlib's
  own `abs_volumeForm_apply_le`, with constant `1`.
* `IsSmoothOrientation`: a pointwise orientation of `TM` is smooth when every point
  has a neighbourhood on which some smooth local frame is positively oriented
  throughout.
* `RiemannianMetric.volumeForm`: Lee's `dV_g`, a section of the bundle
  `fun x ↦ (T_x M) [⋀^Fin n]→L[ℝ] ℝ` of `n`-forms built in
  `LeeLib.AppendixA.AlternatingBundle`.

## Main results

* `volumeFormL_apply_eq_det`, `RiemannianMetric.volumeForm_apply_eq_det`: Lee's
  defining determinant formula `dV_g(v_1, …, v_n) = det [⟨E_i, v_j⟩_g]`.
* `RiemannianMetric.volumeForm_apply_eq_one`: Lee 2.41(b), the characterizing
  property.
* `RiemannianMetric.volumeForm_unique`: the uniqueness half of Lee 2.41.

Reference: Lee, *Introduction to Riemannian Manifolds* (2nd ed.), Proposition 2.41.
-/
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import LeeLib.AppendixA.AlternatingBundle
import LeeLib.Ch02.OrthonormalFrame

namespace LeeLib.Ch02

open Bundle Module InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace Matrix

noncomputable section

/-! ## Gram-Schmidt preserves orientation

Mathlib has `OrthonormalBasis.adjustToOrientation` (*force* a basis to match an orientation) but
nothing saying that Gram-Schmidt *keeps* the orientation it started with.  That is the fact needed
to upgrade an oriented smooth frame to an oriented smooth *orthonormal* frame, and hence the fact
that makes `IsSmoothOrientation` usable.  Note the flag condition
`span (Z_1, …, Z_k) = span (Y_1, …, Y_k)` of Lee's Proposition 2.8 is *not* enough on its own:
`Z_1 = -Y_1` spans the same line but reverses the orientation. -/

section GramSchmidtOrientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- Pairing a Gram-Schmidt output vector with the corresponding input vector recovers the squared
norm: the correction terms lie in the span of earlier `gramSchmidt` vectors, so they pair to zero.

Absent from mathlib; `exact?` finds nothing for it. -/
theorem _root_.InnerProductSpace.real_inner_gramSchmidt_self (f : ι → V) (i : ι) :
    ⟪gramSchmidt ℝ f i, f i⟫_ℝ = ‖gramSchmidt ℝ f i‖ ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' ℝ f i]
  rw [inner_add_right, inner_sum]
  rw [Finset.sum_eq_zero (fun j hj => ?_), add_zero, real_inner_self_eq_norm_sq]
  · rw [real_inner_smul_right, gramSchmidt_orthogonal ℝ f (Finset.mem_Iio.mp hj).ne', mul_zero]

/-- For a linearly independent family, `gramSchmidtNormed` pairs *positively* with its input
vector — the pairing is `‖gramSchmidt ℝ f i‖ > 0`.  This is the per-factor positivity that makes
the Gram-Schmidt determinant positive. -/
theorem _root_.InnerProductSpace.real_inner_gramSchmidtNormed_self_pos {f : ι → V}
    (hf : LinearIndependent ℝ f) (i : ι) : 0 < ⟪gramSchmidtNormed ℝ f i, f i⟫_ℝ := by
  have hpos : 0 < ‖gramSchmidt ℝ f i‖ := norm_pos_iff.mpr (gramSchmidt_ne_zero i hf)
  rw [gramSchmidtNormed, real_inner_smul_left, InnerProductSpace.real_inner_gramSchmidt_self,
    RCLike.ofReal_real_eq_id, id_eq, sq, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  exact hpos

variable [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ V]

/-- **Gram-Schmidt preserves orientation.**

The change of basis from `b` to its Gram-Schmidt orthonormalization is triangular with positive
diagonal, so its determinant `∏ ⟪GS b i, b i⟫` is positive.  Mathlib supplies both halves —
`Basis.orientation_eq_iff_det_pos` and `gramSchmidtOrthonormalBasis_det` — but not the per-factor
positivity, hence not this. -/
theorem _root_.InnerProductSpace.gramSchmidtOrthonormalBasis_orientation
    (h : finrank ℝ V = Fintype.card ι) (b : Basis ι ℝ V) :
    (gramSchmidtOrthonormalBasis h ⇑b).toBasis.orientation = b.orientation := by
  rw [Basis.orientation_eq_iff_det_pos, gramSchmidtOrthonormalBasis_det]
  refine Finset.prod_pos fun i _ => ?_
  rw [gramSchmidtOrthonormalBasis_apply h (f := ⇑b) (i := i) ?_]
  · exact InnerProductSpace.real_inner_gramSchmidtNormed_self_pos b.linearIndependent i
  · simpa [gramSchmidtNormed, norm_eq_zero] using gramSchmidt_ne_zero i b.linearIndependent

end GramSchmidtOrientation

/-! ## Top-degree forms are a line

Two facts that the pinned mathlib leaves just out of reach, and that the smoothness of `dV_g`
needs.  Both are stated here because this file is their only consumer; neither is about volume
forms. -/

section TopForms

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- **Top-degree continuous alternating forms are proportional.**

If `θ` does not vanish on a basis `b`, then every top form `w` is the multiple `w b / θ b` of `θ`.

Mathlib records the one-dimensionality of the space of top forms as
`AlternatingMap.eq_smul_basis_det` — every top form is its value on `b` times `b.det` — which is
the same fact with `b.det` as the distinguished generator, but only for *bare* `AlternatingMap`s.
Allowing an arbitrary generator `θ` is what makes this usable for a *continuous* form: it lets
`dV_g|_x` be compared with `dV_g` at a *fixed* point rather than with `b.det`, which would first
have to be promoted to a continuous form by hand.  That promotion is not routine — the pinned
mathlib has no theorem making an `AlternatingMap` continuous in finite dimensions
(`LinearMap.continuous_of_finiteDimensional` has no multilinear counterpart).

Like `wedgeCovectors` below, this needs **no norm on `V`**, only a topology: the proof is
pure module theory, and `TangentSpace I x` carries no norm, so requiring one would make this
inapplicable to the tangent spaces it is about (`volumeForm_eq_sqrt_det_smul_wedgeCovectors`). -/
theorem _root_.ContinuousAlternatingMap.eq_smul_of_apply_basis_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V)
    (w θ : V [⋀^ι]→L[ℝ] ℝ) (hθ : θ b ≠ 0) :
    w = (w b / θ b) • θ := by
  ext v
  have hwv := congrArg (fun f => f v) (w.toAlternatingMap.eq_smul_basis_det b)
  have hθv := congrArg (fun f => f v) (θ.toAlternatingMap.eq_smul_basis_det b)
  simp only [AlternatingMap.smul_apply, smul_eq_mul,
    ContinuousAlternatingMap.coe_toAlternatingMap] at hwv hθv
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hwv, hθv]
  field_simp

end TopForms

/-! ## The wedge product of covectors

Lee's characterization (a) of `dV_g` is `dV_g = e^1 ∧ ⋯ ∧ e^n` for the coframe `e^i` dual to an
oriented orthonormal frame.  Mathlib has no wedge product of covectors — the `Hom.lean` docstring
lists exterior algebras among the constructions "yet to be formalized" — so it is built here, in
the only degree Lee's §2.5 needs: a full family `(f_i)_{i ∈ ι}` wedged into a top form.

The definition is the classical one, `(f_1 ∧ ⋯ ∧ f_n)(v_1, …, v_n) = det [f_i(v_j)]`, and the
determinant convention Lee fixes (p. 401) is exactly the one that makes it so.

The construction deliberately requires **no norm on `V`**, only a topology: a determinant is a
polynomial in its entries, so `Continuous.matrix_det` gives continuity directly.  This matters —
`TangentSpace I x` carries no norm, so a `mkContinuous`-style definition with an operator-norm
bound could not be applied to it without first installing a Riemannian structure and incurring
the attendant instance diamond. -/

section WedgeCovectors

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The wedge product of a family of covectors, as a bare alternating map: the determinant of
the matrix `[f_i(v_j)]`, seen as an alternating function of `(v_j)`. -/
def wedgeCovectorsₗ (f : ι → (V →L[ℝ] ℝ)) : V [⋀^ι]→ₗ[ℝ] ℝ :=
  Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun i => (f i).toLinearMap)

theorem wedgeCovectorsₗ_apply (f : ι → (V →L[ℝ] ℝ)) (v : ι → V) :
    wedgeCovectorsₗ f v = (Matrix.of fun i j => f i (v j)).det := by
  rw [wedgeCovectorsₗ, AlternatingMap.compLinearMap_apply, ← Matrix.det_transpose]
  rfl

/-- **The wedge product `f_1 ∧ ⋯ ∧ f_n` of a family of covectors**, characterized by
`(f_1 ∧ ⋯ ∧ f_n)(v_1, …, v_n) = det [f_i(v_j)]` (`wedgeCovectors_apply`).

Alternation and multilinearity are inherited from `Matrix.detRowAlternating`; continuity is
`Continuous.matrix_det`, since a determinant is a polynomial in the entries `f_i(v_j)` and each
`f_i` is continuous. -/
def wedgeCovectors (f : ι → (V →L[ℝ] ℝ)) : V [⋀^ι]→L[ℝ] ℝ where
  toMultilinearMap := (wedgeCovectorsₗ f).toMultilinearMap
  map_eq_zero_of_eq' := (wedgeCovectorsₗ f).map_eq_zero_of_eq'
  cont :=
    Continuous.congr
      (Continuous.matrix_det
        (continuous_pi fun i => continuous_pi fun j => (f i).continuous.comp (continuous_apply j)))
      fun v => (wedgeCovectorsₗ_apply f v).symm

@[simp]
theorem wedgeCovectors_apply (f : ι → (V →L[ℝ] ℝ)) (v : ι → V) :
    wedgeCovectors f v = (Matrix.of fun i j => f i (v j)).det :=
  wedgeCovectorsₗ_apply f v

end WedgeCovectors

section LocalFrameSymmL

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The local frame induced by a trivialization `e` and a basis `b` of the model fibre is,
on `e.baseSet`, the family `x ↦ e.symmL x (b i)`.

Mathlib defines `Trivialization.localFrame` through `basisAt`, hence through `linearEquivAt`, and
separately provides `symmL` as "the backwards map, defined everywhere"; the two are the same map
on the base set, but the bridge is not stated upstream.  It is needed whenever a construction
naturally produces `symmL` — as trivializing a bundle of alternating maps does — and the
smoothness of the result has to be read off from `contMDiffOn_localFrame_baseSet`. -/
theorem _root_.Bundle.Trivialization.localFrame_eq_symmL {ι : Type*}
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {x : B}
    (hx : x ∈ e.baseSet) (i : ι) :
    e.localFrame b i x = e.symmL 𝕜 x (b i) := by
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet _ _ hx]
  rfl

end LocalFrameSymmL

/-! ## The volume form of an oriented inner product space, as a continuous form -/

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)]

/-- **The volume form as a continuous alternating map.**

Mathlib's `Orientation.volumeForm` is a bare `AlternatingMap`, but the fibre of the
bundle of `n`-forms over `x` is `(T_x M) [⋀^Fin n]→L[ℝ] ℝ`, a space of *continuous*
alternating maps.  Bridging the two needs a bound, and mathlib's own
`abs_volumeForm_apply_le` — `|dV(v)| ≤ ∏ ‖v i‖` — is exactly a bound with constant
`1`.  (In finite dimensions every multilinear map is continuous, but the pinned
mathlib has no such theorem for multilinear maps, so the explicit bound is the
route.) -/
def _root_.Orientation.volumeFormL (o : Orientation ℝ V (Fin n)) : V [⋀^Fin n]→L[ℝ] ℝ :=
  o.volumeForm.mkContinuous 1 fun v => by simpa using o.abs_volumeForm_apply_le v

@[simp]
theorem _root_.Orientation.volumeFormL_apply (o : Orientation ℝ V (Fin n)) (v : Fin n → V) :
    o.volumeFormL v = o.volumeForm v :=
  rfl

/-- The volume form is computed by Lee's determinant formula
`dV(v_1, …, v_n) = det [⟨e_i, v_j⟩]` against any oriented orthonormal basis `e`. -/
theorem volumeFormL_apply_eq_det (o : Orientation ℝ V (Fin n))
    (e : OrthonormalBasis (Fin n) ℝ V) (he : e.toBasis.orientation = o) (v : Fin n → V) :
    o.volumeFormL v = (Matrix.of fun i j => ⟪e i, v j⟫_ℝ).det := by
  rw [Orientation.volumeFormL_apply, o.volumeForm_robust e he, Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, e.coe_toBasis_repr_apply, e.repr_apply_apply]

/-- **The characterizing property**, fibrewise: the volume form takes the value `1` on any
oriented orthonormal basis.  This is the pointwise content of Lee 2.41(b). -/
theorem volumeFormL_apply_eq_one (o : Orientation ℝ V (Fin n))
    (e : OrthonormalBasis (Fin n) ℝ V) (he : e.toBasis.orientation = o) :
    o.volumeFormL (e ·) = 1 := by
  rw [Orientation.volumeFormL_apply, o.volumeForm_robust e he]
  simpa using e.toBasis.det_self

/-- **The Gram determinant formula**, fibrewise: on an *oriented* basis `b` — not assumed
orthonormal — the volume form is the square root of the determinant of the Gram matrix
`⟪b i, b j⟫`.  This is the pointwise content of Lee 2.41(c): taking `b` to be a coordinate
frame `(∂/∂x^i)` makes the Gram matrix Lee's `(g_ij)`.

The proof is Lee's: orthonormalize `b` to `e` by Gram-Schmidt, which does not change the
orientation (`gramSchmidtOrthonormalBasis_orientation`).  Writing `A i j = ⟪e i, b j⟫` for the
change of basis, the Gram matrix is `AᵀA` (mathlib's `Matrix.gram_eq_conjTranspose_mul`), so its
determinant is `(det A)²`, while `det A` is the volume form on `b` (`volumeFormL_apply_eq_det`).
The square root is taken without an absolute value because `det A > 0`: that is exactly the
statement that `b` and `e` induce the *same* orientation (`Basis.orientation_eq_iff_det_pos`). -/
theorem volumeFormL_apply_eq_sqrt_det_gram (o : Orientation ℝ V (Fin n)) (b : Basis (Fin n) ℝ V)
    (hb : b.orientation = o) :
    o.volumeFormL ⇑b = Real.sqrt ((Matrix.gram ℝ ⇑b).det) := by
  classical
  haveI : FiniteDimensional ℝ V := Module.Basis.finiteDimensional_of_finite b
  have hcard : finrank ℝ V = Fintype.card (Fin n) := by
    rw [Fintype.card_fin]; exact Fact.out
  set e := gramSchmidtOrthonormalBasis hcard ⇑b with he
  have hor : e.toBasis.orientation = o := by
    rw [he, InnerProductSpace.gramSchmidtOrthonormalBasis_orientation, hb]
  set m : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => ⟪e i, b j⟫_ℝ with hm
  have hdet : o.volumeFormL ⇑b = m.det := volumeFormL_apply_eq_det o e hor ⇑b
  have hgram : Matrix.gram ℝ ⇑b = mᴴ * m := by
    have h := Matrix.gram_eq_conjTranspose_mul (𝕜 := ℝ) e ⇑b
    rw [h]
    congr 1 <;> · ext i j; simp [hm, e.repr_apply_apply]
  have hpos : 0 < m.det := by
    have hd : e.toBasis.det ⇑b = m.det := by
      rw [Basis.det_apply]
      congr 1
      ext i j
      simp [hm, Basis.toMatrix_apply, e.coe_toBasis_repr_apply, e.repr_apply_apply]
    rw [← hd]
    exact (e.toBasis.orientation_eq_iff_det_pos b).mp (by rw [hor, hb])
  rw [hdet, hgram, Matrix.det_mul, Matrix.det_conjTranspose, RCLike.star_def,
    starRingEnd_apply, star_trivial, ← sq, Real.sqrt_sq hpos.le]

end Pointwise

/-! ## Smooth orientations of a manifold -/

section SmoothOrientation

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (I M) in
/-- A **pointwise orientation** of `M`: an orientation of each tangent space, with no
compatibility between different points.  This is the most that can be said with mathlib's
current vocabulary, and on its own it is too weak to be useful — see `IsSmoothOrientation`. -/
abbrev PointwiseOrientation : Type _ :=
  ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E))

/-- **A smooth orientation of `M`** (Lee, Appendix B / §2.5).

A pointwise orientation `o` is *smooth* when every point of `M` has a neighbourhood `u`
carrying a smooth local frame that is positively oriented — i.e. induces `o x` — at every
`x ∈ u`.  This is the missing condition that turns the pointwise family `x ↦ dV_g|_x` into
a genuine smooth section of the bundle of `n`-forms.

Mathlib has no orientation of a manifold or of a vector bundle at all, so this definition
has no upstream counterpart.  It is stated in terms of `IsLocalFrameOn`, hence dischargeable
from `exists_orthonormalFrame_nhds` (Lee's Proposition 2.8) — see
`IsSmoothOrientation.of_isLocalFrameOn`, which produces one from any global frame. -/
def IsSmoothOrientation (o : PointwiseOrientation I M) : Prop :=
  ∀ p : M, ∃ (u : Set M) (Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x),
    IsOpen u ∧ p ∈ u ∧ ∃ hY : IsLocalFrameOn I E ∞ Y u,
      ∀ x, ∀ hx : x ∈ u, (hY.toBasisAt hx).orientation = o x

omit [FiniteDimensional ℝ E] in
/-- The orientation determined on `u` by a smooth local frame is smooth at each point of `u`
— the local building block of `IsSmoothOrientation`. -/
theorem isSmoothOrientation_of_globalFrame
    {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x}
    (hY : IsLocalFrameOn I E ∞ Y Set.univ) (o : PointwiseOrientation I M)
    (ho : ∀ x, (hY.toBasisAt (Set.mem_univ x)).orientation = o x) :
    IsSmoothOrientation o := fun p =>
  ⟨Set.univ, Y, isOpen_univ, Set.mem_univ p, hY, fun x _ => ho x⟩

/-- **Every point of a smoothly oriented Riemannian manifold has a neighbourhood carrying a smooth
*oriented orthonormal* frame.**

This is what makes `IsSmoothOrientation` usable rather than decorative: it is the hypothesis that
`volumeForm_apply_eq_one`, `volumeForm_apply_eq_det` and `volumeForm_unique` all ask for, and this
theorem discharges it at every point.

The proof runs Lee's fibrewise Gram-Schmidt (`gramSchmidtFrame`, Proposition 2.8) on the oriented
frame supplied by `IsSmoothOrientation`, and then appeals to
`gramSchmidtOrthonormalBasis_orientation` to see that orthonormalizing did not flip the
orientation.  Lee's own `exists_orthonormalFrame` cannot be used as a black box here: it returns
the orthonormalized frame existentially, keeping only the flag condition, and the flag condition
does not determine the orientation. -/
theorem exists_orientedOrthonormalFrame_nhds (g : RiemannianMetric I M)
    {o : PointwiseOrientation I M} (ho : IsSmoothOrientation o) (p : M) :
    ∃ (u : Set M) (Z : Fin (finrank ℝ E) → (x : M) → TangentSpace I x),
      IsOpen u ∧ p ∈ u ∧ ∃ hZ : IsLocalFrameOn I E ∞ Z u,
        (∀ x ∈ u, ∀ i j, g.inner x (Z i x) (Z j x) = if i = j then 1 else 0) ∧
        ∀ x, ∀ hx : x ∈ u, (hZ.toBasisAt hx).orientation = o x := by
  classical
  obtain ⟨u, Y, hu, hpu, hY, hor⟩ := ho p
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hZframe : IsLocalFrameOn I E ∞
      (gramSchmidtFrame (V := (TangentSpace I : M → Type _)) Y) u :=
    isLocalFrameOn_gramSchmidtFrame (IB := I) (F := E) (V := (TangentSpace I : M → Type _)) hY
  refine ⟨u, gramSchmidtFrame (V := (TangentSpace I : M → Type _)) Y, hu, hpu, hZframe, ?_, ?_⟩
  · -- orthonormality, transported to `g.inner` exactly as `exists_orthonormalFrame` does
    intro x hx i j
    have hon := gramSchmidtFrame_orthonormal (IB := I) (F := E)
      (V := (TangentSpace I : M → Type _)) hY.isLocalIndepOn hx
    show ⟪gramSchmidtFrame (V := (TangentSpace I : M → Type _)) Y i x,
        gramSchmidtFrame (V := (TangentSpace I : M → Type _)) Y j x⟫_ℝ = _
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl, real_inner_self_eq_norm_sq, hon.1 i, one_pow]
    · rw [if_neg hij]
      exact hon.2 hij
  · -- orientation: Gram-Schmidt did not flip it
    intro x hx
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    have hcard : finrank ℝ (TangentSpace I x) = Fintype.card (Fin (finrank ℝ E)) := by
      rw [Fintype.card_fin]; rfl
    have hcoe : ⇑(hY.toBasisAt hx) = fun i => Y i x :=
      funext fun i => IsLocalFrameOn.toBasisAt_coe hY hx i
    -- the Gram-Schmidt'd frame's basis IS mathlib's `gramSchmidtOrthonormalBasis`
    have hbases : hZframe.toBasisAt hx
        = (gramSchmidtOrthonormalBasis hcard ⇑(hY.toBasisAt hx)).toBasis := by
      refine Basis.eq_of_apply_eq fun i => ?_
      rw [IsLocalFrameOn.toBasisAt_coe, OrthonormalBasis.coe_toBasis]
      rw [gramSchmidtOrthonormalBasis_apply hcard (f := ⇑(hY.toBasisAt hx)) (i := i) ?_]
      · rw [hcoe]; rfl
      · rw [hcoe]
        simpa [gramSchmidtNormed, norm_eq_zero] using
          gramSchmidt_ne_zero i (hY.linearIndependent hx)
    rw [hbases, InnerProductSpace.gramSchmidtOrthonormalBasis_orientation]
    exact hor x hx

end SmoothOrientation

/-! ## The Riemannian volume form -/

section VolumeForm

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace RiemannianMetric

/-- **The Riemannian volume form** `dV_g` (Lee, Proposition 2.41).

At each `x`, `dV_g|_x` is the volume form of the oriented inner product space
`(T_x M, g_x, o x)`: the unique `n`-form taking the value `1` on every oriented
orthonormal basis of `T_x M`.  It is valued in the fibre `(T_x M) [⋀^Fin n]→L[ℝ] ℝ`
of the bundle of `n`-forms of `LeeLib.AppendixA.AlternatingBundle`.

Smoothness of `x ↦ dV_g|_x` is *not* part of the definition; it is the theorem
`contMDiffOn_volumeForm`, and it needs `IsSmoothOrientation o` as a hypothesis. -/
def volumeForm (g : RiemannianMetric I M) (o : PointwiseOrientation I M) (x : M) :
    (TangentSpace I x) [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  (o x).volumeFormL

variable {g : RiemannianMetric I M} {o : PointwiseOrientation I M}
  {u : Set M} {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x} {x : M}

omit [FiniteDimensional ℝ E] in
/-- An orthonormal frame — orthonormality stated through `g`, as Lee states it and as
`exists_orthonormalFrame` produces it — is an orthonormal basis of each tangent space in
its domain.  The `letI` installing the fibrewise inner product is the caller's business,
so this is phrased as a proof about `hY.toBasisAt`. -/
theorem orthonormal_toBasisAt (g : RiemannianMetric I M)
    (hY : IsLocalFrameOn I E ∞ Y u)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0)
    (hx : x ∈ u) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    Orthonormal ℝ (hY.toBasisAt hx) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [orthonormal_iff_ite]
  intro i j
  show ⟪hY.toBasisAt hx i, hY.toBasisAt hx j⟫_ℝ = _
  simp only [IsLocalFrameOn.toBasisAt_coe]
  exact hon x hx i j

omit [FiniteDimensional ℝ E] in
/-- **Lee, Proposition 2.41(b) — the characterizing property of `dV_g`.**

`dV_g(E_1, …, E_n) = 1` for every local *oriented* orthonormal frame `(E_i)`.  Orthonormality
is stated through `g` itself, matching `exists_orthonormalFrame`, so that applying this does
not require the caller to install the fibrewise inner product. -/
theorem volumeForm_apply_eq_one (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (hY : IsLocalFrameOn I E ∞ Y u)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0)
    (hx : x ∈ u) (hor : (hY.toBasisAt hx).orientation = o x) :
    g.volumeForm o x (fun i => Y i x) = 1 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  have hon' := orthonormal_toBasisAt g hY hon hx
  have := volumeFormL_apply_eq_one (o x) ((hY.toBasisAt hx).toOrthonormalBasis hon') (by
    rwa [Basis.toBasis_toOrthonormalBasis])
  simpa only [Basis.coe_toOrthonormalBasis, IsLocalFrameOn.toBasisAt_coe] using this

omit [FiniteDimensional ℝ E] in
/-- **The determinant formula for `dV_g`** (Lee, Proposition 2.41): against a local oriented
orthonormal frame `(E_i)`, `dV_g(v_1, …, v_n) = det [⟨E_i, v_j⟩_g]`. -/
theorem volumeForm_apply_eq_det (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (hY : IsLocalFrameOn I E ∞ Y u)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0)
    (hx : x ∈ u) (hor : (hY.toBasisAt hx).orientation = o x)
    (v : Fin (finrank ℝ E) → TangentSpace I x) :
    g.volumeForm o x v = (Matrix.of fun i j => g.inner x (Y i x) (v j)).det := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  have hon' := orthonormal_toBasisAt g hY hon hx
  have := volumeFormL_apply_eq_det (o x) ((hY.toBasisAt hx).toOrthonormalBasis hon') (by
    rwa [Basis.toBasis_toOrthonormalBasis]) v
  simpa only [Basis.coe_toOrthonormalBasis, IsLocalFrameOn.toBasisAt_coe] using this

omit [FiniteDimensional ℝ E] in
/-- **Lee, Proposition 2.41(a) — the coframe characterization of `dV_g`.**

`dV_g = e^1 ∧ ⋯ ∧ e^n`, where `(e^i)` is the coframe dual to a local oriented orthonormal frame
`(E_i)`.  The dual coframe element is `e^i = ⟨E_i, ·⟩_g`, which is literally `g.inner x (E i x)`:
`g.inner x` is already a continuous linear map in each argument, so no dualization is needed.

Given the determinant formula this is immediate — which is the point of defining the wedge by
the determinant convention Lee fixes. -/
theorem volumeForm_eq_wedgeCovectors (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (hY : IsLocalFrameOn I E ∞ Y u)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0)
    (hx : x ∈ u) (hor : (hY.toBasisAt hx).orientation = o x) :
    g.volumeForm o x = wedgeCovectors (fun i => g.inner x (Y i x)) := by
  ext v
  rw [wedgeCovectors_apply]
  exact volumeForm_apply_eq_det g o hY hon hx hor v

omit [FiniteDimensional ℝ E] in
/-- **Uniqueness in Lee's Proposition 2.41.**

An `n`-form agreeing with `dV_g` on one oriented orthonormal frame at `x` — i.e. taking the
value `1` there — *is* `dV_g` at `x`.  The `n`-forms on an `n`-dimensional space form a line,
so a top form is pinned down by its value on a single basis. -/
theorem volumeForm_unique (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    (hY : IsLocalFrameOn I E ∞ Y u)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0)
    (hx : x ∈ u) (hor : (hY.toBasisAt hx).orientation = o x)
    (θ : (TangentSpace I x) [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ)
    (hθ : θ (fun i => Y i x) = 1) :
    θ = g.volumeForm o x := by
  have hcoe : ⇑(hY.toBasisAt hx) = fun i => Y i x :=
    funext fun i => IsLocalFrameOn.toBasisAt_coe hY hx i
  have hbasis : ∀ v : Fin (finrank ℝ E) → TangentSpace I x,
      θ v = (hY.toBasisAt hx).det v * θ (fun i => Y i x) := by
    intro v
    have := (θ.toAlternatingMap).eq_smul_basis_det (hY.toBasisAt hx)
    have hv := congrArg (fun f => f v) this
    simpa [Basis.det_apply, mul_comm, hcoe] using hv
  ext v
  rw [hbasis v, hθ, mul_one]
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  have hon' := orthonormal_toBasisAt g hY hon hx
  have hrob := (o x).volumeForm_robust ((hY.toBasisAt hx).toOrthonormalBasis hon') (by
    rwa [Basis.toBasis_toOrthonormalBasis])
  show _ = (o x).volumeForm v
  rw [hrob, Basis.toBasis_toOrthonormalBasis]

/-! ### Lee 2.41(c): the coordinate formula `dV_g = √det(g_ij) ε¹ ∧ ⋯ ∧ εⁿ`

Lee states (c) for a coordinate frame `(∂/∂x^i)` with its dual coframe `(dx^i)`.  Neither exists
in the pinned mathlib — there is no coordinate frame of `TM` as a named object — so (c) is stated
here for an **arbitrary oriented smooth local frame** `(Y_i)` and a dual coframe `(ε^i)`.  That is
strictly more general and specializes to Lee's statement verbatim: a chart's coordinate frame is a
local frame (`Trivialization.localFrame`), `g_ij = g(∂_i, ∂_j)` is its `frameMatrix`, and `(dx^i)`
is its dual coframe. -/

/-- **Lee's matrix `(g_ij)`**: the matrix `g_ij = g(Y_i, Y_j)` of `g` in the local frame `Y` at
`x`.  For a coordinate frame this is Lee's `g_ij` exactly. -/
def frameMatrix (g : RiemannianMetric I M)
    (Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x) (x : M) :
    Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ :=
  Matrix.of fun i j => g.inner x (Y i x) (Y j x)

omit [FiniteDimensional ℝ E] in
/-- Lee's `(g_ij)` is the Gram matrix of the frame, once the fibrewise inner product is installed.
This is the bridge to mathlib's `Matrix.gram` API, and it holds by `rfl`. -/
theorem frameMatrix_eq_gram (g : RiemannianMetric I M)
    (Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    g.frameMatrix Y x = Matrix.gram ℝ (fun i => Y i x) := rfl

omit [FiniteDimensional ℝ E] in
/-- `det(g_ij) ≠ 0` for a local frame: a Gram matrix is nonsingular exactly on a linearly
independent family (`Matrix.det_gram_ne_zero_iff_linearIndependent`), and a frame is one. -/
theorem frameMatrix_det_ne_zero (g : RiemannianMetric I M)
    (hY : IsLocalFrameOn I E ∞ Y u) (hx : x ∈ u) : (g.frameMatrix Y x).det ≠ 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hcoe : ⇑(hY.toBasisAt hx) = fun i => Y i x :=
    funext fun i => IsLocalFrameOn.toBasisAt_coe hY hx i
  have hli : LinearIndependent ℝ (fun i => Y i x) := hcoe ▸ hY.linearIndependent hx
  rw [frameMatrix_eq_gram]
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hli

/-- **The dual coframe of a local frame**, `ε^i = g^{ij} g(Y_j, ·)` — for a coordinate frame,
Lee's `(dx^i)`.

The point of routing the dual coframe through `g` rather than through `Basis.coord` is that the
result is *manifestly continuous*: `g.inner x v` is already a continuous linear functional, so no
promotion of a bare linear map is needed.  That matters because `TangentSpace I x` carries no
norm, so `LinearMap.toContinuousLinearMap` — which needs one — does not apply to it.

This is what makes the dual-coframe hypothesis of `volumeForm_eq_sqrt_det_smul_wedgeCovectors`
dischargeable rather than decorative; `dualCoframe_apply_frame` discharges it. -/
def dualCoframe (g : RiemannianMetric I M)
    (Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x) (x : M) (i : Fin (finrank ℝ E)) :
    TangentSpace I x →L[ℝ] ℝ :=
  ∑ j, (g.frameMatrix Y x)⁻¹ i j • g.inner x (Y j x)

omit [FiniteDimensional ℝ E] in
/-- **`(ε^i)` is dual to `(Y_i)`**: `ε^i(Y_j) = δ^i_j`.  This is `g^{ik} g_{kj} = δ^i_j`, i.e.
the inverse matrix times the matrix. -/
theorem dualCoframe_apply_frame (g : RiemannianMetric I M)
    (hY : IsLocalFrameOn I E ∞ Y u) (hx : x ∈ u) (i k : Fin (finrank ℝ E)) :
    g.dualCoframe Y x i (Y k x) = if i = k then 1 else 0 := by
  classical
  have hstep : g.dualCoframe Y x i (Y k x)
      = ((g.frameMatrix Y x)⁻¹ * g.frameMatrix Y x) i k := by
    simp [dualCoframe, frameMatrix, ContinuousLinearMap.sum_apply, Matrix.mul_apply]
  rw [hstep, Matrix.nonsing_inv_mul _ (Ne.isUnit (g.frameMatrix_det_ne_zero hY hx))]
  simp [Matrix.one_apply]

omit [FiniteDimensional ℝ E] in
/-- **The value of `dV_g` on an oriented local frame is `√det(g_ij)`** — the numerical content of
Lee 2.41(c).  Lee's `√det(g_ij)` appears here as the square root of the determinant of the
frame matrix, with no absolute value, because the frame is *oriented*. -/
theorem volumeForm_apply_eq_sqrt_det_frameMatrix (g : RiemannianMetric I M)
    (o : PointwiseOrientation I M) (hY : IsLocalFrameOn I E ∞ Y u) (hx : x ∈ u)
    (hor : (hY.toBasisAt hx).orientation = o x) :
    g.volumeForm o x (fun i => Y i x) = Real.sqrt (g.frameMatrix Y x).det := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  have hcoe : ⇑(hY.toBasisAt hx) = fun i => Y i x :=
    funext fun i => IsLocalFrameOn.toBasisAt_coe hY hx i
  have h := volumeFormL_apply_eq_sqrt_det_gram (o x) (hY.toBasisAt hx) hor
  rw [hcoe] at h
  rw [show g.volumeForm o x (fun i => Y i x) = (o x).volumeFormL (fun i => Y i x) from rfl, h,
    frameMatrix_eq_gram]

omit [FiniteDimensional ℝ E] in
/-- **Lee, Proposition 2.41(c).**

`dV_g = √det(g_ij) · ε¹ ∧ ⋯ ∧ εⁿ`, for any oriented local frame `(Y_i)` with dual coframe `(ε^i)`
and `g_ij = g(Y_i, Y_j)`.  Lee's coordinate statement
`dV_g = √det(g_ij) dx¹ ∧ ⋯ ∧ dxⁿ` is the case where `(Y_i)` is a coordinate frame.

The dual coframe is taken as a hypothesis rather than constructed, so that this applies to *any*
coframe dual to `Y` — Lee's `(dx^i)` included.  It is not a vacuous hypothesis:
`dualCoframe_apply_frame` discharges it for `g.dualCoframe Y x`.

Both sides take the value `√det(g_ij)` on the frame — the left by
`volumeForm_apply_eq_sqrt_det_frameMatrix`, the right because `det(δ^i_j) = 1` — and top-degree
forms on an `n`-dimensional space are a line, so agreeing on one basis makes them equal. -/
theorem volumeForm_eq_sqrt_det_smul_wedgeCovectors (g : RiemannianMetric I M)
    (o : PointwiseOrientation I M) (hY : IsLocalFrameOn I E ∞ Y u) (hx : x ∈ u)
    (hor : (hY.toBasisAt hx).orientation = o x)
    (ε : Fin (finrank ℝ E) → (TangentSpace I x →L[ℝ] ℝ))
    (hε : ∀ i k, ε i (Y k x) = if i = k then 1 else 0) :
    g.volumeForm o x = Real.sqrt (g.frameMatrix Y x).det • wedgeCovectors ε := by
  classical
  have hcoe : ⇑(hY.toBasisAt hx) = fun i => Y i x :=
    funext fun i => IsLocalFrameOn.toBasisAt_coe hY hx i
  have hwedge : wedgeCovectors ε (fun i => Y i x) = 1 := by
    rw [wedgeCovectors_apply,
      show (Matrix.of fun i j => ε i (Y j x)) = (1 : Matrix _ _ ℝ) by
        ext i j; rw [Matrix.of_apply, hε i j, Matrix.one_apply]]
    exact Matrix.det_one
  have hne : wedgeCovectors ε ⇑(hY.toBasisAt hx) ≠ 0 := by
    rw [hcoe, hwedge]; norm_num
  rw [ContinuousAlternatingMap.eq_smul_of_apply_basis_ne_zero (hY.toBasisAt hx)
    (g.volumeForm o x) (wedgeCovectors ε) hne, hcoe, hwedge,
    volumeForm_apply_eq_sqrt_det_frameMatrix g o hY hx hor, div_one]

/-! ### Smoothness: `dV_g` is an `n`-form, not merely a pointwise family

This is the existence half of Lee's Proposition 2.41, and the only part of the volume form that
is not fibrewise.  Everything above holds for an arbitrary pointwise orientation; smoothness is
exactly where `IsSmoothOrientation` is used, and it is what makes `dV_g` a *differential form*. -/

/-- **`dV_g` is a smooth section of the bundle of `n`-forms** — the existence half of Lee's
Proposition 2.41.

The proof is Lee's determinant formula plus the observation that the `n`-forms on an
`n`-dimensional space are a *line*.

Trivializing the bundle of `n`-forms over `x₀` (the coordinate change of that bundle is the
pullback along the transition function of `TM`, so the trivialized form at `x` is
`dV_g|_x ∘ e.symmL x`), the whole section is determined by a single scalar: by
`eq_smul_of_apply_basis_ne_zero` it equals `c x • Φ x₀`, where `Φ x₀` is the trivialized form at
the centre — which is nonzero because `dV_g|_{x₀}` takes the value `1` on an oriented orthonormal
frame — and `c x = Φ x b / Φ x₀ b` for a fixed basis `b` of the model fibre.

That scalar is smooth by Lee's own determinant formula: `Φ x b = det [⟨E_i, e.symmL x b_j⟩_g]`,
whose entries pair the smooth oriented orthonormal frame `E` of
`exists_orientedOrthonormalFrame_nhds` against the smooth local frame `x ↦ e.symmL x (b j)` of
`Trivialization.localFrame`, and are therefore smooth by `inner_bundle`.  A determinant is a
polynomial in its entries (`Matrix.det_apply'`), and the pinned mathlib has no smoothness result
for `Matrix.det`, so it is expanded by hand over the permutations. -/
theorem contMDiffAt_volumeForm (g : RiemannianMetric I M) {o : PointwiseOrientation I M}
    (ho : IsSmoothOrientation o) (x₀ : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ) x (g.volumeForm o x)) x₀ := by
  obtain ⟨u, Z, hu, hx₀u, hZ, hon, hor⟩ := exists_orientedOrthonormalFrame_nhds g ho x₀
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hx₀e : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  set b := Module.finBasis ℝ E with hb
  -- the volume form read through the trivialization of the bundle of `n`-forms over `x₀`
  set Φ : M → (E [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ) :=
    fun x => (g.volumeForm o x).compContinuousLinearMap (e.symmL ℝ x) with hΦ
  -- `dV_g|_{x₀} ≠ 0`, because it is `1` on the oriented orthonormal frame
  have hne : (g.volumeForm o x₀).toAlternatingMap ≠ 0 := by
    intro hzero
    have h1 := volumeForm_apply_eq_one g o hZ hon hx₀u (hor x₀ hx₀u)
    rw [show (g.volumeForm o x₀) (fun i => Z i x₀)
      = (g.volumeForm o x₀).toAlternatingMap (fun i => Z i x₀) from rfl, hzero] at h1
    exact zero_ne_one h1
  -- hence the trivialized form at the centre survives the basis `b`, and generates the line
  have hΩ : Φ x₀ (⇑b) ≠ 0 :=
    (AlternatingMap.map_basis_ne_zero_iff (e.basisAt b hx₀e)
      (g.volumeForm o x₀).toAlternatingMap).mpr hne
  -- `x ↦ e.symmL x (b j)` is a smooth local frame near `x₀`
  have hsec : ∀ j : Fin (finrank ℝ E), ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨q, e.symmL ℝ q (b j)⟩ : TangentBundle I M)) x₀ := by
    intro j
    refine ((e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
      e.open_baseSet hx₀e j).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hx₀e] with y hy
    exact congrArg (TotalSpace.mk' E y) (e.localFrame_eq_symmL b hy j).symm
  -- so the entries of Lee's Gram matrix are smooth
  have hentry : ∀ i j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (Z i x) (e.symmL ℝ x (b j))) x₀ := by
    intro i j
    have h1 : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun q => (⟨q, Z i q⟩ : TangentBundle I M)) Set.univ x₀ :=
      (hZ.contMDiffAt hu hx₀u i).contMDiffWithinAt
    have := g.contMDiffWithinAt_innerAt h1 (hsec j).contMDiffWithinAt
    rw [contMDiffWithinAt_univ] at this
    exact this
  -- a determinant is a polynomial in its entries
  have hdet : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => (Matrix.of fun i j => g.inner x (Z i x) (e.symmL ℝ x (b j))).det) x₀ := by
    simp only [Matrix.det_apply']
    refine ContMDiffAt.sum fun σ _ => ?_
    exact contMDiffAt_const.mul (ContMDiffAt.prod fun i _ => hentry (σ i) i)
  -- and it computes the scalar, by Lee's determinant formula
  have hΦb : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => Φ x (⇑b)) x₀ := by
    refine hdet.congr_of_eventuallyEq ?_
    filter_upwards [(hu.inter e.open_baseSet).mem_nhds ⟨hx₀u, hx₀e⟩] with x hx
    exact volumeForm_apply_eq_det g o hZ hon hx.1 (hor x hx.1) (fun j => e.symmL ℝ x (b j))
  -- assemble: the trivialized section is a smooth scalar times a fixed form
  rw [contMDiffAt_section]
  have hrw : ∀ x : M, (trivializationAt (E [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ)
      (fun x : M => (TangentSpace I x) [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ) x₀
        ⟨x, g.volumeForm o x⟩).2 = (Φ x (⇑b) * (Φ x₀ (⇑b))⁻¹) • Φ x₀ := by
    intro x
    show Φ x = _
    rw [← div_eq_mul_inv]
    exact ContinuousAlternatingMap.eq_smul_of_apply_basis_ne_zero b (Φ x) (Φ x₀) hΩ
  simp only [hrw]
  exact (hΦb.mul contMDiffAt_const).smul contMDiffAt_const

/-- **`dV_g` is a globally smooth `n`-form** (Lee, Proposition 2.41).

Together with `volumeForm_apply_eq_one` (the characterization) and `volumeForm_unique` (the
uniqueness), this is Lee's Proposition 2.41 for characterization (b). -/
theorem contMDiff_volumeForm (g : RiemannianMetric I M) {o : PointwiseOrientation I M}
    (ho : IsSmoothOrientation o) :
    ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ) x (g.volumeForm o x)) :=
  fun x₀ => g.contMDiffAt_volumeForm ho x₀

/-! ### Lee's Proposition 2.41 itself

Everything above is either fibrewise or takes a local oriented orthonormal frame as an
argument.  Lee's proposition is a statement about the `n`-form *field* `dV_g` on all of `M`:
it exists, it is smooth, it is characterized by (b), and it is *unique* with that property.

Uniqueness globally does not follow from `volumeForm_unique` by itself — that lemma pins one
fibre, and only once a frame at that point is handed to it.  What upgrades it is
`exists_orientedOrthonormalFrame_nhds`: a smooth orientation supplies an oriented orthonormal
frame near *every* point, so property (b) can be invoked at each `x` in turn. -/

/-- **Global uniqueness of `dV_g`** — an `n`-form field taking the value `1` on every local
oriented orthonormal frame *is* `dV_g`.

This is the half of Lee's Proposition 2.41 that is genuinely global: `volumeForm_unique` is
fibrewise and presupposes a frame, and the frame at each point is produced here by
`exists_orientedOrthonormalFrame_nhds`, which is exactly what `IsSmoothOrientation` buys. -/
theorem volumeForm_eq_of_apply_orientedOrthonormalFrame_eq_one
    (g : RiemannianMetric I M) {o : PointwiseOrientation I M} (ho : IsSmoothOrientation o)
    (θ : ∀ x : M, (TangentSpace I x) [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ)
    (hθ : ∀ (u : Set M) (Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x)
        (hY : IsLocalFrameOn I E ∞ Y u),
        (∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0) →
        ∀ (x : M) (hx : x ∈ u), (hY.toBasisAt hx).orientation = o x →
          θ x (fun i => Y i x) = 1) :
    θ = g.volumeForm o := by
  funext x
  obtain ⟨u, Z, hu, hxu, hZ, hon, hor⟩ := exists_orientedOrthonormalFrame_nhds g ho x
  exact volumeForm_unique g o hZ hon hxu (hor x hxu) (θ x) (hθ u Z hZ hon x hxu (hor x hxu))

/-- **Lee, Proposition 2.41 — the Riemannian volume form.**

On a smoothly oriented Riemannian manifold there is a *unique* smooth `n`-form `dV_g`
characterized by property (b): it takes the value `1` on every local oriented orthonormal
frame.  Existence is `volumeForm` together with `contMDiff_volumeForm`; the characterization
is `volumeForm_apply_eq_one`; uniqueness is
`volumeForm_eq_of_apply_orientedOrthonormalFrame_eq_one`.

Lee's characterizations (a) and (c) are the separate theorems `volumeForm_eq_wedgeCovectors`
and `volumeForm_eq_sqrt_det_smul_wedgeCovectors`; each is an equation satisfied by *this*
`dV_g`, so by the uniqueness proved here each of them characterizes it too, which is the
content of Lee's "any one of the following three equivalent properties". -/
theorem riemannian_volumeForm (g : RiemannianMetric I M) {o : PointwiseOrientation I M}
    (ho : IsSmoothOrientation o) :
    ∃! θ : ∀ x : M, (TangentSpace I x) [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ,
      ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ)) ∞
        (fun x => TotalSpace.mk' (E [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ) x (θ x)) ∧
      ∀ (u : Set M) (Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x)
        (hY : IsLocalFrameOn I E ∞ Y u),
        (∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0) →
        ∀ (x : M) (hx : x ∈ u), (hY.toBasisAt hx).orientation = o x →
          θ x (fun i => Y i x) = 1 := by
  refine ⟨g.volumeForm o, ⟨contMDiff_volumeForm g ho, ?_⟩, ?_⟩
  · intro u Y hY hon x hx hor
    exact volumeForm_apply_eq_one g o hY hon hx hor
  · intro θ hθ
    exact volumeForm_eq_of_apply_orientedOrthonormalFrame_eq_one g ho θ
      (fun u Y hY hon x hx hor => hθ.2 u Y hY hon x hx hor)

end RiemannianMetric

end VolumeForm

end

end LeeLib.Ch02
