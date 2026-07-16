/-
Chapter 2, "Riemannian Metrics", §2.5: the Riemannian density.

Lee's Proposition 2.44: every Riemannian manifold `(M, g)` — *orientable or not* —
carries a unique smooth positive density `μ` with `μ(E_1, …, E_n) = 1` for every
local orthonormal frame.  It is the tool that lets one integrate functions over a
manifold with no orientation to speak of, and it is why Lee introduces densities at
all.

The point of the proposition is precisely that orientability is not needed, so the
formalization must not route through the volume form.  It would be easy to write
`μ := |dV_g|` and be left with a theorem about orientable manifolds only:
`LeeLib.Ch02.RiemannianMetric.volumeForm` takes a `PointwiseOrientation` as an
argument, and its smoothness (`contMDiffAt_volumeForm`) needs `IsSmoothOrientation`,
a *global* predicate that a non-orientable `M` cannot satisfy by definition.  So
`|dV_g|` is undischargeable in exactly the case Lee's proposition is about.

Instead the density is defined by its own closed form, which needs no orientation and
no choice:

  `densityL v = √(det (Gram v))`,   `Gram v = [⟪v_i, v_j⟫]`.

This is orientation-free because the Gram matrix is, and it is the *right* primitive:
on a basis it is positive (`Matrix.posDef_gram_of_linearIndependent`), it satisfies
the density transformation law `μ(f ∘ v) = |det f| μ(v)` (Lee's (B.14)), and it is `1`
on an orthonormal basis, which is Lee's (2.18).

## Densities are absent from mathlib

There is no density on a manifold, no density bundle, and no orientation of a manifold
anywhere in the pinned mathlib (`grep -rn 'ensity' Mathlib/Geometry/` and
`Mathlib/Topology/VectorBundle/` return nothing; every `Density` file is
measure-theoretic or combinatorial).  So both the fibre notion and the smoothness
notion are supplied here.

Smoothness is stated against local frames rather than as smoothness of a section of a
density bundle.  That bundle would be a genuine rank-1 bundle — fibre `ℝ`, transition
functions `|det|` — but the natural fibre `{μ : (Fin n → F) → ℝ // μ (A ∘ v) = |det A| μ v}`
is *not* a normed space, so building it would force the pairing with a frame that
(2.18) is stated in terms of to be thrown away and then recovered.  Against frames the
condition is equivalent, dischargeable, and is the form every consumer (integration)
actually wants.

## Main definitions

* `densityL`: the density of a finite-dimensional real inner product space,
  `v ↦ √(det (Gram v))`.
* `SmoothDensity`: a smooth density on `M` — a pointwise family satisfying the
  transformation law (B.14), smooth against every local frame.
* `RiemannianMetric.density`: Lee's Riemannian density, `densityL` fibrewise.

## Main results

* `densityL_eq_abs_det`: the computational core — `densityL v = |det [⟪e_i, v_j⟫]|`
  against *any* orthonormal basis `e`.  Everything below is a corollary.
* `densityL_apply_orthonormalBasis`: `densityL(e) = 1`; Lee's (2.18), fibrewise.
* `densityL_comp`: `densityL(f ∘ v) = |det f| · densityL(v)`; Lee's (B.14).
* `densityL_unique`: a density taking the value `1` on one orthonormal basis *is*
  `densityL`.
* `densityL_eq_abs_volumeForm`: `μ = |dV_g|` fibrewise when an orientation happens to
  exist — the remark following Lee's Proposition 2.44, and the reason the same symbol
  `dV_g` is used for both.
* `riemannian_density_existsUnique`: **Lee's Proposition 2.44**.

Reference: Lee, *Introduction to Riemannian Manifolds* (2nd ed.), Proposition 2.44.
-/
import LeeLib.Ch02.VolumeForm

namespace LeeLib.Ch02

open Bundle Module InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace Matrix

noncomputable section

/-! ## The density of an inner product space -/

section IsDensity

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-- **A density on a real `n`-dimensional vector space** (Lee, Appendix B, equation (B.14)):
a function on `n`-tuples transforming by `|det|`.

This is the unoriented analogue of a top-degree alternating form, which transforms by `det`.
Losing the sign is exactly what lets a density exist on a manifold with no orientation. -/
def IsDensity (μ : (Fin n → V) → ℝ) : Prop :=
  ∀ (f : V →ₗ[ℝ] V) (v : Fin n → V), μ (f ∘ v) = |LinearMap.det f| * μ v

end IsDensity

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}

/-- **The density of a real inner product space**: `|v_1 ∧ ⋯ ∧ v_n|`, computed as the square
root of the Gram determinant.

Unlike `Orientation.volumeForm` this needs no orientation — the Gram matrix does not know
about one — which is exactly what Lee's Proposition 2.44 is about. -/
def densityL (v : Fin n → V) : ℝ := Real.sqrt ((Matrix.gram ℝ v).det)

theorem densityL_def (v : Fin n → V) : densityL v = Real.sqrt ((Matrix.gram ℝ v).det) := rfl

/-- `densityL` is never negative — it is a square root. -/
theorem densityL_nonneg (v : Fin n → V) : 0 ≤ densityL v := Real.sqrt_nonneg _

/-- **The computational core.**  Against any orthonormal basis `e`, the density is the
absolute value of the determinant of the matrix `[⟪e_i, v_j⟫]` expressing `v` in `e`.

This is the density counterpart of `volumeFormL_apply_eq_det`, and it is where the
orientation drops out: mathlib's `Matrix.gram_eq_conjTranspose_mul` gives `Gram v = MᵀM`
for `M = [⟪e_i, v_j⟫]`, so `det (Gram v) = (det M)²` and the square root is `|det M|`.
The volume form instead gets `det M` on the nose, and paying for the missing absolute value
is precisely what forces it to fix an orientation.

Note `v` is an arbitrary family, not assumed to be a basis: `gram_eq_conjTranspose_mul`
does not need one. -/
theorem densityL_eq_abs_det (e : OrthonormalBasis (Fin n) ℝ V) (v : Fin n → V) :
    densityL v = |(Matrix.of fun i j => ⟪e i, v j⟫_ℝ).det| := by
  classical
  set m : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => ⟪e i, v j⟫_ℝ with hm
  have hgram : Matrix.gram ℝ v = mᴴ * m := by
    have h := Matrix.gram_eq_conjTranspose_mul (𝕜 := ℝ) e v
    rw [h]
    congr 1 <;> · ext i j; simp [hm, e.repr_apply_apply]
  rw [densityL_def, hgram, Matrix.det_mul, Matrix.det_conjTranspose, RCLike.star_def,
    starRingEnd_apply, star_trivial, ← sq, Real.sqrt_sq_eq_abs]

/-- **Lee's equation (2.18)**, fibrewise: the density takes the value `1` on any orthonormal
basis.  No orientation-compatibility hypothesis appears — contrast
`volumeFormL_apply_eq_one`, which needs `e.toBasis.orientation = o`. -/
theorem densityL_apply_orthonormalBasis (e : OrthonormalBasis (Fin n) ℝ V) :
    densityL (e ·) = 1 := by
  rw [densityL_eq_abs_det e]
  rw [show (Matrix.of fun i j => ⟪e i, e j⟫_ℝ) = (1 : Matrix (Fin n) (Fin n) ℝ) by
    ext i j
    rw [Matrix.of_apply, Matrix.one_apply, orthonormal_iff_ite.mp e.orthonormal i j]]
  simp

/-- **Lee's equation (B.14)** — the defining transformation law of a density:
`μ(f v_1, …, f v_n) = |det f| μ(v_1, …, v_n)`.

Read through an orthonormal basis, the matrix of `f ∘ v` is the matrix of `f` times the
matrix of `v`, so this is multiplicativity of the determinant.  This holds for every `n`,
including `n = 0`, since no orientation and hence no nonempty-basis argument is involved. -/
theorem densityL_comp (e : OrthonormalBasis (Fin n) ℝ V) (f : V →ₗ[ℝ] V) (v : Fin n → V) :
    densityL (f ∘ v) = |LinearMap.det f| * densityL v := by
  classical
  haveI : FiniteDimensional ℝ V := e.toBasis.finiteDimensional_of_finite
  -- the matrix of `f ∘ v` in `e` is the matrix of `f` times the matrix of `v`
  have hmul : (Matrix.of fun i j => ⟪e i, (f ∘ v) j⟫_ℝ)
      = (LinearMap.toMatrix e.toBasis e.toBasis f) * (Matrix.of fun i j => ⟪e i, v j⟫_ℝ) := by
    ext i j
    rw [Matrix.of_apply, Matrix.mul_apply]
    show ⟪e i, f (v j)⟫_ℝ = _
    -- expand `v j` in the orthonormal basis `e` and use linearity of `f`
    conv_lhs => rw [← e.sum_repr (v j)]
    rw [map_sum, inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, real_inner_smul_right, LinearMap.toMatrix_apply, e.coe_toBasis,
      e.coe_toBasis_repr_apply, e.repr_apply_apply, e.repr_apply_apply, mul_comm,
      Matrix.of_apply]
  rw [densityL_eq_abs_det e, densityL_eq_abs_det e, hmul, Matrix.det_mul, abs_mul,
    LinearMap.det_toMatrix]

/-- `densityL` is a density in the sense of `IsDensity` — Lee's (B.14). -/
theorem isDensity_densityL (e : OrthonormalBasis (Fin n) ℝ V) :
    IsDensity (densityL : (Fin n → V) → ℝ) := densityL_comp e

/-- **Uniqueness of the density**, fibrewise: any density taking the value `1` on one
orthonormal basis is `densityL`.

The proof is Lee's one-line argument: for arbitrary `v`, the linear map `f` sending `e i` to
`v i` has `f ∘ e = v`, so both sides are `|det f|`. -/
theorem densityL_unique (e : OrthonormalBasis (Fin n) ℝ V) (μ : (Fin n → V) → ℝ)
    (hμ : IsDensity μ) (h1 : μ (e ·) = 1) :
    μ = densityL := by
  funext v
  set f : V →ₗ[ℝ] V := e.toBasis.constr ℝ v with hf
  have hfe : f ∘ (e ·) = v := by
    funext i
    show f (e i) = v i
    rw [hf, ← e.coe_toBasis, Basis.constr_basis]
  rw [← hfe, hμ f (e ·), h1, mul_one, densityL_comp e f (e ·),
    densityL_apply_orthonormalBasis e, mul_one]

/-- **The density is positive on a basis.**

Positivity is Lee's "positive density" condition, and it is what makes `√` smooth at the
Gram determinant — the analytic hinge of `RiemannianMetric.contMDiffOn_density`. -/
theorem densityL_pos {v : Fin n → V} (hv : LinearIndependent ℝ v) : 0 < densityL v := by
  rw [densityL_def, Real.sqrt_pos]
  exact (Matrix.posDef_gram_of_linearIndependent (𝕜 := ℝ) hv).det_pos

/-- **The density is `|dV_g|`** — the remark following Lee's Proposition 2.44, and the reason
Lee writes `dV_g` for both.

This is *not* how the density is defined here, and deliberately so: an orientation `o` is a
hypothesis of this theorem, and on a non-orientable manifold there is none, whereas
`densityL` is defined regardless.  The theorem records the compatibility on the orientable
manifolds where both exist. -/
theorem densityL_eq_abs_volumeForm [Fact (finrank ℝ V = n)] [FiniteDimensional ℝ V] (hn : 0 < n)
    (o : Orientation ℝ V (Fin n)) (v : Fin n → V) :
    densityL v = |o.volumeForm v| := by
  classical
  obtain ⟨e, he⟩ : ∃ e : OrthonormalBasis (Fin n) ℝ V, e.toBasis.orientation = o :=
    ⟨o.finOrthonormalBasis hn Fact.out, o.finOrthonormalBasis_orientation hn Fact.out⟩
  rw [densityL_eq_abs_det e, ← Orientation.volumeFormL_apply,
    volumeFormL_apply_eq_det o e he v]

end Pointwise

/-! ## Smooth densities on a manifold -/

section Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (I M) in
/-- **A smooth density on `M`** (Lee, Appendix B).

A pointwise family `μ_x` of densities on the tangent spaces, obeying the transformation law
(B.14) at each point, and *smooth* in the sense that pairing it with any smooth local frame
gives a smooth function.

Smoothness is stated against frames because mathlib has no density bundle to be a section of
— see the header.  It is the honest analogue of `IsSmoothOrientation`, which the volume form
needs for the same reason, and unlike that predicate it costs nothing: it is not an extra
hypothesis on `M`, just the smoothness of `μ` itself. -/
structure SmoothDensity where
  /-- The value of the density on a tuple of tangent vectors at `x`. -/
  toFun : ∀ x : M, (Fin (finrank ℝ E) → TangentSpace I x) → ℝ
  /-- Each `μ_x` is a density on `T_x M` — Lee's (B.14). -/
  isDensity : ∀ x : M, IsDensity (toFun x)
  /-- Pairing with a smooth local frame gives a smooth function. -/
  contMDiffOn : ∀ {u : Set M} {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x},
    IsLocalFrameOn I E ∞ Y u → ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => toFun x (Y · x)) u

omit [FiniteDimensional ℝ E] in
@[ext]
theorem SmoothDensity.ext {μ ν : SmoothDensity I M} (h : μ.toFun = ν.toFun) : μ = ν := by
  cases μ; cases ν; congr

namespace RiemannianMetric

variable (g : RiemannianMetric I M)

/-- **The Riemannian density**, pointwise: `√det(g_ij)` against the given tuple.

Stated with `g.inner` rather than through the fibrewise inner product of
`Bundle.RiemannianBundle`, so that no instance needs to be installed to use it — see
`densityAt_eq_densityL` for the bridge to the pointwise theory. -/
def densityAt (x : M) (v : Fin (finrank ℝ E) → TangentSpace I x) : ℝ :=
  Real.sqrt ((Matrix.of fun i j => g.inner x (v i) (v j)).det)

omit [FiniteDimensional ℝ E] in
/-- `densityAt` *is* `densityL` of the fibrewise inner product induced by `g`. -/
theorem densityAt_eq_densityL (x : M) (v : Fin (finrank ℝ E) → TangentSpace I x) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    g.densityAt x v = densityL v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [densityAt, densityL_def]
  rfl

/-- **Lee's (B.14)** for the Riemannian density. -/
theorem densityAt_comp (x : M) (f : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (v : Fin (finrank ℝ E) → TangentSpace I x) :
    g.densityAt x (f ∘ v) = |LinearMap.det f| * g.densityAt x v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have hcard : finrank ℝ (TangentSpace I x) = finrank ℝ E := rfl
  set e : OrthonormalBasis (Fin (finrank ℝ E)) ℝ (TangentSpace I x) :=
    (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex (finCongr hcard) with he
  rw [g.densityAt_eq_densityL x, g.densityAt_eq_densityL x, densityL_comp e f v]

omit [FiniteDimensional ℝ E] in
/-- **The Riemannian density is positive on a frame** — Lee's "positive density".

Positivity is not assumed anywhere: it is the Gram determinant of a linearly independent
family, which mathlib's `Matrix.posDef_gram_of_linearIndependent` makes positive. -/
theorem densityAt_pos {x : M} {v : Fin (finrank ℝ E) → TangentSpace I x}
    (hv : LinearIndependent ℝ v) : 0 < g.densityAt x v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [g.densityAt_eq_densityL x]
  exact densityL_pos hv

omit [FiniteDimensional ℝ E] in
/-- **Lee's (2.18)**: the Riemannian density is `1` on every orthonormal frame.

Orthonormality is stated through `g`, matching `exists_orthonormalFrame_nhds`, so applying
this needs no fibrewise instance installed. -/
theorem densityAt_apply_eq_one {x : M} {v : Fin (finrank ℝ E) → TangentSpace I x}
    (hv : ∀ i j, g.inner x (v i) (v j) = if i = j then 1 else 0) :
    g.densityAt x v = 1 := by
  rw [densityAt, show (Matrix.of fun i j => g.inner x (v i) (v j))
      = (1 : Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ) by
    ext i j; rw [Matrix.of_apply, hv i j, Matrix.one_apply]]
  simp

omit [FiniteDimensional ℝ E] in
/-- **Smoothness of the Riemannian density** — the analytic half of Lee's Proposition 2.44.

This is where the proof deliberately parts company with the volume form.  `dV_g` is smooth
only relative to a *smooth orientation*, a global predicate that fails on a non-orientable
`M`; the density instead reads its smoothness straight off the Gram matrix, which exists
whatever `M` is:

* the entries `x ↦ g(Y_i, Y_j)` are smooth by `contMDiffWithinAt_innerAt` (mathlib's
  `inner_bundle`);
* the determinant is a polynomial in them — the pin has no smoothness lemma for
  `Matrix.det`, so it is expanded by hand over the permutations exactly as
  `contMDiffAt_volumeForm` does;
* the square root is smooth *because the determinant is positive on a frame*
  (`densityAt_pos`), which is the one place linear independence of `Y` is used. -/
theorem contMDiffOn_densityAt {u : Set M} {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x}
    (hY : IsLocalFrameOn I E ∞ Y u) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => g.densityAt x (Y · x)) u := by
  classical
  intro x hx
  -- the Gram entries are smooth
  have hentry : ∀ i j, ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun q => g.inner q (Y i q) (Y j q)) u x := fun i j =>
    g.contMDiffWithinAt_innerAt (hY.contMDiffOn i x hx) (hY.contMDiffOn j x hx)
  -- a determinant is a polynomial in its entries
  have hdet : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun q => (Matrix.of fun i j => g.inner q (Y i q) (Y j q)).det) u x := by
    simp only [Matrix.det_apply']
    refine ContMDiffWithinAt.sum fun σ _ => ?_
    exact contMDiffWithinAt_const.mul (ContMDiffWithinAt.prod fun i _ => hentry (σ i) i)
  -- the determinant is positive at `x`, so `√` is smooth there
  have hpos : 0 < (Matrix.of fun i j => g.inner x (Y i x) (Y j x)).det := by
    have := g.densityAt_pos (x := x) (v := (Y · x)) (hY.linearIndependent hx)
    rw [densityAt, Real.sqrt_pos] at this
    exact this
  show ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
    (fun q => Real.sqrt ((Matrix.of fun i j => g.inner q (Y i q) (Y j q)).det)) u x
  exact (Real.contDiffAt_sqrt (ne_of_gt hpos)).comp_contMDiffWithinAt
    (f := fun q => (Matrix.of fun i j => g.inner q (Y i q) (Y j q)).det) hdet

/-- **Lee's Riemannian density** as a smooth density. -/
def density : SmoothDensity I M where
  toFun := g.densityAt
  isDensity := fun x f v => g.densityAt_comp x f v
  contMDiffOn := g.contMDiffOn_densityAt

@[simp]
theorem density_toFun (x : M) (v : Fin (finrank ℝ E) → TangentSpace I x) :
    g.density.toFun x v = g.densityAt x v := rfl

end RiemannianMetric

variable (g : RiemannianMetric I M)

/-- **Lee's characterizing property (2.18)**: `μ(E_1, …, E_n) = 1` for every local
orthonormal frame `(E_i)` of `g`.

Orthonormality is stated through `g`, exactly as `exists_orthonormalFrame_nhds` (Lee's
Proposition 2.8) produces it. -/
def SmoothDensity.IsRiemannianFor (μ : SmoothDensity I M) (g : RiemannianMetric I M) : Prop :=
  ∀ (u : Set M) (Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x),
    IsLocalFrameOn I E ∞ Y u →
    (∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0) →
    ∀ x ∈ u, μ.toFun x (Y · x) = 1

/-- **Lee, Proposition 2.44 — the Riemannian density.**

On *any* Riemannian manifold — orientable or not — there is a unique smooth density `μ`
taking the value `1` on every local orthonormal frame.

This is the density counterpart of `riemannian_volumeForm`, and the contrast is the whole
point of Lee's §2.5: that theorem needs `IsSmoothOrientation o`, this one needs nothing.

Uniqueness is genuinely global, and `exists_orthonormalFrame_nhds` is what buys it: it
supplies an orthonormal frame near *every* point, so the characterization — which speaks
only about frames — can be invoked at each `x` in turn, and `densityL_unique` then pins the
whole fibre from that single basis.  Positivity ("unique smooth *positive* density" in Lee's
statement) is not a hypothesis and not a conjunct here because it is a *consequence*:
see `RiemannianMetric.densityAt_pos`. -/
theorem riemannian_density_existsUnique :
    ∃! μ : SmoothDensity I M, μ.IsRiemannianFor g := by
  refine ⟨g.density, fun u Y hY hon x hx => g.densityAt_apply_eq_one (hon x hx), ?_⟩
  intro μ hμ
  refine SmoothDensity.ext (funext fun x => ?_)
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  -- an orthonormal frame near `x`, hence an orthonormal basis of `T_x M`
  obtain ⟨u, Y, hu, hxu, hY, hon⟩ := exists_orthonormalFrame_nhds g x
  have hon' : Orthonormal ℝ (hY.toBasisAt hxu) := RiemannianMetric.orthonormal_toBasisAt g hY hon hxu
  set e : OrthonormalBasis (Fin (finrank ℝ E)) ℝ (TangentSpace I x) :=
    (hY.toBasisAt hxu).toOrthonormalBasis hon' with he
  have hecoe : ∀ i, e i = Y i x := by
    intro i
    rw [he, Basis.coe_toOrthonormalBasis, IsLocalFrameOn.toBasisAt_coe]
  -- `μ_x` and `densityL` are two densities agreeing on that basis
  have h1 : μ.toFun x (e ·) = 1 := by
    rw [show (fun i => e i) = (Y · x) from funext hecoe]
    exact hμ u Y hY hon x hxu
  have hxu' := densityL_unique e (μ.toFun x) (μ.isDensity x) h1
  funext v
  rw [RiemannianMetric.density_toFun, g.densityAt_eq_densityL x]
  exact congrFun hxu' v

namespace RiemannianMetric

end RiemannianMetric

end Manifold

end

end LeeLib.Ch02
