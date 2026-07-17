/-
Chapter 2, "Riemannian Metrics", §"The Pseudo-Riemannian Case": the pointwise
core of Lee's Corollary 2.71 (the embedding criterion for level sets).

Lee 2.71.  Let `(M̃, g̃)` be a pseudo-Riemannian manifold of signature `(r,s)`,
let `f ∈ C^∞(M̃)`, and let `M = f^{-1}(c)`.  If `g̃(grad f, grad f) > 0` everywhere
on `M` then `M` is an embedded pseudo-Riemannian submanifold of signature
`(r-1,s)`; if `g̃(grad f, grad f) < 0` everywhere then the signature is
`(r,s-1)`.  In either case `grad f` is normal to `M`.

This file formalizes that statement **at a point**, which is where all of its
linear-algebra content lives.  Fix `p ∈ M`, put `V = T_p M̃` and `B = g̃_p`, a
nondegenerate symmetric bilinear form.  Then:

* `df_p` is a nonzero linear functional `a : V →ₗ[ℝ] ℝ` (nonzero exactly because
  `p` is a regular point);
* `T_p M = ker a`, a hyperplane;
* `grad f|_p` is the `B`-representative of `a`, which is `bilinGrad` below;
* Lee's conclusion is then the signature drop on `ker a`, keyed by the sign of
  `B(grad f, grad f)` — `sigPos_sigNeg_restrict_ker_bilinGrad`.

**Why a new gradient.**  `LeeLib.Ch02.grad` (`MusicalIsomorphism`) raises indices
with `InnerProductSpace.toDual`, the Riesz isomorphism, which needs a genuine —
*positive definite* — inner product.  A pseudo-Riemannian `g̃` is indefinite, so
that construction does not transfer: there is no `InnerProductSpace` instance to
be had.  The replacement uses **nondegeneracy alone**.  `B` nondegenerate says
`v ↦ B v` is injective into `V*`; in finite dimensions `dim V* = dim V` forces it
to be bijective, and its inverse is the sharp operator.  That is mathlib's
`LinearMap.BilinForm.toDual`, so `bilinGrad` is a wrapper on it and
`apply_bilinGrad` — the defining property `B(a^♯, w) = a(w)` — is immediate.

**Lee 2.71 proper is now assembled in `LeeLib.Ch02.PseudoLevelSet`**, out of this
file plus the two pieces that were once missing and have since been built:
`PseudoRiemannianMetric` (a pseudo-Riemannian metric on a manifold — mathlib still
has none, cf. issue I-0263) and `LevelSetChartedSpace` (the codimension-one regular
level set theorem, Lee's Corollary A.26, which identifies `T_pM = ker df_p`).  So
the theorems below are the pointwise core of a *discharged* corollary, not of a
conditional one; `PseudoLevelSet` supplies the globalization.

The bridge between the two is `orthogonal_ker_eq_span_bilinGrad` and
`pos_apply_self_of_mem_orthogonal_ker` below: the normal space of `ker a` is the
*line* spanned by `a^♯`, so the sign of `B(v,v)` is constant on the nonzero
normals.  That is what turns Lee's hypothesis on `grad f` alone into Proposition
2.70's hypothesis on every normal vector.
-/
import LeeLib.Ch02.HypersurfaceSignature

namespace LeeLib.Ch02

open Module Submodule
open LinearMap (BilinForm)
open QuadraticMap QuadraticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

section BilinGrad

variable (B : BilinForm ℝ V)

/-- **The `B`-gradient of a linear functional**: the pseudo-Riemannian sharp
operator, `a^♯`.

For an indefinite `B` the Riesz route of `LeeLib.Ch02.sharp` is unavailable (no
inner product), but nondegeneracy is enough: `v ↦ B v` is injective into `V*`,
hence bijective since `dim V* = dim V`, and `bilinGrad` is the inverse.  Applied
to `a = df_p` and `B = g̃_p` this is Lee's `grad f|_p` in the pseudo-Riemannian
setting. -/
noncomputable def bilinGrad (hnd : B.Nondegenerate) (a : Module.Dual ℝ V) : V :=
  (B.toDual hnd).symm a

/-- **The defining property of the `B`-gradient**: `B(a^♯, w) = a(w)` for all `w`.

This is Lee's (2.14) for an indefinite metric — the equation that characterizes
the gradient. -/
@[simp] theorem apply_bilinGrad (hnd : B.Nondegenerate) (a : Module.Dual ℝ V) (w : V) :
    B (bilinGrad B hnd a) w = a w :=
  LinearMap.BilinForm.apply_toDual_symm_apply a w

/-- The `B`-gradient is the unique vector representing `a`; uniqueness comes from
nondegeneracy of `B`. -/
theorem eq_bilinGrad_of_apply (hnd : B.Nondegenerate) (a : Module.Dual ℝ V) {v : V}
    (hv : ∀ w, B v w = a w) : v = bilinGrad B hnd a := by
  have hva : B.toDual hnd v = a := LinearMap.ext hv
  rw [bilinGrad, ← hva, LinearEquiv.symm_apply_apply]

/-- The `B`-gradient of a nonzero functional is nonzero — the algebraic form of
"`grad f|_p ≠ 0` at a regular point of `f`". -/
theorem bilinGrad_ne_zero (hnd : B.Nondegenerate) {a : Module.Dual ℝ V} (ha : a ≠ 0) :
    bilinGrad B hnd a ≠ 0 := by
  intro h
  refine ha (LinearMap.ext fun w => ?_)
  rw [← apply_bilinGrad B hnd a w, h]
  simp

/-- **The `B`-gradient is `B`-orthogonal to the kernel of the functional.**

With `a = df_p` and `ker a = T_p M`, this is Lee's "`grad f` is everywhere normal
to `M`" at the point `p`. -/
theorem bilinGrad_mem_orthogonal_ker (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (a : Module.Dual ℝ V) : bilinGrad B hnd a ∈ B.orthogonal (LinearMap.ker a) := by
  intro w hw
  show B w (bilinGrad B hnd a) = 0
  rw [hB.eq w (bilinGrad B hnd a), apply_bilinGrad B hnd a w]
  exact hw

end BilinGrad

section Criterion

variable (B : BilinForm ℝ V)

/-- **Lee's Corollary 2.71, at a point.**

Let `B = g̃_p` be a nondegenerate symmetric bilinear form on `V = T_p M̃`, and let
`a = df_p` be a nonzero functional, so that `ker a = T_p M` is a hyperplane and
`bilinGrad B hnd a = grad f|_p`.  Then the signature of `B` restricted to
`ker a` drops by one, in the positive direction if `B(grad f, grad f) > 0` and in
the negative direction if `B(grad f, grad f) < 0`:

* `g̃(grad f, grad f) > 0` gives signature `(r-1, s)`;
* `g̃(grad f, grad f) < 0` gives signature `(r, s-1)`.

The proof is `sigPos_sigNeg_restrict_of_mem_orthogonal` (Lee 2.70 at a point)
applied with `W = ker a` and `x = grad f|_p`: `ker a` is a hyperplane because `a`
is a nonzero functional, `grad f|_p` is a nonzero element of its `B`-orthogonal,
and Lee 2.70 does the rest.  So 2.71 really is 2.70 read through the gradient,
exactly as Lee presents it. -/
theorem sigPos_sigNeg_restrict_ker_bilinGrad (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {a : Module.Dual ℝ V} (ha : a ≠ 0) :
    (0 < B (bilinGrad B hnd a) (bilinGrad B hnd a) →
      sigPos (LinearMap.BilinMap.toQuadraticMap (B.restrict (LinearMap.ker a))) + 1
          = sigPos (LinearMap.BilinMap.toQuadraticMap B) ∧
        sigNeg (LinearMap.BilinMap.toQuadraticMap (B.restrict (LinearMap.ker a)))
          = sigNeg (LinearMap.BilinMap.toQuadraticMap B)) ∧
    (B (bilinGrad B hnd a) (bilinGrad B hnd a) < 0 →
      sigPos (LinearMap.BilinMap.toQuadraticMap (B.restrict (LinearMap.ker a)))
          = sigPos (LinearMap.BilinMap.toQuadraticMap B) ∧
        sigNeg (LinearMap.BilinMap.toQuadraticMap (B.restrict (LinearMap.ker a))) + 1
          = sigNeg (LinearMap.BilinMap.toQuadraticMap B)) :=
  sigPos_sigNeg_restrict_of_mem_orthogonal hB hnd
    (Module.Dual.finrank_ker_add_one_of_ne_zero ha)
    (bilinGrad_mem_orthogonal_ker B hB hnd a) (bilinGrad_ne_zero B hnd ha)

/-- **The restriction to `ker a` is nondegenerate when the `B`-gradient is
non-null** — the hypothesis half of Lee's Corollary 2.71, at a point.

`sigPos_sigNeg_restrict_ker_bilinGrad` computes the signature of `B|_{ker a}`
but does not by itself say that `B|_{ker a}` is nondegenerate, which is what
"`M` is a pseudo-Riemannian submanifold" asserts and what constructing the
induced metric requires.  Both come from the same source: `ker a` is the
`B`-orthogonal of the line spanned by `grad f|_p` (Lee 2.59(b)), and the
orthogonal complement of a non-null line is nondegenerate (Lee 2.60). -/
theorem nondegenerate_restrict_ker_bilinGrad (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {a : Module.Dual ℝ V} (ha : a ≠ 0)
    (hnn : B (bilinGrad B hnd a) (bilinGrad B hnd a) ≠ 0) :
    (B.restrict (LinearMap.ker a)).Nondegenerate := by
  have heq : B.orthogonal (Submodule.span ℝ {bilinGrad B hnd a}) = LinearMap.ker a :=
    orthogonal_span_singleton_eq hB hnd
      (Module.Dual.finrank_ker_add_one_of_ne_zero ha)
      (bilinGrad_mem_orthogonal_ker B hB hnd a) (bilinGrad_ne_zero B hnd ha)
  rw [← heq]
  exact restrict_orthogonal_span_singleton_nondegenerate hB hnd hnn

/-- **The normal line of the hyperplane `ker a` is spanned by the `B`-gradient.**

`bilinGrad_mem_orthogonal_ker` says `grad f|_p` *lies in* the normal space `N_pM`; this says it
*spans* it.  The extra content is that `N_pM` is a line, which is the dimension count
`span_singleton_eq_orthogonal` performs: `ker a` is a hyperplane, so its `B`-orthogonal is
one-dimensional, and a nonzero member of a line spans it.

This is the step Lee leaves implicit when he says "`grad f` is normal to `M`, and the normal
space is one-dimensional, so the sign of `g̃(v,v)` for `v ∈ N_pM` is decided by
`g̃(grad f, grad f)`" — see `pos_apply_self_of_mem_orthogonal_ker` below. -/
theorem orthogonal_ker_eq_span_bilinGrad (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {a : Module.Dual ℝ V} (ha : a ≠ 0) :
    B.orthogonal (LinearMap.ker a) = Submodule.span ℝ {bilinGrad B hnd a} :=
  (span_singleton_eq_orthogonal hnd (Module.Dual.finrank_ker_add_one_of_ne_zero ha)
    (bilinGrad_mem_orthogonal_ker B hB hnd a) (bilinGrad_ne_zero B hnd ha)).symm

/-- **Every normal vector is a multiple of the `B`-gradient, and `B(v,v)` scales by the square.**

The quantitative form of `orthogonal_ker_eq_span_bilinGrad`: on the normal line, `B(v,v)` is
`t²` times `B(grad f, grad f)`.  Since `t² > 0` for `v ≠ 0`, the *sign* of `B(v,v)` is constant
on the nonzero normals — which is exactly what lets a hypothesis about `grad f` alone discharge
the "all normals are positive/negative" hypothesis of Lee's Proposition 2.70. -/
theorem exists_smul_bilinGrad_of_mem_orthogonal_ker (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {a : Module.Dual ℝ V} (ha : a ≠ 0) {v : V} (hv : v ∈ B.orthogonal (LinearMap.ker a)) :
    ∃ t : ℝ, v = t • bilinGrad B hnd a ∧
      B v v = t ^ 2 * B (bilinGrad B hnd a) (bilinGrad B hnd a) := by
  rw [orthogonal_ker_eq_span_bilinGrad B hB hnd ha, Submodule.mem_span_singleton] at hv
  obtain ⟨t, rfl⟩ := hv
  refine ⟨t, rfl, ?_⟩
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **A positive `B`-gradient makes every nonzero normal positive.**

The hypothesis half of Lee's Corollary 2.71 in the form Proposition 2.70 consumes: Lee assumes
only `g̃(grad f, grad f) > 0`, while 2.70 asks that *every* nonzero normal be positive.  The two
agree because the normal space is the line `⟨grad f⟩`. -/
theorem pos_apply_self_of_mem_orthogonal_ker (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {a : Module.Dual ℝ V} (ha : a ≠ 0)
    (hpos : 0 < B (bilinGrad B hnd a) (bilinGrad B hnd a))
    {v : V} (hv : v ∈ B.orthogonal (LinearMap.ker a)) (hv0 : v ≠ 0) : 0 < B v v := by
  obtain ⟨t, rfl, hval⟩ := exists_smul_bilinGrad_of_mem_orthogonal_ker B hB hnd ha hv
  have ht : t ≠ 0 := by rintro rfl; exact hv0 (by simp)
  rw [hval]
  exact mul_pos (by positivity) hpos

/-- **A negative `B`-gradient makes every nonzero normal negative** — the mirror of
`pos_apply_self_of_mem_orthogonal_ker`, giving the `(r, s-1)` case of Lee's Corollary 2.71. -/
theorem neg_apply_self_of_mem_orthogonal_ker (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {a : Module.Dual ℝ V} (ha : a ≠ 0)
    (hneg : B (bilinGrad B hnd a) (bilinGrad B hnd a) < 0)
    {v : V} (hv : v ∈ B.orthogonal (LinearMap.ker a)) (hv0 : v ≠ 0) : B v v < 0 := by
  obtain ⟨t, rfl, hval⟩ := exists_smul_bilinGrad_of_mem_orthogonal_ker B hB hnd ha hv
  have ht : t ≠ 0 := by rintro rfl; exact hv0 (by simp)
  rw [hval]
  exact mul_neg_of_pos_of_neg (by positivity) hneg

end Criterion

end LeeLib.Ch02
