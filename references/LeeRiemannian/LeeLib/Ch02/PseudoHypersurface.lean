/-
Chapter 2, "Riemannian Metrics", §"Pseudo-Riemannian Submanifolds": Lee's Proposition
2.70, which decides *which* hypersurfaces of a pseudo-Riemannian manifold are themselves
pseudo-Riemannian and computes their signature.  The induced tensor `ι^*g̃` is
nondegenerate exactly when no nonzero normal vector is null, and then one sign is deleted
from the ambient signature: the positive sign if the normals are positive, the negative
one if they are negative.

The pointwise content is already discharged in `LeeLib.Ch02.HypersurfaceSignature`, stated
for a bare scalar product space `(V, B)`, a hyperplane `W ≤ V`, and a normal `x ∈ W⊥`
(`restrict_nondegenerate_iff_forall_orthogonal` and `sigPos_sigNeg_restrict_of_mem_orthogonal`).
What this file adds is the passage from a point to a manifold, and there are exactly three
steps to it.

* `T_xM` and `N_xM` must be a hyperplane and its normal line *in one and the same space*.
  They already are: the ambient tangent bundle along `M` is the pullback `f *ᵖ T M̃`, whose
  fibre at `x` *is* `T_{f x} M̃`, and `tangentRange f x` and `pseudoNormalSpace g' f x` are
  both submodules of that fibre.  Nothing is transported.
* `pseudoNormalSpace` is defined by *left* orthogonality against `tangentRange`, mathlib's
  `B.orthogonal` by *right* orthogonality.  Symmetry of `g̃` identifies the two
  (`pseudoNormalSpace_eq_orthogonal`); the pointwise results are stated with mathlib's.
* The metric `g` of `M` is a form on `T_xM`, whereas the pointwise results compute the
  signature of `g̃|_{tangentRange f x}`, a form on a submodule of `T_{f x}M̃`.  Those are
  different spaces, and `dι_x` is an isometry between them
  (`isometryEquivRestrictTangentRange`); mathlib's `QuadraticMap.Equivalent.sigPos_eq`
  carries the signature across.

`M` enters only through a smooth map `f : M → M̃` constrained by `IsPullbackAlong`, exactly
as in the rest of the pseudo-Riemannian submanifold stack (`exists_adapted_pseudo_orthonormalFrame`,
`contMDiffVectorBundle_pseudoNormalSpace`).  So no submanifold theory is needed, and in
particular Lee's Corollary A.26 (the regular level set theorem, unformalized here) is not.
Nor is an immersion hypothesis: `dι_x` is injective because `g` is nondegenerate
(`injective_mfderiv_of_isPullbackAlong`), which is Lee's own observation that nondegeneracy
of the induced tensor is the substantive hypothesis.

Lee's conclusion "signature `(r-1,s)`" is stated here as `g.sigPosAt x + 1 = r`, not with
truncated subtraction: the `+1` form is what the proof produces and it carries the extra
information `1 ≤ r`.  `hasSignature_of_forall_normal_pos` records Lee's own phrasing as a
corollary.
-/

import LeeLib.Ch02.PseudoNormalBundle
import LeeLib.Ch02.PseudoPullbackMetric
import LeeLib.Ch02.HypersurfaceSignature

namespace LeeLib.Ch02

open Bundle Module Submodule
open scoped Manifold ContDiff
open QuadraticMap QuadraticForm

section PseudoHypersurface

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

variable {g : PseudoRiemannianMetric I M} {g' : PseudoRiemannianMetric I' M'}
  {f : C^∞⟮I, M; I', M'⟯} {x : M}

/-! ### The normal space is an orthogonal complement -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
/-- **`N_xM = (T_xM)⊥`**: the normal space of `LeeLib.Ch02.PseudoNormalBundle` is the
orthogonal complement, in mathlib's sense, of the tangent space inside the ambient fibre.

The two definitions differ only in which slot the tested vector occupies —
`pseudoNormalSpace` asks `g̃(v,w) = 0` for tangent `w`, mathlib's `B.orthogonal` asks
`B w v = 0` — so symmetry of `g̃` is the whole content.  It is nonetheless the lemma that
lets the pointwise theory of `HypersurfaceSignature`, which is stated throughout with
`B.orthogonal`, be applied to Lee's normal space. -/
theorem pseudoNormalSpace_eq_orthogonal (g' : PseudoRiemannianMetric I' M')
    (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    pseudoNormalSpace g' f x = ((g'.pullback f).bilin x).orthogonal (tangentRange f x) := by
  ext v
  refine ⟨fun h w hw => ?_, fun h w hw => ?_⟩
  · show g'.form (f x) w v = 0
    rw [← g'.symm (f x) v w]
    exact h w hw
  · show g'.form (f x) v w = 0
    rw [g'.symm (f x) v w]
    exact h w hw

omit [FiniteDimensional ℝ E'] in
/-- **A hypersurface's tangent space is a hyperplane in the ambient fibre.**

This is the codimension hypothesis of the pointwise results, in the form they ask for it.
Both halves of Lee 2.70 need it, and it is exactly where `dim M = dim M̃ - 1` is used. -/
theorem finrank_tangentRange_add_one (f : C^∞⟮I, M; I', M'⟯)
    (himm : Function.Injective (mfderiv I I' f x)) (hcodim : finrank ℝ E + 1 = finrank ℝ E') :
    finrank ℝ (tangentRange f x) + 1
      = finrank ℝ (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) := by
  -- Both rewrites must go through type-ascribed `have`s: in a pullback fibre the `finrank`
  -- of the goal and the `finrank` a bare `rw` would produce carry different (though defeq)
  -- module instances, so `rw` cannot fire.  Ascription forces elaboration at the goal's.
  have h1 : finrank ℝ (tangentRange f x) = finrank ℝ E := finrank_tangentRange f himm
  have h2 : finrank ℝ (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) = finrank ℝ E' :=
    finrank_fibre (F := E') (V := ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _))) x
  omega

/-- **The normal space of a hypersurface is a line** — Lee's `N_pM` is 1-dimensional.

This is why *one* non-null normal vector decides Lee 2.70: it spans `N_xM`, so the sign of
`g̃(v,v)` cannot depend on which nonzero normal is chosen (rescaling `v ↦ cv` multiplies it
by `c² > 0`). -/
theorem finrank_pseudoNormalSpace (g' : PseudoRiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (himm : Function.Injective (mfderiv I I' f x)) (hcodim : finrank ℝ E + 1 = finrank ℝ E') :
    finrank ℝ (pseudoNormalSpace g' f x) = 1 := by
  haveI : ∀ y : M, FiniteDimensional ℝ (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) y) :=
    fun y => finiteDimensional_fibre (F := E') y
  rw [pseudoNormalSpace_eq_orthogonal]
  have h := finrank_add_finrank_orthogonal_eq_finrank
    ((g'.pullback f).bilin_nondegenerate x) (tangentRange f x)
  have h2 := finrank_tangentRange_add_one f himm hcodim
  -- `h` and `h2` end in the same fibre dimension, but the two occurrences carry different
  -- (defeq) module instances, so `omega` sees two atoms and fails.  `Eq.trans` closes the
  -- gap up to defeq; cancelling `finrank (tangentRange f x)` then finishes.
  exact Nat.add_left_cancel (h.trans h2.symm)

/-! ### One normal decides the sign

`finrank_pseudoNormalSpace` says `N_xM` is a line, and a line is spanned by any one of its
nonzero vectors.  So the hypothesis of Lee's Proposition 2.70 — a sign condition on *every*
nonzero normal — is really a condition on a *single* one, which is what a caller such as
Lee's Corollary 2.71 (where the distinguished normal is `\opnorm{grad} f`) actually has. -/

section RankOneSign

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The sign of a line is decided by any one of its nonzero vectors.**

If `N` is `1`-dimensional, `x ∈ N` is nonzero with `B(x,x) > 0`, then `B(v,v) > 0` for every
nonzero `v ∈ N`: such a `v` is `a • x` with `a ≠ 0`, and `B(a•x, a•x) = a² B(x,x)`. -/
theorem pos_of_mem_of_finrank_eq_one {N : Submodule ℝ V} (hN : finrank ℝ N = 1)
    (B : LinearMap.BilinForm ℝ V) {x : V} (hxN : x ∈ N) (hx : x ≠ 0) (hpos : 0 < B x x)
    {v : V} (hvN : v ∈ N) (hv : v ≠ 0) : 0 < B v v := by
  haveI : FiniteDimensional ℝ N := .of_finrank_pos (by rw [hN]; norm_num)
  have hspan : N = Submodule.span ℝ {x} :=
    (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_le).mpr (Set.singleton_subset_iff.mpr hxN))
      (by rw [finrank_span_singleton hx, hN])).symm
  rw [hspan] at hvN
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hvN
  have ha : a ≠ 0 := by rintro rfl; simp at hv
  have hexp : B (a • x) (a • x) = a * a * B x x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hexp]
  exact mul_pos (mul_self_pos.mpr ha) hpos

/-- **The sign of a line is decided by any one of its nonzero vectors**, negative case. -/
theorem neg_of_mem_of_finrank_eq_one {N : Submodule ℝ V} (hN : finrank ℝ N = 1)
    (B : LinearMap.BilinForm ℝ V) {x : V} (hxN : x ∈ N) (hx : x ≠ 0) (hneg : B x x < 0)
    {v : V} (hvN : v ∈ N) (hv : v ≠ 0) : B v v < 0 := by
  have := pos_of_mem_of_finrank_eq_one hN (-B) hxN hx (by simpa using hneg) hvN hv
  simpa using this

end RankOneSign

/-- **One positive normal makes every normal positive** — the hypothesis of Lee's
Proposition 2.70, reduced to a condition at a single vector.

This is what makes Proposition 2.70 applicable in practice: a caller never verifies a sign
for *all* normals, it exhibits one distinguished normal — for a regular level set, the
gradient of the defining function — and checks the sign there. -/
theorem forall_pos_of_pos_mem_pseudoNormalSpace (g' : PseudoRiemannianMetric I' M')
    (f : C^∞⟮I, M; I', M'⟯) (himm : Function.Injective (mfderiv I I' f x))
    (hcodim : finrank ℝ E + 1 = finrank ℝ E')
    {x₀ : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x}
    (hx₀ : x₀ ∈ pseudoNormalSpace g' f x) (hx₀ne : x₀ ≠ 0)
    (hpos : 0 < (g'.pullback f).bilin x x₀ x₀) :
    ∀ v ∈ pseudoNormalSpace g' f x, v ≠ 0 → 0 < (g'.pullback f).bilin x v v :=
  fun _ hv hvne => pos_of_mem_of_finrank_eq_one
    (finrank_pseudoNormalSpace g' f himm hcodim) ((g'.pullback f).bilin x) hx₀ hx₀ne hpos hv hvne

/-- **One negative normal makes every normal negative** — the negative counterpart. -/
theorem forall_neg_of_neg_mem_pseudoNormalSpace (g' : PseudoRiemannianMetric I' M')
    (f : C^∞⟮I, M; I', M'⟯) (himm : Function.Injective (mfderiv I I' f x))
    (hcodim : finrank ℝ E + 1 = finrank ℝ E')
    {x₀ : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x}
    (hx₀ : x₀ ∈ pseudoNormalSpace g' f x) (hx₀ne : x₀ ≠ 0)
    (hneg : (g'.pullback f).bilin x x₀ x₀ < 0) :
    ∀ v ∈ pseudoNormalSpace g' f x, v ≠ 0 → (g'.pullback f).bilin x v v < 0 :=
  fun _ hv hvne => neg_of_mem_of_finrank_eq_one
    (finrank_pseudoNormalSpace g' f himm hcodim) ((g'.pullback f).bilin x) hx₀ hx₀ne hneg hv hvne

/-- **A hypersurface has a nonzero normal vector at every point**, because its normal space
is a line.  This is what lets Lee's hypothesis "`g̃(v,v) > 0` for every nonzero normal `v`"
actually be *used*: without it the hypothesis could be vacuous and would prove nothing. -/
theorem exists_ne_zero_mem_pseudoNormalSpace (g' : PseudoRiemannianMetric I' M')
    (f : C^∞⟮I, M; I', M'⟯) (himm : Function.Injective (mfderiv I I' f x))
    (hcodim : finrank ℝ E + 1 = finrank ℝ E') :
    ∃ v ∈ pseudoNormalSpace g' f x, v ≠ 0 := by
  haveI : ∀ y : M, FiniteDimensional ℝ (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) y) :=
    fun y => finiteDimensional_fibre (F := E') y
  haveI : Nontrivial (pseudoNormalSpace g' f x) :=
    finrank_pos_iff.mp (by rw [finrank_pseudoNormalSpace g' f himm hcodim]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : pseudoNormalSpace g' f x)
  exact ⟨v, v.2, fun h => hv (Subtype.ext h)⟩

/-! ### The differential is an isometry onto the tangent space -/

/-- **`dι_x : T_xM → T_xM ⊆ T_{ι x}M̃` is an isometry** of scalar product spaces.

This is the formal content of Lee's "we usually identify `T_pM` with its image in `T_pM̃`
under `dι_p`".  The identification is not definitional — `g` is a form on `T_xM` and the
pointwise results compute the signature of `g̃` restricted to `tangentRange f x`, a
submodule of a different space — so the isometry is what makes the two signatures the
same number.  `IsPullbackAlong` is precisely the statement that `dι_x` preserves the
forms, and injectivity comes free from nondegeneracy of `g`. -/
noncomputable def isometryEquivRestrictTangentRange (hg : IsPullbackAlong I I' g g' f) (x : M) :
    (LinearMap.BilinMap.toQuadraticMap (g.bilin x)).IsometryEquiv
      (LinearMap.BilinMap.toQuadraticMap
        (((g'.pullback f).bilin x).restrict (tangentRange f x))) where
  toLinearEquiv :=
    LinearEquiv.ofInjective
      (show TangentSpace I x →ₗ[ℝ] ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x from
        (mfderiv I I' f x).toLinearMap)
      (injective_mfderiv_of_isPullbackAlong hg x)
  map_app' v := (hg x v v).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **The signature of a pseudo-Riemannian submanifold is computed in the ambient fibre.**

`g.sigPosAt x` is by definition the number of positive terms in a diagonalization of `g_x`;
this says it equals the number of positive terms for `g̃` restricted to `T_xM ⊆ T_{ι x}M̃`,
which is what the pointwise results of `HypersurfaceSignature` speak about. -/
theorem sigPosAt_eq_sigPos_restrict_tangentRange (hg : IsPullbackAlong I I' g g' f) (x : M) :
    g.sigPosAt x
      = sigPos (LinearMap.BilinMap.toQuadraticMap
          (((g'.pullback f).bilin x).restrict (tangentRange f x))) :=
  QuadraticMap.Equivalent.sigPos_eq ⟨isometryEquivRestrictTangentRange hg x⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The negative counterpart of `sigPosAt_eq_sigPos_restrict_tangentRange`: Lee's *index*
of the induced metric is computed in the ambient fibre. -/
theorem sigNegAt_eq_sigNeg_restrict_tangentRange (hg : IsPullbackAlong I I' g g' f) (x : M) :
    g.sigNegAt x
      = sigNeg (LinearMap.BilinMap.toQuadraticMap
          (((g'.pullback f).bilin x).restrict (tangentRange f x))) :=
  QuadraticMap.Equivalent.sigNeg_eq ⟨isometryEquivRestrictTangentRange hg x⟩

/-! ### Lee's Proposition 2.70 -/

/-- **Lee, Proposition 2.70, nondegeneracy half.**  For a hypersurface `M ⊆ M̃`, the induced
tensor `ι^*g̃` is nondegenerate at `x` if and only if every nonzero normal vector at `x` is
non-null.

This is stated for an arbitrary immersion `f`, not for a map already carrying an
`IsPullbackAlong` witness: `IsPullbackAlong` presupposes a *nondegenerate* `g` on `M`, and
nondegeneracy of the induced tensor is exactly what this iff decides.  So the induced
tensor appears here as `g̃` restricted to `tangentRange f x` — the honest "pullback form"
of a possibly-degenerate situation — rather than as a `PseudoRiemannianMetric`. -/
theorem restrict_tangentRange_nondegenerate_iff (g' : PseudoRiemannianMetric I' M')
    (f : C^∞⟮I, M; I', M'⟯) (himm : Function.Injective (mfderiv I I' f x))
    (hcodim : finrank ℝ E + 1 = finrank ℝ E') :
    (((g'.pullback f).bilin x).restrict (tangentRange f x)).Nondegenerate ↔
      ∀ v ∈ pseudoNormalSpace g' f x, v ≠ 0 → (g'.pullback f).bilin x v v ≠ 0 := by
  haveI : ∀ y : M, FiniteDimensional ℝ (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) y) :=
    fun y => finiteDimensional_fibre (F := E') y
  rw [pseudoNormalSpace_eq_orthogonal]
  exact restrict_nondegenerate_iff_forall_orthogonal ((g'.pullback f).bilin_isSymm x)
    ((g'.pullback f).bilin_nondegenerate x) (finrank_tangentRange_add_one f himm hcodim)

/-- **Lee, Proposition 2.70, signature half.**  If `(M̃, g̃)` has signature `(r,s)` and `M ⊆ M̃`
is a hypersurface whose induced metric is `g`, then a single non-null normal vector at `x`
decides the signature of `g` at `x`: a positive one deletes a positive sign, a negative one
deletes a negative sign.

One normal vector suffices because `N_xM` is a line, so any nonzero normal spans it.
Lee: "`g̃_p` has a basis representation `(β¹)² ± (β²)² ± ⋯ ± (βⁿ)²` with a positive sign on
the first term.  Therefore `ι^*g̃_p = ±(β²)² ± ⋯ ± (βⁿ)²` has signature `(r-1,s)`." -/
theorem sigPosAt_sigNegAt_of_mem_pseudoNormalSpace (hg : IsPullbackAlong I I' g g' f)
    (hcodim : finrank ℝ E + 1 = finrank ℝ E') {r s : ℕ} (hsig : HasSignature g' r s) (x : M)
    {v : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x}
    (hv : v ∈ pseudoNormalSpace g' f x) (hv0 : v ≠ 0) :
    (0 < (g'.pullback f).bilin x v v → g.sigPosAt x + 1 = r ∧ g.sigNegAt x = s) ∧
      ((g'.pullback f).bilin x v v < 0 → g.sigPosAt x = r ∧ g.sigNegAt x + 1 = s) := by
  haveI : ∀ y : M, FiniteDimensional ℝ (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) y) :=
    fun y => finiteDimensional_fibre (F := E') y
  have himm := injective_mfderiv_of_isPullbackAlong hg x
  -- The ambient signature at `f x`, transported to the pullback fibre.  `pullback_bilin` is
  -- `rfl`, so the two `sigPos`es are the same term.
  obtain ⟨hr, hs⟩ := hsig (f x)
  have hrp : sigPos (LinearMap.BilinMap.toQuadraticMap ((g'.pullback f).bilin x)) = r := hr
  have hrn : sigNeg (LinearMap.BilinMap.toQuadraticMap ((g'.pullback f).bilin x)) = s := hs
  have hpt := sigPos_sigNeg_restrict_of_mem_orthogonal ((g'.pullback f).bilin_isSymm x)
    ((g'.pullback f).bilin_nondegenerate x) (finrank_tangentRange_add_one f himm hcodim)
    (by rwa [← pseudoNormalSpace_eq_orthogonal]) hv0
  rw [sigPosAt_eq_sigPos_restrict_tangentRange hg x, sigNegAt_eq_sigNeg_restrict_tangentRange hg x]
  refine ⟨fun hpos => ?_, fun hneg => ?_⟩
  · obtain ⟨h1, h2⟩ := hpt.1 hpos
    exact ⟨h1.trans hrp, h2.trans hrn⟩
  · obtain ⟨h1, h2⟩ := hpt.2 hneg
    exact ⟨h1.trans hrp, h2.trans hrn⟩

/-- **Lee, Proposition 2.70**, in Lee's own phrasing: a hypersurface all of whose nonzero
normal vectors are positive is a pseudo-Riemannian submanifold of signature `(r-1, s)`.

Truncated subtraction is harmless here because `sigPosAt_sigNegAt_of_mem_pseudoNormalSpace`
delivers `g.sigPosAt x + 1 = r`, which forces `1 ≤ r`. -/
theorem hasSignature_of_forall_normal_pos (hg : IsPullbackAlong I I' g g' f)
    (hcodim : finrank ℝ E + 1 = finrank ℝ E') {r s : ℕ} (hsig : HasSignature g' r s)
    (hpos : ∀ (x : M), ∀ v ∈ pseudoNormalSpace g' f x, v ≠ 0 →
      0 < (g'.pullback f).bilin x v v) :
    HasSignature g (r - 1) s := by
  intro x
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_pseudoNormalSpace g' f
    (injective_mfderiv_of_isPullbackAlong hg x) hcodim
  obtain ⟨h1, h2⟩ :=
    (sigPosAt_sigNegAt_of_mem_pseudoNormalSpace hg hcodim hsig x hv hv0).1 (hpos x v hv hv0)
  exact ⟨by omega, h2⟩

/-- **Lee, Proposition 2.70**, negative case: a hypersurface all of whose nonzero normal
vectors are negative is a pseudo-Riemannian submanifold of signature `(r, s-1)`. -/
theorem hasSignature_of_forall_normal_neg (hg : IsPullbackAlong I I' g g' f)
    (hcodim : finrank ℝ E + 1 = finrank ℝ E') {r s : ℕ} (hsig : HasSignature g' r s)
    (hneg : ∀ (x : M), ∀ v ∈ pseudoNormalSpace g' f x, v ≠ 0 →
      (g'.pullback f).bilin x v v < 0) :
    HasSignature g r (s - 1) := by
  intro x
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_pseudoNormalSpace g' f
    (injective_mfderiv_of_isPullbackAlong hg x) hcodim
  obtain ⟨h1, h2⟩ :=
    (sigPosAt_sigNegAt_of_mem_pseudoNormalSpace hg hcodim hsig x hv hv0).2 (hneg x v hv hv0)
  exact ⟨h1, by omega⟩

/-! ### The induced metric exists -/

/-- **Lee, Proposition 2.70, constructive half**: on a hypersurface all of whose nonzero
normal vectors are non-null, the induced tensor really is nondegenerate.

This is what turns `restrict_tangentRange_nondegenerate_iff` from a criterion into a
construction: fed to `pseudoPullbackMetric` it produces the induced metric `g = ι^*g̃`, and
`isPullbackAlong_pseudoPullbackMetric` then discharges the `IsPullbackAlong` hypothesis of
the signature half.  Without it, `hasSignature_of_forall_normal_pos` could only be applied
to metrics a caller obtained some other way — and for an indefinite `g̃` there is no other
way. -/
theorem exists_pseudoPullbackForm_ne_zero (g' : PseudoRiemannianMetric I' M')
    (F : C^∞⟮I, M; I', M'⟯) (himm : ∀ p : M, Function.Injective (mfderiv I I' F p))
    (hcodim : finrank ℝ E + 1 = finrank ℝ E')
    (hnull : ∀ (p : M), ∀ v ∈ pseudoNormalSpace g' F p, v ≠ 0 →
      (g'.pullback F).bilin p v v ≠ 0)
    (p : M) (v : TangentSpace I p) (hv : v ≠ 0) :
    ∃ w, pseudoPullbackForm g' F p v w ≠ 0 := by
  have hnd := (restrict_tangentRange_nondegenerate_iff g' F (himm p) hcodim).mpr (hnull p)
  by_contra hcon
  push Not at hcon
  -- `dF_p v` is a nonzero member of `T_pM ⊆ T_{F p}M̃` ...
  have hu0 : (⟨mfderiv I I' F p v, ⟨v, rfl⟩⟩ : tangentRange F p) ≠ 0 := by
    intro h
    exact hv (himm p (by simpa using congrArg Subtype.val h))
  -- ... and by hypothesis it pairs to zero with every tangent vector, contradicting
  -- nondegeneracy of the restricted form.
  refine hu0 (hnd.1 _ ?_)
  rintro ⟨-, w, rfl⟩
  exact hcon w

/-- **Lee, Proposition 2.70**, in full: a hypersurface of a pseudo-Riemannian manifold of
signature `(r,s)` all of whose nonzero normal vectors are positive *is* a pseudo-Riemannian
submanifold, of signature `(r-1, s)`.

This is the form of the proposition in which every hypothesis is one a caller actually has:
an ambient metric, a codimension-1 immersion, and the sign of the normals.  The induced
metric is not assumed — it is *built*, by `pseudoPullbackMetric` out of the nondegeneracy
that `exists_pseudoPullbackForm_ne_zero` derives from the normals being non-null. -/
theorem hasSignature_pseudoPullbackMetric_of_forall_normal_pos
    (g' : PseudoRiemannianMetric I' M') (F : C^∞⟮I, M; I', M'⟯)
    (himm : ∀ p : M, Function.Injective (mfderiv I I' F p))
    (hcodim : finrank ℝ E + 1 = finrank ℝ E') {r s : ℕ} (hsig : HasSignature g' r s)
    (hpos : ∀ (p : M), ∀ v ∈ pseudoNormalSpace g' F p, v ≠ 0 →
      0 < (g'.pullback F).bilin p v v) :
    HasSignature (pseudoPullbackMetric g' F (exists_pseudoPullbackForm_ne_zero g' F himm hcodim
      (fun p v hv hv0 => (hpos p v hv hv0).ne'))) (r - 1) s :=
  hasSignature_of_forall_normal_pos (isPullbackAlong_pseudoPullbackMetric g' F _) hcodim hsig hpos

/-- **Lee, Proposition 2.70**, negative case in full: if every nonzero normal is negative,
the hypersurface is a pseudo-Riemannian submanifold of signature `(r, s-1)`. -/
theorem hasSignature_pseudoPullbackMetric_of_forall_normal_neg
    (g' : PseudoRiemannianMetric I' M') (F : C^∞⟮I, M; I', M'⟯)
    (himm : ∀ p : M, Function.Injective (mfderiv I I' F p))
    (hcodim : finrank ℝ E + 1 = finrank ℝ E') {r s : ℕ} (hsig : HasSignature g' r s)
    (hneg : ∀ (p : M), ∀ v ∈ pseudoNormalSpace g' F p, v ≠ 0 →
      (g'.pullback F).bilin p v v < 0) :
    HasSignature (pseudoPullbackMetric g' F (exists_pseudoPullbackForm_ne_zero g' F himm hcodim
      (fun p v hv hv0 => (hneg p v hv hv0).ne))) r (s - 1) :=
  hasSignature_of_forall_normal_neg (isPullbackAlong_pseudoPullbackMetric g' F _) hcodim hsig hneg

end PseudoHypersurface

end LeeLib.Ch02
