/-
Chapter 2, "Riemannian Metrics", §"Raising and Lowering Indices": **Problem 2-10**,
the characterization of the gradient among nowhere-vanishing vector fields.

Lee: *let `(M, g)` be a Riemannian manifold, `f ∈ C^∞(M)`, and `X` a
nowhere-vanishing vector field.  Then `X = grad f` if and only if `Xf = |X|_g²`
and `X` is orthogonal to the level sets of `f` at all regular points of `f`.*

## The shape of the proof

The interesting direction is the converse, and the two hypotheses play quite
different roles.

*The orthogonality hypothesis alone is far from enough*: it only pins `X_p` down
to the line `(ker df_p)^⊥`, i.e. to a scalar multiple `λ · grad f|_p`. The
equation `Xf = |X|²_g` is what fixes the scalar: it reads
`λ|grad f|² = λ²|grad f|²`, forcing `λ ∈ {0, 1}`, and `λ = 0` is excluded exactly
because `X` is nowhere vanishing.

*The regularity proviso costs nothing.* Lee only assumes orthogonality at regular
points, but under these hypotheses **every** point is regular: at any `p`,
`df_p(X_p) = |X_p|²_g > 0` because `X_p ≠ 0`, so `df_p ≠ 0`. So `f` has no
critical points at all, and the proviso never bites. (Equivalently: at a critical
point `df_p = 0` would force `|X_p|² = 0`, i.e. `X_p = 0`.) This is why
`eq_grad_of_ne_zero_of_innerAt_self_of_orthogonal_ker` below needs no hypothesis
about `p` being regular — its own hypotheses already imply it.

## Why there is no dimension counting

The informal argument above ("`(ker df_p)^⊥` is a line, so `X_p = λ grad f|_p`")
needs `ker df_p` to be a hyperplane and a rank-nullity count. None of that is
necessary. Since `df_p(X_p) = ⟨X_p, X_p⟩ ≠ 0`, the vector `X_p` is transversal to
`ker df_p`, so every `w ∈ T_pM` splits as
`w = (w - t·X_p) + t·X_p` with `t = df_p(w)/df_p(X_p)`,
where the first summand lies in `ker df_p` by construction. Pairing with `X_p`
kills that summand (orthogonality) and leaves `⟨X_p, w⟩ = t⟨X_p, X_p⟩ = df_p(w)`;
since this holds for every `w`, `X_p` represents `df_p`, which is exactly
`X_p = grad f|_p` by uniqueness of the sharp operator. The splitting is explicit,
so no finite-dimensionality, rank theorem, or orthogonal-complement theory is used
— and the lemma holds on any Riemannian manifold, of any dimension.
-/
import LeeLib.Ch02.RegularLevelSet

namespace LeeLib.Ch02

open scoped Manifold ContDiff

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

variable (g : RiemannianMetric I M) (f : M → ℝ)

omit [I.Boundaryless] in
/-- **Problem 2-10, pointwise.**  A nonzero vector `v` that is `g`-orthogonal to
`ker df_p` and satisfies `⟨v, v⟩_g = df_p(v)` is the gradient of `f` at `p`.

No regularity hypothesis on `p` is needed: `df_p(v) = ⟨v, v⟩_g > 0` already forces
`df_p ≠ 0`.

The proof splits an arbitrary `w` along the transversal `v`: with
`t = df_p(w)/df_p(v)`, the vector `w - t·v` lies in `ker df_p`, so orthogonality
gives `⟨v, w⟩ = t⟨v, v⟩ = t·df_p(v) = df_p(w)`.  As `w` was arbitrary, `v`
represents `df_p` under `g`, which is `eq_grad_of_innerAt`. -/
theorem eq_grad_of_ne_zero_of_innerAt_self_of_orthogonal_ker (p : M) (v : TangentSpace I p)
    (hne : v ≠ 0) (hself : g.innerAt p v v = extDerivFun (I := I) f p v)
    (horth : ∀ w : TangentSpace I p, extDerivFun (I := I) f p w = 0 → g.innerAt p v w = 0) :
    v = grad g f p := by
  -- `v ≠ 0` makes the pairing with itself strictly positive, so `v ∉ ker df_p`.
  have hpos : 0 < g.innerAt p v v :=
    lt_of_le_of_ne (g.innerAt_self_nonneg p v)
      (Ne.symm fun h => hne ((g.innerAt_self_eq_zero_iff p v).mp h))
  have hdv : extDerivFun (I := I) f p v ≠ 0 := hself ▸ hpos.ne'
  refine eq_grad_of_innerAt g f p v fun w => ?_
  set t : ℝ := extDerivFun (I := I) f p w / extDerivFun (I := I) f p v with ht
  -- `w - t • v` lies in `ker df_p` by the choice of `t`.
  have hu : extDerivFun (I := I) f p (w - t • v) = 0 := by
    rw [map_sub, map_smul, ht, smul_eq_mul, div_mul_cancel₀ _ hdv, sub_self]
  have h0 := horth _ hu
  -- Expand the pairing against the split vector.
  have hexp : g.innerAt p v (w - t • v) = g.innerAt p v w - t * g.innerAt p v v := by
    show (g.inner p v) (w - t • v) = (g.inner p v) w - t * (g.inner p v) v
    rw [map_sub, map_smul]
    rfl
  rw [hexp] at h0
  have hvw : g.innerAt p v w = t * g.innerAt p v v := by linarith
  rw [hvw, hself, ht]
  field_simp

/-- **Problem 2-10** (Lee): *for a nowhere-vanishing vector field `X`, `X = grad f`
if and only if `Xf = |X|_g²` and `X` is orthogonal to the level sets of `f` at
every regular point of `f`.*

The tangent space to the level set of `f` through a regular point `p` is `ker df_p`
(Corollary A.26), so "orthogonal to the level sets at regular points" is rendered
as `⟨X_p, w⟩_g = 0` for every `w ∈ ker df_p` and every regular `p`. The quantity
`Xf` is `df(X)`, and `|X|²_g` is `⟨X, X⟩_g`.

Note the forward direction needs neither hypothesis on `X`, and the converse never
uses the regularity proviso: as explained in the module docstring, the hypotheses
force every point of `M` to be regular. -/
theorem eq_grad_iff_of_forall_ne_zero (X : ∀ p : M, TangentSpace I p) (hX : ∀ p, X p ≠ 0) :
    (∀ p, X p = grad g f p) ↔
      (∀ p, extDerivFun (I := I) f p (X p) = g.innerAt p (X p) (X p)) ∧
        (∀ p ∈ regularSet I f, ∀ w : TangentSpace I p,
          extDerivFun (I := I) f p w = 0 → g.innerAt p (X p) w = 0) := by
  constructor
  · intro h
    refine ⟨fun p => ?_, fun p _ w hw => ?_⟩
    · rw [h p, innerAt_grad]
    · rw [h p, innerAt_grad, hw]
  · rintro ⟨hself, horth⟩ p
    -- Every point is regular: `df_p(X_p) = ⟨X_p, X_p⟩ > 0`.
    have hpos : 0 < g.innerAt p (X p) (X p) :=
      lt_of_le_of_ne (g.innerAt_self_nonneg p (X p))
        (Ne.symm fun h => hX p ((g.innerAt_self_eq_zero_iff p (X p)).mp h))
    have hreg : p ∈ regularSet I f := by
      rw [mem_regularSet_iff_grad_ne_zero g f p]
      intro hgrad
      -- If `grad f|_p = 0` then `df_p(X_p) = ⟨0, X_p⟩ = 0`, contradicting positivity.
      have hz : extDerivFun (I := I) f p (X p) = 0 := by
        rw [← innerAt_grad g f p (X p), hgrad]
        simp [RiemannianMetric.innerAt]
      rw [hself p] at hz
      exact hpos.ne' hz
    exact eq_grad_of_ne_zero_of_innerAt_self_of_orthogonal_ker g f p (X p) (hX p)
      (hself p).symm (horth p hreg)

end

end LeeLib.Ch02
