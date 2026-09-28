import PetersenLib.Ch05.Geodesics
import PetersenLib.Ch05.MetricStructure
import Mathlib.Analysis.Convex.Function

/-!
# Petersen Ch. 6, §6.2 — convex functions on a Riemannian manifold (GTM 171, 3rd ed.)

Petersen's §6.2 (p. 259), `def:pet-ch6-convex-function`: a function on a Riemannian
manifold is **(strictly) convex** if its restriction to every geodesic is (strictly)
convex as a function of the affine parameter.

## Two design decisions, both load-bearing

**1. The definitions are relative to a set `U`.** Petersen states convexity globally, but
every downstream consumer in this chapter wants "convex *on* `B(p,R)`" — in particular
`thm:pet-ch6-convexity-radius-criterion`, whose whole content is that a *ball* is convex.
A global-only definition would have to be rewritten, so `IsConvexOn g U f` quantifies over
the geodesics that *stay inside* `U` (`Set.MapsTo γ J U`). The global notion is the special
case `U = Set.univ`. Note the resulting antitonicity in `U` (`IsConvexOn.mono`): shrinking
the set shrinks the family of test geodesics.

**2. Strict convexity must exclude constant geodesics — see the trap below.**

## TRAP (failure memory): the strict-convexity vacuity trap

Constant curves **are** geodesics in this project's encoding: `Geodesic.IsGeodesicOn`
imposes only that the covariant acceleration vanish, which a constant curve satisfies. So
the naive reading of "the restriction to *every* geodesic is strictly convex" is **false for
every `f` whatsoever**: take `γ` constant, and `f ∘ γ` is a constant function, which is not
strictly convex. That definition would be uniformly empty — and, worse, a `\leanok` on it
would let every downstream theorem be discharged from a hypothesis nobody can ever satisfy.

`IsStrictlyConvexOn` therefore quantifies only over `IsNonconstantGeodesicOn` geodesics.
This guard is not an artifact of the encoding: it is exactly what Petersen's own argument
supplies. In `rem:pet-ch6-hessian-f0-positive-definite` he derives strict convexity of
`f₀ = r²/2` from `Hess f₀ ≻ 0` via `(f₀ ∘ c)'' = Hess f₀ (ċ, ċ) > 0`, and that last
inequality needs `ċ ≠ 0`, i.e. `c` nonconstant. Positive definiteness of the Hessian gives
nothing at all along a constant curve.

Honest status: the guard removes the known universal counterexample, so the definition is
**not obviously vacuous**. It is *not* known to be inhabited — no positive witness has been
produced in this project yet, because `hess_f0_posDef_nonpositiveCurvature` (the intended
first witness) is still open. Do not read `IsStrictlyConvexOn` as certified nonvacuous.

## Naming

Mathlib's one-dimensional notions are `ConvexOn` / `StrictConvexOn` (no `Is`), and they are
what the *conclusion* of each definition below is stated with, applied to `fun t => f (γ t)`
on the parameter set `J ⊆ ℝ`. The Riemannian notions here are `IsConvexOn` /
`IsStrictlyConvexOn`, so there is no name clash to disambiguate — the two families never
compete for the same identifier.

## Scope

The definitions and the structural lemmas that need no analysis are here. Not here:
`hess_f0_posDef_nonpositiveCurvature` (needs `rem:pet-ch6-jacobi-hessian-r`, i.e. a
differential of `exp_p` away from the origin) and `centerOfMassLinfty` (needs the previous
one, plus properness/existence of the minimum via Hopf–Rinow).
-/

open Set
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen §6.2 (p. 259), serving `def:pet-ch6-convex-function`: `γ` is a
**nonconstant** geodesic on the parameter set `J`.

This exists solely to state strict convexity without vacuity. In this project's encoding a
geodesic is a curve with vanishing covariant acceleration, and a *constant* curve qualifies;
since `f ∘ γ` is then constant and no constant function is strictly convex, quantifying
strict convexity over all geodesics would be false for every `f`. Nonconstancy is recorded
as "two parameters in `J` with distinct images", which is the weakest form that kills the
counterexample and is trivially available in practice: for a geodesic joining two distinct
points `p ≠ q`, the endpoints themselves witness it. -/
def IsNonconstantGeodesicOn (g : RiemannianMetric I M) (γ : ℝ → M) (J : Set ℝ) : Prop :=
  Geodesic.IsGeodesicOn (I := I) g γ J ∧ ∃ s ∈ J, ∃ t ∈ J, γ s ≠ γ t

/-- **Math.** Petersen §6.2 (p. 259), `def:pet-ch6-convex-function`: `f` is **convex on
`U`** if its restriction to every geodesic that stays in `U` is a convex function of the
affine parameter.

The affine parameter is the point: convexity of `t ↦ f (γ t)` is asserted for the geodesic
parametrization, not for arclength along an arbitrary curve, and it is this parametrization
that makes the notion equivalent to `Hess f ≥ 0` (Petersen's route). `J` ranges over convex
parameter sets so that mathlib's `ConvexOn ℝ J` is the intended one-dimensional statement.

`U` is a parameter rather than `Set.univ` because `thm:pet-ch6-convexity-radius-criterion`
asks precisely for convexity on a ball; the global notion of the blueprint is `U = univ`. -/
def IsConvexOn (g : RiemannianMetric I M) (U : Set M) (f : M → ℝ) : Prop :=
  ∀ (γ : ℝ → M) (J : Set ℝ), Convex ℝ J → Geodesic.IsGeodesicOn (I := I) g γ J →
    Set.MapsTo γ J U → ConvexOn ℝ J (fun t => f (γ t))

/-- **Math.** Petersen §6.2 (p. 259), `def:pet-ch6-convex-function`: `f` is **strictly
convex on `U`** if its restriction to every *nonconstant* geodesic staying in `U` is a
strictly convex function of the affine parameter.

The nonconstancy guard is mandatory, not cosmetic: without it the definition is satisfied by
no function at all, since a constant geodesic makes `f ∘ γ` constant. See the module
docstring for the full trap and for why Petersen's `Hess f₀ ≻ 0` argument supplies exactly
this guard (it needs `ċ ≠ 0`). -/
def IsStrictlyConvexOn (g : RiemannianMetric I M) (U : Set M) (f : M → ℝ) : Prop :=
  ∀ (γ : ℝ → M) (J : Set ℝ), Convex ℝ J → IsNonconstantGeodesicOn (I := I) g γ J →
    Set.MapsTo γ J U → StrictConvexOn ℝ J (fun t => f (γ t))

/-- **Math.** Convexity on a set is *antitone* in the set: a function convex on `V` is convex
on any smaller `U ⊆ V`, because every geodesic confined to `U` is in particular confined to
`V`, hence already a test curve for `V`. This is the lemma that lets the global notion
(`U = Set.univ`, the blueprint's reading of `def:pet-ch6-convex-function`) be specialized to
the balls that `thm:pet-ch6-convexity-radius-criterion` works with. -/
theorem IsConvexOn.mono {g : RiemannianMetric I M} {U V : Set M} {f : M → ℝ}
    (h : IsConvexOn (I := I) g V f) (hUV : U ⊆ V) : IsConvexOn (I := I) g U f :=
  fun γ J hJ hγ hm => h γ J hJ hγ (hm.mono_right hUV)

/-- **Math.** Strict convexity on a set is antitone in the set, for the same reason as
`IsConvexOn.mono`: shrinking `U` only shrinks the family of admissible test geodesics. -/
theorem IsStrictlyConvexOn.mono {g : RiemannianMetric I M} {U V : Set M} {f : M → ℝ}
    (h : IsStrictlyConvexOn (I := I) g V f) (hUV : U ⊆ V) :
    IsStrictlyConvexOn (I := I) g U f :=
  fun γ J hJ hγ hm => h γ J hJ hγ (hm.mono_right hUV)

/-- **Math.** Petersen §6.2 (p. 259), one half of `rem:pet-ch6-max-of-convex-functions`: the
maximum of **two** convex functions is convex. As Petersen notes, the statement "reduces to
the one-dimensional statement by restricting to geodesics" — and that is literally the proof
here: restrict both to a common test geodesic and apply mathlib's `ConvexOn.sup`.

This does **not** close `rem:pet-ch6-max-of-convex-functions`, which asserts the maximum of
*finitely many* convex functions is convex. Mathlib's `ConvexOn.sup` is binary and has no
`iSup`/finite-family version, so the finite case needs its own induction over a `Finset`
(with the nonemptiness side condition that a max over a family requires). Deriving the
finite case from this binary one is routine but has not been done; until it is, the node
stays open. `def:pet-ch6-linfty-center-of-mass` is the consumer that will need the finite
form (a max over `p₁, …, p_k`). -/
theorem IsConvexOn.max {g : RiemannianMetric I M} {U : Set M} {f₁ f₂ : M → ℝ}
    (h₁ : IsConvexOn (I := I) g U f₁) (h₂ : IsConvexOn (I := I) g U f₂) :
    IsConvexOn (I := I) g U (fun x => max (f₁ x) (f₂ x)) :=
  fun γ J hJ hγ hm => (h₁ γ J hJ hγ hm).sup (h₂ γ J hJ hγ hm)

/-- **Math.** Petersen §6.2 (p. 259), the *uniqueness core* of the second half of
`rem:pet-ch6-max-of-convex-functions`: a strictly convex function has at most one global
minimum — "if there were two minima, strict convexity restricted to a geodesic joining them
would force smaller values on the interior of the segment than at either endpoint".

Note the structure of the argument, which is the reason the nonconstancy guard costs nothing
here: one assumes `p ≠ q` for contradiction, and *that very assumption* is what makes the
joining geodesic nonconstant, so `IsStrictlyConvexOn` applies. Both `0` and `1` are then
minima of `f ∘ γ` on `[0,1]`, and strict convexity forces `0 = 1`.

This is deliberately **not** named `strictlyConvex_uniqueMinimum` and does **not** close
`rem:pet-ch6-max-of-convex-functions`: the blueprint's statement is *existence and*
uniqueness of a minimum for a proper nonnegative strictly convex function on a *complete*
manifold. Existence (properness plus boundedness below) and the production of the joining
geodesic (Hopf–Rinow) are both missing; here the geodesic is a hypothesis. -/
theorem strictlyConvexOn_univ_unique_min {g : RiemannianMetric I M} {f : M → ℝ}
    (hf : IsStrictlyConvexOn (I := I) g Set.univ f) {p q : M}
    (hp : IsMinOn f Set.univ p) (hq : IsMinOn f Set.univ q)
    (γ : ℝ → M) (hγ : Geodesic.IsGeodesicOn (I := I) g γ (Icc 0 1))
    (h0 : γ 0 = p) (h1 : γ 1 = q) : p = q := by
  by_contra hne
  have hnc : IsNonconstantGeodesicOn (I := I) g γ (Icc 0 1) :=
    ⟨hγ, 0, by norm_num, 1, by norm_num, by rw [h0, h1]; exact hne⟩
  have hsc := hf γ (Icc 0 1) (convex_Icc 0 1) hnc (fun t _ => mem_univ _)
  have hmin0 : IsMinOn (fun t => f (γ t)) (Icc 0 1) 0 := by
    rw [isMinOn_iff, h0]; exact fun t _ => isMinOn_iff.mp hp (γ t) (mem_univ _)
  have hmin1 : IsMinOn (fun t => f (γ t)) (Icc 0 1) 1 := by
    rw [isMinOn_iff, h1]; exact fun t _ => isMinOn_iff.mp hq (γ t) (mem_univ _)
  have : (0 : ℝ) = 1 := hsc.eq_of_isMinOn hmin0 hmin1 (by norm_num) (by norm_num)
  norm_num at this

end PetersenLib
