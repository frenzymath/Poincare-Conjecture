import MorganTianLib.Ch01.CurvatureNormSectional
import MorganTianLib.Ch01.PointwiseCurvature

/-!
# Poincaré Ch. 1, §1.2 — `|Rm| ≤ K` at a *point of `M`*

`CurvatureNormSectional.lean` proves the algebraic half of `def:curvature-operator-norm`: on a
single inner product space, `|Rm| ≤ K` bounds `|K(P)|` for every `2`-plane. That statement lives
on a fibre, and the comparison lemmas of §1.5 consume a bound on `sectionalCurvatureAt` — a
*manifold-level* notion at a point `x ∈ M`. This file crosses that last step.

The crossing is not quite a `rfl`: `sectionalCurvatureAt` is defined under a *local*
`Bundle.RiemannianBundle` instance (`⟨g.toRiemannianMetric⟩`), which is what puts the inner
product of `g_x` on the fibre `T_xM`. Every statement here opens that same `letI`, exactly as
`isAlgCurvatureForm_curvatureFormAt` and `IsEinstein.sectionalCurvature_const` do.

## Main results

* `HasCurvatureOperatorNormLeAt` — Morgan–Tian's `|Rm(x)| ≤ K`, at a point of `M`.
* `abs_sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeAt` — `|Rm(x)| ≤ K ⟹ |K(P)| ≤ K`
  for every `2`-plane `P ⊂ T_xM`, spanned by an arbitrary (not necessarily orthonormal,
  not necessarily independent) pair.
* `sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeAt` and
  `neg_le_sectionalCurvatureAt_of_hasCurvatureOperatorNormLeAt` — the two one-sided forms. The
  first is the hypothesis of `lem:conjugate-sturm` (and so of
  `lem:local-diffeomorphism-bounded-curvature`); the second is the hypothesis of
  `thm:sectional-curvature-comparison`.

Blueprint: `def:curvature-operator-norm`, `def:sectional-curvature`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2.
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Morgan–Tian's `|Rm(x)| ≤ K`** at a point `x ∈ M`: the curvature operator of
`(M, g)` at `x`, a symmetric bilinear form on `⋀²(T_xM)`, is bounded by `K` times the induced
inner product, `|Rm(φ,φ)| ≤ K·⟨φ,φ⟩`. Equivalently (self-adjointness) all its eigenvalues lie
in `[-K, K]`.

This is `HasCurvatureOperatorNormLe` of `CurvatureOperator.lean`, applied to the algebraic
curvature form `curvatureFormAt g nabla x` on the fibre `T_xM` — which is an algebraic curvature
form precisely because `nabla` is Levi-Civita (`isAlgCurvatureForm_curvatureFormAt`, i.e.
`claim:curvature-symmetries-bianchi`).

Blueprint: `def:curvature-operator-norm`. -/
def HasCurvatureOperatorNormLeAt (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (x : M) (K : ℝ) : Prop :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  HasCurvatureOperatorNormLe (isAlgCurvatureForm_curvatureFormAt g nabla hLC x) K

/-- **Math.** **`|Rm(x)| ≤ K` bounds every sectional curvature at `x`** — the final claim of
`def:curvature-operator-norm`, now at a point of the manifold rather than on a bare inner
product space.

The pair `(v, w)` is arbitrary: neither orthonormal nor even independent. In the degenerate case
`sectionalCurvatureAt` takes the junk value `0`, which is `≤ K` since `K ≥ 0`; otherwise
Gram–Schmidt reduces to the orthonormal case
(`abs_sectionalCurvature_le_of_hasCurvatureOperatorNormLe`).

Blueprint: `def:curvature-operator-norm`, `def:sectional-curvature`. -/
theorem abs_sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeAt
    {g : RiemannianMetric I M} {nabla : AffineConnection I M} {hLC : nabla.IsLeviCivita g}
    {x : M} {K : ℝ} (hK : 0 ≤ K) (h : HasCurvatureOperatorNormLeAt g nabla hLC x K)
    (v w : TangentSpace I x) :
    |sectionalCurvatureAt g nabla x v w| ≤ K := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact abs_sectionalCurvature_le_of_hasCurvatureOperatorNormLe
    (isAlgCurvatureForm_curvatureFormAt g nabla hLC x) hK h v w

/-- **Math.** The **upper** half of `abs_sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeAt`:
`|Rm(x)| ≤ K ⟹ K(P) ≤ K`. This is the hypothesis shape consumed by `lem:conjugate-sturm` and
hence by `lem:local-diffeomorphism-bounded-curvature`.
Blueprint: `def:curvature-operator-norm`. -/
theorem sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeAt
    {g : RiemannianMetric I M} {nabla : AffineConnection I M} {hLC : nabla.IsLeviCivita g}
    {x : M} {K : ℝ} (hK : 0 ≤ K) (h : HasCurvatureOperatorNormLeAt g nabla hLC x K)
    (v w : TangentSpace I x) :
    sectionalCurvatureAt g nabla x v w ≤ K :=
  (abs_le.mp (abs_sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeAt hK h v w)).2

/-- **Math.** The **lower** half: `|Rm(x)| ≤ K ⟹ −K ≤ K(P)`. This is the hypothesis shape
consumed by `thm:sectional-curvature-comparison` (whose bound is `−k ≤ K(P)`).
Blueprint: `def:curvature-operator-norm`. -/
theorem neg_le_sectionalCurvatureAt_of_hasCurvatureOperatorNormLeAt
    {g : RiemannianMetric I M} {nabla : AffineConnection I M} {hLC : nabla.IsLeviCivita g}
    {x : M} {K : ℝ} (hK : 0 ≤ K) (h : HasCurvatureOperatorNormLeAt g nabla hLC x K)
    (v w : TangentSpace I x) :
    -K ≤ sectionalCurvatureAt g nabla x v w :=
  (abs_le.mp (abs_sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeAt hK h v w)).1

end MorganTianLib

end
