/-
Chapter 2, "Riemannian Metrics", §"Isometries": **local isometries**, and Lee's
Exercise 2.7 identifying them, between manifolds of equal dimension, with the
smooth maps satisfying `φ^* g̃ = g`.

Lee defines a *local isometry* `φ : M → M̃` as a map each of whose points has a
neighbourhood on which `φ` restricts to an isometry onto an open subset of `M̃`,
and Exercise 2.7 asks:

> if `(M,g)` and `(M̃,g̃)` are Riemannian manifolds of the same dimension, a
> smooth map `φ : M → M̃` is a local isometry if and only if `φ^* g̃ = g`.

The easy direction needs no hypothesis on dimensions and was already available
(`IsMetricPreserving` is a pointwise condition, so it is inherited by any
restriction).  The substance is the converse: `φ^* g̃ = g` forces each `dφ_p` to be
injective — it is a linear isometry onto its image — and equal dimensions promote
that to invertible, at which point the **inverse function theorem for manifolds**
makes `φ` a local diffeomorphism.  That theorem is neither in mathlib (it is the
`## TODO` of `Mathlib/Geometry/Manifold/LocalDiffeomorph.lean`) nor in Lee's
Appendix A other than as a citation of the *Smooth Manifolds* volume; it is proved
in `LeeLib.AppendixA.InverseFunctionTheorem`, and this file is its first consumer.

## Why `IsLocalDiffeomorph ∧ IsMetricPreserving` is Lee's definition

`IsLocalIsometry` is spelled below as `IsLocalDiffeomorph I I' ∞ φ ∧ IsMetricPreserving g g' φ`
rather than as an explicit "`∀ p`, there are `U ∋ p` and open `V` with `φ|_U : U → V`
an isometry".  These agree, and the reason is that metric preservation is a
*pointwise* condition on `dφ_p`:

* Lee's version gives, at each `p`, a neighbourhood `U` on which `φ` restricts to a
  diffeomorphism onto an open set — that is exactly mathlib's `IsLocalDiffeomorph`,
  which unfolds to a `PartialDiffeomorph` through each point — and on which `dφ_q`
  carries `g_q` to `g̃_{φ(q)}`; since every `p` lies in its own `U`, that holds at
  every point of `M`, which is `IsMetricPreserving`.
* Conversely, given both conditions, the `U` supplied by `IsLocalDiffeomorph` at `p`
  restricts `φ` to a diffeomorphism onto an open `V`, and it preserves the metric
  because `dφ` does so at every point.

Taking the conjunction as the definition avoids having to restrict `g` and `g̃` to
open submanifolds merely in order to *state* the definition, and it keeps Exercise
2.7 honest: the content of the exercise is entirely the implication
`IsMetricPreserving → IsLocalDiffeomorph`, and that is where the inverse function
theorem is used.
-/
import LeeLib.AppendixA.InverseFunctionTheorem
import LeeLib.Ch02.Isometry

namespace LeeLib.Ch02

open Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

noncomputable section

/-! ### An injective map between equal finite dimensions is invertible -/

/-- An injective continuous linear map between finite-dimensional spaces of equal dimension is
invertible.

Stated over bare normed spaces rather than over `TangentSpace`s: instances on `TangentSpace I x`
are a defeq copy of those on the model `E`, but they are not *syntactically* the model's, so
`FiniteDimensional` will not synthesize for them even though `exact` accepts the result. -/
theorem isInvertible_of_injective_of_finrank_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') {A : E →L[ℝ] E'}
    (hA : Function.Injective A) : A.IsInvertible := by
  have hbij : Function.Bijective (A : E →ₗ[ℝ] E') :=
    ⟨hA, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hA⟩
  exact ⟨(LinearEquiv.ofBijective (A : E →ₗ[ℝ] E') hbij).toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun _ => rfl⟩

section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ### Local isometries -/

/-- **Local isometry** (Lee, §"Isometries"): a map that restricts, near every point, to an isometry
onto an open subset.

See the module docstring for why this conjunction is Lee's definition: `IsLocalDiffeomorph` *is*
"restricts near every point to a diffeomorphism onto an open set", and metric preservation is a
pointwise condition, so localizing it changes nothing. -/
def IsLocalIsometry (g : RiemannianMetric I M) (g' : RiemannianMetric I' M') (φ : M → M') : Prop :=
  IsLocalDiffeomorph I I' ∞ φ ∧ IsMetricPreserving g g' φ

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'} {φ : M → M'}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- A local isometry preserves the metric.  This is the easy half of Lee's Exercise 2.7, and it
needs no hypothesis on dimensions. -/
theorem IsLocalIsometry.isMetricPreserving (h : IsLocalIsometry g g' φ) :
    IsMetricPreserving g g' φ := h.2

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- A local isometry is a local diffeomorphism. -/
theorem IsLocalIsometry.isLocalDiffeomorph (h : IsLocalIsometry g g' φ) :
    IsLocalDiffeomorph I I' ∞ φ := h.1

/-- **A metric-preserving smooth map between manifolds of equal dimension is a local
diffeomorphism** — the substance of Lee's Exercise 2.7.

`φ^* g̃ = g` makes each `dφ_p` a linear isometry onto its image, hence injective; equal dimensions
promote injective to invertible; and the inverse function theorem for manifolds
(`LeeLib.AppendixA.isLocalDiffeomorphAt_of_contMDiff_mfderiv_isInvertible`, which is mathlib's own
`LocalDiffeomorph` TODO) turns that into a local diffeomorphism at each point. -/
theorem IsMetricPreserving.isLocalDiffeomorph [I.Boundaryless]
    (h : IsMetricPreserving g g' φ) (hφ : ContMDiff I I' ∞ φ)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') :
    IsLocalDiffeomorph I I' ∞ φ := by
  intro p
  refine LeeLib.AppendixA.isLocalDiffeomorphAt_of_contMDiff_mfderiv_isInvertible
    (by simp) BoundarylessManifold.isInteriorPoint hφ ?_
  exact isInvertible_of_injective_of_finrank_eq hdim (h.injective_mfderiv p)

/-- **Lee, Exercise 2.7**: *between Riemannian manifolds of the same dimension, a smooth map is a
local isometry if and only if `φ^* g̃ = g`.*

The forward implication is immediate from the definition.  The converse is the inverse function
theorem for manifolds, applied to the differentials that `φ^* g̃ = g` forces to be injective; see
`IsMetricPreserving.isLocalDiffeomorph`. -/
theorem isLocalIsometry_iff_isMetricPreserving [I.Boundaryless] (hφ : ContMDiff I I' ∞ φ)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') :
    IsLocalIsometry g g' φ ↔ IsMetricPreserving g g' φ :=
  ⟨fun h => h.2, fun h => ⟨h.isLocalDiffeomorph hφ hdim, h⟩⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- An isometry is in particular a local isometry. -/
theorem IsIsometry.isLocalIsometry {Φ : Diffeomorph I I' M M' ∞} (h : IsIsometry g g' Φ) :
    IsLocalIsometry g g' (Φ : M → M') :=
  ⟨Φ.isLocalDiffeomorph, h⟩

end

end

end LeeLib.Ch02
