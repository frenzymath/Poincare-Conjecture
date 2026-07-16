/-
Chapter 2, "Riemannian Metrics", §2.5: the behaviour of the volume form under isometries.

Lee's Exercise 2.42 asserts that an orientation-preserving isometry `φ : (M, g) → (M̃, g̃)`
satisfies `φ^* dV_g̃ = dV_g`.  Stating it needs the **pullback of a differential form along a
smooth map**, which the pinned mathlib does not have at the manifold level: the only pullbacks
upstream are `extDerivWithin_pullback` and friends in `Mathlib/Analysis/Calculus/`, which pull
forms back between *open subsets of normed spaces* along `fderiv`.  There is no `mfderiv`-based
pullback of a section of the bundle of alternating forms anywhere.  `pullbackAlternating` below
supplies it.

`LeeLib.Ch02.pullbackForm` is a *different* map: it pulls back a **bilinear** form (a metric),
and lives in `LeeLib.Ch02.PullbackMetric`.  The two cannot be unified — a metric is a
`ContinuousLinearMap`-valued object and a differential form a `ContinuousAlternatingMap`-valued
one.

## Main definitions

* `pullbackAlternating`: `(φ^* w)|_x = w|_{φ x} ∘ (dφ_x, …, dφ_x)`, the pullback of a `k`-form
  field along a smooth map.  Only `mfderiv` is used, so no smoothness hypothesis is needed to
  *state* it.
* `IsMetricPreserving.pushBasis`: the pushforward `(dφ_x E_i)` of a `g`-orthonormal frame,
  packaged as a basis of `T_{φ x} M̃`.

## Main results

* `IsMetricPreserving.orthonormal_pushforward`: a metric-preserving map carries a `g`-orthonormal
  frame to a `g̃`-orthonormal family — the defining property of `IsMetricPreserving`, read
  fibrewise.
* `IsMetricPreserving.pullbackAlternating_volumeForm`: Lee's Exercise 2.42.

Both manifolds are modelled on the **same** normed space `E`.  That is how "`φ` preserves
dimension" is said without a `Fin n`-to-`Fin m` cast: `dV_g` has degree `finrank ℝ E` on either
side, so with two model spaces the two volume forms would not even have the same degree.  An
isometry is a diffeomorphism, so this costs no generality.

Reference: Lee, *Introduction to Riemannian Manifolds* (2nd ed.), Exercise 2.42.
-/
import LeeLib.Ch02.Isometry
import LeeLib.Ch02.VolumeForm

namespace LeeLib.Ch02

open Bundle Module InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ## The pullback of a differential form -/

/-- **The pullback of a `k`-form field along a smooth map**: `(φ^* w)|_x` is `w|_{φ x}` precomposed
with the differential `dφ_x` in each of its `k` arguments.

This is the missing manifold-level analogue of mathlib's `fderiv`-based pullback of forms between
open subsets of normed spaces.  Note it is *definable* with no smoothness hypothesis on `φ`:
`mfderiv` is total, so `φ^* w` is a well-defined family of forms for any `φ`, and smoothness of
`φ` is only needed to conclude that `φ^* w` is a smooth section. -/
def pullbackAlternating {k : ℕ} (φ : M → M')
    (w : ∀ y : M', (TangentSpace I' y) [⋀^Fin k]→L[ℝ] ℝ) (x : M) :
    (TangentSpace I x) [⋀^Fin k]→L[ℝ] ℝ :=
  (w (φ x)).compContinuousLinearMap (mfderiv I I' φ x)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp]
theorem pullbackAlternating_apply {k : ℕ} (φ : M → M')
    (w : ∀ y : M', (TangentSpace I' y) [⋀^Fin k]→L[ℝ] ℝ) (x : M)
    (v : Fin k → TangentSpace I x) :
    pullbackAlternating φ w x v = w (φ x) (fun i => mfderiv I I' φ x (v i)) := rfl

/-! ## Pushing a frame forward by a metric-preserving map -/

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'} {φ : M → M'}
  {o : PointwiseOrientation I M} {o' : PointwiseOrientation I' M'}
  {u : Set M} {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x} {x : M}

omit [FiniteDimensional ℝ E] in
/-- **A metric-preserving map carries an orthonormal frame to an orthonormal family.**  This is
just `IsMetricPreserving.inner_mfderiv` — `⟨dφ v, dφ w⟩_g̃ = ⟨v, w⟩_g` — read on the frame.
Orthonormality of the source frame is stated through `g`, as `exists_orthonormalFrame` produces
it, so no fibrewise inner product has to be installed by the caller. -/
theorem IsMetricPreserving.orthonormal_pushforward (h : IsMetricPreserving g g' φ)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0) (hx : x ∈ u) :
    letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
    Orthonormal ℝ (fun i => mfderiv I I' φ x (Y i x)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  rw [orthonormal_iff_ite]
  intro i j
  show ⟪mfderiv I I' φ x (Y i x), mfderiv I I' φ x (Y j x)⟫_ℝ = _
  rw [show ⟪mfderiv I I' φ x (Y i x), mfderiv I I' φ x (Y j x)⟫_ℝ
      = g'.inner (φ x) (mfderiv I I' φ x (Y i x)) (mfderiv I I' φ x (Y j x)) from rfl,
    h.inner_mfderiv x (Y i x) (Y j x)]
  exact hon x hx i j

omit [FiniteDimensional ℝ E] in
/-- The pushforward of an orthonormal frame is linearly independent.  Stated separately from
`orthonormal_pushforward` so that its statement carries no fibrewise inner product: `pushBasis`
must not depend on the `RiemannianBundle` instance, or its type would. -/
theorem IsMetricPreserving.linearIndependent_pushforward (h : IsMetricPreserving g g' φ)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0) (hx : x ∈ u) :
    LinearIndependent ℝ (fun i => mfderiv I I' φ x (Y i x)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  exact (h.orthonormal_pushforward hon hx).linearIndependent

/-- **The pushforward of an orthonormal frame, as a basis of the target tangent space.**

A linearly independent family of `finrank` many vectors spans, so it is a basis.  The route is
`Basis.mk` on `LinearIndependent.span_eq_top_of_card_eq_finrank'` rather than the packaged
`basisOfLinearIndependentOfCardEqFinrank`, because the latter carries a `[Nonempty ι]` hypothesis
— i.e. `0 < finrank ℝ E` — which would exclude `0`-dimensional manifolds for no reason.  The
primed span lemma needs only `FiniteDimensional`. -/
def IsMetricPreserving.pushBasis (h : IsMetricPreserving g g' φ)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0) (hx : x ∈ u) :
    Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I' (φ x)) :=
  haveI : FiniteDimensional ℝ (TangentSpace I' (φ x)) := inferInstanceAs (FiniteDimensional ℝ E)
  Basis.mk (h.linearIndependent_pushforward hon hx)
    ((h.linearIndependent_pushforward hon hx).span_eq_top_of_card_eq_finrank'
      (by simp only [Fintype.card_fin]; rfl)).ge

@[simp]
theorem IsMetricPreserving.coe_pushBasis (h : IsMetricPreserving g g' φ)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0) (hx : x ∈ u) :
    ⇑(h.pushBasis hon hx) = fun i => mfderiv I I' φ x (Y i x) :=
  Basis.coe_mk _ _

/-! ## Lee's Exercise 2.42 -/

/-- **Lee, Exercise 2.42**: an orientation-preserving isometry pulls the volume form back to the
volume form, `φ^* dV_g̃ = dV_g`.

Orientation-preservation is the hypothesis `hor'`: the frame pushed forward by `dφ_x` is
positively oriented at `φ x`.  It is a genuine hypothesis on `φ`, `o` and `o'`, and it is
dischargeable — for the identity map it reduces to `hor`, since `pushBasis` is then the frame
itself.

The proof is Lee's, and needs only the *pointwise* pullback, not its smoothness: `φ^* dV_g̃` takes
the value `1` on the oriented orthonormal frame `(E_i)`, because `(dφ_x E_i)` is again an oriented
orthonormal basis — orthonormal by `orthonormal_pushforward`, oriented by hypothesis.  An `n`-form
taking the value `1` on one oriented orthonormal frame *is* `dV_g`, by `volumeForm_unique`. -/
theorem IsMetricPreserving.pullbackAlternating_volumeForm (h : IsMetricPreserving g g' φ)
    (hY : IsLocalFrameOn I E ∞ Y u)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0) (hx : x ∈ u)
    (hor : (hY.toBasisAt hx).orientation = o x)
    (hor' : (h.pushBasis hon hx).orientation = o' (φ x)) :
    pullbackAlternating φ (g'.volumeForm o') x = g.volumeForm o x := by
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I' (φ x)) = finrank ℝ E) := ⟨rfl⟩
  refine RiemannianMetric.volumeForm_unique g o hY hon hx hor _ ?_
  rw [pullbackAlternating_apply]
  have hon' : Orthonormal ℝ ⇑(h.pushBasis hon hx) := by
    rw [h.coe_pushBasis hon hx]; exact h.orthonormal_pushforward hon hx
  have hval := volumeFormL_apply_eq_one (o' (φ x)) ((h.pushBasis hon hx).toOrthonormalBasis hon')
    (by rwa [Basis.toBasis_toOrthonormalBasis])
  simpa only [Basis.coe_toOrthonormalBasis, h.coe_pushBasis hon hx] using hval

/-- The orientation hypothesis of `pullbackAlternating_volumeForm` is dischargeable: for the
identity map, which is metric-preserving, the pushed-forward frame is the original frame, so
positive orientation of the pushforward is positive orientation of the frame. -/
theorem IsMetricPreserving.pushBasis_id_orientation (hY : IsLocalFrameOn I E ∞ Y u)
    (hon : ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0) (hx : x ∈ u)
    (hor : (hY.toBasisAt hx).orientation = o x) :
    ((IsMetricPreserving.id g).pushBasis hon hx).orientation = o (_root_.id x) := by
  show ((IsMetricPreserving.id g).pushBasis hon hx).orientation = o x
  rw [← hor]
  congr 1
  refine Basis.eq_of_apply_eq fun i => ?_
  rw [IsMetricPreserving.coe_pushBasis]
  simp only [mfderiv_id]
  exact (IsLocalFrameOn.toBasisAt_coe hY hx i).symm

end

end LeeLib.Ch02
