import PetersenLib.Foundations.RiemannianMetric
import PetersenLib.Ch01.RiemannianManifolds
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Petersen Ch. 1, §1.2 — The Volume Form

The signed volume on an oriented inner product space (`signedVolume`),
its independence of the positively oriented orthonormal basis
(`signedVolume_orthonormal_basis_invariant`), the volume form of an
oriented Riemannian manifold (`volumeForm`), the local volume form
relative to a local orthonormal frame (`localVolumeForm`), the
"height times base" projection identity (`volumeForm_projection`),
and integration on Riemannian manifolds
(`integrateOnRiemannianManifold`).

## Design notes

* **Pointwise layer.** `signedVolume` is defined on a finite-dimensional
  real inner product space `V` with `finrank ℝ V = n`, relative to an
  orientation `o : Orientation ℝ V (Fin n)`, as Mathlib's
  `Orientation.volumeForm`. The blueprint's defining formula
  `vol(v₁, …, vₙ) = det [⟪vᵢ, eⱼ⟫]` for any positively oriented
  orthonormal basis `e` is the unfolding lemma `signedVolume_eq_det`
  (via `Orientation.volumeForm_robust`).

* **Orientation on manifolds.** Mathlib has *no* notion of an oriented
  manifold yet (no orientation bundle, no compatibility/continuity
  condition for a family of fibrewise orientations). The manifold-level
  volume form is therefore parametrized by a *pointwise orientation
  datum* `o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n)`; no
  smoothness or local-constancy of `x ↦ o x` is (or can currently be)
  imposed. Every statement here is pointwise, so this loses no
  mathematical content of Petersen §1.2.

* **Fibre inner products.** `volumeForm` assumes `[HasMetric I M]`: the
  bridge instance `instRiemannianBundleOfHasMetric` then activates
  Mathlib's scoped `Bundle.RiemannianBundle` instances, endowing each
  `TangentSpace I x` with the inner product `g_x` of the metric — which
  is definitionally `(HasMetric.metric).metricInner x`. The local
  (frame-relative) objects `localVolumeForm`, `volumeForm_projection`
  instead take an explicit `g : RiemannianMetric I M` and phrase
  orthonormality through `g.metricInner`, so they apply to any metric
  (and on non-orientable manifolds) without instance plumbing.

* **Integration.** Mathlib has neither integration of top-degree
  differential forms on manifolds nor a canonical Riemannian volume
  measure (the vector-space case `Orientation.measure_eq_volume` exists,
  the manifold case does not). `integrateOnRiemannianManifold` is
  therefore parametrized by a measure `μ` on `M`, standing in for the
  Riemannian measure induced by `vol_g`; see its docstring.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.2.
-/

open Bundle Module MeasureTheory
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## The signed volume on an oriented inner product space -/

section SignedVolume

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)]

/-- **Math.** Petersen §1.2 (signed volume): on an `n`-dimensional
oriented inner product space `(V, g)`, the **signed volume** of vectors
`v₁, …, vₙ` is `det [g(vᵢ, eⱼ)]`, where `e₁, …, eₙ` is any positively
oriented orthonormal basis. Implemented as Mathlib's
`Orientation.volumeForm` relative to the orientation `o`; the defining
determinant formula is `signedVolume_eq_det`, and its independence of
the choice of `e` is `signedVolume_orthonormal_basis_invariant`. -/
def signedVolume (o : Orientation ℝ V (Fin n)) (v : Fin n → V) : ℝ :=
  o.volumeForm v

/-- **Math.** Petersen §1.2: the signed volume is computed by the
defining formula `vol(v₁, …, vₙ) = det [g(vᵢ, eⱼ)]` for any positively
oriented (`e.toBasis.orientation = o`) orthonormal basis `e`. -/
theorem signedVolume_eq_det (o : Orientation ℝ V (Fin n))
    (e : OrthonormalBasis (Fin n) ℝ V) (he : e.toBasis.orientation = o)
    (v : Fin n → V) :
    signedVolume o v = (Matrix.of fun i j => ⟪v i, e j⟫).det := by
  rw [signedVolume, o.volumeForm_robust e he, Basis.det_apply, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply, Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  exact real_inner_comm _ _

/-- **Math.** Petersen §1.2 (independence of orthonormal basis): the
value `det [g(vᵢ, eⱼ)]` is the same for every positively oriented
orthonormal basis of `(V, g)` — here for any two positively oriented
orthonormal bases `e`, `f`. Petersen's proof factors through the
change-of-basis matrix, orthogonal with determinant `1`; in Mathlib this
is `Orientation.volumeForm_robust`, which both determinants equal. -/
theorem signedVolume_orthonormal_basis_invariant (o : Orientation ℝ V (Fin n))
    (e f : OrthonormalBasis (Fin n) ℝ V)
    (he : e.toBasis.orientation = o) (hf : f.toBasis.orientation = o)
    (v : Fin n → V) :
    (Matrix.of fun i j => ⟪v i, e j⟫).det = (Matrix.of fun i j => ⟪v i, f j⟫).det :=
  (signedVolume_eq_det o e he v).symm.trans (signedVolume_eq_det o f hf v)

end SignedVolume

/-! ## The volume form of an oriented Riemannian manifold -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen §1.2 (volume form on an oriented manifold): on an
oriented Riemannian `n`-manifold `(M, g)` the **volume form** is the
`n`-form `vol_g(v₁, …, vₙ) = det [g(vᵢ, eⱼ)]` on `T_xM`, where
`e₁, …, eₙ` is any positively oriented orthonormal basis of `T_xM`
(well defined by `signedVolume_orthonormal_basis_invariant`; the
determinant formula is `volumeForm_eq_det`). The notation `d vol` is
also common, although `vol` need not be exact.

Mathlib has no manifold orientations yet, so the orientation is a
pointwise datum `o : ∀ x, Orientation ℝ (TangentSpace I x) (Fin n)`
with no smoothness/compatibility imposed (see the module docstring);
the metric is the `[HasMetric I M]` instance metric, which induces the
inner product on each `TangentSpace I x`. -/
def volumeForm [HasMetric I M] {n : ℕ} (hn : finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n)) (x : M) :
    (TangentSpace I x) [⋀^Fin n]→ₗ[ℝ] ℝ :=
  haveI : Fact (finrank ℝ (TangentSpace I x) = n) := ⟨hn⟩
  (o x).volumeForm

omit [FiniteDimensional ℝ E] in
/-- **Math.** The volume form of `(M, g)` at `x` is the pointwise signed
volume of `(T_xM, g_x)` relative to the orientation `o x`. Definitional. -/
theorem volumeForm_apply_eq_signedVolume [HasMetric I M] {n : ℕ}
    (hn : finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n)) (x : M)
    (v : Fin n → TangentSpace I x) :
    volumeForm hn o x v = @signedVolume (TangentSpace I x) _ _ n ⟨hn⟩ (o x) v :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Math.** Petersen §1.2: the volume form is computed by
`vol_g(v₁, …, vₙ) = det [g(vᵢ, eⱼ)]` for any positively oriented
orthonormal basis `e` of `(T_xM, g_x)`. -/
theorem volumeForm_eq_det [hm : HasMetric I M] {n : ℕ} (hn : finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n)) (x : M)
    (e : OrthonormalBasis (Fin n) ℝ (TangentSpace I x))
    (he : e.toBasis.orientation = o x) (v : Fin n → TangentSpace I x) :
    volumeForm hn o x v =
      (Matrix.of fun i j => hm.metric.metricInner x (v i) (e j)).det := by
  haveI : Fact (finrank ℝ (TangentSpace I x) = n) := ⟨hn⟩
  exact signedVolume_eq_det (o x) e he v

/-! ## The local volume form relative to an orthonormal frame -/

/-- **Math.** Petersen §1.2 (local volume form): even when `M` is not
orientable, the volume form exists locally. Given vector fields
`E₁, …, Eₙ` (a family `frame : Fin n → Π x, T_xM` of sections, intended
as a local orthonormal frame on a domain `U ⊆ M`, declared positive),
set `vol(X₁, …, Xₙ) = det [g(Xᵢ, Eⱼ)]` at each point.

The definition is the raw determinant; the frame's domain `U` and its
pointwise orthonormality are hypotheses of the lemmas about it
(`volumeForm_projection`, `localVolumeForm_eq_volumeForm`), not data of
the definition. -/
def localVolumeForm (g : RiemannianMetric I M) {n : ℕ}
    (frame : Fin n → ∀ x : M, TangentSpace I x) (x : M)
    (X : Fin n → TangentSpace I x) : ℝ :=
  (Matrix.of fun i j => g.metricInner x (X i) (frame j x)).det

omit [FiniteDimensional ℝ E] in
/-- **Math.** Consistency of Petersen §1.2's two constructions: at a
point `x` where the local frame is a positively oriented orthonormal
basis of `(T_xM, g_x)`, the local volume form agrees with the volume
form of the oriented manifold. -/
theorem localVolumeForm_eq_volumeForm [hm : HasMetric I M] {n : ℕ}
    (hn : finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n))
    (frame : Fin n → ∀ x : M, TangentSpace I x) (x : M)
    (e : OrthonormalBasis (Fin n) ℝ (TangentSpace I x))
    (hef : ∀ j, frame j x = e j) (he : e.toBasis.orientation = o x)
    (X : Fin n → TangentSpace I x) :
    localVolumeForm hm.metric frame x X = volumeForm hn o x X := by
  rw [volumeForm_eq_det hn o x e he X, localVolumeForm]
  congr 1
  ext i j
  simp only [Matrix.of_apply, hef]

omit [FiniteDimensional ℝ E] in
/-- **Math.** Petersen §1.2 ("height times base"): replacing the `i`-th
vector of an orthonormal frame `E₁, …, Eₙ` by a general vector `X` gives
`vol(E₁, …, X, …, Eₙ) = g(X, Eᵢ)`, the projection of `X` onto `Eᵢ` —
the "height in the `i`-th coordinate direction" times the unit base.
Orthonormality at `x` is phrased through `g`:
`g(Eⱼ, Eₖ) = δⱼₖ` (equivalently, `Orthonormal ℝ (fun j => frame j x)`
for the `g`-induced inner product). -/
theorem volumeForm_projection (g : RiemannianMetric I M) {n : ℕ}
    (frame : Fin n → ∀ x : M, TangentSpace I x) (x : M)
    (hframe : ∀ j k, g.metricInner x (frame j x) (frame k x) =
      if j = k then 1 else 0)
    (i : Fin n) (X : TangentSpace I x) :
    localVolumeForm g frame x (Function.update (fun j => frame j x) i X) =
      g.metricInner x X (frame i x) := by
  set c : Fin n → ℝ := fun j => g.metricInner x X (frame j x) with hc
  have hmat : (Matrix.of fun l j =>
      g.metricInner x (Function.update (fun k => frame k x) i X l) (frame j x)) =
      (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i c := by
    ext l j
    rcases eq_or_ne l i with rfl | hl
    · simp [Matrix.updateRow_self, Function.update_self, hc]
    · simp only [Matrix.of_apply, Matrix.updateRow_ne hl, Function.update_of_ne hl]
      rw [Matrix.one_apply]
      exact hframe l j
  have hrow : c = ∑ k, c k • (1 : Matrix (Fin n) (Fin n) ℝ) k := by
    funext j
    simp [Matrix.one_apply, Finset.sum_apply, mul_ite, Finset.sum_ite_eq']
  rw [localVolumeForm, hmat, hrow, Matrix.det_updateRow_sum, Matrix.det_one,
    smul_eq_mul, mul_one]

/-! ## Integration on Riemannian manifolds -/

set_option linter.unusedVariables false in
/-- **Math.** Petersen §1.2 (integration on Riemannian manifolds): on an
oriented Riemannian manifold one integrates a function `f` by
integrating the `n`-form `f · vol_g`; and since every manifold contains
an open dense set `O` with trivial (hence orientable) tangent bundle
carrying an orthonormal frame, integration over `O` extends this to any
Riemannian manifold, orientable or not.

**Implementation.** Mathlib currently has *no* integration of
top-degree forms on manifolds and *no* Riemannian volume measure (the
vector-space analogue is `Orientation.measure_eq_volume`; there is no
manifold version). This definition is therefore parametrized by a
measure `μ` on `M`, standing in for the measure induced by `vol_g`
(a genuine datum determined by `g` once that infrastructure exists),
and integrates `f` against it as a Bochner integral. The metric `g` is
kept in the signature as the datum that mathematically determines the
intended `μ`. -/
-- TODO(PET.1): replace the measure parameter by the canonical Riemannian
-- volume measure of `g` (equivalently, integration of `f · vol_g` as a
-- top-degree form) once mathlib has integration of forms on manifolds
-- or a Riemannian measure.
def integrateOnRiemannianManifold [MeasurableSpace M]
    (g : RiemannianMetric I M) (μ : Measure M) (f : M → ℝ) : ℝ :=
  ∫ x, f x ∂μ

end Manifold

end PetersenLib
