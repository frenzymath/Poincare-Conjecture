/-
Chapter 2, "Riemannian Metrics", §2 "Riemannian Metrics": the definition itself.

Lee defines a Riemannian metric on a smooth manifold `M` to be a smooth
covariant 2-tensor field `g` whose value `g p` at each `p ∈ M` is an inner
product on `T p M`; equivalently, a symmetric, positive definite, smoothly
varying choice of inner product on each tangent space.

That is exactly mathlib's `Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`,
whose fields are Lee's axioms verbatim (`symm`, `pos`, `contMDiff`), so
`RiemannianMetric` below is a type alias rather than a new structure.  This is
also the abstraction the sibling DoCarmoLib (do Carmo) and PetersenLib (Petersen)
projects converged on independently, so the three books share a substrate
without any project depending on another.

What this file adds is Lee's own reading of the definition:

* Lee states positive definiteness as "`g p v v ≥ 0`, with equality if and only
  if `v = 0`", whereas mathlib's `pos` field states only the `v ≠ 0` direction;
  `inner_self_nonneg` and `inner_self_eq_zero_iff` recover Lee's phrasing.
* Lee's angle-bracket notation `⟨v, w⟩_g` and length `|v|_g = ⟨v, v⟩_g ^ (1/2)`,
  together with the basic properties he uses without comment.
* The Euclidean metric (Lee, Example 2.6).
-/
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LeeLib.Ch02

open Bundle Manifold
open scoped Manifold ContDiff

section Defs

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (I M) in
/-- **Riemannian metric** (Lee, §2.2): a smooth covariant 2-tensor field on `M`
whose value at each point is an inner product on the tangent space there.

This aliases mathlib's `Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`,
whose fields are precisely Lee's axioms: `inner` is the 2-tensor, `symm` its
symmetry, `pos` its positive definiteness, and `contMDiff` the smooth variation
with the base point.  A `RiemannianMetric I M` is *data*, not a typeclass; a
Riemannian manifold in Lee's sense is a pair `(M, g)` with `g : RiemannianMetric I M`. -/
abbrev RiemannianMetric [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

namespace RiemannianMetric

variable (g : RiemannianMetric I M) (p : M)

/-- Lee's angle-bracket notation: `⟨v, w⟩_g = g p (v, w)` for `v w : T p M`. -/
noncomputable def innerAt (v w : TangentSpace I p) : ℝ := g.inner p v w

/-- Lee's length of a tangent vector: `|v|_g = ⟨v, v⟩_g ^ (1/2)`. -/
noncomputable def normAt (v : TangentSpace I p) : ℝ := Real.sqrt (g.innerAt p v v)

@[simp] theorem innerAt_apply (v w : TangentSpace I p) : g.innerAt p v w = g.inner p v w := rfl

/-- Symmetry of the metric (Lee's axiom (i)). -/
theorem innerAt_comm (v w : TangentSpace I p) : g.innerAt p v w = g.innerAt p w v :=
  g.symm p v w

/-- Positive semidefiniteness: Lee states positive definiteness as
`g p v v ≥ 0` with equality iff `v = 0`, while mathlib's `pos` field covers only
`v ≠ 0`.  This is the `≥ 0` half. -/
theorem innerAt_self_nonneg (v : TangentSpace I p) : 0 ≤ g.innerAt p v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [innerAt]
  · exact (g.pos p v hv).le

/-- Definiteness: `⟨v, v⟩_g = 0` exactly when `v = 0`.  Together with
`innerAt_self_nonneg` this is Lee's axiom (iii) in the form he states it. -/
theorem innerAt_self_eq_zero_iff (v : TangentSpace I p) : g.innerAt p v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact absurd h (ne_of_gt (g.pos p v hv))
  · rintro rfl
    simp [innerAt]

/-- Lee's length is nonnegative. -/
theorem normAt_nonneg (v : TangentSpace I p) : 0 ≤ g.normAt p v := Real.sqrt_nonneg _

/-- Lee's length vanishes exactly on the zero vector. -/
theorem normAt_eq_zero_iff (v : TangentSpace I p) : g.normAt p v = 0 ↔ v = 0 := by
  rw [normAt, Real.sqrt_eq_zero (g.innerAt_self_nonneg p v), g.innerAt_self_eq_zero_iff p v]

/-- `|v|_g ^ 2 = ⟨v, v⟩_g`, the defining relation between Lee's length and his
inner product. -/
theorem normAt_sq (v : TangentSpace I p) : g.normAt p v ^ 2 = g.innerAt p v v :=
  Real.sq_sqrt (g.innerAt_self_nonneg p v)

/-- **A Riemannian metric is determined by its inner product.**  The remaining
fields of `Bundle.ContMDiffRiemannianMetric` (`symm`, `pos`, `isVonNBounded`,
`contMDiff`) are all propositions about `inner`, so proof irrelevance makes two
metrics with the same `inner` equal.

This is what lets a uniqueness statement be phrased as an honest `∃!` on
`RiemannianMetric` rather than as an equality of inner products. -/
theorem ext_inner {g₁ g₂ : RiemannianMetric I M} (h : ∀ p : M, g₁.inner p = g₂.inner p) :
    g₁ = g₂ := by
  obtain ⟨inn₁, symm₁, pos₁, bdd₁, cont₁⟩ := g₁
  obtain ⟨inn₂, symm₂, pos₂, bdd₂, cont₂⟩ := g₂
  obtain rfl : inn₁ = inn₂ := funext h
  rfl

end RiemannianMetric

end Defs

section VectorFields

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace RiemannianMetric

variable (g : RiemannianMetric I M) {X Y : ∀ p : M, TangentSpace I p} {s : Set M} {p : M}

/-- **The metric pairing of two smooth vector fields is smooth** (Lee, §2.2):
"a Riemannian metric `g` acts on smooth vector fields `X, Y ∈ 𝔛(M)` to yield a
real-valued function `⟨X, Y⟩` … expressed locally by `⟨X,Y⟩ = g_ij X^i Y^j` and
therefore … smooth".

Lee argues in a local frame; the formal proof instead installs the fibrewise
inner product coming from `g` (mathlib's `RiemannianBundle`) and appeals to
`ContMDiffWithinAt.inner_bundle`, which is the same computation done once and for
all in a trivialization. -/
theorem contMDiffWithinAt_innerAt
    (hX : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) ∞ (fun q => (⟨q, X q⟩ : TangentBundle I M)) s p)
    (hY : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) ∞ (fun q => (⟨q, Y q⟩ : TangentBundle I M)) s p) :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (fun q => g.innerAt q (X q) (Y q)) s p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact ContMDiffWithinAt.inner_bundle (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _)) (b := fun q => q) (v := X) (w := Y) (IM := I) hX hY

/-- `⟨X, Y⟩` is smooth on `M` for smooth vector fields `X, Y` (Lee, §2.2). -/
theorem contMDiff_innerAt
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun q => (⟨q, X q⟩ : TangentBundle I M)))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun q => (⟨q, Y q⟩ : TangentBundle I M))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => g.innerAt q (X q) (Y q)) := fun p =>
  g.contMDiffWithinAt_innerAt (s := Set.univ) (hX p).contMDiffWithinAt (hY p).contMDiffWithinAt
    |>.contMDiffAt (by simp)

/-- **The length of a smooth vector field is continuous** (Lee, §2.2): `|X| =
⟨X, X⟩^{1/2}` is "continuous everywhere", because the square root is continuous
at `0` even though it is not differentiable there. -/
theorem continuous_normAt
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun q => (⟨q, X q⟩ : TangentBundle I M))) :
    Continuous fun q => g.normAt q (X q) :=
  Real.continuous_sqrt.comp (g.contMDiff_innerAt hX hX).continuous

/-- **The length of a smooth vector field is smooth where the field does not
vanish** (Lee, §2.2): `|X|` is "smooth on the open subset where `X ≠ 0`".

This is exactly where Lee's caveat bites: `√·` is smooth away from `0`, and
`⟨X, X⟩ = 0` precisely when `X = 0`, so smoothness of `|X|` holds at `p` as soon
as `X p ≠ 0` and fails in general at the zeros of `X`. -/
theorem contMDiffAt_normAt
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun q => (⟨q, X q⟩ : TangentBundle I M)))
    (hp : X p ≠ 0) : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q => g.normAt q (X q)) p := by
  have hq : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q => g.innerAt q (X q) (X q)) p :=
    g.contMDiff_innerAt hX hX p
  have hne : g.innerAt p (X p) (X p) ≠ 0 := fun h => hp ((g.innerAt_self_eq_zero_iff p _).mp h)
  exact ContDiffAt.comp_contMDiffAt (g := Real.sqrt)
    (f := fun q => g.innerAt q (X q) (X q)) (Real.contDiffAt_sqrt hne) hq

end RiemannianMetric

end VectorFields

section Euclidean

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The Euclidean metric** (Lee, Example 2.6): the Riemannian metric on an
inner product space whose value at each point is the given inner product, under
the canonical identification `T x F ≅ F`.

Lee's starting example is `ℝⁿ` with the dot product; `euclideanMetric` states it
at the natural generality of an inner product space, and
`euclideanMetric_innerAt_euclideanSpace` below specialises it to Lee's `ℝⁿ`. -/
noncomputable def euclideanMetric : RiemannianMetric 𝓘(ℝ, F) F :=
  { riemannianMetricVectorSpace F with
    contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top }

@[simp] theorem euclideanMetric_inner (x : F) :
    (euclideanMetric F).inner x = (innerSL ℝ (E := F) : F →L[ℝ] F →L[ℝ] ℝ) := rfl

/-- The Euclidean metric is the given inner product on each tangent space. -/
theorem euclideanMetric_innerAt (x : F) (v w : TangentSpace 𝓘(ℝ, F) x) :
    (euclideanMetric F).innerAt x v w = inner ℝ (show F from v) (show F from w) := rfl

/-- **Lee's `|v|_ḡ` is the ambient norm.**  The length a tangent vector has for the
Euclidean metric is just its norm in `F`, under `T x F ≅ F`.

This is what makes Lee's comparison `c |v|_ḡ ≤ |v|_g ≤ C |v|_ḡ` (Lemma 2.53) a
statement about the norm of `F`. -/
@[simp] theorem euclideanMetric_normAt (x : F) (v : TangentSpace 𝓘(ℝ, F) x) :
    (euclideanMetric F).normAt x v = ‖(show F from v)‖ := by
  rw [RiemannianMetric.normAt, euclideanMetric_innerAt, ← norm_eq_sqrt_real_inner]

end Euclidean

section EuclideanSpaceCoords

/-- **The Euclidean metric in standard coordinates** (Lee, Example 2.6): on `ℝⁿ`
the Euclidean metric is the dot product,

`⟨v, w⟩ = ∑ i, v i * w i`,

which is Lee's defining formula for the metric he calls `ḡ`. -/
theorem euclideanMetric_innerAt_euclideanSpace {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    (euclideanMetric (EuclideanSpace ℝ (Fin n))).innerAt x v w
      = ∑ i, (show EuclideanSpace ℝ (Fin n) from v) i * (show EuclideanSpace ℝ (Fin n) from w) i := by
  rw [euclideanMetric_innerAt]
  simp [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end EuclideanSpaceCoords

end LeeLib.Ch02
