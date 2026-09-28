/-
Chapter 2, "Riemannian Metrics", §"The Riemannian Distance Function": Lee's
Lemma 2.53.

Lee states it as follows.  Let `g` be a Riemannian metric on an open subset
`W ⊆ ℝⁿ` and let `ḡ` be the Euclidean metric on `W`.  For every compact `K ⊆ W`
there are positive constants `c, C` with

  `c |v|_ḡ ≤ |v|_g ≤ C |v|_ḡ`   for all `x ∈ K` and all `v ∈ T_x ℝⁿ`.

This is the one place in the chapter where compactness converts the *pointwise*
positive definiteness of a metric into a bound that is **uniform over `K`**, and
that uniformity is the whole content: at a single point the comparison is just
the (finite-dimensional) equivalence of two norms, but the constants must not
degenerate as `x` ranges over `K`.

The proof is Lee's: on the compact set `K × S` (`S` the Euclidean unit sphere)
the continuous function `(x, v) ↦ ⟨v, v⟩_g` is strictly positive, hence bounded
away from `0` and bounded above; homogeneity then transfers the bound from `S`
to every tangent vector.

**Structure of this file.**  The mathematical core is stated *without any
manifold*, for a bare family `q : F → F →L[ℝ] F →L[ℝ] ℝ` of bilinear forms
(`exists_forall_sqrt_comparison`).  There are two reasons for factoring it this
way rather than proving Lee's statement directly:

* The core is what Lee's Lemma 2.54 actually consumes.  There, `q` arises as the
  coordinate representation of a metric pushed forward through a *chart*, whose
  domain is a proper open subset of `ℝⁿ`; a lemma phrased in terms of a
  `RiemannianMetric` on all of `ℝⁿ` could not be applied to it, since a
  chart-pushforward metric does not extend to `ℝⁿ`.  Keeping the hypotheses to
  "continuous on `K × S`" and "positive definite on `K`" makes the lemma
  applicable to *any* domain, open or not.
* It isolates the analysis from the bundle-theoretic work of producing the
  continuity hypothesis, which is where all the friction lives (see
  `RiemannianMetric.continuous_innerAt_prod`).

`RiemannianMetric.exists_forall_normAt_le_euclidean` is then Lee's statement for a
metric on the model space `ℝⁿ`, and
`RiemannianMetric.exists_forall_normAt_le_euclidean_opens` is Lee's statement as he
makes it, for a metric on an open `W ⊆ ℝⁿ` regarded as a manifold in its own right.
The step between the two is not a formality: it needs the identification of `T(↥W)`
with `↥W × F`, for which mathlib has no analogue of
`tangentBundleModelSpaceHomeomorph`.  It is supplied here by
`continuous_opens_tangentBundle_mk`; see the `OpenSubsets` section for why it is
cheap (all charts of `↥W` are literally the same chart).
-/
import LeeLib.Ch02.OpenSubmanifold

namespace LeeLib.Ch02

open Bundle Manifold Metric Set
open scoped ContDiff Topology

noncomputable section

section Core

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bilinear form is `2`-homogeneous along the diagonal: `q (r • v) (r • v) =
r² q v v`.  This is what lets a bound on the unit sphere be transported to every
vector, and is the only algebraic input to Lemma 2.53. -/
theorem apply_smul_smul_self (q : F →L[ℝ] F →L[ℝ] ℝ) (r : ℝ) (v : F) :
    q (r • v) (r • v) = r ^ 2 * q v v := by
  rw [map_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

variable [FiniteDimensional ℝ F]

/-- **The analytic core of Lee's Lemma 2.53**, with no manifold in sight.

Given a family `q x` of bilinear forms on a finite-dimensional space `F`, indexed
by a point `x` of an arbitrary topological space `B`, jointly continuous in
`(x, v)` for `x` in a compact `K ⊆ B` and `v` on the unit sphere, and positive
definite at each `x ∈ K`, the "norms" `√(q x v v)` are comparable to the ambient
norm `‖v‖` *uniformly in `x ∈ K`*.

The hypotheses are deliberately confined to `K` and to the unit sphere, so that
the lemma applies to a form family defined only on some open set containing `K`
— which is the situation of Lee's Lemma 2.54, where `q` is a metric read in a
chart and is undefined outside the chart's image.

The index space `B` is arbitrary rather than `F` itself because Lee's `W ⊆ ℝⁿ` is
consumed both as a subset of `ℝⁿ` (Lemma 2.54, where `q` is a chart representation
indexed by points of `ℝⁿ`) and as a manifold in its own right
(`exists_forall_normAt_le_euclidean_opens`, where the index is `↥W`).  Nothing in
the proof uses a linear structure on the index.

Note that no nondegeneracy is needed away from `K`, and that `K = ∅` and `F = 0`
are permitted: the constants are then produced vacuously. -/
theorem exists_forall_sqrt_comparison {B : Type*} [TopologicalSpace B]
    {q : B → F →L[ℝ] F →L[ℝ] ℝ} {K : Set B} (hK : IsCompact K)
    (hcont : ContinuousOn (fun p : B × F => q p.1 p.2 p.2) (K ×ˢ sphere (0 : F) 1))
    (hpos : ∀ x ∈ K, ∀ v : F, v ≠ 0 → 0 < q x v v) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : F,
      c * ‖v‖ ≤ Real.sqrt (q x v v) ∧ Real.sqrt (q x v v) ≤ C * ‖v‖ := by
  have hS : IsCompact (K ×ˢ sphere (0 : F) 1) := hK.prod (isCompact_sphere 0 1)
  -- On the sphere, vectors are nonzero.
  have hne : ∀ p : B × F, p ∈ K ×ˢ sphere (0 : F) 1 → p.2 ≠ 0 := by
    rintro ⟨x, v⟩ ⟨-, hv⟩
    simp only [mem_sphere_iff_norm, sub_zero] at hv
    exact norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  -- Lower bound: `q` is strictly positive on the compact `K × S`, hence bounded below by
  -- some `c₀ > 0`.  `exists_forall_le'` also covers the degenerate case `K × S = ∅`.
  obtain ⟨c₀, hc₀pos, hc₀⟩ :=
    hS.exists_forall_le' (a := 0) hcont fun p hp => hpos p.1 hp.1 p.2 (hne p hp)
  -- Upper bound: a continuous function on a compact set is bounded.
  obtain ⟨C₀, hC₀⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨Real.sqrt c₀, Real.sqrt (max C₀ 1), Real.sqrt_pos.mpr hc₀pos,
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _)), fun x hx v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  -- Rescale `v` to the unit sphere and use homogeneity.
  set u : F := ‖v‖⁻¹ • v with hu
  have hvne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have huS : u ∈ sphere (0 : F) 1 := by
    simp only [mem_sphere_iff_norm, sub_zero, hu, norm_smul, norm_inv, norm_norm]
    field_simp
  have hvu : v = ‖v‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hvne, one_smul]
  have hqv : q x v v = ‖v‖ ^ 2 * q x u u := by
    conv_lhs => rw [hvu]
    exact apply_smul_smul_self (q x) _ _
  have hmem : ((x, u) : B × F) ∈ K ×ˢ sphere (0 : F) 1 := ⟨hx, huS⟩
  have hsplit : Real.sqrt (q x v v) = ‖v‖ * Real.sqrt (q x u u) := by
    rw [hqv, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  constructor
  · rw [hsplit, mul_comm (Real.sqrt c₀) ‖v‖]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hc₀ _ hmem)) (norm_nonneg _)
  · rw [hsplit, mul_comm (Real.sqrt (max C₀ 1)) ‖v‖]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (norm_nonneg _)
    exact le_trans (le_trans (le_abs_self _) (hC₀ _ hmem)) (le_max_left _ _)

end Core

section Bridge

namespace RiemannianMetric

section AnyManifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The energy function `z ↦ ⟨z, z⟩_g` is smooth on the total space of the
tangent bundle**, for an arbitrary Riemannian manifold.

This is the two-variable ("jointly in the base point and the vector") form of
smoothness of the metric, and it is the hypothesis that Lemma 2.53 needs.  It is
worth recording how cheaply it comes out, because the obvious routes both fail:

* One cannot strip `g.inner` down to an ordinary map `M → (E →L[ℝ] E →L[ℝ] ℝ)`
  into the operator-norm space and apply `ContinuousOn.clm_apply`: `g.contMDiff`
  asserts smoothness of `inner` as a *section of a hom-bundle*, and the pinned
  mathlib has no lemma converting that into continuity of a CLM-valued map.
* Pairing two vector *fields* (`contMDiff_innerAt`) gives only the one-variable
  statement, with the vector determined by the base point.

The observation that makes it trivial is that `ContMDiff.inner_bundle` pairs
sections along an **arbitrary base map** `b : M' → M`, not just along the
identity.  Taking the source manifold `M'` to be the total space
`TangentBundle I M` itself, `b := TotalSpace.proj` and both sections
`:= TotalSpace.snd`, the section-smoothness hypothesis it demands becomes
smoothness of `z ↦ ⟨z.proj, z.snd⟩` — which is literally the identity map of the
total space.  So `contMDiff_id` discharges it. -/
theorem contMDiff_innerAt_totalSpace (g : RiemannianMetric I M) :
    ContMDiff I.tangent 𝓘(ℝ, ℝ) ∞
      (fun z : TangentBundle I M => g.innerAt z.proj z.2 z.2) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hid : ContMDiff I.tangent (I.prod 𝓘(ℝ, E)) ∞
      (fun z : TangentBundle I M => (z : TotalSpace E (TangentSpace I : M → Type _))) :=
    contMDiff_id
  -- Elaborate the pairing with no expected type: fixing the goal first forces typeclass
  -- synthesis to pick the fibre norm coming from `letI` before it can be unified with `g`'s.
  have hpair := ContMDiff.inner_bundle (IM := I.tangent) (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _)) (n := ∞) (M := TangentBundle I M)
    (b := TotalSpace.proj) (v := fun z : TangentBundle I M => z.2)
    (w := fun z : TangentBundle I M => z.2) hid hid
  exact hpair

end AnyManifold

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The metric is jointly continuous in the base point and the vector**, for a
metric on the model space.

This is `contMDiff_innerAt_totalSpace` read through mathlib's canonical
identification `tangentBundleModelSpaceHomeomorph` of the tangent bundle of a
model space with a product — the one case in which the total space *is* a
product, so that "jointly continuous" can be said in the naive way.  It is the
form Lemma 2.53 consumes. -/
theorem continuous_innerAt_prod (g : RiemannianMetric 𝓘(ℝ, F) F) :
    Continuous fun p : F × F => g.innerAt p.1 p.2 p.2 :=
  g.contMDiff_innerAt_totalSpace.continuous.comp
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).symm.continuous

/-- **Lee's Lemma 2.53**, for a Riemannian metric on `ℝⁿ`: on a compact set the
metric is comparable to the Euclidean metric, with constants uniform over the set.

`normAt_le_of_isCompact` below restates this in Lee's own notation
`c |v|_ḡ ≤ |v|_g ≤ C |v|_ḡ`. -/
theorem exists_forall_norm_comparison_of_isCompact [FiniteDimensional ℝ F]
    (g : RiemannianMetric 𝓘(ℝ, F) F) {K : Set F} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : TangentSpace 𝓘(ℝ, F) x,
      c * ‖(show F from v)‖ ≤ g.normAt x v ∧ g.normAt x v ≤ C * ‖(show F from v)‖ :=
  exists_forall_sqrt_comparison (q := fun x => g.inner x) hK
    (g.continuous_innerAt_prod.continuousOn)
    fun x _ v hv => g.pos x v hv

end RiemannianMetric

end Bridge

section LeeStatement

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Lee's Lemma 2.53**, verbatim in his notation.

Let `g` be a Riemannian metric on `ℝⁿ` and let `ḡ` be the Euclidean metric.  For
every compact `K` there are constants `c, C > 0` with

  `c |v|_ḡ ≤ |v|_g ≤ C |v|_ḡ`

for all `x ∈ K` and all `v ∈ T_x ℝⁿ` — Lee's inequality (2.21).

The constants are uniform in `x`, which is the entire point; for each *fixed* `x`
the inequality is just the equivalence of two norms on a finite-dimensional
space.

Lee states this for a metric on an open `W ⊆ ℝⁿ` rather than on all of `ℝⁿ`,
because he applies it to a metric read in a chart.  That extra generality lives
in `exists_forall_sqrt_comparison`, whose hypotheses are imposed only on `K` and
so accommodate a form family defined on any domain containing `K`; it is the form
in which Lemma 2.54 consumes this result. -/
theorem RiemannianMetric.exists_forall_normAt_le_euclidean
    (g : RiemannianMetric 𝓘(ℝ, F) F) {K : Set F} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : TangentSpace 𝓘(ℝ, F) x,
      c * (euclideanMetric F).normAt x v ≤ g.normAt x v ∧
        g.normAt x v ≤ C * (euclideanMetric F).normAt x v := by
  obtain ⟨c, C, hc, hC, h⟩ := g.exists_forall_norm_comparison_of_isCompact hK
  refine ⟨c, C, hc, hC, fun x hx v => ?_⟩
  rw [euclideanMetric_normAt]
  exact h x hx v

end LeeStatement

section OpenSubsets

/-!
### Lee's open subset `W ⊆ ℝⁿ`

Lee states Lemma 2.53 for a metric on an open `W ⊆ ℝⁿ` (or `ℝⁿ₊`) rather than on
all of `ℝⁿ`, because he applies it to a metric read in a chart.  Part of that
generality is already available: `exists_forall_sqrt_comparison` imposes its
hypotheses only on `K`, so it accepts a form family defined on any domain
containing `K`, and that is the shape in which Lemma 2.54 uses it.

This section supplies the rest: the statement for a `RiemannianMetric 𝓘(ℝ, F) ↥W`
with `W : Opens F` — a metric on an open subset regarded as a manifold in its own
right, which is literally Lee's hypothesis.  The obstruction is one of transport.
`contMDiff_innerAt_totalSpace` already applies to `↥W`, so the metric is jointly
smooth on `T(↥W)`; what is missing is the identification of `T(↥W)` with the
product `↥W × F`, which turns "jointly smooth on the total space" into the
two-variable continuity the comparison consumes.  For the model space that
identification is `tangentBundleModelSpaceHomeomorph`; for an open subset mathlib
provides no analogue.

**Why it is cheap.**  Every chart of `↥W` is *the same* chart — the inclusion.
`Opens.chartAt_eq` gives `chartAt F x = (chartAt F ↑x).subtypeRestr ⟨x⟩`, whose
only dependence on `x` is through the `Nonempty ↥W` instance `⟨x⟩`; `Nonempty` is
a `Prop`, so definitional proof irrelevance makes `chartAt F x` and `achart F x`
independent of `x` *by `rfl`*.  Hence the tangent bundle's coordinate changes are
all `coordChange i i`, i.e. the identity (`tangentCoordChange_self`), and the
canonical trivialization at any point is the identity map on the nose
(`opens_trivializationAt_apply`).  It has `baseSet = univ`, so it is a single
global chart and no gluing is required. -/

variable {F : Type*} [NormedAddCommGroup F]

open TopologicalSpace

/-- **Charts on an open subset of a normed space are global.**  An open set `W ⊆ F`
is a manifold whose chart at any point is the inclusion `W ↪ F`, defined on all of
`W`; there is no chart domain to keep track of. -/
theorem opens_chartAt_source_eq_univ (W : Opens F) (x : W) :
    (chartAt F x).source = Set.univ := by
  rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
  simp

variable [NormedSpace ℝ F]

/-- **The tangent bundle of an open subset of a normed space is globally trivial**:
the canonical trivialization at any point has all of `W` as its base set. -/
theorem opens_trivializationAt_baseSet_eq_univ (W : Opens F) (x : W) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F) : W → Type _) x).baseSet = Set.univ := by
  simp [trivializationAt, opens_chartAt_source_eq_univ]

/-- **The canonical trivialization of `T(↥W)` is the identity.**

`trivializationAt` sends `⟨z.proj, z.snd⟩` to `z.snd` transported by the
coordinate change from the chart at `z.proj` to the chart at `x`.  On an open
subset of a model space those two charts are the *same* chart (see the section
comment: the only dependence on the point is a `Nonempty` instance, and `Nonempty`
is a `Prop`), so the coordinate change is `coordChange i i = id`. -/
theorem opens_trivializationAt_apply (W : Opens F) (x : W)
    (z : TangentBundle 𝓘(ℝ, F) (W : Type _)) :
    trivializationAt F (TangentSpace 𝓘(ℝ, F)) x z = (z.1, z.2) := by
  rw [TangentBundle.trivializationAt_apply]
  exact Prod.ext rfl (tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ, F)) z.proj))

theorem opens_trivializationAt_source (W : Opens F) (x : W) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F) : W → Type _) x).source = Set.univ := by
  rw [Trivialization.source_eq, opens_trivializationAt_baseSet_eq_univ]
  simp

theorem opens_trivializationAt_target (W : Opens F) (x : W) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F) : W → Type _) x).target = Set.univ := by
  rw [Trivialization.target_eq, opens_trivializationAt_baseSet_eq_univ]
  simp

/-- **`T(↥W)` is the product `↥W × F`**, in the only form the comparison needs:
the tautological map `(x, v) ↦ ⟨x, v⟩` into the total space is continuous.

This is the analogue, for an open subset of a model space, of mathlib's
`tangentBundleModelSpaceHomeomorph`.  It is proved by exhibiting the map as the
inverse of the canonical trivialization, which by `opens_trivializationAt_apply`
*is* this map and by `opens_trivializationAt_target` is defined on all of
`↥W × F`.  Choosing the trivialization at the point under consideration avoids
having to assume `Nonempty ↥W`. -/
theorem continuous_opens_tangentBundle_mk (W : Opens F) :
    Continuous (fun q : ↥W × F => (⟨q.1, q.2⟩ : TangentBundle 𝓘(ℝ, F) (W : Type _))) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  set e := trivializationAt F (TangentSpace 𝓘(ℝ, F)) q₀.1 with he
  have hsymm : (fun q : ↥W × F => (⟨q.1, q.2⟩ : TangentBundle 𝓘(ℝ, F) (W : Type _)))
      = e.toOpenPartialHomeomorph.symm := by
    funext q
    have hmem : (⟨q.1, q.2⟩ : TangentBundle 𝓘(ℝ, F) (W : Type _)) ∈ e.source := by
      rw [he, opens_trivializationAt_source]; trivial
    have hinv := e.toOpenPartialHomeomorph.left_inv hmem
    rw [← hinv]
    congr 1
    exact opens_trivializationAt_apply W q₀.1 ⟨q.1, q.2⟩
  rw [hsymm]
  have hc : Continuous e.toOpenPartialHomeomorph.symm := by
    rw [← continuousOn_univ, ← opens_trivializationAt_target W q₀.1]
    exact e.toOpenPartialHomeomorph.continuousOn_symm
  exact hc.continuousAt

namespace RiemannianMetric

/-- **The metric on an open subset is jointly continuous in the base point and the
vector.**  This is `continuous_innerAt_prod` for `↥W` in place of the model space,
read through `continuous_opens_tangentBundle_mk` instead of
`tangentBundleModelSpaceHomeomorph`. -/
theorem continuous_innerAt_prod_opens (W : Opens F) (g : RiemannianMetric 𝓘(ℝ, F) (W : Type _)) :
    Continuous fun p : ↥W × F => g.innerAt p.1 p.2 p.2 :=
  g.contMDiff_innerAt_totalSpace.continuous.comp (continuous_opens_tangentBundle_mk W)

/-- **Lee's Lemma 2.53**, for a metric on an open subset `W ⊆ ℝⁿ` regarded as a
manifold in its own right — Lee's own hypothesis.  On a compact `K ⊆ W` the metric
is comparable to the ambient norm, with constants uniform over `K`.

`exists_forall_normAt_le_euclidean_opens` restates this in Lee's notation
`c |v|_ḡ ≤ |v|_g ≤ C |v|_ḡ`. -/
theorem exists_forall_norm_comparison_of_isCompact_opens [FiniteDimensional ℝ F] (W : Opens F)
    (g : RiemannianMetric 𝓘(ℝ, F) (W : Type _)) {K : Set W} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : TangentSpace 𝓘(ℝ, F) x,
      c * ‖(show F from v)‖ ≤ g.normAt x v ∧ g.normAt x v ≤ C * ‖(show F from v)‖ :=
  exists_forall_sqrt_comparison (q := fun x => g.inner x) hK
    (g.continuous_innerAt_prod_opens W).continuousOn
    fun x _ v hv => g.pos x v hv

end RiemannianMetric

end OpenSubsets

section LeeStatementOpen

/-!
### Lee's Lemma 2.53, verbatim

Lee's hypothesis is a metric on an open `W ⊆ ℝⁿ`; this section states the
comparison for that hypothesis, in his notation, with `ḡ` the Euclidean metric of
`W` as an open submanifold of `ℝⁿ`. -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

open TopologicalSpace

namespace RiemannianMetric

/-- **The Euclidean metric on an open subset measures the ambient norm**: `ḡ` is
the ambient inner product read at points of `W`, so `|v|_ḡ = ‖v‖`. -/
@[simp] theorem openSubmanifoldMetric_euclidean_normAt (W : Opens F)
    (x : W) (v : TangentSpace 𝓘(ℝ, F) x) :
    (openSubmanifoldMetric (euclideanMetric F) W).normAt x v = ‖(show F from v)‖ := by
  rw [RiemannianMetric.normAt, openSubmanifoldMetric_innerAt, ← RiemannianMetric.normAt,
    euclideanMetric_normAt]

/-- **Lee's Lemma 2.53** in Lee's own notation: for a Riemannian metric `g` on an
open subset `W ⊆ ℝⁿ` and `ḡ` the Euclidean metric on `W`, every compact `K ⊆ W`
admits positive constants `c, C` with `c |v|_ḡ ≤ |v|_g ≤ C |v|_ḡ` for all `x ∈ K`
and all `v ∈ T_x W` — Lee's inequality (2.21).

This is the statement Lee makes; `exists_forall_normAt_le_euclidean` is the
special case `W = ℝⁿ`. -/
theorem exists_forall_normAt_le_euclidean_opens (W : Opens F)
    (g : RiemannianMetric 𝓘(ℝ, F) (W : Type _)) {K : Set W} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : TangentSpace 𝓘(ℝ, F) x,
      c * (openSubmanifoldMetric (euclideanMetric F) W).normAt x v ≤ g.normAt x v ∧
        g.normAt x v ≤ C * (openSubmanifoldMetric (euclideanMetric F) W).normAt x v := by
  obtain ⟨c, C, hc, hC, h⟩ := g.exists_forall_norm_comparison_of_isCompact_opens W hK
  refine ⟨c, C, hc, hC, fun x hx v => ?_⟩
  rw [openSubmanifoldMetric_euclidean_normAt]
  exact h x hx v

end RiemannianMetric

end LeeStatementOpen

end

end LeeLib.Ch02
