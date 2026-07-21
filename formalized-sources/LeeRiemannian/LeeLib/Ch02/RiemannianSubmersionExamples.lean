/-
Chapter 2, "Riemannian Metrics", §"Riemannian Submersions", **Example 2.27**.

Lee lists three families of Riemannian submersions:

* **(a)** the projection `ℝ^{n+k} → ℝ^n` onto the first `n` coordinates, with the
  Euclidean metrics on both spaces;
* **(b)** for Riemannian manifolds `(M, g)` and `(N, h)`, both projections
  `π_M : M × N → M` and `π_N : M × N → N` of the product metric `g ⊕ h`;
* **(c)** the projection `π_M : M ×_f N → M` of a warped product (while `π_N` is
  typically *not* a Riemannian submersion).

All three are the same computation, carried out here for the two product
projections and the warped product.  The block form of the metric — read off
`ProductMetric.prodForm_apply` / `warpedProductForm_apply` — is what makes it
work:

* The differential of `Prod.fst` is `ContinuousLinearMap.fst` (`mfderiv_fst`), so
  `IsSubmersion` is immediate and the vertical space `V_{(x,y)} = ker dπ` is the
  `N`-factor `{v | v.1 = 0}`.
* The horizontal space is then the `M`-factor `{v | v.2 = 0}`: a vector `v` is
  `g ⊕ h`-orthogonal to *every* vertical `(0, w₂)` exactly when its own second
  block has zero `h`-length, i.e. when `v.2 = 0`.  (For the warped product the
  second block carries the strictly positive factor `f(x)²`, which changes
  nothing.)  This is `mem_horizontalSpace_prodMetric_fst_iff` and its siblings.
* On such horizontal vectors the cross term of the block form vanishes, so
  `dπ_x` is a linear isometry `H_x → T_x M`, which is exactly Lee's isometry
  condition.

Part (a) is then part (b) applied to the Euclidean metrics of `ℝ^n` and `ℝ^k`,
with `ℝ^{n+k}` modelled as `ℝ^n × ℝ^k` (mathlib gives the plain product a sup
norm, not an inner product, so the honest Euclidean statement is the product of
the two Euclidean metrics — which *is* `g ⊕ h` with the dot products as blocks).

Only pointwise facts are used; nothing here needs the smoothness machinery of
`RiemannianSubmersion.lean` or the group action of `SubmersionMetric.lean`.

Two `TangentSpace`-diamond hazards recur below and dictate the proof style:

* `TangentSpace (I.prod J) x` is *definitionally* `E × E'`, but `mfderiv`'s value
  is only *propositionally* `ContinuousLinearMap.fst` (via `mfderiv_fst`), and the
  term produced by unfolding `IsRiemannianSubmersion` differs from
  `mfderiv_contMDiffMap_fst`'s left-hand side in a hidden implicit.  A `show`
  restates the goal with the latter's exact term (they are defeq) so that `rw`
  can fire.
* The zero of `E` and the (derived) zero of `TangentSpace I x` are defeq but not
  syntactically equal, so `simp`/`rw [map_zero]` will not fire on
  `g.inner x v 0`.  Each such term is instead discharged by a `map_zero _` used
  as a *term* (defeq-checked), never as a rewrite.
-/
import LeeLib.Ch02.ProductMetric
import LeeLib.Ch02.SubmersionMetric

namespace LeeLib.Ch02

open Manifold
open scoped Manifold ContDiff Topology

section ProductProjection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-! ### The two projections as smooth submersions -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ N] in
/-- The differential of the first projection is the first-coordinate projection of
tangent vectors: `dπ_M (x,y) v = v.1` (mathlib's `mfderiv_fst`). -/
theorem mfderiv_contMDiffMap_fst (x : M × N) (v : TangentSpace (I.prod J) x) :
    mfderiv (I.prod J) I (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x v = v.1 := by
  have h : (mfderiv (I.prod J) I (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x)
      = ContinuousLinearMap.fst ℝ (TangentSpace I x.1) (TangentSpace J x.2) := mfderiv_fst
  rw [h]; rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ N] in
/-- The differential of the second projection is the second-coordinate projection
of tangent vectors: `dπ_N (x,y) v = v.2` (mathlib's `mfderiv_snd`). -/
theorem mfderiv_contMDiffMap_snd (x : M × N) (v : TangentSpace (I.prod J) x) :
    mfderiv (I.prod J) J (ContMDiffMap.snd : C^∞⟮I.prod J, M × N; J, N⟯) x v = v.2 := by
  have h : (mfderiv (I.prod J) J (ContMDiffMap.snd : C^∞⟮I.prod J, M × N; J, N⟯) x)
      = ContinuousLinearMap.snd ℝ (TangentSpace I x.1) (TangentSpace J x.2) := mfderiv_snd
  rw [h]; rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ N] in
/-- The first projection `M × N → M` is a smooth submersion: its differential is
`ContinuousLinearMap.fst`, which is surjective. -/
theorem isSubmersion_contMDiffMap_fst :
    IsSubmersion (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) := by
  intro x u
  exact ⟨(u, 0), by erw [mfderiv_contMDiffMap_fst]⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] [IsManifold J ∞ N] in
/-- The second projection `M × N → N` is a smooth submersion: its differential is
`ContinuousLinearMap.snd`, which is surjective. -/
theorem isSubmersion_contMDiffMap_snd :
    IsSubmersion (ContMDiffMap.snd : C^∞⟮I.prod J, M × N; J, N⟯) := by
  intro x u
  exact ⟨(0, u), by erw [mfderiv_contMDiffMap_snd]⟩

/-! ### The horizontal spaces of the product metric -/

/-- **The horizontal space of `π_M` for the product metric is the `M`-factor**:
`v` is horizontal exactly when its `N`-component vanishes.

A horizontal `v` is `g ⊕ h`-orthogonal to the vertical vector `(0, v.2)`, and
that inner product is `h_y(v.2, v.2)`, which forces `v.2 = 0` by positive
definiteness; conversely a vector with `v.2 = 0` is orthogonal to every vertical
vector `(0, w.2)`. -/
theorem mem_horizontalSpace_prodMetric_fst_iff (g : RiemannianMetric I M)
    (h : RiemannianMetric J N) {x : M × N} {v : TangentSpace (I.prod J) x} :
    v ∈ horizontalSpace (prodMetric g h) (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x
      ↔ v.2 = 0 := by
  rw [mem_horizontalSpace_iff]
  constructor
  · intro hv
    have hvert : ((0, v.2) : TangentSpace (I.prod J) x)
        ∈ verticalSpace (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x :=
      mfderiv_contMDiffMap_fst x (0, v.2)
    have key := hv _ hvert
    rw [prodMetric_inner, prodForm_apply,
      show (g.inner x.1) v.1 ((0, v.2) : TangentSpace (I.prod J) x).1 = 0 from map_zero _,
      zero_add] at key
    by_contra hne
    exact absurd key (h.pos x.2 v.2 hne).ne'
  · intro hv2 w hw
    have hw1 : mfderiv (I.prod J) I (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x w = 0 := hw
    rw [mfderiv_contMDiffMap_fst] at hw1
    have hg0 : g.inner x.1 v.1 w.1 = 0 := by rw [hw1]; exact map_zero _
    have hh0 : h.inner x.2 v.2 = 0 := by rw [hv2]; exact map_zero _
    rw [prodMetric_inner, prodForm_apply, hg0, hh0]
    simp

/-- **The horizontal space of `π_N` for the product metric is the `N`-factor**:
`v` is horizontal exactly when its `M`-component vanishes.  Symmetric to
`mem_horizontalSpace_prodMetric_fst_iff`. -/
theorem mem_horizontalSpace_prodMetric_snd_iff (g : RiemannianMetric I M)
    (h : RiemannianMetric J N) {x : M × N} {v : TangentSpace (I.prod J) x} :
    v ∈ horizontalSpace (prodMetric g h) (ContMDiffMap.snd : C^∞⟮I.prod J, M × N; J, N⟯) x
      ↔ v.1 = 0 := by
  rw [mem_horizontalSpace_iff]
  constructor
  · intro hv
    have hvert : ((v.1, 0) : TangentSpace (I.prod J) x)
        ∈ verticalSpace (ContMDiffMap.snd : C^∞⟮I.prod J, M × N; J, N⟯) x :=
      mfderiv_contMDiffMap_snd x (v.1, 0)
    have key := hv _ hvert
    rw [prodMetric_inner, prodForm_apply,
      show (h.inner x.2) v.2 ((v.1, 0) : TangentSpace (I.prod J) x).2 = 0 from map_zero _,
      add_zero] at key
    by_contra hne
    exact absurd key (g.pos x.1 v.1 hne).ne'
  · intro hv1 w hw
    have hw2 : mfderiv (I.prod J) J (ContMDiffMap.snd : C^∞⟮I.prod J, M × N; J, N⟯) x w = 0 := hw
    rw [mfderiv_contMDiffMap_snd] at hw2
    have hg0 : g.inner x.1 v.1 = 0 := by rw [hv1]; exact map_zero _
    have hh0 : h.inner x.2 v.2 w.2 = 0 := by rw [hw2]; exact map_zero _
    rw [prodMetric_inner, prodForm_apply, hh0, hg0]
    simp

/-! ### Example 2.27(b): the product projections are Riemannian submersions -/

/-- **Lee, Example 2.27(b)** (first projection): if `M × N` carries the product
metric `g ⊕ h`, then `π_M : M × N → M` is a Riemannian submersion onto `(M, g)`.

On a horizontal vector `v` (one with `v.2 = 0`) the cross term of the block form
vanishes, so `g ⊕ h`-length agrees with the `g`-length of `dπ_M v = v.1`. -/
theorem isRiemannianSubmersion_prodMetric_fst (g : RiemannianMetric I M)
    (h : RiemannianMetric J N) :
    IsRiemannianSubmersion (prodMetric g h) g
      (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) := by
  refine ⟨isSubmersion_contMDiffMap_fst, fun x v w hv hw => ?_⟩
  have hv2 : v.2 = 0 := (mem_horizontalSpace_prodMetric_fst_iff g h).mp hv
  have hh0 : h.inner x.2 v.2 = 0 := by rw [hv2]; exact map_zero _
  show g.inner x.1 (mfderiv (I.prod J) I (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x v)
      (mfderiv (I.prod J) I (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x w)
    = (prodMetric g h).inner x v w
  rw [mfderiv_contMDiffMap_fst, mfderiv_contMDiffMap_fst, prodMetric_inner, prodForm_apply, hh0]
  simp

/-- **Lee, Example 2.27(b)** (second projection): `π_N : M × N → N` is a
Riemannian submersion onto `(N, h)`.  Symmetric to
`isRiemannianSubmersion_prodMetric_fst`. -/
theorem isRiemannianSubmersion_prodMetric_snd (g : RiemannianMetric I M)
    (h : RiemannianMetric J N) :
    IsRiemannianSubmersion (prodMetric g h) h
      (ContMDiffMap.snd : C^∞⟮I.prod J, M × N; J, N⟯) := by
  refine ⟨isSubmersion_contMDiffMap_snd, fun x v w hv hw => ?_⟩
  have hv1 : v.1 = 0 := (mem_horizontalSpace_prodMetric_snd_iff g h).mp hv
  have hg0 : g.inner x.1 v.1 = 0 := by rw [hv1]; exact map_zero _
  show h.inner x.2 (mfderiv (I.prod J) J (ContMDiffMap.snd : C^∞⟮I.prod J, M × N; J, N⟯) x v)
      (mfderiv (I.prod J) J (ContMDiffMap.snd : C^∞⟮I.prod J, M × N; J, N⟯) x w)
    = (prodMetric g h).inner x v w
  rw [mfderiv_contMDiffMap_snd, mfderiv_contMDiffMap_snd, prodMetric_inner, prodForm_apply, hg0]
  simp

end ProductProjection

/-! ### Example 2.27(a): the Euclidean projection `ℝ^{n+k} → ℝ^n` -/

section Euclidean

/-- **Lee, Example 2.27(a)**: the projection `ℝ^{n+k} → ℝ^n` onto the first `n`
coordinates is a Riemannian submersion for the Euclidean metrics.

`ℝ^{n+k}` is modelled as `ℝ^n × ℝ^k`: mathlib gives the plain product a sup norm
rather than an inner product, so the Euclidean metric of `ℝ^{n+k}` is realised as
the product `ḡ_n ⊕ ḡ_k` of the two dot products, and this is exactly the case of
`isRiemannianSubmersion_prodMetric_fst` with both factors Euclidean. -/
theorem isRiemannianSubmersion_euclidean_fst (n k : ℕ) :
    IsRiemannianSubmersion
      (prodMetric (euclideanMetric (EuclideanSpace ℝ (Fin n)))
        (euclideanMetric (EuclideanSpace ℝ (Fin k))))
      (euclideanMetric (EuclideanSpace ℝ (Fin n)))
      (ContMDiffMap.fst :
        C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin k)),
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k);
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)), EuclideanSpace ℝ (Fin n)⟯) :=
  isRiemannianSubmersion_prodMetric_fst _ _

end Euclidean

/-! ### Example 2.27(c): the warped product projection `M ×_f N → M` -/

section Warped

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- **The horizontal space of `π_M` for a warped product is the `M`-factor**:
`v` is horizontal exactly when its `N`-component vanishes.  Same computation as
`mem_horizontalSpace_prodMetric_fst_iff`, except the second block carries the
strictly positive factor `f(x.1)²` — nonzero precisely because `f` never
vanishes — which does not affect the conclusion. -/
theorem mem_horizontalSpace_warpedProductMetric_fst_iff (g : RiemannianMetric I M)
    (h : RiemannianMetric J N) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hf0 : ∀ p, f p ≠ 0)
    {x : M × N} {v : TangentSpace (I.prod J) x} :
    v ∈ horizontalSpace (warpedProductMetric g h hf hf0)
        (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x
      ↔ v.2 = 0 := by
  rw [mem_horizontalSpace_iff]
  constructor
  · intro hv
    have hvert : ((0, v.2) : TangentSpace (I.prod J) x)
        ∈ verticalSpace (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x :=
      mfderiv_contMDiffMap_fst x (0, v.2)
    have key := hv _ hvert
    rw [show (warpedProductMetric g h hf hf0).inner x = warpedProductForm g h f x from rfl,
      warpedProductForm_apply,
      show (g.inner x.1) v.1 ((0, v.2) : TangentSpace (I.prod J) x).1 = 0 from map_zero _,
      zero_add] at key
    -- key : (f x.1) ^ 2 * h.inner x.2 v.2 ((0, v.2)).2 = 0
    have hpos : (0 : ℝ) < (f x.1) ^ 2 := sq_pos_of_ne_zero (hf0 x.1)
    have hz : h.inner x.2 v.2 v.2 = 0 := by
      rcases mul_eq_zero.mp key with h1 | h2
      · exact absurd h1 hpos.ne'
      · exact h2
    by_contra hne
    exact absurd hz (h.pos x.2 v.2 hne).ne'
  · intro hv2 w hw
    have hw1 : mfderiv (I.prod J) I (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x w = 0 := hw
    rw [mfderiv_contMDiffMap_fst] at hw1
    have hg0 : g.inner x.1 v.1 w.1 = 0 := by rw [hw1]; exact map_zero _
    have hh0 : h.inner x.2 v.2 = 0 := by rw [hv2]; exact map_zero _
    rw [show (warpedProductMetric g h hf hf0).inner x = warpedProductForm g h f x from rfl,
      warpedProductForm_apply, hg0, hh0]
    simp

/-- **Lee, Example 2.27(c)**: the projection `π_M : M ×_f N → M` of a warped
product is a Riemannian submersion onto `(M, g)`.

Just as in part (b), a horizontal vector `v` has `v.2 = 0`, so the (warped)
second block `f(x.1)² h_y(v.2, w.2)` drops out and `g ⊕ f² h`-length agrees with
the `g`-length of `dπ_M v = v.1`.  (The other projection `π_N` is typically not a
Riemannian submersion, since its second block carries the point-dependent factor
`f(x.1)²`; that is not formalised.) -/
theorem isRiemannianSubmersion_warpedProductMetric_fst (g : RiemannianMetric I M)
    (h : RiemannianMetric J N) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf0 : ∀ p, f p ≠ 0) :
    IsRiemannianSubmersion (warpedProductMetric g h hf hf0) g
      (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) := by
  refine ⟨isSubmersion_contMDiffMap_fst, fun x v w hv hw => ?_⟩
  have hv2 : v.2 = 0 := (mem_horizontalSpace_warpedProductMetric_fst_iff g h hf hf0).mp hv
  have hh0 : h.inner x.2 v.2 = 0 := by rw [hv2]; exact map_zero _
  show g.inner x.1 (mfderiv (I.prod J) I (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x v)
      (mfderiv (I.prod J) I (ContMDiffMap.fst : C^∞⟮I.prod J, M × N; I, M⟯) x w)
    = (warpedProductMetric g h hf hf0).inner x v w
  rw [mfderiv_contMDiffMap_fst, mfderiv_contMDiffMap_fst,
    show (warpedProductMetric g h hf hf0).inner x = warpedProductForm g h f x from rfl,
    warpedProductForm_apply, hh0]
  simp

end Warped

end LeeLib.Ch02
