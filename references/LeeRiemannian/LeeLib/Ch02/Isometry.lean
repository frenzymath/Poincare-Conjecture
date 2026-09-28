/-
Chapter 2, "Riemannian Metrics", §"Isometries": isometries of Riemannian
manifolds, and the invariance of length and of the Riemannian distance under
them.

Lee introduces isometries in running prose right after the Euclidean metric:
an *isometry* from `(M, g)` to `(M̃, g̃)` is a diffeomorphism `φ : M → M̃` with
`φ^* g̃ = g`, and he immediately notes that this is equivalent to asking that each
differential `dφ_p : T_p M → T_{φ(p)} M̃` be a linear isometry.  A *local
isometry* is a map each of whose points has a neighbourhood on which it
restricts to an isometry onto an open subset; Exercise 2.7 identifies these,
between manifolds of equal dimension, with the smooth maps satisfying
`φ^* g̃ = g`.

`IsMetricPreserving` below is that condition `φ^* g̃ = g`, and `IsIsometry` is
Lee's isometry.  The two headline results are

* `IsMetricPreserving.pathELength_comp` — Lee's Proposition 2.47(c), the
  isometry invariance of length, and
* `IsIsometry.riemannianEDist_comp` — Lee's Proposition 2.51, the isometry
  invariance of the Riemannian distance.

**Why `IsMetricPreserving` and not "local isometry" as the hypothesis of 2.47(c).**
Lee states 2.47(c) for a local isometry.  Every local isometry is metric
preserving (that is the easy half of Exercise 2.7, and it needs no hypothesis on
dimensions), so the statement proved here *implies* Lee's.  It is strictly more
general: length invariance uses only `φ^* g̃ = g`, never local invertibility, so
it holds for maps that are not local isometries at all — an isometric immersion
of a `k`-manifold into an `n`-manifold with `k < n`, say.  Restricting to local
isometries would be assuming an irrelevant hypothesis.  The converse half of
Exercise 2.7, which does need equal dimensions and the inverse function theorem
for manifolds, is not needed for any result in this file.

**Why length invariance is not just the chain rule.**  It nearly is, and the
pointwise statement `‖dφ_p v‖ = ‖v‖` (`IsMetricPreserving.norm_mfderiv`) is
indeed immediate.  The work is that mathlib's `pathELength` integrates
`‖mfderiv γ t 1‖ₑ` using the *unrestricted* `mfderiv`, which is a junk value
where `γ` is not differentiable, and Lee's curves are only `C^1` on a closed
interval `[a,b]`.  At the endpoints `mfderiv` need not agree with the honest
one-sided derivative, so the chain rule is unavailable exactly there.  We
therefore compare the two integrals over the *open* interval `Ioo a b`, where
`Icc a b` is a neighbourhood of each point and `ContMDiffOn` really does give
`MDifferentiableAt`; the endpoints are a null set, which is precisely what
`pathELength_eq_lintegral_mfderiv_Ioo` is for.

**Why the distance result needs the inverse and not just `≤`.**  A metric
preserving map only gives `d_g̃(φx, φy) ≤ d_g(x,y)`: it maps curves in `M` to
curves of equal length in `M̃`, but `M̃` may have shortcuts missing from the image
of `φ`.  Equality is genuinely a statement about isometries, and we get it by
running the inequality in both directions, the reverse one along `φ⁻¹`, which is
metric preserving because `φ` is (`IsIsometry.symm`).
-/
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import LeeLib.Ch02.Distance
import LeeLib.Ch02.PullbackMetric

namespace LeeLib.Ch02

open Bundle Manifold Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology RealInnerProductSpace

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ### Metric-preserving maps -/

/-- **`φ` preserves the metric**: `φ^* g̃ = g` (Lee, §"Isometries", the condition of
Exercise 2.7).

Unwinding `pullbackForm`, this says `g̃_{φ(p)}(dφ_p v, dφ_p w) = g_p(v, w)` for all
`p`, `v`, `w`: each differential `dφ_p` carries `g_p` to `g̃_{φ(p)}`, which is Lee's
own reading of `φ^* g̃ = g`.  Stated as an equality of the pullback *forms* rather
than pointwise on vectors, so that it is literally Lee's equation of tensor
fields; `IsMetricPreserving.inner_mfderiv` is the pointwise form. -/
def IsMetricPreserving (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (φ : M → M') : Prop :=
  ∀ p : M, pullbackForm g' φ p = g.inner p

namespace IsMetricPreserving

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'} {φ : M → M'}

/-- The pointwise form of `φ^* g̃ = g`: `dφ_p` carries `g_p` to `g̃_{φ(p)}`. -/
theorem inner_mfderiv (h : IsMetricPreserving g g' φ) (p : M) (v w : TangentSpace I p) :
    g'.inner (φ p) (mfderiv I I' φ p v) (mfderiv I I' φ p w) = g.inner p v w := by
  rw [← pullbackForm_apply g' φ p v w, h p]

/-- A metric-preserving map is an immersion: `dφ_p` is injective at every point.

This is Lee's Lemma 2.11 (`pullbackForm_posDef_iff_immersion`) read backwards —
`φ^* g̃ = g` is in particular positive definite, being `g`. -/
theorem injective_mfderiv (h : IsMetricPreserving g g' φ) (p : M) :
    Function.Injective (mfderiv I I' φ p) := by
  refine (pullbackForm_posDef_iff_immersion g' φ).1 (fun q v hv => ?_) p
  rw [h q]
  exact g.pos q v hv

/-- The identity map preserves the metric. -/
theorem id (g : RiemannianMetric I M) : IsMetricPreserving g g (id : M → M) := by
  intro p
  ext v w
  rw [pullbackForm_apply, mfderiv_id]
  rfl

end IsMetricPreserving

/-! ### Isometries -/

/-- **Isometry** (Lee, §"Isometries"): a diffeomorphism `Φ : M → M̃` with
`Φ^* g̃ = g`.

Lee's `(M,g)` and `(M̃,g̃)` are *isometric* when such a `Φ` exists.  Being a
diffeomorphism is carried by mathlib's `Diffeomorph`, so the only condition to
impose is metric preservation. -/
def IsIsometry (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (Φ : Diffeomorph I I' M M' ∞) : Prop :=
  IsMetricPreserving g g' (Φ : M → M')

namespace IsIsometry

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}

/-- The identity diffeomorphism is an isometry of `(M, g)`. -/
theorem refl (g : RiemannianMetric I M) : IsIsometry g g (Diffeomorph.refl I M ∞) :=
  IsMetricPreserving.id g

/-- **The inverse of an isometry is an isometry** (Lee, §"Isometries": "the inverse
of an isometry is again an isometry", the step that makes "isometric" symmetric).

`dΦ_p` is invertible with inverse `d(Φ⁻¹)_{Φ(p)}`, so the defining identity
`g̃(dΦ v, dΦ w) = g(v, w)` read at `v = d(Φ⁻¹) v'`, `w = d(Φ⁻¹) w'` is exactly the
defining identity for `Φ⁻¹`. -/
theorem symm {Φ : Diffeomorph I I' M M' ∞} (h : IsIsometry g g' Φ) :
    IsIsometry g' g Φ.symm := by
  intro q
  ext v w
  rw [pullbackForm_apply]
  -- Push `v, w : T_q M̃` down to `T_{Φ.symm q} M` and use `h` there.  The chain rule
  -- applied to `Φ ∘ Φ⁻¹ = id` says `dΦ_{Φ⁻¹ q}` undoes `d(Φ⁻¹)_q`.
  have hid : (Φ : M → M') ∘ (Φ.symm : M' → M) = _root_.id := funext Φ.apply_symm_apply
  have key : ∀ u : TangentSpace I' q,
      mfderiv I I' (Φ : M → M') (Φ.symm q) (mfderiv I' I (Φ.symm : M' → M) q u) = u := by
    intro u
    have hcomp := mfderiv_comp_apply (I'' := I') q
      (Φ.mdifferentiable (by simp) (Φ.symm q)) (Φ.symm.mdifferentiable (by simp) q) u
    rw [hid, mfderiv_id] at hcomp
    exact hcomp.symm
  have hkey := h.inner_mfderiv (Φ.symm q)
    (mfderiv I' I (Φ.symm : M' → M) q v) (mfderiv I' I (Φ.symm : M' → M) q w)
  rw [key v, key w, Φ.apply_symm_apply] at hkey
  exact hkey.symm

end IsIsometry

/-! ### Norms of tangent vectors

The bridge from Lee's `g.inner` to the norm mathlib's `pathELength` integrates.
Installing a `RiemannianBundle` instance from `g` puts an `InnerProductSpace ℝ`
structure on each `T_p M` whose inner product *is* `g.inner p`, definitionally; a
`NormedAddCommGroup`, and hence the `ENorm` that `pathELength` needs, comes with
it.
-/

section Norm

/-- Under the `RiemannianBundle` instance built from `g`, the abstract fibre inner
product on `T_p M` is Lee's `g_p` on the nose. -/
theorem inner_eq_inner (g : RiemannianMetric I M) (p : M) (v w : TangentSpace I p) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ⟪v, w⟫ = g.inner p v w := rfl

/-- Under the `RiemannianBundle` instance built from `g`, the fibre norm on `T_p M`
is Lee's `|v|_g = ⟨v, v⟩_g^{1/2}`. -/
theorem norm_eq_normAt (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ‖v‖ = g.normAt p v := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [norm_eq_sqrt_real_inner]
  rfl

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'} {φ : M → M'}

/-- **The differential of a metric-preserving map is a linear isometry** — Lee's
"unwinding the definitions shows that this is equivalent to the requirement that
each differential `dφ_p` be a linear isometry".

This is the pointwise heart of every invariance statement below. -/
theorem IsMetricPreserving.norm_mfderiv (h : IsMetricPreserving g g' φ) (p : M)
    (v : TangentSpace I p) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
    ‖mfderiv I I' φ p v‖ = ‖v‖ := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  congr 1
  exact h.inner_mfderiv p v v

/-- The extended-norm form of `IsMetricPreserving.norm_mfderiv`, which is what
`pathELength` actually integrates. -/
theorem IsMetricPreserving.enorm_mfderiv (h : IsMetricPreserving g g' φ) (p : M)
    (v : TangentSpace I p) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
    ‖mfderiv I I' φ p v‖ₑ = ‖v‖ₑ := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h.norm_mfderiv p v]

end Norm

/-! ### Invariance of length

Lee's Proposition 2.47.  Parts (a) and (b) — additivity of length and
independence of the parametrization — hold for the length of a path in any
manifold whose tangent spaces are normed, with no reference to a metric, and are
exactly mathlib's `pathELength_add` and `pathELength_comp_of_monotoneOn`.  Part
(c), the isometry invariance, is the one that needs `φ^* g̃ = g` and is proved
here.
-/

section Length

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'} {φ : M → M'}

/-- **Lee's Proposition 2.47(c)**: *isometry invariance of length*.  A
metric-preserving smooth map carries every `C^1` curve to a curve of the same
length, `L_g(γ) = L_{g̃}(φ ∘ γ)`.

`γ` is only assumed `C^1` on the closed interval `[a,b]`, which is Lee's notion of
an (unbroken) admissible curve segment.  The integrands are compared on the open
interval `Ioo a b`: there `Icc a b` is a neighbourhood of each point, so
`ContMDiffOn` upgrades to `MDifferentiableAt` and the chain rule applies, and the
two endpoints form a null set. -/
theorem IsMetricPreserving.pathELength_comp (h : IsMetricPreserving g g' φ)
    (hφ : ContMDiff I I' ∞ φ) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
    pathELength I' (φ ∘ γ) a b = pathELength I γ a b := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Ioo, pathELength_eq_lintegral_mfderiv_Ioo]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    (hγ.mdifferentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  rw [mfderiv_comp_apply t (hφ.contMDiffAt.mdifferentiableAt (by simp)) hγt]
  exact h.enorm_mfderiv (γ t) _

end Length

/-! ### Invariance of the Riemannian distance -/

section Distance

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'} {φ : M → M'}

/-- **A metric-preserving map does not increase the Riemannian distance**:
`d_{g̃}(φ(x), φ(y)) ≤ d_g(x, y)`.

Only the inequality holds in general: `φ` carries each `C^1` curve from `x` to `y`
to a curve of equal length from `φ(x)` to `φ(y)` (`pathELength_comp`), so every
competitor in the infimum defining `d_g(x,y)` produces a competitor of the same
length for `d_{g̃}(φx, φy)`.  It cannot go the other way, because `M̃` may contain
shorter curves that do not lie in the image of `φ`. -/
theorem IsMetricPreserving.riemannianEDist_le (h : IsMetricPreserving g g' φ)
    (hφ : ContMDiff I I' ∞ φ) (x y : M) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
    riemannianEDist I' (φ x) (φ y) ≤ riemannianEDist I x y := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  haveI := g.isContinuousRiemannianBundle
  haveI := g'.isContinuousRiemannianBundle
  refine le_of_forall_gt_imp_ge_of_dense (fun r hr => ?_)
  obtain ⟨γ, hγa, hγb, hγsmooth, hγlen⟩ := exists_lt_of_riemannianEDist_lt hr
  have hcomp : pathELength I' (φ ∘ γ) 0 1 = pathELength I γ 0 1 := h.pathELength_comp hφ hγsmooth
  have hle : riemannianEDist I' (φ x) (φ y) ≤ pathELength I' (φ ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength
      ((hφ.of_le (by simp)).comp_contMDiffOn hγsmooth) (by simp [hγa]) (by simp [hγb]) zero_le_one
  exact ((hle.trans hcomp.le).trans_lt hγlen).le

/-- **Lee's Proposition 2.51**: *isometry invariance of the Riemannian distance*.
If `Φ : (M,g) → (M̃,g̃)` is an isometry then `d_{g̃}(Φ(x), Φ(y)) = d_g(x, y)`.

Both inequalities are `IsMetricPreserving.riemannianEDist_le`, the reverse one
applied to `Φ⁻¹`, which is metric preserving by `IsIsometry.symm`.  This is where
being a *diffeomorphism*, and not merely metric preserving, is used. -/
theorem IsIsometry.riemannianEDist_comp {Φ : Diffeomorph I I' M M' ∞}
    (h : IsIsometry g g' Φ) (x y : M) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
    riemannianEDist I' (Φ x) (Φ y) = riemannianEDist I x y := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  refine le_antisymm (h.riemannianEDist_le Φ.contMDiff x y) ?_
  have hrev := h.symm.riemannianEDist_le Φ.symm.contMDiff (Φ x) (Φ y)
  rwa [Φ.symm_apply_apply, Φ.symm_apply_apply] at hrev

end Distance

/-! ### Isometries of Euclidean space

A witness that the theory above is not vacuous, and Lee's first example of an
isometry: a linear isometry of inner product spaces is an isometry of the
corresponding Euclidean manifolds (Example 2.6).  Applied to `F = F' = ℝⁿ` these
are the orthogonal maps, the linear part of the rigid motions of Chapter 1.

This matters beyond the example.  `IsIsometry` is a hypothesis of
`IsIsometry.riemannianEDist_comp`, and a hypothesis satisfied only by the
identity would make that theorem say nothing; `isIsometry_euclideanMetric`
exhibits a large supply of genuinely non-identity witnesses.
-/

section EuclideanIsometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

/-- The differential of a continuous linear equivalence, viewed as a
diffeomorphism of the underlying manifolds, is the equivalence itself. -/
theorem mfderiv_toDiffeomorph (e : F ≃L[ℝ] F') (p : F) (v : TangentSpace 𝓘(ℝ, F) p) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F') (e.toDiffeomorph : F → F') p v = e v := by
  rw [e.coe_toDiffeomorph, mfderiv_eq_fderiv, e.fderiv]
  rfl

/-- **A linear isometry of inner product spaces is an isometry of the associated
Euclidean manifolds** (Lee, Example 2.6).

The differential of a linear map is the map itself, so `Φ^* ḡ = ḡ` reduces to
`⟨e v, e w⟩ = ⟨v, w⟩`, which is exactly what `e` being a linear isometry says. -/
theorem isIsometry_euclideanMetric (e : F ≃ₗᵢ[ℝ] F') :
    IsIsometry (euclideanMetric F) (euclideanMetric F')
      e.toContinuousLinearEquiv.toDiffeomorph := by
  intro p
  ext v w
  rw [pullbackForm_apply, mfderiv_toDiffeomorph, mfderiv_toDiffeomorph,
    euclideanMetric_inner, euclideanMetric_inner]
  exact e.inner_map_map v w

/-- **A linear isometry of Euclidean space preserves the Euclidean distance**, as a
consequence of the general Proposition 2.51.

This is the end-to-end check on the whole chain: it discharges the hypothesis of
`IsIsometry.riemannianEDist_comp` with a genuinely non-identity map, and lands on
a conclusion whose truth is known independently — `d_ḡ` on an inner product space
is the ambient distance (`euclideanMetric_riemannianEDist`), and linear isometries
preserve that.  Lee's Problem 2-2 is the converse: a distance-preserving *bijection*
between Euclidean spaces is necessarily such a linear isometry, up to translation. -/
theorem isIsometry_euclideanMetric_riemannianEDist (e : F ≃ₗᵢ[ℝ] F') (x y : F) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, F) : F → Type _) :=
      ⟨(euclideanMetric F).toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, F') : F' → Type _) :=
      ⟨(euclideanMetric F').toRiemannianMetric⟩
    riemannianEDist 𝓘(ℝ, F') (e x) (e y) = edist x y := by
  letI : RiemannianBundle (TangentSpace 𝓘(ℝ, F) : F → Type _) :=
    ⟨(euclideanMetric F).toRiemannianMetric⟩
  letI : RiemannianBundle (TangentSpace 𝓘(ℝ, F') : F' → Type _) :=
    ⟨(euclideanMetric F').toRiemannianMetric⟩
  calc riemannianEDist 𝓘(ℝ, F') (e x) (e y)
      = riemannianEDist 𝓘(ℝ, F) x y :=
        (isIsometry_euclideanMetric e).riemannianEDist_comp x y
    _ = edist x y := euclideanMetric_riemannianEDist F x y

end EuclideanIsometry

end

end LeeLib.Ch02
