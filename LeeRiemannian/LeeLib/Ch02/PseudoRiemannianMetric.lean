/-
Chapter 2, "Riemannian Metrics", §7 "Pseudo-Riemannian Metrics": the definition.

Lee: "a *pseudo-Riemannian metric* on `M` is a smooth symmetric 2-tensor field `g`
that is nondegenerate at each point of `M`, and with the same signature everywhere.
Every Riemannian metric is also a pseudo-Riemannian metric."

Mathlib has no such object.  Every Riemannian structure there —
`Bundle.RiemannianMetric`, `Bundle.ContinuousRiemannianMetric`,
`Bundle.ContMDiffRiemannianMetric` — carries a `pos` field, and the whole
`RiemannianBundle` mechanism exists precisely to install an `InnerProductSpace ℝ (E b)`
on each fibre.  An indefinite form induces no inner product, so none of that
machinery transfers: this file has to build the structure from scratch.

What makes that cheap is the observation that mathlib's positivity is used only
to *interpret* the form as an inner product, never in the analysis.  The proof of
`ContMDiffWithinAt.inner_bundle` immediately destructures the `RiemannianBundle`
class back down to a bare family `g : Π x, E x →L[ℝ] E x →L[ℝ] ℝ` and calls
`ContMDiffWithinAt.clm_bundle_apply₂` on the hom-bundle; the inner product
reappears only in the final `simp only [hg]` rewriting `⟪v,w⟫` into `g x v w`.
So `contMDiff_pairing` below — "the `g`-pairing of two smooth sections is a
smooth function", the analytic workhorse of the whole pseudo-Riemannian theory —
is available verbatim without positivity, by calling the same hom-bundle lemma
directly.

The design choices worth naming:

* **Nondegeneracy is stated in existential-witness form**, `v ≠ 0 → ∃ w, g v w ≠ 0`,
  because that is the shape a construction can discharge (see
  `RiemannianMetric.toPseudoRiemannianMetric`, where the witness is `v` itself).
  Consumers get mathlib's `LinearMap.BilinForm.Nondegenerate` from `bilin_nondegenerate`,
  which is what `LeeLib.Ch02.ScalarProduct` — the entire pointwise theory of
  indefinite forms, Lee's §2.6 — is phrased in.  `bilin` is the bridge between the
  two, and is the reason this file exists as more than a structure declaration.
* **The signature is mathlib's `QuadraticForm.sigPos`/`sigNeg`**, not a hand-rolled
  `sSup` over negative-definite subspaces.  Those come with Sylvester's law of
  inertia already proved in the pin, which `ScalarProduct` has already connected to
  `IsOrthonormal` bases; `HasSignature` is therefore a statement Lee's Propositions
  2.70-2.73 can consume directly.

Note on prior art: the sibling PetersenLib has a `PseudoRiemannianMetric` of the
same shape (`PetersenLib/Ch01/RiemannianManifolds.lean`), reached independently,
together with a `pseudoRiemannianIndex` defined as an `sSup` over negative-definite
subspaces.  Cross-project imports are not permitted, and the `sSup` index is in any
case weaker than the route taken here: it is junk-valued unless bounded, and it is
connected neither to Sylvester's law nor to `sigNeg`, so Petersen's own
point-independence claim stays prose.  The structure below is stated for a general
vector bundle rather than just `TM`, matching `LeeLib.Ch02.OrthonormalFrame`.
-/
import LeeLib.Ch02.RiemannianMetric
import LeeLib.Ch02.ScalarProduct
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

namespace Bundle

open Bundle Manifold
open scoped Manifold ContDiff

section Defs

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
/-- A **smooth field of nondegenerate symmetric bilinear forms** on the fibres of a
vector bundle — the structure underlying Lee's pseudo-Riemannian metrics.

This is mathlib's `Bundle.ContMDiffRiemannianMetric` with the `pos` and
`isVonNBounded` fields replaced by nondegeneracy.  The `contMDiff` field is
identical: a section of the bundle of continuous bilinear forms, whose model fibre
is `F →L[ℝ] F →L[ℝ] ℝ`.  Nothing here refers to an `InnerProductSpace` on the
fibres, and nothing can: an indefinite form does not induce one. -/
structure ContMDiffPseudoMetric where
  /-- The bilinear form along the fibres of the bundle. -/
  form (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : form b v w = form b w v
  /-- Nondegeneracy, in the witness form a construction can discharge.  Consumers
  should use `bilin_nondegenerate`, which is mathlib's `BilinForm.Nondegenerate`. -/
  nondegenerate (b : B) (v : E b) (hv : v ≠ 0) : ∃ w, form b v w ≠ 0
  contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (form b))

namespace ContMDiffPseudoMetric

variable (g : ContMDiffPseudoMetric IB n F E)

/-- The fibre form as a mathlib `BilinForm`, i.e. as an honest `LinearMap` in each
slot rather than a `ContinuousLinearMap`.

This is the bridge to `LeeLib.Ch02.ScalarProduct`, where Lee's whole §2.6 theory of
scalar product spaces — Gram-Schmidt, Sylvester's law, orthogonal complements,
signatures — is stated for `LinearMap.BilinForm ℝ V`.  Without it the pointwise
theory and the bundle theory could not talk to each other. -/
noncomputable def bilin (b : B) : LinearMap.BilinForm ℝ (E b) :=
  LinearMap.mk₂ ℝ (fun v w => g.form b v w)
    (fun v₁ v₂ w => by simp)
    (fun c v w => by simp)
    (fun v w₁ w₂ => by simp)
    (fun c v w => by simp)

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
@[simp] theorem bilin_apply (b : B) (v w : E b) : g.bilin b v w = g.form b v w := rfl

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- The fibre form is symmetric as a `BilinForm` — Lee's "symmetric 2-tensor field". -/
theorem bilin_isSymm (b : B) : (g.bilin b).IsSymm := ⟨fun v w => g.symm b v w⟩

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- The fibre form is left-separating: the only vector orthogonal to everything is `0`.
This is the direct translation of the `nondegenerate` field, and needs no finiteness. -/
theorem bilin_separatingLeft (b : B) : (g.bilin b).SeparatingLeft := by
  intro v hv
  by_contra hne
  obtain ⟨w, hw⟩ := g.nondegenerate b v hne
  exact hw (hv w)

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- **The fibre form is nondegenerate** in mathlib's sense.  This is the form
`LeeLib.Ch02.ScalarProduct` consumes, and it is what makes each fibre a *scalar
product space* in Lee's sense (§2.6).

Mathlib's `Nondegenerate` is the conjunction of left- and right-separation, which are
independent conditions in general but agree in finite dimensions
(`Nondegenerate.ofSeparatingLeft`) — hence the fibrewise finiteness hypothesis, which
costs nothing here since every fibre is isomorphic to the model fibre `F`. -/
theorem bilin_nondegenerate [∀ b, FiniteDimensional ℝ (E b)] (b : B) :
    (g.bilin b).Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (g.bilin_separatingLeft b)

end ContMDiffPseudoMetric

end Defs

section Pairing

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

namespace ContMDiffPseudoMetric

variable (g : ContMDiffPseudoMetric IB n F E) {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

/-- **The `g`-pairing of two smooth sections is a smooth function**, within a set at a
point.  This is Lee's Lemma 2.7 with positivity deleted, and it is the analytic
workhorse of the pseudo-Riemannian theory: it is what makes the indefinite
Gram-Schmidt recursion of `LeeLib.Ch02.PseudoOrthonormalFrame` smooth.

The proof is mathlib's own proof of `ContMDiffWithinAt.inner_bundle`, minus its last
step.  That lemma destructures the `RiemannianBundle` class to recover a bare family
of forms and calls `clm_bundle_apply₂` on the hom-bundle; here the bare family is
`g.form` to begin with, so the hom-bundle lemma applies directly and the inner
product never appears.  `E₃ := Bundle.Trivial B ℝ` is the trivial line bundle in
which the pairing takes its values. -/
theorem contMDiffWithinAt_pairing
    (hb : ContMDiffWithinAt IM IB n b s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m => TotalSpace.mk' F (b m) (v m)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m => TotalSpace.mk' F (b m) (w m)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ, ℝ) n (fun m => g.form (b m) (v m) (w m)) s x := by
  have h : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, ℝ)) n
      (fun m => TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g.form (b m) (v m) (w m))) s x :=
    ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F)
      ((g.contMDiff (b x)).contMDiffWithinAt.comp x hb (Set.mapsTo_univ _ _)) hv hw
  rw [contMDiffWithinAt_totalSpace] at h
  exact h.2

/-- The `g`-pairing of two smooth sections is smooth at a point. -/
theorem contMDiffAt_pairing
    (hb : ContMDiffAt IM IB n b x)
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m => TotalSpace.mk' F (b m) (v m)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m => TotalSpace.mk' F (b m) (w m)) x) :
    ContMDiffAt IM 𝓘(ℝ, ℝ) n (fun m => g.form (b m) (v m) (w m)) x :=
  g.contMDiffWithinAt_pairing (s := Set.univ) hb.contMDiffWithinAt hv.contMDiffWithinAt
    hw.contMDiffWithinAt |>.contMDiffAt (by simp)

/-- The `g`-pairing of two smooth sections is smooth on a set. -/
theorem contMDiffOn_pairing
    (hb : ContMDiffOn IM IB n b s)
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m => TotalSpace.mk' F (b m) (v m)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m => TotalSpace.mk' F (b m) (w m)) s) :
    ContMDiffOn IM 𝓘(ℝ, ℝ) n (fun m => g.form (b m) (v m) (w m)) s :=
  fun y hy => g.contMDiffWithinAt_pairing (hb y hy) (hv y hy) (hw y hy)

/-- The `g`-pairing of two smooth sections is smooth. -/
theorem contMDiff_pairing
    (hb : ContMDiff IM IB n b)
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m => TotalSpace.mk' F (b m) (v m)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m => TotalSpace.mk' F (b m) (w m))) :
    ContMDiff IM 𝓘(ℝ, ℝ) n (fun m => g.form (b m) (v m) (w m)) :=
  fun y => g.contMDiffAt_pairing (hb y) (hv y) (hw y)

end ContMDiffPseudoMetric

end Pairing

end Bundle

namespace LeeLib.Ch02

open Bundle Manifold Module
open scoped Manifold ContDiff

section Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Tangent spaces of a finite-dimensional manifold are finite-dimensional.**

A gap in mathlib: `TangentSpace I x` is a non-reducible type synonym for the model
space `E` (deliberately, so that instance search does not pick up wrong instances),
and it `deriving`s `TopologicalSpace`, `AddCommGroup`, `Module`, `ContinuousSMul` and
`ContinuousConstSMul` — but not `FiniteDimensional`.  Every consumer therefore has to
re-derive it by hand; `LeeLib.Ch02.MusicalIsomorphism` does exactly that three times
over.  Registering it once as an instance is safe because `FiniteDimensional` is a
`Prop` class, so no diamond can result. -/
instance TangentSpace.finiteDimensional [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

variable (I M) in
/-- **Pseudo-Riemannian metric** (Lee, §2.7): "a smooth symmetric 2-tensor field `g`
that is nondegenerate at each point of `M`, and with the same signature everywhere".

The constant-signature requirement is *not* part of this structure; it is
`HasSignature` below.  Splitting them is deliberate.  Lee's Propositions 2.70 and
2.71 both *conclude* that a pullback tensor has a particular constant signature, and
that conclusion is only sayable if a metric can first be exhibited without it; and on
a connected manifold constancy is automatic, so building it in would make the
structure carry a redundant field.  A "pseudo-Riemannian manifold of signature
`(r,s)`" in Lee's sense is a pair `(g, h)` with `h : HasSignature g r s`.

Like `RiemannianMetric`, this is *data*, not a typeclass. -/
abbrev PseudoRiemannianMetric : Type _ :=
  Bundle.ContMDiffPseudoMetric I ∞ E (TangentSpace I : M → Type _)

namespace PseudoRiemannianMetric

variable (g : PseudoRiemannianMetric I M) (p : M)

/-- Lee's angle-bracket notation, in the pseudo-Riemannian case: `⟨v, w⟩_g = g p (v, w)`.
Unlike the Riemannian `RiemannianMetric.innerAt` there is no companion `normAt`:
`⟨v,v⟩_g` may be negative or zero on a nonzero vector, so `√⟨v,v⟩_g` is not a length.
This is Lee's "proofs that use positivity in an essential way, such as those involving
lengths of curves, do not [carry over]". -/
noncomputable def innerAt (v w : TangentSpace I p) : ℝ := g.form p v w

@[simp] theorem innerAt_apply (v w : TangentSpace I p) : g.innerAt p v w = g.form p v w := rfl

/-- Symmetry of the metric. -/
theorem innerAt_comm (v w : TangentSpace I p) : g.innerAt p v w = g.innerAt p w v := g.symm p v w

/-- **A pseudo-Riemannian metric makes each tangent space a scalar product space** in
Lee's sense (§2.6): a finite-dimensional real vector space with a symmetric
nondegenerate bilinear form.  This is the hypothesis of every result in
`LeeLib.Ch02.ScalarProduct`, so this lemma is what lets the pointwise theory be
applied fibrewise. -/
theorem bilin_isSymm_nondegenerate [FiniteDimensional ℝ E] :
    (g.bilin p).IsSymm ∧ (g.bilin p).Nondegenerate :=
  ⟨g.bilin_isSymm p, g.bilin_nondegenerate p⟩

/-- A pseudo-Riemannian metric is determined by its form: the remaining fields are
propositions about it, so proof irrelevance makes two metrics with the same form
equal.  Compare `RiemannianMetric.ext_inner`. -/
theorem ext_form {g₁ g₂ : PseudoRiemannianMetric I M} (h : ∀ p : M, g₁.form p = g₂.form p) :
    g₁ = g₂ := by
  obtain ⟨f₁, s₁, nd₁, c₁⟩ := g₁
  obtain ⟨f₂, s₂, nd₂, c₂⟩ := g₂
  obtain rfl : f₁ = f₂ := funext h
  rfl

end PseudoRiemannianMetric

/-- **Every Riemannian metric is a pseudo-Riemannian metric** (Lee, §2.7, last
sentence of the definition).

The only field needing an argument is nondegeneracy, and positive definiteness
discharges it with the witness `w := v`: if `v ≠ 0` then `g v v > 0 ≠ 0`.  Note this
is exactly the step that *fails* in the indefinite case, where `⟨v,v⟩ ≠ 0` does not
follow from `v ≠ 0` — a null vector is nonzero and orthogonal to itself.  The
`isVonNBounded` field of the Riemannian structure is simply dropped: it exists only
to build the fibrewise `InnerProductSpace`, which has no pseudo-Riemannian analogue. -/
def RiemannianMetric.toPseudoRiemannianMetric (g : RiemannianMetric I M) :
    PseudoRiemannianMetric I M where
  form := g.inner
  symm := g.symm
  nondegenerate p v hv := ⟨v, ne_of_gt (g.pos p v hv)⟩
  contMDiff := g.contMDiff

@[simp] theorem RiemannianMetric.toPseudoRiemannianMetric_form (g : RiemannianMetric I M) (p : M) :
    g.toPseudoRiemannianMetric.form p = g.inner p := rfl

end Manifold

section Signature

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open QuadraticMap QuadraticForm

namespace PseudoRiemannianMetric

/-- The **signature of a pseudo-Riemannian metric at a point**: the pair `(r, s)` of
the numbers of positive and negative terms in a diagonalization of `g_p`, which
Sylvester's law of inertia (`LeeLib.Ch02.IsOrthonormal.isGreatest_ncard`) shows is
independent of the diagonalization.

This routes through mathlib's `QuadraticForm.sigPos`/`sigNeg` rather than a
hand-rolled supremum, so uniqueness of inertia is already available in the pin and
`ScalarProduct`'s bridge (`IsOrthonormal.sigPos_eq_ncard`) computes it from any
orthonormal basis of the fibre. -/
noncomputable def sigPosAt (g : PseudoRiemannianMetric I M) (p : M) : ℕ :=
  sigPos (LinearMap.BilinMap.toQuadraticMap (g.bilin p))

/-- The number of negative terms in a diagonalization of `g_p` — Lee's *index* of the
metric at `p`.  A Lorentz metric is one of index `1` everywhere. -/
noncomputable def sigNegAt (g : PseudoRiemannianMetric I M) (p : M) : ℕ :=
  sigNeg (LinearMap.BilinMap.toQuadraticMap (g.bilin p))

/-- **`r + s = n` at every point.**  Lee's signature `(r,s)` of a scalar product space
of dimension `n` always satisfies `r + s = n`, because nondegeneracy makes the radical
trivial.  This is `ScalarProduct.sigPos_add_sigNeg_eq_finrank` applied fibrewise, and
it is why `HasSignature` can be stated with `r` and `s` independent: it constrains
them to a single degree of freedom once `dim M` is fixed. -/
theorem sigPosAt_add_sigNegAt (g : PseudoRiemannianMetric I M) (p : M) :
    g.sigPosAt p + g.sigNegAt p = finrank ℝ (TangentSpace I p) :=
  sigPos_add_sigNeg_eq_finrank (g.bilin_isSymm p) (g.bilin_nondegenerate p)

end PseudoRiemannianMetric

/-- **A pseudo-Riemannian metric of signature `(r,s)`** (Lee, §2.7): nondegenerate at
each point, "and with the same signature everywhere".

This is the second half of Lee's definition, carried as a separate predicate rather
than a structure field — see the docstring of `PseudoRiemannianMetric`.  Lee's
"pseudo-Riemannian manifold of signature `(r,s)`" is `(M, g)` together with a proof of
`HasSignature g r s`. -/
def HasSignature (g : PseudoRiemannianMetric I M) (r s : ℕ) : Prop :=
  ∀ p : M, g.sigPosAt p = r ∧ g.sigNegAt p = s

/-- A **Lorentz metric** (Lee, §2.7): a pseudo-Riemannian metric "of index 1, and thus
signature `(r, 1)`".  Lee's index is the number of negative terms, `sigNeg`. -/
def IsLorentzMetric (g : PseudoRiemannianMetric I M) : Prop :=
  ∃ r : ℕ, HasSignature g r 1

end Signature

end LeeLib.Ch02
