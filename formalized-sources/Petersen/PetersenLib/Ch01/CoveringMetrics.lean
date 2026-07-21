import PetersenLib.Ch01.MetricConstructions
import PetersenLib.Ch01.Sphere

/-!
# Petersen Ch. 1, §1.3.3 — Riemannian coverings and real projective space

The deck-transformation symmetry of the covering-induced (pullback) metric
of Petersen §1.3.3, and Example 1.3.7: the antipodal involution of the unit
sphere is a Riemannian isometry, inducing the Riemannian covering
`Sⁿ → ℝPⁿ` and hence the canonical quotient metric on real projective
space.

* The covering-induced metric itself (`coveringInducedMetric`) and the
  quotient-metric existence-and-uniqueness statement (`quotientMetric`)
  live in `PetersenLib.Ch01.MetricConstructions`; this file adds the
  remaining clause of Petersen §1.3.3: **deck transformations act by
  isometries** on the pullback metric
  (`coveringInducedMetric_deck_preservesMetric`,
  `coveringInducedMetric_deck_isRiemannianIsometry`). A deck
  transformation is any smooth `τ : M → M` with `F ∘ τ = F`; by the chain
  rule `DF_{τ(p)} ∘ Dτ_p = DF_p`, so `τ` preserves `F^*g_N`.

* For Example 1.3.7 (`realProjectiveSpaceCovering`): the antipodal map
  `x ↦ -x` of `Sⁿ = Sⁿ(1) ⊆ E` is a diffeomorphism
  (`antipodalDiffeomorph`) and a Riemannian isometry of the canonical
  metric (`antipodal_isRiemannianIsometry`), because the differential of
  the sphere inclusion intertwines it with `-id` on the ambient space
  (`mfderiv_coe_sphere_comp_neg`), and the ambient inner product is
  invariant under simultaneous sign change.

## Design notes

Mathlib has *no* smooth-manifold structure on real projective space (the
`Projectivization` type has no `ChartedSpace` instances at this pin), and
no quotient-manifold construction. Following the representation choice of
`quotientMetric` in `MetricConstructions.lean`, `ℝPⁿ` is therefore
represented by hypotheses: a smooth manifold `P` together with a smooth
surjective covering map `q : Sⁿ → P` whose differentials are linear
isomorphisms and whose fibres are exactly the antipodal pairs
(`q x = q y ↔ y = x ∨ y = -x` — the 2-to-1 covering with deck group
`{id, -I}`). The conclusion — existence and uniqueness of a Riemannian
metric on `P` making `q` a local isometry — is derived from
`quotientMetric`, whose invariance hypothesis is discharged by the
antipodal isometry. (`quotientMetric` is fully proved, `sorry`-free.)

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.3.3,
Example 1.3.7.
-/

open Bundle Metric Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## Deck transformations act by isometries (Petersen §1.3.3) -/

section DeckTransformations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [FiniteDimensional ℝ E]

/-- **Math.** Petersen §1.3.3: if `F : M → N` is a normal covering with deck
group `Γ`, then `Γ` **acts by isometries** on the pullback metric. Stated for
a single deck transformation, and in the generality in which it is true: any
smooth `τ : M → M` over `F` (i.e. `F ∘ τ = F`) preserves the covering-induced
metric `F^*g_N`. Chain rule: `DF_{τ(p)} ∘ Dτ_p = D(F ∘ τ)_p = DF_p`, so
`(F^*g_N)(Dτ u, Dτ v) = g_N(DF u, DF v) = (F^*g_N)(u, v)`. -/
theorem coveringInducedMetric_deck_preservesMetric
    (gN : RiemannianMetric I' M') (F : M → M')
    (hF : IsSmoothImmersion (I := I) (I' := I') F)
    (τ : M → M) (hτ : ContMDiff I I ∞ τ) (hdeck : F ∘ τ = F) :
    PreservesMetric (coveringInducedMetric gN F hF)
      (coveringInducedMetric gN F hF) τ := by
  intro p u v
  -- transport of the target metric along an equality of base points
  have hpoint : ∀ {x y : M'}, x = y → ∀ a b : E',
      gN.metricInner x a b = gN.metricInner y a b := by
    rintro x y rfl a b; rfl
  -- the chain rule collapses the differential of `F` through `τ`
  have hcomp : ∀ w : TangentSpace I p,
      mfderiv I I' F (τ p) (mfderiv I I τ p w) = mfderiv I I' F p w := by
    intro w
    have hFd : MDifferentiableAt I I' F (τ p) :=
      hF.1.mdifferentiableAt (by simp)
    have hτd : MDifferentiableAt I I τ p :=
      hτ.mdifferentiableAt (by simp)
    have h1 : mfderiv I I' (F ∘ τ) p w
        = mfderiv I I' F (τ p) (mfderiv I I τ p w) :=
      mfderiv_comp_apply p hFd hτd w
    rw [← h1, hdeck]
  show gN.metricInner (F p) (mfderiv I I' F p u) (mfderiv I I' F p v)
      = gN.metricInner (F (τ p))
          (mfderiv I I' F (τ p) (mfderiv I I τ p u))
          (mfderiv I I' F (τ p) (mfderiv I I τ p v))
  rw [hcomp u, hcomp v]
  exact hpoint (congrFun hdeck p).symm _ _

/-- **Math.** Petersen §1.3.3: a deck transformation that is moreover a
diffeomorphism (as deck transformations of a smooth covering always are) is a
full **Riemannian isometry** of the covering-induced metric. -/
theorem coveringInducedMetric_deck_isRiemannianIsometry
    (gN : RiemannianMetric I' M') (F : M → M')
    (hF : IsSmoothImmersion (I := I) (I' := I') F)
    (τ : Diffeomorph I I M M ∞) (hdeck : F ∘ τ = F) :
    IsRiemannianIsometry (coveringInducedMetric gN F hF)
      (coveringInducedMetric gN F hF) τ :=
  ⟨⟨τ, rfl⟩,
    coveringInducedMetric_deck_preservesMetric gN F hF τ τ.contMDiff hdeck⟩

end DeckTransformations

/-! ## Example 1.3.7 — the antipodal isometry and `Sⁿ → ℝPⁿ` -/

section RealProjectiveSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- **Math.** Petersen Example 1.3.7: the antipodal involution `-I : x ↦ -x`
of the unit sphere `Sⁿ ⊆ E` is a diffeomorphism — it is smooth (Mathlib's
`contMDiff_neg_sphere`) and its own inverse. -/
def antipodalDiffeomorph :
    Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : E) 1) (sphere (0 : E) 1) ∞ :=
  ⟨⟨fun x => -x, fun x => -x, fun x => neg_neg x, fun x => neg_neg x⟩,
    contMDiff_neg_sphere, contMDiff_neg_sphere⟩

@[simp]
theorem antipodalDiffeomorph_apply (x : sphere (0 : E) 1) :
    antipodalDiffeomorph (n := n) x = -x :=
  rfl

/-- **Math.** The differential of the sphere inclusion `ι : Sⁿ ↪ E`
intertwines the antipodal map with `-id` on the ambient space:
`Dι_{-p} ∘ D(-I)_p = D(ι ∘ (-I))_p = D(-ι)_p = -Dι_p`, since `ι ∘ (-I) = -ι`
and negation is linear on `E`. -/
theorem mfderiv_coe_sphere_comp_neg (p : sphere (0 : E) 1)
    (u : TangentSpace (𝓡 n) p) :
    (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (-p)
        (mfderiv (𝓡 n) (𝓡 n) (fun x : sphere (0 : E) 1 => -x) p u) : E)
      = -(mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p u : E) := by
  have hιd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (-p) :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  have hνd : MDifferentiableAt (𝓡 n) (𝓡 n)
      (fun x : sphere (0 : E) 1 => -x) p :=
    (contMDiff_neg_sphere (m := 1)).mdifferentiableAt one_ne_zero
  have hfun : (((↑) : sphere (0 : E) 1 → E) ∘ (fun x : sphere (0 : E) 1 => -x))
      = -((↑) : sphere (0 : E) 1 → E) := by
    funext y
    exact coe_neg_sphere y
  have h1 : mfderiv (𝓡 n) 𝓘(ℝ, E)
      (((↑) : sphere (0 : E) 1 → E) ∘ (fun x : sphere (0 : E) 1 => -x)) p u
      = mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (-p)
          (mfderiv (𝓡 n) (𝓡 n) (fun x : sphere (0 : E) 1 => -x) p u) :=
    mfderiv_comp_apply p hιd hνd u
  rw [← h1, hfun, mfderiv_neg]
  rfl

/-- **Math.** Petersen Example 1.3.7: the involution `-I` on `Sⁿ(1) ⊆ E` is
a **Riemannian isometry** of the canonical (round) metric. It is a
diffeomorphism (`antipodalDiffeomorph`), and it preserves the pullback
metric because `Dι ∘ D(-I) = -Dι` (`mfderiv_coe_sphere_comp_neg`) and the
ambient inner product satisfies `⟪-a, -b⟫ = ⟪a, b⟫`. -/
theorem antipodal_isRiemannianIsometry :
    IsRiemannianIsometry (sphereMetricUnit (n := n) E) (sphereMetricUnit (n := n) E)
      (fun x : sphere (0 : E) 1 => -x) := by
  refine ⟨⟨antipodalDiffeomorph, rfl⟩, fun p u v => ?_⟩
  show (sphereMetricUnit (n := n) E).metricInner p u v
      = (sphereMetricUnit (n := n) E).metricInner (-p)
          (mfderiv (𝓡 n) (𝓡 n) (fun x : sphere (0 : E) 1 => -x) p u)
          (mfderiv (𝓡 n) (𝓡 n) (fun x : sphere (0 : E) 1 => -x) p v)
  rw [sphereMetricUnit_apply, sphereMetricUnit_apply,
    mfderiv_coe_sphere_comp_neg p u, mfderiv_coe_sphere_comp_neg p v]
  exact (inner_neg_neg _ _).symm

/-- **Math.** Petersen Example 1.3.7: the antipodal isometry of `Sⁿ(1)`
induces a Riemannian covering `Sⁿ → ℝPⁿ`: real projective space carries a
*unique* Riemannian metric making the covering map a local isometry.

**Representation.** Mathlib has no smooth-manifold structure on `ℝPⁿ`
(no `ChartedSpace` instances on `Projectivization`) and no
quotient-manifold construction, so — exactly as in `quotientMetric` — the
projective space is represented by hypotheses: a smooth manifold `P` and a
map `q : Sⁿ → P` that is a smooth surjective covering map with invertible
differentials whose fibres are exactly the antipodal pairs
(`hq_fib : q x = q y ↔ y = x ∨ y = -x`, i.e. `q` is the quotient by the
deck group `{id, -I}`). The conclusion is the existence of a unique metric
`g_P` with `q^*g_P = g_{Sⁿ}` — the local-isometry clause for `q`. The
invariance hypothesis of `quotientMetric` is discharged by
`antipodal_isRiemannianIsometry`. Both halves of `quotientMetric` are now
proved, so this statement is unconditional (existence of the quotient metric
comes from the smooth local sections of
`PetersenLib.exists_localSection_of_mfderiv_surjective`). -/
theorem realProjectiveSpaceCovering
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold I' ∞ P]
    (q : sphere (0 : E) 1 → P)
    (hq_cont : ContMDiff (𝓡 n) I' ∞ q)
    (hq_cov : IsCoveringMap q)
    (hq_surj : Function.Surjective q)
    (hq_bij : ∀ x : sphere (0 : E) 1, Function.Bijective (mfderiv (𝓡 n) I' q x))
    (hq_fib : ∀ x y : sphere (0 : E) 1, q x = q y ↔ y = x ∨ y = -x) :
    ∃! gP : RiemannianMetric I' P,
      PreservesMetric (sphereMetricUnit (n := n) E) gP q := by
  have hν_pres :=
    (antipodal_isRiemannianIsometry (E := E) (n := n)).preservesMetric
  refine quotientMetric (sphereMetricUnit (n := n) E) q hq_cont hq_cov hq_surj
    hq_bij ?_
  intro p p' hpp' u v u' v' hu hv
  rcases (hq_fib p p').mp hpp' with rfl | rfl
  · -- the two points agree: the vectors agree by injectivity of `Dq`
    obtain rfl : u = u' := (hq_bij _).1 hu
    obtain rfl : v = v' := (hq_bij _).1 hv
    rfl
  · -- the two points are antipodal: the vectors correspond under `D(-I)`,
    -- and `-I` is an isometry
    have hqν : q ∘ (fun x : sphere (0 : E) 1 => -x) = q := by
      funext x
      exact ((hq_fib x (-x)).mpr (Or.inr rfl)).symm
    have hcomp : ∀ w : TangentSpace (𝓡 n) p,
        mfderiv (𝓡 n) I' q (-p)
            (mfderiv (𝓡 n) (𝓡 n) (fun x : sphere (0 : E) 1 => -x) p w)
          = mfderiv (𝓡 n) I' q p w := by
      intro w
      have hqd : MDifferentiableAt (𝓡 n) I' q (-p) :=
        hq_cont.mdifferentiableAt (by simp)
      have hνd : MDifferentiableAt (𝓡 n) (𝓡 n)
          (fun x : sphere (0 : E) 1 => -x) p :=
        (contMDiff_neg_sphere (m := 1)).mdifferentiableAt one_ne_zero
      have h1 : mfderiv (𝓡 n) I' (q ∘ (fun x : sphere (0 : E) 1 => -x)) p w
          = mfderiv (𝓡 n) I' q (-p)
              (mfderiv (𝓡 n) (𝓡 n) (fun x : sphere (0 : E) 1 => -x) p w) :=
        mfderiv_comp_apply p hqd hνd w
      rw [← h1, hqν]
    obtain rfl : u' = mfderiv (𝓡 n) (𝓡 n) (fun x : sphere (0 : E) 1 => -x) p u :=
      (hq_bij (-p)).1 (hu.symm.trans (hcomp u).symm)
    obtain rfl : v' = mfderiv (𝓡 n) (𝓡 n) (fun x : sphere (0 : E) 1 => -x) p v :=
      (hq_bij (-p)).1 (hv.symm.trans (hcomp v).symm)
    exact hν_pres p u v

end RealProjectiveSpace

end PetersenLib
