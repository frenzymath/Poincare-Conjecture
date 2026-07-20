/-
Chapter 2, "Riemannian Metrics", §3–§4: the flat torus as a Riemannian
submanifold, and the identification of its induced metric with a product of
circle metrics.

Lee's Example 2.21 realizes the `n`-torus `T^n` as a Riemannian submanifold: the
covering `X : ℝ^n → T^n` restricts to local parametrizations, and the induced
metric is flat (equal to the Euclidean metric in the covering coordinates).  The
faithful formalizable model of the `2`-torus is the product of two unit circles
`S¹ × S¹`, each `S¹ ⊆ ℂ` carrying the round metric it inherits from ℂ (a special
case of the round sphere metric `LeeLib.Ch02.roundMetric` of Lee's Example 2.13);
the resulting product metric (`LeeLib.Ch02.prodMetric`, Lee's (2.12)) is the flat
torus.

Exercise 2.23 (`exer:product-metric-torus`) asks to check that the metric `T²`
inherits from its embedding into Euclidean space equals this product metric.  We
embed `T² = S¹ × S¹` into `ℝ⁴ = ℂ ×₂ ℂ` (the `L²`-product, so the ambient norm
is Euclidean) by the pair of circle inclusions, and prove
`torusEmbedding^* ḡ = torusMetric` (`torusEmbedding_preservesMetric`): the
ambient `L²` inner product splits (`WithLp.prod_inner_apply`) as the sum of the
two `ℂ`-inner products, which are precisely the two circle (pullback) metrics.

This is a port of Petersen's Example 1.3.6 development (`PetersenLib.circleMetric`,
`PetersenLib.flatTorus`, `PetersenLib.torusEmbedding_preservesMetric`) onto the
LeeLib substrate: `LeeLib.Ch02.pullbackMetric` (Lemma 2.11),
`LeeLib.Ch02.prodMetric` (2.12), and `LeeLib.Ch02.IsMetricPreserving`.

The two facts about the circle inclusion `S¹ ↪ ℂ` are mathlib's, from the
stereographic-projection development of the sphere:

* `contMDiff_coe_sphere` — the inclusion is smooth;
* `mfderiv_coe_sphere_injective` — its differential is injective (an immersion).
-/
import LeeLib.Ch02.Sphere
import LeeLib.Ch02.ProductMetric
import LeeLib.Ch02.Isometry
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace LeeLib.Ch02

open Manifold Metric Module ContinuousLinearMap
open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

section FlatTorus

open Complex

attribute [local instance] finrank_real_complex_fact'

/-! ### The circle metric and the flat torus -/

/-- **Math.** The inclusion `S¹ ↪ ℂ` of the unit circle is smooth
(`contMDiff_coe_sphere` specialised to `Circle = sphere (0 : ℂ) 1`). -/
theorem contMDiff_circle_coe :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
  contMDiff_coe_sphere (E := ℂ) (n := 1)

/-- **Math.** The differential of the inclusion `S¹ ↪ ℂ` is injective at every
point (`mfderiv_coe_sphere_injective`): the circle inclusion is an immersion. -/
theorem mfderiv_circle_coe_injective (z : Circle) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) z) :=
  mfderiv_coe_sphere_injective (E := ℂ) (n := 1) z

/-- **Math.** The **round metric on the circle** `S¹ ⊆ ℂ` (Lee, Example 2.13 with
`n = 1`): the pullback of the Euclidean metric of `ℂ ≅ ℝ²` along the smooth
immersion `S¹ ↪ ℂ`.  This is `LeeLib.Ch02.roundMetric` for the circle; it is
stated directly on `Circle` for use in the flat torus below. -/
noncomputable def circleMetric : RiemannianMetric (𝓡 1) Circle :=
  pullbackMetric (euclideanMetric ℂ) (fun z : Circle => (z : ℂ))
    contMDiff_circle_coe mfderiv_circle_coe_injective

/-- The circle metric is the ambient dot product of ℂ restricted to vectors
tangent to `S¹` (Lee, §2.3): its value on `v, w ∈ T_z S¹` is the ℂ-inner product
of the images of `v` and `w` under `dι_z`. -/
theorem circleMetric_innerAt (z : Circle) (v w : TangentSpace (𝓡 1) z) :
    circleMetric.innerAt z v w =
      inner ℝ (show ℂ from mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) z v)
        (show ℂ from mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) z w) :=
  rfl

/-- **Math.** Lee's Example 2.21 (2-torus case): **the flat torus**
`T² = S¹ × S¹`, with the product of the two round circle metrics.

Lee constructs the flat torus as the quotient `ℝ²/ℤ²`; mathlib has no
quotient-manifold construction, so the faithful formalizable model is the
product of two unit circles, which is flat and, as a product of the Lie group
`S¹` with itself, has a bi-invariant metric.  By Exercise 2.23
(`torusEmbedding_preservesMetric`) this product metric coincides with the metric
`T²` inherits from its embedding into Euclidean `ℝ⁴`. -/
noncomputable def torusMetric :
    RiemannianMetric ((𝓡 1).prod (𝓡 1)) (Circle × Circle) :=
  prodMetric circleMetric circleMetric

/-- Lee's (2.12) for the flat torus: the metric of `T² = S¹ × S¹` on a pair of
tangent vectors is the sum of the two circle inner products of the components. -/
theorem torusMetric_innerAt (p : Circle × Circle)
    (v w : TangentSpace ((𝓡 1).prod (𝓡 1)) p) :
    torusMetric.innerAt p v w =
      circleMetric.innerAt p.1 v.1 w.1 + circleMetric.innerAt p.2 v.2 w.2 :=
  prodForm_apply circleMetric circleMetric p v w

/-! ### Exercise 2.23 — the induced metric of the `ℝ⁴`-embedding is the product metric

Lee's Exercise 2.23 (`exer:product-metric-torus`): the metric `T²` inherits from
its embedding into Euclidean space equals the product of the circle metrics.  We
embed `T² = S¹ × S¹` into `ℝ⁴ = ℂ ×₂ ℂ`, the `L²`-product of two copies of ℂ, by
the pair of circle inclusions. -/

/-- **Math.** Lee's Exercise 2.23: the embedding of the torus `T² = S¹ × S¹` into
`ℝ⁴ = ℂ ×₂ ℂ` (the `L²`-product, so the ambient norm is Euclidean),
`(z, w) ↦ (z, w)`.  The classical `F(θ₁, θ₂) = (cos θ₁, sin θ₁, cos θ₂, sin θ₂)`
is this map written in the angle parametrization; the formalized `torusMetric`
uses unit circles, for which the embedding is the plain product of the two
inclusions `S¹ ↪ ℂ`. -/
def torusEmbedding (p : Circle × Circle) : WithLp 2 (ℂ × ℂ) :=
  WithLp.toLp 2 ((p.1 : ℂ), (p.2 : ℂ))

/-- The identification `ℂ × ℂ ≃ ℂ ×₂ ℂ` as a continuous linear map. -/
private def toL2CLM : (ℂ × ℂ) →L[ℝ] WithLp 2 (ℂ × ℂ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm : (ℂ × ℂ) ≃L[ℝ] WithLp 2 (ℂ × ℂ))

/-- **Eng.** The torus embedding is smooth: it is the `L²`-repackaging of the
pair of smooth circle inclusions. -/
theorem contMDiff_torusEmbedding :
    ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) ∞ torusEmbedding := by
  have h : ContMDiff ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, ℂ × ℂ) ∞
      (fun p : Circle × Circle => ((p.1 : ℂ), (p.2 : ℂ))) :=
    (contMDiff_circle_coe.comp contMDiff_fst).prodMk_space
      (contMDiff_circle_coe.comp contMDiff_snd)
  exact toL2CLM.contMDiff.comp h

/-- **Eng.** Pairing two maps into model vector spaces differentiates to the
product of the differentials — the vector-space-target analogue of
`HasMFDerivAt.prodMk` (whose target model would be `𝓘(ℝ, E').prod 𝓘(ℝ, F')`
rather than `𝓘(ℝ, E' × F')`).  Structural, as for `prodMk`. -/
private theorem hasMFDerivAt_prodMk_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {f : M → E'} {g : M → F'} {x : M}
    {df : TangentSpace I x →L[ℝ] E'} {dg : TangentSpace I x →L[ℝ] F'}
    (hf : HasMFDerivAt I 𝓘(ℝ, E') f x df) (hg : HasMFDerivAt I 𝓘(ℝ, F') g x dg) :
    HasMFDerivAt I 𝓘(ℝ, E' × F') (fun y => (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- **Math.** The torus embedding has, at `p = (z, w)`, the manifold derivative
`(u₁, u₂) ↦ (Dι_z(u₁), Dι_w(u₂))` (as a map into `ℂ ×₂ ℂ`): the pair of the
differentials of the circle inclusions. -/
theorem hasMFDerivAt_torusEmbedding (p : Circle × Circle) :
    HasMFDerivAt ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) torusEmbedding p
      (toL2CLM.comp
        (((mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.1).comp
            (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1))
              (EuclideanSpace ℝ (Fin 1)))).prod
          ((mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.2).comp
            (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1))
              (EuclideanSpace ℝ (Fin 1)))))) := by
  have hι1 : HasMFDerivAt ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, ℂ)
      (fun q : Circle × Circle => (q.1 : ℂ)) p
      ((mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1))
          (EuclideanSpace ℝ (Fin 1)))) :=
    HasMFDerivAt.comp p
      (((contMDiff_circle_coe.mdifferentiable (by simp)) p.1).hasMFDerivAt)
      (hasMFDerivAt_fst p)
  have hι2 : HasMFDerivAt ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, ℂ)
      (fun q : Circle × Circle => (q.2 : ℂ)) p
      ((mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.2).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1))
          (EuclideanSpace ℝ (Fin 1)))) :=
    HasMFDerivAt.comp p
      (((contMDiff_circle_coe.mdifferentiable (by simp)) p.2).hasMFDerivAt)
      (hasMFDerivAt_snd p)
  exact HasMFDerivAt.comp p toL2CLM.hasMFDerivAt
    (hasMFDerivAt_prodMk_space hι1 hι2)

/-- **Math.** The differential of the torus embedding is the pair of the
differentials of the circle inclusions:
`D(ι × ι)(u₁, u₂) = (Dι(u₁), Dι(u₂))` under `T(S¹ × S¹) = TS¹ × TS¹`. -/
theorem mfderiv_torusEmbedding_apply (p : Circle × Circle)
    (u : TangentSpace ((𝓡 1).prod (𝓡 1)) p) :
    mfderiv ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) torusEmbedding p u =
      WithLp.toLp 2
        (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.1 u.1,
          mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) p.2 u.2) := by
  rw [(hasMFDerivAt_torusEmbedding p).mfderiv]
  rfl

/-- **Math.** Lee's Exercise 2.23: the torus embedding is a smooth immersion —
its differential `(Dι, Dι)` is injective componentwise. -/
theorem mfderiv_torusEmbedding_injective (p : Circle × Circle) :
    Function.Injective
      (mfderiv ((𝓡 1).prod (𝓡 1)) 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) torusEmbedding p) := by
  intro u v huv
  rw [mfderiv_torusEmbedding_apply, mfderiv_torusEmbedding_apply] at huv
  have h := WithLp.toLp_injective (V := ℂ × ℂ) 2 huv
  exact Prod.ext (mfderiv_circle_coe_injective p.1 (congrArg Prod.fst h))
    (mfderiv_circle_coe_injective p.2 (congrArg Prod.snd h))

/-- **Math.** Lee's Exercise 2.23 (`exer:product-metric-torus`): the metric that
`T²` inherits from its embedding into Euclidean `ℝ⁴ = ℂ ×₂ ℂ` **equals the
product metric** obtained from the round circle metrics,
`torusEmbedding^* ḡ = torusMetric`.

The ambient `L²` inner product of `ℂ ×₂ ℂ` splits (`WithLp.prod_inner_apply`) as
the sum of the two ℂ-inner products, and the differential of the embedding is the
pair of the two circle differentials (`mfderiv_torusEmbedding_apply`), so each
summand is exactly one circle (pullback) metric — which is the product metric by
Lee's (2.12). -/
theorem torusEmbedding_preservesMetric :
    IsMetricPreserving torusMetric (euclideanMetric (WithLp 2 (ℂ × ℂ))) torusEmbedding := by
  intro p
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
  rw [pullbackForm_apply, mfderiv_torusEmbedding_apply, mfderiv_torusEmbedding_apply]
  show _ = (prodMetric circleMetric circleMetric).inner p u v
  rw [prodMetric_inner, prodForm_apply]
  rfl

end FlatTorus

end

end LeeLib.Ch02
