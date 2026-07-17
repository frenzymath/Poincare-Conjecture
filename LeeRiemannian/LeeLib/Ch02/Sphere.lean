/-
Chapter 2, "Riemannian Metrics", §3 "Methods for Constructing Riemannian
Metrics": the round metric on the sphere.

Lee's Example 2.13: the unit `n`-sphere `S^n ⊆ ℝ^{n+1}` is an embedded
`n`-dimensional submanifold, and the Riemannian metric induced on it by the
Euclidean metric is the *round metric* (or *standard metric*) `g̊`.

Lee's construction is the general one of §2.3: a Riemannian submanifold carries
the metric `ι^* g̃` pulled back along its inclusion, which is a metric because
`ι` is an immersion (Lemma 2.11).  So the round metric is exactly

  `roundMetric = pullbackMetric (euclideanMetric E) (coe : S^n → E)`,

and the two facts it needs about the inclusion are both already in mathlib's
stereographic-projection development of the sphere:

* `contMDiff_coe_sphere` — the inclusion `S^n ↪ E` is smooth;
* `mfderiv_coe_sphere_injective` — its differential is injective at each point,
  i.e. the inclusion is an immersion.

The identification `roundMetric_innerAt` records that the round metric really is
Lee's "restriction of the ambient dot product to vectors tangent to the sphere":
its value on `v, w ∈ T_p S^n` is the ambient inner product of the images of `v`
and `w` under `dι_p`, which is what Lee's identification of `T_p S^n` with a
subspace of `T_p ℝ^{n+1}` silently performs.

Following mathlib's sphere development, the ambient space is a real inner
product space `E` with `[Fact (finrank ℝ E = n + 1)]` rather than literally
`ℝ^{n+1}`; `roundMetricEuclidean` specialises to Lee's `S^n ⊆ ℝ^{n+1}`.
-/
import LeeLib.Ch02.PullbackMetric
import Mathlib.Geometry.Manifold.Instances.Sphere

namespace LeeLib.Ch02

open Manifold Metric Module
open scoped Manifold ContDiff RealInnerProductSpace

section RoundMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (E) in
/-- **The round metric on `S^n`** (Lee, Example 2.13): the Riemannian metric that
the unit sphere `S^n ⊆ ℝ^{n+1}` inherits from the Euclidean metric of the
ambient space, as a Riemannian submanifold in the sense of §2.3.

This is the induced metric `ι^* ḡ` of `def:induced-metric` applied to the
inclusion `ι : S^n ↪ ℝ^{n+1}`, which is a smooth immersion — so Lemma 2.11
(`pullbackForm_posDef_iff_immersion`) is what makes it a metric at all. -/
noncomputable def roundMetric (n : ℕ) [Fact (finrank ℝ E = n + 1)] :
    RiemannianMetric (𝓡 n) (sphere (0 : E) 1) :=
  pullbackMetric (euclideanMetric E) ((↑) : sphere (0 : E) 1 → E)
    contMDiff_coe_sphere mfderiv_coe_sphere_injective

/-- The round metric is the ambient dot product restricted to vectors tangent to
the sphere (Lee, §2.3): under Lee's identification of `T_p S^n` with its image in
`T_p ℝ^{n+1}` under `dι_p`, this reads `g̊_p(v, w) = ⟪v, w⟫`. -/
theorem roundMetric_innerAt (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (p : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) p) :
    (roundMetric E n).innerAt p v w =
      inner ℝ (show E from mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p v)
        (show E from mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p w) :=
  rfl

end RoundMetric

section EuclideanSphere

/-- **The round metric on Lee's `S^n ⊆ ℝ^{n+1}`** (Lee, Example 2.13), the case
of `roundMetric` in which the ambient inner product space is literally `ℝ^{n+1}`
with the dot product. -/
noncomputable def roundMetricEuclidean (n : ℕ) :
    RiemannianMetric (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  roundMetric (EuclideanSpace ℝ (Fin (n + 1))) n

end EuclideanSphere

end LeeLib.Ch02
