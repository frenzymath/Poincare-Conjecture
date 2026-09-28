import Mathlib.Geometry.Manifold.SmoothEmbedding
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe u𝕜 uE uH uM uE' uH'

-- These derived smoothness lemmas are now part of mathlib's immersion API.
#check Manifold.IsImmersionAtOfComplement.contMDiffAt
#check Manifold.IsImmersionAt.contMDiffAt
#check Manifold.IsImmersion.contMDiff

section RealFiniteDimensionalLocalDiffeomorph

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]
variable {f : M → N}

namespace Manifold.IsLocalDiffeomorph

/-- A smooth local diffeomorphism between finite-dimensional real manifolds is a smooth
immersion. -/
theorem isImmersion (hf : IsLocalDiffeomorph I J ∞ f) : IsImmersion I J ∞ f := by
  -- The local diffeomorphism gives a continuous linear equivalence model for each manifold
  -- derivative, so the derivative is injective at every point.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hf.contMDiff).2 ?_
  intro x
  exact (hf.mfderivToContinuousLinearEquiv (by simp) x).injective

end Manifold.IsLocalDiffeomorph

end RealFiniteDimensionalLocalDiffeomorph

section SubmanifoldsWithBoundary

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable (J : ModelWithCorners 𝕜 E' H') (S : Set M)
variable [ChartedSpace H' S] [IsManifold J ⊤ S]

/- Definition 5.36-extra-1, immersed form: once the manifold-with-boundary structure on the
subtype `S` is fixed, the owner abstraction is the canonical immersion predicate for the subtype
inclusion. -/
#check Manifold.IsImmersion J I ⊤ (Subtype.val : S → M)

/- Definition 5.36-extra-1, embedded form: the corresponding embedded notion is the canonical
smooth-embedding predicate for the same subtype inclusion. -/
#check Manifold.IsSmoothEmbedding J I ⊤ (Subtype.val : S → M)

end SubmanifoldsWithBoundary
