import DoCarmoLib.Riemannian.Variation.Basic
import DoCarmoLib.Riemannian.Jacobi.Geodesics

/-!
# Jacobi fields

The definition here follows Chow--Knopf, Appendix B.3: a Jacobi field is the
variational field of a smooth one-parameter family of geodesics.
-/

open Set
open scoped ContDiff Manifold Topology

set_option autoImplicit false

noncomputable section

namespace ChowKnopf

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A smooth two-parameter variation whose curves are geodesics on `T`. -/
def IsGeodesicVariationOn (g : Riemannian.RiemannianMetric I M)
    (F : ℝ × ℝ → M) (S T : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ F (S ×ˢ T) ∧
    ∀ s ∈ S, Riemannian.Geodesic.IsGeodesicCurveOn (I := I) g (fun t ↦ F (s, t)) T

/-- **Math.** A field along `γ` is a Jacobi field on `T` when it is the variational field
of a smooth one-parameter family of geodesics whose zero slice is `γ`. -/
def IsJacobiFieldOn (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) (T : Set ℝ) : Prop :=
  ∃ (S : Set ℝ) (F : ℝ × ℝ → M),
    IsOpen S ∧ 0 ∈ S ∧
      IsGeodesicVariationOn g F S T ∧
      Set.EqOn (fun t ↦ F (0, t)) γ T ∧
      Set.EqOn (Riemannian.Variation.variationalField I F) J T

end ChowKnopf
