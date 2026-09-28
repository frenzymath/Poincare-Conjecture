import PetersenLib.Ch01.MetricConstructions

/-!
# Petersen Ch. 4, §4.4.1 — left-invariant metrics and left translations

The opening nodes of §4.4.1:

* `leftInvariantMetricViaTranslation` — fixing an inner product on the Lie
  algebra `T_eG` and translating it to every `T_gG` via `L_g` produces a
  Riemannian metric on `G` (the Ch. 1 construction `leftInvariantMetric`,
  re-exported here as the §4.4.1 anchor).
* `leftTranslationDiffeomorph` — left translation `L_g : x ↦ g·x` as a smooth
  diffeomorphism of `G` (inverse `L_{g⁻¹}`).
* `leftTranslationIsIsometry` — with the left-invariant metric, every left
  translation is a Riemannian isometry (Petersen §4.4.1); the metric
  preservation is the Ch. 1 chain-rule computation
  `leftInvariantMetric_leftInvariant`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §4.4.1, p. 155.
-/

noncomputable section

open scoped ContDiff Manifold Topology

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G]

/-- **Math.** Petersen §4.4.1: fixing an inner product `b` on `T_eG` and
translating it to `T_gG` via the differential of the left translation
`L_g(x) = g·x` produces a Riemannian metric on `G` — the left-invariant
metric. This is the Ch. 1 construction (`leftInvariantMetric`, Petersen
§1.3.2), re-exported as the §4.4.1 anchor; left-invariant vector fields and
the identification of `T_eG` with the Lie algebra of left-invariant fields
are the Ch. 2 layer (`GroupLieAlgebra`, `mulInvariantVectorField`). -/
abbrev leftInvariantMetricViaTranslation [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < b u u) :
    RiemannianMetric I G :=
  leftInvariantMetric (I := I) b hsymm hpos

/-- **Math.** Left translation `L_g : x ↦ g·x` on a Lie group is a smooth
diffeomorphism, with smooth inverse `L_{g⁻¹}`. -/
def leftTranslationDiffeomorph (g : G) : G ≃ₘ⟮I, I⟯ G where
  toFun := (g * ·)
  invFun := (g⁻¹ * ·)
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  contMDiff_toFun := contMDiff_const.mul contMDiff_id
  contMDiff_invFun := contMDiff_const.mul contMDiff_id

omit [IsManifold I ∞ G] in
@[simp]
theorem leftTranslationDiffeomorph_apply (g x : G) :
    leftTranslationDiffeomorph (I := I) g x = g * x := rfl

/-- **Math.** Petersen §4.4.1: with the left-invariant metric of
`leftInvariantMetricViaTranslation`, every left translation `L_g` is a
Riemannian isometry. `L_g` is a diffeomorphism
(`leftTranslationDiffeomorph`), and it preserves the metric by the chain
rule `d(L_{(gx)⁻¹})_{gx} ∘ d(L_g)_x = d(L_{x⁻¹})_x`
(`leftInvariantMetric_leftInvariant`). -/
theorem leftTranslationIsIsometry [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < b u u) (g : G) :
    IsRiemannianIsometry (leftInvariantMetricViaTranslation (I := I) b hsymm hpos)
      (leftInvariantMetricViaTranslation (I := I) b hsymm hpos) (g * ·) :=
  ⟨⟨leftTranslationDiffeomorph g, rfl⟩,
    leftInvariantMetric_leftInvariant b hsymm hpos g⟩

end PetersenLib
