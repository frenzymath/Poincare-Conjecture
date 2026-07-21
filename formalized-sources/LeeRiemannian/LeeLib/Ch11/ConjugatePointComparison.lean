import MorganTianLib.Ch01.JacobiManifold

/-!
# Lee Chapter 11: conjugate-point comparison

This file states Lee's Conjugate Point Comparison I using the shared
manifold-level notions of sectional curvature and conjugate points.  The
positive-curvature Sturm comparison is supplied by the Morgan--Tian
development, whose conjugate-point predicate directly formalizes the Jacobi
field definition used by Lee.
-/

noncomputable section

namespace LeeLib.Ch11

open Set Riemannian Riemannian.Geodesic
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Lee's Conjugate Point Comparison I, in a single sharp form.
Along a unit-speed geodesic segment of positive length, an upper sectional
curvature bound `c` rules out conjugacy when either `c ≤ 0`, with no length
restriction, or `c > 0` and `√c b < π`. -/
theorem conjugatePointComparisonI
    {g : RiemannianMetric I M} {γ : ℝ → M} {b c : ℝ}
    (hb : 0 < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 b))
    (hγc : ∀ t ∈ Icc (0 : ℝ) b, ContinuousAt γ t)
    (hunit : ∀ t ∈ Icc (0 : ℝ) b, Geodesic.speedSq (I := I) g γ t = 1)
    (hsec : ∀ t ∈ Icc (0 : ℝ) b, ∀ v w : TangentSpace I (γ t),
      MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection (γ t) v w ≤ c)
    (hc : c ≤ 0 ∨ (0 < c ∧ Real.sqrt c * b < Real.pi)) :
    ¬ MorganTianLib.IsConjugatePointAt (I := I) g γ b := by
  rcases hc with hc | ⟨hc, hshort⟩
  · exact MorganTianLib.not_isConjugatePointAt_of_sectionalCurvatureAt_le
      (I := I) hb le_rfl (by simpa using Real.pi_pos) hgeo hγc hunit
      (fun t ht v w => (hsec t ht v w).trans hc)
  · exact MorganTianLib.not_isConjugatePointAt_of_sectionalCurvatureAt_le
      (I := I) hb hc.le hshort hgeo hγc hunit hsec

/-- **Math.** The nonpositive-curvature clause of Lee's Conjugate Point
Comparison I: an upper bound `c ≤ 0` rules out conjugate points along every
unit-speed geodesic segment, without a length restriction. -/
theorem conjugatePointComparisonI_nonpos
    {g : RiemannianMetric I M} {γ : ℝ → M} {b c : ℝ}
    (hb : 0 < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 b))
    (hγc : ∀ t ∈ Icc (0 : ℝ) b, ContinuousAt γ t)
    (hunit : ∀ t ∈ Icc (0 : ℝ) b, Geodesic.speedSq (I := I) g γ t = 1)
    (hsec : ∀ t ∈ Icc (0 : ℝ) b, ∀ v w : TangentSpace I (γ t),
      MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection (γ t) v w ≤ c)
    (hc : c ≤ 0) :
    ¬ MorganTianLib.IsConjugatePointAt (I := I) g γ b :=
  conjugatePointComparisonI hb hgeo hγc hunit hsec (Or.inl hc)

/-- **Math.** The positive-curvature clause of Lee's Conjugate Point
Comparison I: if the sectional curvatures are at most `1 / R²`, where
`R > 0`, then a unit-speed segment of length `b < π R` contains no conjugate
point to its initial point. -/
theorem conjugatePointComparisonI_pos
    {g : RiemannianMetric I M} {γ : ℝ → M} {b R : ℝ}
    (hR : 0 < R) (hb : 0 < b) (hshort : b < Real.pi * R)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 b))
    (hγc : ∀ t ∈ Icc (0 : ℝ) b, ContinuousAt γ t)
    (hunit : ∀ t ∈ Icc (0 : ℝ) b, Geodesic.speedSq (I := I) g γ t = 1)
    (hsec : ∀ t ∈ Icc (0 : ℝ) b, ∀ v w : TangentSpace I (γ t),
      MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection (γ t) v w
        ≤ (1 / R) ^ 2) :
    ¬ MorganTianLib.IsConjugatePointAt (I := I) g γ b := by
  have hRinv : 0 < 1 / R := one_div_pos.mpr hR
  have hsqrt : Real.sqrt ((1 / R) ^ 2) = 1 / R := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hRinv]
  have hsqrt_short : Real.sqrt ((1 / R) ^ 2) * b < Real.pi := by
    rw [hsqrt]
    calc
      1 / R * b = b / R := by ring
      _ < Real.pi := (div_lt_iff₀ hR).2 hshort
  exact conjugatePointComparisonI hb hgeo hγc hunit hsec
    (Or.inr ⟨sq_pos_of_pos hRinv, hsqrt_short⟩)

end LeeLib.Ch11

end
