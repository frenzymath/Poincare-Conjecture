import PetersenLib.Ch06.SpaceFormConjugate
import PetersenLib.Ch06.IndexJacobiBoundary
import PetersenLib.Ch06.ConvexityRadius
import PetersenLib.Ch05.InjectivityRadiusCutLocus
import Mathlib.Analysis.Convex.Deriv

/-!
# Petersen Ch. 6, Section 6.4 comparison interfaces

This module records the strongest chart-free interfaces currently supplied by
the Ch. 5--6 infrastructure for the two geometric comparison steps that are
still missing from the blueprint-level development.

The declarations are deliberately conditional.  In particular, the existing
`expMap` is chart-anchored, while Klingenberg's and Petersen's statements use
the maximal geodesic domain.  We therefore expose the exponential-domain and
segment-domain certificates as hypotheses instead of silently identifying them.
Likewise, the convexity criterion below takes the radial second-derivative
certificate produced by a Rauch/Hessian argument and derives the convexity
conclusion with the one-dimensional convexity theorem.  These interfaces are
useful consumers without claiming that the missing geometric bridges have
already been proved.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

/-! ## The nonpositive model has no positive conjugate zero -/

/-- **Math.** Petersen Section 6.4, remark on nonpositive curvature (analytic
core).  For `K <= 0`, the model Jacobi coefficient `sn_K` is positive on every
positive time, hence has no positive zero.  The manifold statement that this
implies an infinite injectivity radius additionally needs the Cartan--Hadamard
and cut-locus bridges, which are intentionally not hidden in this theorem. -/
theorem snFunction_noPositiveZero_nonpositiveCurvature {K : ℝ} (hK : K ≤ 0) :
    ∀ t : ℝ, 0 < t → snFunction K t ≠ 0 := by
  intro t ht
  exact snFunction_ne_zero_of_nonpos hK ht

/-! ## Index-form version of the Jacobi identity -/

/-- **Math.** Petersen's index-form route to Rauch comparison, in the form of
the Jacobi boundary identity.  For a Jacobi field with the regularity needed by
the chart-free product rule, the index-form integrand integrates to
`g(J(b), J'(b)) - g(J(0), J'(0))`.  The usual Dirichlet case is obtained by
adding `J 0 = 0`; the identity is the concrete analytic step used by the
index-form proof, while the comparison argument remains a separate bridge. -/
theorem rauchComparisonViaIndexForm_jacobiBoundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
    (g : RiemannianMetric I M) {c : ℝ → M}
    {J : ∀ t, TangentSpace I (c t)}
    (hJ : IsJacobiFieldAlong g c J)
    (hc : ∀ t, ContinuousAt c t)
    (hu : ∀ t, DifferentiableAt ℝ (fun τ => extChartAt I (c t) (c τ)) t)
    (hJd : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) J) t)
    (hDJd : ∀ t, DifferentiableAt ℝ
      (chartFieldRep c (c t) (derivAlongCurve g c J)) t)
    (hG : ∀ t, ∀ i j, DifferentiableAt ℝ (chartGramOnE g (c t) i j)
      (extChartAt I (c t) (c t)))
    (hint : IntervalIntegrable (fun t =>
      g.metricInner (c t) (derivAlongCurve g c J t) (derivAlongCurve g c J t)
      - g.metricInner (c t)
          (curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
            (J t) (curveVelocity c t) (curveVelocity c t)) (J t)) volume 0 1)
    (hJ0 : J 0 = 0) :
    indexForm (I := I) g c J J
      = g.metricInner (c 1) (J 1) (derivAlongCurve g c J 1) := by
  have hboundary := indexForm_jacobi_eq_boundary (I := I) g hJ hc hu hJd hDJd hG hint
    (b := (1 : ℝ))
  rw [indexForm]
  simpa [hJ0] using hboundary

/-! ## Klingenberg's lower-bound kernel -/

/-- **Math.** Petersen Lemma 6.4.7, conditional radius form.  Assume that the
exponential map is defined on the ball of radius `pi/sqrt K` (the conjugate
radius certificate) and that every vector of norm below half the supplied loop
length lies in the segment domain.  Then the injectivity radius is at least
the minimum of those two radii.

The hypotheses are the two geometric certificates used in Klingenberg's
argument.  They are intentionally stated over the existing chart-anchored
`expDomain` and intrinsic `segmentDomain`; proving the certificates from the
Rauch theorem and a shortest-loop construction is separate work. -/
theorem klingenbergInjectivityEstimate_of_domainCertificates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] [T2Space M] [ConnectedSpace M]
    (g : RiemannianMetric I M) (p : M) {K L : ℝ}
    (hK : 0 < K) (hL : 0 < L)
    (hconj : ∀ v : TangentSpace I p,
      g.metricInner p v v < (Real.pi / Real.sqrt K) ^ 2 →
        v ∈ expDomain (I := I) g p)
    (hloop : ∀ v : TangentSpace I p,
      g.metricInner p v v < (L / 2) ^ 2 →
        v ∈ segmentDomain (I := I) g p) :
    ENNReal.ofReal (min (Real.pi / Real.sqrt K) (L / 2))
      ≤ injectivityRadius (I := I) g p := by
  have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hconjRadius : 0 < Real.pi / Real.sqrt K :=
    div_pos Real.pi_pos hsqrtK
  have hhalfLoop : 0 < L / 2 := by linarith
  let δ : ℝ := min (Real.pi / Real.sqrt K) (L / 2)
  have hδ : 0 < δ := (lt_min_iff.mpr ⟨hconjRadius, hhalfLoop⟩)
  have hδK : δ ≤ Real.pi / Real.sqrt K := min_le_left _ _
  have hδL : δ ≤ L / 2 := min_le_right _ _
  have hδKsq : δ ^ 2 ≤ (Real.pi / Real.sqrt K) ^ 2 := by
    nlinarith [hδ, hδK]
  have hδLsq : δ ^ 2 ≤ (L / 2) ^ 2 := by
    nlinarith [hδ, hδL]
  have hdom : ∀ v : TangentSpace I p, g.metricInner p v v < δ ^ 2 →
      v ∈ expDomain (I := I) g p := by
    intro v hv
    exact hconj v (lt_of_lt_of_le hv hδKsq)
  have hseg : ∀ v : TangentSpace I p, g.metricInner p v v < δ ^ 2 →
      v ∈ segmentDomain (I := I) g p := by
    intro v hv
    exact hloop v (lt_of_lt_of_le hv hδLsq)
  exact ofReal_le_injectivityRadius_of_gBall_subset_segmentDomain
    (I := I) g p hδ hdom hseg

/-! ## A differential convexity criterion -/

/-- **Math.** Petersen Theorem 6.4.8, differential core.  If the supplied
Rauch/Hessian bridge gives a nonnegative second derivative for the radial
distance along every geodesic in the ball, and the segment certificate gives
existence and uniqueness there, then the ball is a convexity-radius witness.

The one-dimensional conclusion is obtained from
`convexOn_of_deriv2_nonneg'`; no convexity conclusion is assumed.  The missing
geometric work is precisely the production of the derivative certificate and
the segment certificate from the injectivity and curvature bounds in Petersen's
statement. -/
theorem convexityRadiusCriterion_of_secondDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    (g : RiemannianMetric I M) (p : M) {R : ℝ} (hR : 0 < R)
    (hsegments : UniqueSegmentsInBall (I := I) g p R)
    (hsecond : ∀ (γ : ℝ → M) (J : Set ℝ),
      Convex ℝ J →
      Geodesic.IsGeodesicOn (I := I) g γ J →
      Set.MapsTo γ J (metricBall (I := I) g p R) →
      (DifferentiableOn ℝ (fun t =>
          riemannianDistance (I := I) g p (γ t)) J ∧
       DifferentiableOn ℝ (deriv (fun t =>
          riemannianDistance (I := I) g p (γ t))) J ∧
       (∀ t ∈ J, 0 ≤ deriv^[2] (fun s =>
          riemannianDistance (I := I) g p (γ s)) t))) :
    IsConvexityRadiusWitness (I := I) g p R := by
  refine ⟨hR, ?_, hsegments⟩
  intro γ J hJ hγ hmap
  obtain ⟨h₁, h₂, h₃⟩ := hsecond γ J hJ hγ hmap
  exact convexOn_of_deriv2_nonneg' hJ h₁ h₂ h₃

end PetersenLib

end
