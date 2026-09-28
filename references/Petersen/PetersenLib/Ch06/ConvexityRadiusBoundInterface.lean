import PetersenLib.Ch06.ComparisonInterfaces

/-!
# Petersen Ch. 6, §6.4 — convexity-radius lower-bound interface

The corollary after Theorem 6.4.8 (`cor:pet-ch6-convexity-radius-bound`) combines
three geometric bridges: Rauch supplies the radial second-derivative estimate,
Klingenberg turns exponential/segment-domain information into an injectivity
bound, and the definition of `convexityRadius` takes the supremum of the resulting
ball witnesses.  The first two bridges are not yet available in a global,
chart-free form in this project.

This file keeps those missing inputs explicit.  `ConvexityRadiusCriterionData` is
the exact certificate consumed by `convexityRadiusCriterion_of_secondDerivative`; its local theorem
therefore contributes a genuine `ofReal R` member to the defining supremum.
`KlingenbergConvexityRadiusData` packages the domain certificates consumed by
`klingenbergInjectivityEstimate_of_domainCertificates` together with the radial convexity certificate.
The resulting theorem returns both the pointwise/global injectivity estimate and
the corresponding global convexity-radius estimate.  It is intentionally a
conditional kernel, not a claim that the universal-cover, cut-locus, or Rauch
bridges have been proved.
-/

open Set
open scoped ENNReal Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-! ## The global injectivity-radius convention -/

/-- **Math.** The global injectivity radius, in the same `ℝ≥0∞` convention as
`globalConvexityRadius`: the infimum of the pointwise radii.  The Ch. 5 API
currently exposes only `injectivityRadius g p`, so this definition is the
chart-free global wrapper used by the conditional §6.4 interface. -/
def globalInjectivityRadius (g : RiemannianMetric I M) : ℝ≥0∞ :=
  ⨅ p : M, injectivityRadius (I := I) g p

/-! ## Certificates for the differential criterion -/

/-- The explicit data needed by `convexityRadiusCriterion_of_secondDerivative` at one point and one
real radius.  In applications `second` is the output of the Rauch/Hessian
comparison argument; it is not hidden in this structure. -/
structure ConvexityRadiusCriterionData
    (g : RiemannianMetric I M) (p : M) (R : ℝ) where
  positive : 0 < R
  segments : UniqueSegmentsInBall (I := I) g p R
  second : ∀ (γ : ℝ → M) (J : Set ℝ),
    Convex ℝ J →
    Geodesic.IsGeodesicOn (I := I) g γ J →
    Set.MapsTo γ J (metricBall (I := I) g p R) →
    (DifferentiableOn ℝ (fun t =>
        riemannianDistance (I := I) g p (γ t)) J ∧
     DifferentiableOn ℝ (deriv (fun t =>
        riemannianDistance (I := I) g p (γ t))) J ∧
     (∀ t ∈ J, 0 ≤ deriv^[2] (fun s =>
        riemannianDistance (I := I) g p (γ s)) t))

/-- A local convexity-radius witness obtained from the differential criterion.
This is the direct supremum step in Petersen's corollary. -/
theorem ofReal_le_convexityRadius_of_criterion
    (g : RiemannianMetric I M) (p : M) {R : ℝ}
    (D : ConvexityRadiusCriterionData (I := I) g p R) :
    ENNReal.ofReal R ≤ convexityRadius (I := I) g p := by
  exact le_sSup ⟨R, rfl,
    convexityRadiusCriterion_of_secondDerivative (I := I) g p D.positive D.segments D.second⟩

/-- Pointwise criterion certificates give the corresponding infimum lower bound
for the global convexity radius.  The radius function may vary with the base
point; this avoids silently assuming a uniform injectivity radius. -/
theorem globalConvexityRadius_ge_iInf_of_criterion
    (g : RiemannianMetric I M) (R : M → ℝ)
    (hD : ∀ p : M, ConvexityRadiusCriterionData (I := I) g p (R p)) :
    (⨅ p : M, ENNReal.ofReal (R p)) ≤ globalConvexityRadius (I := I) g := by
  unfold globalConvexityRadius
  apply iInf_mono
  intro p
  exact ofReal_le_convexityRadius_of_criterion (I := I) g p (hD p)

/-! ## Klingenberg's conditional composition -/

/-- Domain and convexity certificates for the radius used in the Klingenberg
argument.  `K` is the supplied upper-curvature model constant and `L` is the
supplied length certificate for the shortest-loop step.  The latter is exactly
the global input missing from the current chart-anchored Ch. 5 development. -/
structure KlingenbergConvexityRadiusData
    (g : RiemannianMetric I M) (K L : ℝ) where
  positiveK : 0 < K
  positiveL : 0 < L
  expCertificate : ∀ p : M, ∀ v : TangentSpace I p,
    g.metricInner p v v < (Real.pi / Real.sqrt K) ^ 2 →
      v ∈ expDomain (I := I) g p
  segmentCertificate : ∀ p : M, ∀ v : TangentSpace I p,
    g.metricInner p v v < (L / 2) ^ 2 →
      v ∈ segmentDomain (I := I) g p
  criterion : ∀ p : M,
    ConvexityRadiusCriterionData (I := I) g p
      ((min (Real.pi / Real.sqrt K) (L / 2)) / 2)

/-- Conditional kernel of Petersen's convexity-radius lower bound.

The first conjunct is Klingenberg's estimate at every base point.  The second
conjunct applies the differential convexity criterion to the half-radius and
takes the global infimum.  Supplying the domain and `criterion` fields is the
explicit placeholder for the missing Rauch, cut-locus, compactness, and
shortest-loop constructions; no such global theorem is asserted here. -/
theorem convexityRadius_lowerBound_of_klingenberg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] [T2Space M] [ConnectedSpace M]
    (g : RiemannianMetric I M) {K L : ℝ}
    (D : KlingenbergConvexityRadiusData (I := I) g K L) :
    (∀ p : M, ENNReal.ofReal (min (Real.pi / Real.sqrt K) (L / 2)) ≤
      injectivityRadius (I := I) g p) ∧
    ENNReal.ofReal ((min (Real.pi / Real.sqrt K) (L / 2)) / 2) ≤
      globalConvexityRadius (I := I) g := by
  have hinj : ∀ p : M,
      ENNReal.ofReal (min (Real.pi / Real.sqrt K) (L / 2)) ≤
        injectivityRadius (I := I) g p := by
    intro p
    exact klingenbergInjectivityEstimate_of_domainCertificates (I := I) g p D.positiveK D.positiveL
      (D.expCertificate p) (D.segmentCertificate p)
  refine ⟨hinj, ?_⟩
  unfold globalConvexityRadius
  apply le_iInf
  intro p
  exact ofReal_le_convexityRadius_of_criterion (I := I) g p (D.criterion p)

end PetersenLib

end
