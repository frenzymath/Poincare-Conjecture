import PetersenLib.Ch06.BonnetSyngeIntrinsic

/-!
# Petersen Ch. 6, Section 6.3 — intrinsic Bonnet--Synge distance consequence

`BonnetSyngeIntrinsic.lean` constructs the smooth sine variation and proves that its
second variation is strictly negative.  The generic distance bridge in
`DiameterBound.lean` still accepts the variation certificate explicitly.  This
module composes the two results, so callers with a unit-speed geodesic and a
sectional lower bound no longer need to rebuild that certificate.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval Real

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [LocallyCompactSpace M]
  [T2Space (TangentBundle I M)] [ConnectedSpace M]

/-- **Math.** Intrinsic Bonnet--Synge distance estimate.  A unit-speed geodesic
of length `l > π / √k` on a manifold with `sec ≥ k > 0` has endpoints at
Riemannian distance strictly less than `l`.  The smooth proper variation and
its negative second variation are supplied internally by
`bonnetSynge_longGeodesicsNotMinimizing_of_secLowerBound`; the theorem is the
resulting callback-free form of the §6.3.1 variational obstruction.
-/
theorem bonnetSynge_distance_lt_of_secLowerBound
    (g : RiemannianMetric I M) {σ : ℝ → M} {l k : ℝ}
    (hk : 0 < k) (hlk : π / Real.sqrt k < l)
    (hσc : Continuous σ) (hσgeo : Geodesic.IsGeodesic (I := I) g σ)
    (hspeed : ∀ t, g.metricInner (σ t) (curveVelocity (I := I) σ t)
      (curveVelocity (I := I) σ t) = 1)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hsec : HasSecBoundedBelow g.leviCivita k) :
    riemannianDistance (I := I) g (σ 0) (σ l) < l := by
  obtain ⟨f, δ, a, b, hδ, hsub, hf, hbase, hfix₀, hfixl, hneg, _hnotMin⟩ :=
    bonnetSynge_longGeodesicsNotMinimizing_of_secLowerBound (I := I) g hk hlk
      hσc hσgeo hspeed hdim hsec
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos hsk) hlk
  have hspeed' : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (curveVelocity (I := I) (f 0) t)
        (curveVelocity (I := I) (f 0) t) = 1 := by
    intro t ht
    rw [hbase]
    exact hspeed t
  have hlt := riemannianDistance_lt_of_negSecondVar_unitSpeed_on_segment
    (I := I) g hl hδ hsub hf hfix₀ hfixl hspeed' hneg
  rwa [hbase] at hlt

end PetersenLib

end
