import MorganTianLib.Ch03.RicciFlow.ParabolicRescaling

/-!
# Morgan--Tian Ch. 3 - generalized-chart equation transport

The ordinary metric-family rescaling theorem is stated with the canonical
Ricci tensor.  Generalized Ricci-flow charts expose the same equation through
`spatialRicciTensorAt`; this module records the bridge explicitly so a future
transformed space-time chart can reuse the checked equation transport.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian TopologicalSpace

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

private abbrev SpatialModel (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable local instance (n : ℕ) [NeZero n] :
    NeZero (Module.finrank ℝ (SpatialModel n)) :=
  ⟨by simpa using (NeZero.out : n ≠ 0)⟩

/- The open chart domain is locally compact and sigma-compact as a subtype. -/
noncomputable local instance (n : ℕ) (U : Opens (SpatialModel n)) :
    LocallyCompactSpace U :=
  U.isOpen.locallyCompactSpace

noncomputable local instance (n : ℕ) (U : Opens (SpatialModel n)) :
    SigmaCompactSpace U :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

/-- **Math.** The generalized-chart Ricci equation is preserved by positive
affine time change together with constant metric scaling.  This is the
equation-level bridge needed by a future transformed `GeneralizedRicciFlow`
constructor; it does not assume or manufacture transformed space-time data. -/
theorem GeneralizedSpaceTimeLocalChart.isRicciFlowEquationOn_parabolicRescaledMetricFamily
    [NeZero n]
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    {g : ℝ → RiemannianMetric
      (modelWithCornersSelf ℝ (SpatialModel n)) (c.spatialOpens n)}
    (hflow : c.IsRicciFlowEquationOn n g)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    ∀ s ∈ parabolicTimeOrderIso Q hQ a '' c.timeSource,
      ∀ p : c.spatialOpens n,
      ∀ v w : TangentSpace (modelWithCornersSelf ℝ (SpatialModel n)) p,
      HasDerivWithinAt
        (fun u =>
          (parabolicRescaledMetricFamily g Q hQ a u).metricInner p v w)
        (-2 * spatialRicciTensorAt n (c.spatialOpens n)
          (parabolicRescaledMetricFamily g Q hQ a s) p v w)
        (parabolicTimeOrderIso Q hQ a '' c.timeSource) s := by
  letI : LocallyCompactSpace (c.spatialOpens n) :=
    c.spatialOpens n |>.isOpen.locallyCompactSpace
  letI : SigmaCompactSpace (c.spatialOpens n) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hordinary : MorganTianLib.IsRicciFlowEquationOn g c.timeSource := by
    intro t ht p v w
    have h := hflow t ht p v w
    rw [spatialRicciTensorAt_eq_ricciTensorAt] at h
    exact h
  have hscaled := MorganTianLib.isRicciFlowEquationOn_parabolicRescaledMetricFamily
    (I := modelWithCornersSelf ℝ (SpatialModel n))
    hordinary Q hQ a
  intro s hs p v w
  have h := hscaled s hs p v w
  simpa only [spatialRicciTensorAt_eq_ricciTensorAt] using h

end MorganTianLib

end
