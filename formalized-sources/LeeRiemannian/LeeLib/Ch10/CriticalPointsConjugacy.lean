import LeeLib.Ch02.Distance
import DoCarmoLib.Riemannian.Jacobi.CartanMFDerivBridge

/-!
# Lee Chapter 10: critical points and conjugate points

Lee's Proposition 10.20 identifies the critical points of the exponential map
with conjugate points.  The shared Riemannian engine expresses the exponential
map globally on a complete manifold and represents its differential by `mfderiv`.
The theorem below is the corresponding Lee-facing statement: a point is
critical exactly when that differential is not injective, and this is equivalent
to conjugacy at parameter `1` along the radial geodesic.

The `CompleteSpace` argument is explicit because the global exponential encoding
is used here; on the restricted exponential domain this is precisely the
``v ∈ \xi_p`` hypothesis in Lee's statement.
-/

noncomputable section

namespace LeeLib.Ch10

open Manifold
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T3Space M] [ConnectedSpace M] [I.Boundaryless]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]

private theorem leeMetric_isRiemannianDist
    (g : LeeLib.Ch02.RiemannianMetric I M) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    Riemannian.RiemannianMetric.IsRiemannianDist g := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ⟨fun _ _ ↦ rfl⟩

/-- **Math.** **Critical points and conjugacy (Lee, Proposition 10.20).**

For a complete Riemannian manifold, `v` is a critical point of the exponential
map at `p` exactly when `exp_p(v)` is conjugate to `p` along the radial geodesic
`t ↦ exp_p(tv)`.  In the manifold calculus API, criticality is the failure of
injectivity of the intrinsic differential `mfderiv`.

The theorem uses the global exponential map, so `CompleteSpace M` is passed
explicitly; this is the global form of Lee's restricted-domain hypothesis
`v ∈ ξ_p`.

Blueprint: `prop:critical-points-conjugate`. -/
theorem criticalPoints_conjugate
    (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) :
    letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
    ∀ _hcomplete : CompleteSpace M, ∀ v : E,
      (¬ Function.Injective
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E =>
            Riemannian.Exponential.expMapGlobal (I := I)
              g (leeMetric_isRiemannianDist g) p w) v)) ↔
        Riemannian.Jacobi.IsConjugatePointAt (I := I) g
          (Riemannian.Geodesic.globalGeodesic (I := I) g
            (leeMetric_isRiemannianDist g) p v) 1 := by
  letI : MetricSpace M := LeeLib.Ch02.RiemannianMetric.toMetricSpace g
  intro hcomplete
  letI : CompleteSpace M := hcomplete
  intro v
  let hg : Riemannian.RiemannianMetric.IsRiemannianDist g :=
    leeMetric_isRiemannianDist g
  constructor
  · intro hcritical
    by_contra hnotconj
    have hlocal :=
      (Riemannian.Jacobi.isLocalDiffeomorphAt_expMapGlobal_iff_not_isConjugatePointAt
        (I := I) g hg p).2 hnotconj
    have hinj : Function.Injective
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => Riemannian.Exponential.expMapGlobal (I := I) g hg p w) v) := by
      have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
      have hcoe := hlocal.mfderivToContinuousLinearEquiv_coe (n := ∞) hn
      rw [← hcoe]
      exact (hlocal.mfderivToContinuousLinearEquiv (n := ∞) hn).injective
    exact hcritical hinj
  · intro hconj hinj
    exact (Riemannian.Jacobi.not_isConjugatePointAt_globalGeodesic_of_injective_mfderiv
      (I := I) g hg p hinj) hconj

end LeeLib.Ch10

end
