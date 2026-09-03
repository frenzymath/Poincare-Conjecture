import MorganTianLib.Ch03.RicciFlow.GeneralizedScaling
import MorganTianLib.Ch03.RicciFlow.ExactSolutions

/-!
# Morgan--Tian Ch. 3 - ordinary parabolic rescaling

This module records the equation-level part of parabolic rescaling.  The
analytic existence and uniqueness theorem is deliberately not used: from an
existing Ricci-flow equation we transport the within-derivative through the
positive affine time order isomorphism and use the checked constant-metric
Ricci identity.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The ordinary metric family obtained by the positive parabolic
rescaling `s = Q t + a`, with a harmless definition on all real times. -/
def parabolicRescaledMetricFamily
    (g : ℝ → RiemannianMetric I M) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    ℝ → RiemannianMetric I M :=
  fun s => rescaledMetric (g ((s - a) / Q)) Q hQ

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem parabolicRescaledMetricFamily_metricInner
    (g : ℝ → RiemannianMetric I M) (Q : ℝ) (hQ : 0 < Q) (a s : ℝ)
    (p : M) (x y : TangentSpace I p) :
    (parabolicRescaledMetricFamily g Q hQ a s).metricInner p x y =
      Q * (g ((s - a) / Q)).metricInner p x y := by
  change (rescaledMetric (g ((s - a) / Q)) Q hQ).metricInner p x y = _
  exact rescaledMetric_metricInner (g ((s - a) / Q)) Q hQ p x y

private theorem parabolicRescaling_inverse_mapsTo
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (J : Set ℝ) :
    Set.MapsTo (fun s : ℝ => (s - a) / Q)
      (parabolicTimeOrderIso Q hQ a '' J) J := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  have hcancel : (Q * t + a - a) / Q = t := by
    field_simp [hQ.ne']
    ring
  change (Q * t + a - a) / Q ∈ J
  rw [hcancel]
  exact ht

/-- **Math.** A positive affine time change preserves the Ricci-flow equation
after the metric is multiplied by the same factor. -/
theorem isRicciFlowEquationOn_parabolicRescaledMetricFamily
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowEquationOn g J)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    IsRicciFlowEquationOn
      (parabolicRescaledMetricFamily g Q hQ a)
      (parabolicTimeOrderIso Q hQ a '' J) := by
  intro s hs p x y
  let t : ℝ := (s - a) / Q
  have ht : t ∈ J := by
    exact parabolicRescaling_inverse_mapsTo Q hQ a J hs
  have hst : parabolicTimeOrderIso Q hQ a t = s := by
    change Q * t + a = s
    dsimp [t]
    field_simp [hQ.ne']
    ring
  have hinv : HasDerivAt (fun u : ℝ => (u - a) / Q) (1 / Q) s := by
    simpa [id] using ((hasDerivAt_id s).sub_const a).div_const Q
  have hcomp := (hflow t ht p x y).comp s
    hinv.hasDerivWithinAt
    (parabolicRescaling_inverse_mapsTo Q hQ a J)
  have hscaled := HasDerivWithinAt.const_mul Q hcomp
  have hricci :
      ricciTensorAt (parabolicRescaledMetricFamily g Q hQ a s) p x y =
        ricciTensorAt (g t) p x y := by
    rw [parabolicRescaledMetricFamily, ricciTensorAt_rescaledMetric_eq]
  have hscaled' :
      HasDerivWithinAt
        (fun u => Q * ((g ((u - a) / Q)).metricInner p x y))
        (Q * ((-2 * ricciTensorAt (g t) p x y) * (1 / Q)))
        (parabolicTimeOrderIso Q hQ a '' J) s := by
    simpa only [Function.comp_apply] using hscaled
  have hmetric : ∀ u : ℝ,
      (parabolicRescaledMetricFamily g Q hQ a u).metricInner p x y =
        Q * (g ((u - a) / Q)).metricInner p x y := by
    intro u
    exact parabolicRescaledMetricFamily_metricInner g Q hQ a u p x y
  have htarget :
      Q * ((-2 * ricciTensorAt (g t) p x y) * (1 / Q)) =
        -2 * ricciTensorAt
          (parabolicRescaledMetricFamily g Q hQ a s) p x y := by
    rw [hricci]
    field_simp [hQ.ne']
  exact (hscaled'.congr (fun u _ => hmetric u) (hmetric s)).congr_deriv htarget

/-- **Math.** Package the transported interval and equation into a full Ricci-flow
structure once the rescaled metric section has been supplied as smooth.  The
smoothness field is explicit because `IsSmoothMetricFamilyOn` is a bundle-section
predicate and the current API does not yet expose its composition/scaling law. -/
theorem isRicciFlowOn_parabolicRescaledMetricFamily_of_smooth
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (hSmooth : IsSmoothMetricFamilyOn
      (parabolicRescaledMetricFamily g Q hQ a)
      (parabolicTimeOrderIso Q hQ a '' J)) :
    IsRicciFlowOn
      (parabolicRescaledMetricFamily g Q hQ a)
      (parabolicTimeOrderIso Q hQ a '' J) := by
  let e := parabolicTimeOrderIso Q hQ a
  have hord : (e '' J).OrdConnected := by
    refine ⟨?_⟩
    intro s hs t ht
    rcases hs with ⟨s', hs', rfl⟩
    rcases ht with ⟨t', ht', rfl⟩
    intro u hu
    have hu' : e.symm u ∈ Set.Icc s' t' := by
      constructor
      · simpa using (e.symm.map_rel_iff).2 hu.1
      · simpa using (e.symm.map_rel_iff).2 hu.2
    exact ⟨e.symm u, hflow.ordConnected.out hs' ht' hu', e.apply_symm_apply u⟩
  exact
    { ordConnected := by simpa [e] using hord
      nontrivial := by
        simpa [e] using hflow.nontrivial.image (parabolicTimeOrderIso Q hQ a).injective
      smooth := hSmooth
      equation := isRicciFlowEquationOn_parabolicRescaledMetricFamily hflow.equation Q hQ a }

/-- **Math.** A transformed time has its source time in the original flow
interval; this is the inverse-time compatibility needed for parabolic
neighborhood restrictions. -/
theorem parabolicRescaledMetricFamily_sourceTime_mem
    {J : Set ℝ} {s : ℝ} (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (hs : s ∈ parabolicTimeOrderIso Q hQ a '' J) :
    (s - a) / Q ∈ J := by
  exact parabolicRescaling_inverse_mapsTo Q hQ a J hs

end MorganTianLib

end
