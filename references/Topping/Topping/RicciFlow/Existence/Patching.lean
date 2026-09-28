import Topping.RicciFlow.Existence.FlowIntervals
import MorganTianLib.Ch03.RicciFlow.EndpointPatching
import MorganTianLib.Ch03.RicciFlow.EndpointLocalGerm
import MorganTianLib.Ch03.RicciFlow.SmoothPatchingFlow

/-!
# Chapter 5 restart and smooth patching interface

The endpoint argument in Chapter 5 restarts a flow at a limiting metric and
then identifies the restarted piece with the old one.  Morgan--Tian's
patching theorem supplies the equation-level gluing step once smoothness and
the two coefficient limits are proved.  This file exposes that theorem in the
Topping existence namespace, while keeping every analytic hypothesis explicit.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A smooth endpoint extension of the horizontal metric sections
supplies the smoothness field required by the patched-family Ricci-flow
consumer. -/
theorem isSmoothMetricFamilyOn_patchedMetricFamily_of_endpointExtension
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {gLeft gRight : ℝ → RiemannianMetric I M}
    (h : MorganTianLib.SmoothEndpointExtension
      (I := I) (a := a) (b := b) (c := c) gLeft gRight) :
    MorganTianLib.IsSmoothMetricFamilyOn
      (MorganTianLib.patchedMetricFamily b gLeft gRight) (Ico a c) :=
  MorganTianLib.smoothMetricFamilyOn_patchedMetricFamily_of_extension hab hbc h

/-- **Math.** A genuine Ricci flow restricts to any nontrivial
order-connected subinterval.  This is the basic time-domain producer used
when a restarted solution is compared on an overlap. -/
theorem isRicciFlowOn_mono
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g K)
    (hJK : J ⊆ K) (hJord : J.OrdConnected) (hJnontrivial : J.Nontrivial) :
    MorganTianLib.IsRicciFlowOn g J := by
  refine
    { ordConnected := hJord
      nontrivial := hJnontrivial
      smooth := hflow.smooth.mono (Set.prod_mono subset_rfl hJK)
      equation := ?_ }
  intro t ht p x y
  exact (hflow.equation t (hJK ht) p x y).mono hJK

/-- **Math.** Two smooth Ricci-flow pieces patch to a genuine Ricci flow on
their union interval when the patched metric is smooth and the left metric
and Ricci coefficients converge to the right endpoint. -/
theorem isRicciFlowOn_patchedMetricFamily
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (gLeft gRight : ℝ → RiemannianMetric I M)
    (hLeft : MorganTianLib.IsRicciFlowOn gLeft (Ico a b))
    (hRight : MorganTianLib.IsRicciFlowOn gRight (Ico b c))
    (hSmooth : MorganTianLib.IsSmoothMetricFamilyOn
      (MorganTianLib.patchedMetricFamily b gLeft gRight) (Ico a c))
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x y) (𝓝[Ioo a b] b)
        (𝓝 ((gRight b).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gLeft t) p x y) (𝓝[Ioo a b] b)
        (𝓝 (ricciTensorAt (gRight b) p x y))) :
    MorganTianLib.IsRicciFlowOn
      (MorganTianLib.patchedMetricFamily b gLeft gRight) (Ico a c) := by
  exact MorganTianLib.isRicciFlowOn_patchedMetricFamily_of_smooth
    hab hbc gLeft gRight hLeft hRight hSmooth hMetric hRicci

/-- **Math.** A local smooth endpoint germ, the two side Ricci-flow pieces, and
the endpoint coefficient limits assemble the joined Ricci flow.  The local
germ is the genuine smoothness input; this adapter does not infer it from
bounded curvature or from pointwise coefficient limits. -/
theorem isRicciFlowOn_patchedMetricFamily_of_localEndpointGerm
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {gLeft gRight : ℝ → RiemannianMetric I M}
    (hLeft : MorganTianLib.IsRicciFlowOn gLeft (Ico a b))
    (hRight : MorganTianLib.IsRicciFlowOn gRight (Ico b c))
    (hGerm : MorganTianLib.LocalSmoothEndpointGerm
      (I := I) (a := a) (b := b) (c := c) gLeft gRight)
    (hLimits : MorganTianLib.EndpointCoefficientLimits a b gLeft gRight) :
    MorganTianLib.IsRicciFlowOn
      (MorganTianLib.patchedMetricFamily b gLeft gRight) (Ico a c) := by
  apply isRicciFlowOn_patchedMetricFamily hab hbc gLeft gRight hLeft hRight
  · exact MorganTianLib.smoothMetricFamilyOn_patchedMetricFamily_of_local_germ
      hab hbc hGerm
  · exact hLimits.metric
  · exact hLimits.ricci

/-- **Math.** Endpoint coefficient limits stated on the natural left-neighbourhood
filter assemble the patched Ricci flow after rewriting that filter as the
interior approach to the joining time. -/
theorem isRicciFlowOn_patchedMetricFamily_of_endpoint_limits
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (gLeft gRight : ℝ → RiemannianMetric I M)
    (hLeft : MorganTianLib.IsRicciFlowOn gLeft (Ico a b))
    (hRight : MorganTianLib.IsRicciFlowOn gRight (Ico b c))
    (hSmooth : MorganTianLib.IsSmoothMetricFamilyOn
      (MorganTianLib.patchedMetricFamily b gLeft gRight) (Ico a c))
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x y)
        (nhdsWithin b (Iio b))
        (𝓝 ((gRight b).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gLeft t) p x y)
        (nhdsWithin b (Iio b))
        (𝓝 (ricciTensorAt (gRight b) p x y))) :
    MorganTianLib.IsRicciFlowOn
      (MorganTianLib.patchedMetricFamily b gLeft gRight) (Ico a c) := by
  apply isRicciFlowOn_patchedMetricFamily hab hbc gLeft gRight hLeft hRight hSmooth
  · intro p x y
    rw [nhdsWithin_Ioo_eq_nhdsLT hab]
    exact hMetric p x y
  · intro p x y
    rw [nhdsWithin_Ioo_eq_nhdsLT hab]
    exact hRicci p x y

/-- **Math.** The patched family agrees with the left flow on its old half-open
interval.  This is the equality needed by `ExtendsRicciFlowOn` in a restart
argument. -/
theorem patchedMetricFamily_agrees_left
    {a b c : ℝ} (_hab : a < b) (_hbc : b < c)
    (gLeft gRight : ℝ → RiemannianMetric I M) :
    ∀ t ∈ Ico a b,
      MorganTianLib.patchedMetricFamily b gLeft gRight t = gLeft t := by
  intro t ht
  exact MorganTianLib.patchedMetricFamily_of_lt b gLeft gRight ht.2

/-- **Math.** The patched family agrees with the restarted right flow from the joining
time onward. -/
theorem patchedMetricFamily_agrees_right
    {a b c : ℝ} (_hab : a < b) (_hbc : b < c)
    (gLeft gRight : ℝ → RiemannianMetric I M) :
    ∀ t ∈ Ico b c,
      MorganTianLib.patchedMetricFamily b gLeft gRight t = gRight t := by
  intro t ht
  exact MorganTianLib.patchedMetricFamily_of_le b gLeft gRight ht.1

/-- **Math.** The patched flow is an extension of the left-hand flow in the precise
`ExtendsRicciFlowOn` sense used by maximality arguments. -/
theorem patchedMetricFamily_extends_left
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (gLeft gRight : ℝ → RiemannianMetric I M)
    (hLeft : MorganTianLib.IsRicciFlowOn gLeft (Ico a b))
    (hRight : MorganTianLib.IsRicciFlowOn gRight (Ico b c))
    (hSmooth : MorganTianLib.IsSmoothMetricFamilyOn
      (MorganTianLib.patchedMetricFamily b gLeft gRight) (Ico a c))
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x y) (𝓝[Ioo a b] b)
        (𝓝 ((gRight b).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gLeft t) p x y) (𝓝[Ioo a b] b)
        (𝓝 (ricciTensorAt (gRight b) p x y))) :
    ExtendsRicciFlowOn gLeft (Ico a b)
      (MorganTianLib.patchedMetricFamily b gLeft gRight) (Ico a c) := by
  refine ⟨?_, isRicciFlowOn_patchedMetricFamily hab hbc gLeft gRight
    hLeft hRight hSmooth hMetric hRicci, ?_⟩
  · intro t ht
    exact ⟨ht.1, lt_trans ht.2 hbc⟩
  · exact patchedMetricFamily_agrees_left hab hbc gLeft gRight

/-- **Math.** The same patching construction contains the restarted right-hand flow as
the post-join subinterval. -/
theorem patchedMetricFamily_extends_right
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (gLeft gRight : ℝ → RiemannianMetric I M)
    (hLeft : MorganTianLib.IsRicciFlowOn gLeft (Ico a b))
    (hRight : MorganTianLib.IsRicciFlowOn gRight (Ico b c))
    (hSmooth : MorganTianLib.IsSmoothMetricFamilyOn
      (MorganTianLib.patchedMetricFamily b gLeft gRight) (Ico a c))
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x y) (𝓝[Ioo a b] b)
        (𝓝 ((gRight b).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gLeft t) p x y) (𝓝[Ioo a b] b)
        (𝓝 (ricciTensorAt (gRight b) p x y))) :
    ExtendsRicciFlowOn gRight (Ico b c)
      (MorganTianLib.patchedMetricFamily b gLeft gRight) (Ico a c) := by
  refine ⟨?_, isRicciFlowOn_patchedMetricFamily hab hbc gLeft gRight
    hLeft hRight hSmooth hMetric hRicci, ?_⟩
  · intro t ht
    exact ⟨(le_of_lt hab).trans ht.1, ht.2⟩
  · exact patchedMetricFamily_agrees_right hab hbc gLeft gRight

/-! ## Maximality consumer -/

/-- **Math.** An actual smooth endpoint extension together with an explicitly
restarted right-hand flow and the coefficient-limit data produces a longer
flow, so it is incompatible with forward maximality.  The theorem leaves the
short-time existence and endpoint-regularity producers as its named inputs. -/
theorem not_isMaximalForwardRicciFlowOn_of_endpoint_restart
    {T epsilon : ℝ}
    {g gBar gRight : ℝ → RiemannianMetric I M}
    (hBar : MorganTianLib.IsRicciFlowOn gBar (Icc 0 T))
    (hAgree : ∀ t ∈ Ico 0 T, gBar t = g t)
    (hepsilon : 0 < epsilon)
    (hRight : MorganTianLib.IsRicciFlowOn gRight (Ico T (T + epsilon)))
    (hSmooth : MorganTianLib.IsSmoothMetricFamilyOn
      (MorganTianLib.patchedMetricFamily T gBar gRight)
      (Ico 0 (T + epsilon)))
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gBar t).metricInner p x y) (𝓝[Ioo 0 T] T)
        (𝓝 ((gRight T).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gBar t) p x y) (𝓝[Ioo 0 T] T)
        (𝓝 (ricciTensorAt (gRight T) p x y))) :
    ¬ IsMaximalForwardRicciFlowOn g T := by
  intro hmax
  have hT : 0 < T := hmax.1
  have hIcoNontrivial : (Ico (0 : ℝ) T).Nontrivial := by
    apply nontrivial_of_mem_mem_ne
      (show (0 : ℝ) ∈ Ico 0 T from ⟨le_rfl, hT⟩)
      (show T / 2 ∈ Ico 0 T by constructor <;> linarith)
      (by linarith)
  have hLeft : MorganTianLib.IsRicciFlowOn gBar (Ico 0 T) :=
    isRicciFlowOn_mono hBar
      (show Ico (0 : ℝ) T ⊆ Icc 0 T by
        intro t ht
        exact ⟨ht.1, le_of_lt ht.2⟩)
      ordConnected_Ico hIcoNontrivial
  have hPatched := patchedMetricFamily_extends_left
    (a := (0 : ℝ)) (b := T) (c := T + epsilon)
    (by linarith) (by linarith) gBar gRight hLeft hRight hSmooth hMetric hRicci
  have hLongSubset : Ico (0 : ℝ) T ⊆ Ico 0 (T + epsilon) := by
    intro t ht
    exact ⟨ht.1, lt_trans ht.2 (by linarith [hepsilon])⟩
  exact hmax.2.2 ⟨epsilon, hepsilon,
    MorganTianLib.patchedMetricFamily T gBar gRight,
    ⟨hLongSubset, hPatched.2.1, fun t ht => by
      calc
        MorganTianLib.patchedMetricFamily T gBar gRight t = gBar t :=
          hPatched.2.2 t ht
        _ = g t := hAgree t ht⟩⟩

#print axioms isRicciFlowOn_patchedMetricFamily
#print axioms patchedMetricFamily_agrees_left
#print axioms patchedMetricFamily_agrees_right
#print axioms patchedMetricFamily_extends_left
#print axioms patchedMetricFamily_extends_right
#print axioms not_isMaximalForwardRicciFlowOn_of_endpoint_restart

end Topping

end
