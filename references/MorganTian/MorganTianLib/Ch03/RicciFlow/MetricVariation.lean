import MorganTianLib.Ch03.RicciFlow.Basic

/-!
# Variations of Riemannian metrics

A metric variation records the time derivative of a family of Riemannian
metrics as a pointwise bilinear form. The derivative is taken within the time
set, so the same definition applies at endpoints of closed and half-open
intervals.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** `h` is the time derivative of the metric family `g` on `J`:
`h_t(x,y) = ∂_t(g_t(x,y))` for every pair of tangent vectors. -/
def IsMetricVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ (p : M) (x y : TangentSpace I p),
    HasDerivWithinAt (fun s => (g s).metricInner p x y) (h t p x y) J t

/-- **Math.** The Ricci flow equation says exactly that `-2 Ric(g_t)` is the
metric variation of `g`. -/
theorem isMetricVariationOn_neg_two_ricci_iff
    (g : ℝ → RiemannianMetric I M) (J : Set ℝ) :
    IsMetricVariationOn g
        (fun t p x y => -2 * ricciTensorAt (g t) p x y) J ↔
      IsRicciFlowEquationOn g J :=
  Iff.rfl

/-- **Math.** A Ricci flow has metric variation `-2 Ric(g_t)`. -/
theorem isMetricVariationOn_of_isRicciFlowOn {g : ℝ → RiemannianMetric I M}
    {J : Set ℝ} (hflow : IsRicciFlowOn g J) :
    IsMetricVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y) J :=
  hflow.equation

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A metric variation is unique at times where the time set has a
unique within-derivative. -/
theorem isMetricVariationOn_unique {g : ℝ → RiemannianMetric I M}
    {h h' : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) (hh' : IsMetricVariationOn g h' J) :
    ∀ t ∈ J, ∀ (p : M) (x y : TangentSpace I p),
      h t p x y = h' t p x y := by
  intro t ht p x y
  exact (hJ t ht).eq_deriv _ (hh t ht p x y) (hh' t ht p x y)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A metric variation is symmetric because it is the derivative of
a family of symmetric bilinear forms. -/
theorem isMetricVariationOn_symm {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) :
    ∀ t ∈ J, ∀ (p : M) (x y : TangentSpace I p),
      h t p x y = h t p y x := by
  intro t ht p x y
  have hxy := hh t ht p x y
  have hyx := hh t ht p y x
  have hcomm : (fun s => (g s).metricInner p y x) =
      fun s => (g s).metricInner p x y :=
    funext fun s => (g s).metricInner_comm p y x
  rw [hcomm] at hyx
  exact (hJ t ht).eq_deriv _ hxy hyx

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A metric variation is additive in its first tangent-vector slot. -/
theorem isMetricVariationOn_add_left {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) :
    ∀ t ∈ J, ∀ (p : M) (x x' y : TangentSpace I p),
      h t p (x + x') y = h t p x y + h t p x' y := by
  intro t ht p x x' y
  have htarget := hh t ht p (x + x') y
  have hsum := (hh t ht p x y).add (hh t ht p x' y)
  have hfun : (fun s => (g s).metricInner p (x + x') y) =
      fun s => (g s).metricInner p x y + (g s).metricInner p x' y :=
    funext fun s => (g s).metricInner_add_left p x x' y
  rw [hfun] at htarget
  exact (hJ t ht).eq_deriv _ htarget hsum

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A metric variation commutes with real scalar multiplication in
its first tangent-vector slot. -/
theorem isMetricVariationOn_smul_left {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) :
    ∀ t ∈ J, ∀ (p : M) (c : ℝ) (x y : TangentSpace I p),
      h t p (c • x) y = c * h t p x y := by
  intro t ht p c x y
  have htarget := hh t ht p (c • x) y
  have hscaled := (hh t ht p x y).const_mul c
  have hfun : (fun s => (g s).metricInner p (c • x) y) =
      fun s => c * (g s).metricInner p x y :=
    funext fun s => (g s).metricInner_smul_left p c x y
  rw [hfun] at htarget
  exact (hJ t ht).eq_deriv _ htarget hscaled

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A metric variation is additive in its second tangent-vector slot. -/
theorem isMetricVariationOn_add_right {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) :
    ∀ t ∈ J, ∀ (p : M) (x y y' : TangentSpace I p),
      h t p x (y + y') = h t p x y + h t p x y' := by
  intro t ht p x y y'
  have htarget := hh t ht p x (y + y')
  have hsum := (hh t ht p x y).add (hh t ht p x y')
  have hfun : (fun s => (g s).metricInner p x (y + y')) =
      fun s => (g s).metricInner p x y + (g s).metricInner p x y' :=
    funext fun s => (g s).metricInner_add_right p x y y'
  rw [hfun] at htarget
  exact (hJ t ht).eq_deriv _ htarget hsum

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A metric variation commutes with real scalar multiplication in
its second tangent-vector slot. -/
theorem isMetricVariationOn_smul_right {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) :
    ∀ t ∈ J, ∀ (p : M) (c : ℝ) (x y : TangentSpace I p),
      h t p x (c • y) = c * h t p x y := by
  intro t ht p c x y
  have htarget := hh t ht p x (c • y)
  have hscaled := (hh t ht p x y).const_mul c
  have hfun : (fun s => (g s).metricInner p x (c • y)) =
      fun s => c * (g s).metricInner p x y :=
    funext fun s => (g s).metricInner_smul_right p c x y
  rw [hfun] at htarget
  exact (hJ t ht).eq_deriv _ htarget hscaled

end MorganTianLib

end
