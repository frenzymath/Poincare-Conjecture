import MorganTianLib.Ch03.RicciFlow.Basic
import MorganTianLib.Ch03.RicciFlow.CurvatureCoordinateVariation
import MorganTianLib.Ch01.ManifoldCurvature
import MorganTianLib.Ch01.MetricRescaling

/-!
# Morgan--Tian Ch. 3 -- exact Einstein scalings

This file records the reusable calculation behind the exact solutions in
`ex:einstein-ricci-flow`: an Einstein metric remains Einstein under constant
positive rescaling, and a linearly scaled family satisfies the Ricci-flow
equation whenever its scale stays positive.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Einstein condition in the bundled Ricci-flow interface. -/
def IsEinsteinTensor (g : RiemannianMetric I M) (lam : ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace I p),
    ricciTensorAt g p v w = lam * g.metricInner p v w

/-- **Math.** The affine scale of the Einstein Ricci-flow solution. -/
def einsteinScale (lam t : ℝ) : ℝ := 1 - 2 * lam * t

@[simp] theorem einsteinScale_zero (lam : ℝ) : einsteinScale lam 0 = 1 := by
  simp [einsteinScale]

/-- **Math.** A positive Einstein constant gives precisely the shrinking
lifespan `t < (2 λ)⁻¹`. -/
theorem einsteinScale_pos_iff_of_pos {lam t : ℝ} (hlam : 0 < lam) :
    0 < einsteinScale lam t ↔ t < (2 * lam)⁻¹ := by
  rw [einsteinScale, inv_eq_one_div]
  constructor <;> intro h
  · apply (lt_div_iff₀ (by positivity : 0 < 2 * lam)).2
    nlinarith
  · have := (lt_div_iff₀ (by positivity : 0 < 2 * lam)).1 h
    nlinarith

/-- **Math.** The Ricci-flat Einstein scale is steady. -/
@[simp] theorem einsteinScale_zero_lambda (t : ℝ) : einsteinScale 0 t = 1 := by
  simp [einsteinScale]

/-- **Math.** A negative Einstein constant gives an expanding positive scale
for every nonnegative time. -/
theorem einsteinScale_pos_of_neg_of_nonneg {lam t : ℝ}
    (hlam : lam < 0) (ht : 0 ≤ t) : 0 < einsteinScale lam t := by
  unfold einsteinScale
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
    (by norm_num : (0 : ℝ) ≤ 2) hlam.le) ht]

/-- **Math.** The canonical Einstein scale has derivative `-2 * lam`. -/
theorem hasDerivAt_einsteinScale (lam t : ℝ) :
    HasDerivAt (einsteinScale lam) (-2 * lam) t := by
  have h := (hasDerivAt_const_mul (x := t) (2 * lam)).const_sub (1 : ℝ)
  change HasDerivAt (fun s : ℝ => 1 - 2 * lam * s) (-2 * lam) t
  simpa only [sub_eq_add_neg, einsteinScale, Pi.add_apply, Pi.neg_apply,
    neg_mul, mul_one, zero_sub] using h

omit [I.Boundaryless] in
private theorem canonicalLC_exactSolutions (g : RiemannianMetric I M) :
    g.leviCivitaConnection.IsLeviCivita g :=
  g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)

/-- **Math.** Positive constant metric rescaling leaves the canonical Ricci
tensor unchanged as a `(0,2)` tensor. -/
theorem ricciTensorAt_rescaledMetric_eq
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (p : M) (v w : TangentSpace I p) :
    ricciTensorAt (rescaledMetric g c hc) p v w = ricciTensorAt g p v w := by
  rw [← ricciAt_leviCivita_eq_ricciTensorAt
      (rescaledMetric g c hc) (canonicalLC_exactSolutions (rescaledMetric g c hc)) p v w,
    ← ricciAt_leviCivita_eq_ricciTensorAt g (canonicalLC_exactSolutions g) p v w]
  exact rescaledMetric_ricciAt g c hc (canonicalLC_exactSolutions g)
    (canonicalLC_exactSolutions (rescaledMetric g c hc)) p v w

/-- **Math.** A positive scale `u(t)` with derivative `u' = -2 λ` produces a
Ricci-flow equation from an Einstein metric of constant `λ`. -/
theorem isRicciFlowEquationOn_einsteinScale
    (g₀ : RiemannianMetric I M) (J : Set ℝ) (lam : ℝ)
    (u : ℝ → ℝ) (hu : ∀ t, 0 < u t)
    (hu' : ∀ t, HasDerivAt u (-2 * lam) t)
    (hE : IsEinsteinTensor g₀ lam) :
    IsRicciFlowEquationOn
      (fun t => rescaledMetric g₀ (u t) (hu t)) J := by
  intro t ht p x y
  have hderiv : HasDerivAt
      (fun s => (rescaledMetric g₀ (u s) (hu s)).metricInner p x y)
      ((-2 * lam) * g₀.metricInner p x y) t := by
    simp_rw [rescaledMetric_metricInner]
    convert (hu' t).mul_const (g₀.metricInner p x y) using 1
  have hRicci := ricciTensorAt_rescaledMetric_eq g₀ (u t) (hu t) p x y
  have hEinstein := hE p x y
  rw [hRicci, hEinstein]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hderiv.hasDerivWithinAt

/-- **Math.** Extend the affine Einstein scale away from its intended time set
by the constant scale one.  Values outside the time set are bookkeeping only. -/
noncomputable def einsteinScaleExtension (J : Set ℝ) (lam : ℝ)
    (_hpos : ∀ t ∈ J, 0 < einsteinScale lam t) (t : ℝ) : ℝ :=
  by
    classical
    exact if ht : t ∈ J then einsteinScale lam t else 1

/-- **Math.** The bookkeeping extension is positive at every time. -/
theorem einsteinScaleExtension_pos (J : Set ℝ) (lam : ℝ)
    (hpos : ∀ t ∈ J, 0 < einsteinScale lam t) (t : ℝ) :
    0 < einsteinScaleExtension J lam hpos t := by
  classical
  by_cases ht : t ∈ J
  · simp [einsteinScaleExtension, ht, hpos t ht]
  · simp [einsteinScaleExtension, ht]

/-- **Math.** On its intended time set, the bookkeeping extension has the
same within-derivative as the affine Einstein scale. -/
theorem hasDerivWithinAt_einsteinScaleExtension (J : Set ℝ) (lam : ℝ)
    (hpos : ∀ t ∈ J, 0 < einsteinScale lam t) {t : ℝ} (ht : t ∈ J) :
    HasDerivWithinAt (einsteinScaleExtension J lam hpos) (-2 * lam) J t := by
  classical
  apply (hasDerivAt_einsteinScale lam t).hasDerivWithinAt.congr
  · intro s hs
    simp [einsteinScaleExtension, hs]
  · simp [einsteinScaleExtension, ht]

/-- **Math.** The literal source family `(1 - 2 * lam * t) g0`, represented
on all real times by an irrelevant positive extension away from `J`. -/
def einsteinMetricFamilyOn (g₀ : RiemannianMetric I M) (J : Set ℝ) (lam : ℝ)
    (hpos : ∀ t ∈ J, 0 < einsteinScale lam t) :
    ℝ → RiemannianMetric I M :=
  fun t => rescaledMetric g₀ (einsteinScaleExtension J lam hpos t)
    (einsteinScaleExtension_pos J lam hpos t)

/-- **Math.** An Einstein metric evolves by the exact affine family
`g(t) = (1 - 2 * lam * t) g0` on every time set where the scale is positive. -/
theorem isRicciFlowEquationOn_einsteinMetricFamilyOn
    (g₀ : RiemannianMetric I M) (J : Set ℝ) (lam : ℝ)
    (hpos : ∀ t ∈ J, 0 < einsteinScale lam t)
    (hE : IsEinsteinTensor g₀ lam) :
    IsRicciFlowEquationOn (einsteinMetricFamilyOn g₀ J lam hpos) J := by
  classical
  intro t ht p x y
  have hderiv : HasDerivWithinAt
      (fun s => (einsteinMetricFamilyOn g₀ J lam hpos s).metricInner p x y)
      ((-2 * lam) * g₀.metricInner p x y) J t := by
    simpa only [einsteinMetricFamilyOn, rescaledMetric_metricInner] using
      (hasDerivWithinAt_einsteinScaleExtension J lam hpos ht).mul_const
        (g₀.metricInner p x y)
  have hRicci := ricciTensorAt_rescaledMetric_eq g₀
    (einsteinScaleExtension J lam hpos t)
    (einsteinScaleExtension_pos J lam hpos t) p x y
  change HasDerivWithinAt
    (fun s => (einsteinMetricFamilyOn g₀ J lam hpos s).metricInner p x y)
    (-2 * ricciTensorAt (einsteinMetricFamilyOn g₀ J lam hpos t) p x y) J t
  have hRicci' :
      ricciTensorAt (einsteinMetricFamilyOn g₀ J lam hpos t) p x y =
        ricciTensorAt g₀ p x y := by
    simpa [einsteinMetricFamilyOn] using hRicci
  rw [hRicci', hE p x y]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hderiv

end MorganTianLib

end
