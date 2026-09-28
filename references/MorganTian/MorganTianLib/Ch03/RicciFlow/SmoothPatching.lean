import MorganTianLib.Ch03.RicciFlow.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Smooth patching at a Ricci-flow joining time

This file isolates the endpoint calculus used in Morgan--Tian's smooth-patching
proposition.  A left-hand solution whose values and derivatives converge at the
joining time has the expected one-sided derivative there.  The Ricci-specific
application then patches that derivative with the right-hand flow equation.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Filter Set Riemannian

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

/-- **Math.** Extend a derivative to the right endpoint of an interval when the
function and its derivative both have left limits there. -/
theorem hasDerivWithinAt_Iic_of_deriv_tendsto_from_Ioo
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} {f df : ℝ → F} {e : F} (hab : a < b)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (df t) t)
    (hcont : Tendsto f (𝓝[Ioo a b] b) (𝓝 (f b)))
    (hdf : Tendsto df (𝓝[Ioo a b] b) (𝓝 e)) :
    HasDerivWithinAt f e (Iic b) b := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
      (s := Ioo a b)
      (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
      hcont (Ioo_mem_nhdsLT hab)
  rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
  exact hdf.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hderiv t ht).deriv.symm)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Concatenate two metric families at `b`, using the left family for
times strictly before `b` and the right family from `b` onward. -/
def patchedMetricFamily (b : ℝ) (gLeft gRight : ℝ → RiemannianMetric I M) :
    ℝ → RiemannianMetric I M :=
  fun t => if t < b then gLeft t else gRight t

@[simp] theorem patchedMetricFamily_of_lt (b : ℝ)
    (gLeft gRight : ℝ → RiemannianMetric I M) {t : ℝ} (ht : t < b) :
    patchedMetricFamily b gLeft gRight t = gLeft t := by
  simp [patchedMetricFamily, ht]

@[simp] theorem patchedMetricFamily_of_le (b : ℝ)
    (gLeft gRight : ℝ → RiemannianMetric I M) {t : ℝ} (ht : b ≤ t) :
    patchedMetricFamily b gLeft gRight t = gRight t := by
  simp [patchedMetricFamily, not_lt.mpr ht]

@[simp] theorem patchedMetricFamily_at (b : ℝ)
    (gLeft gRight : ℝ → RiemannianMetric I M) :
    patchedMetricFamily b gLeft gRight b = gRight b := by
  exact patchedMetricFamily_of_le b gLeft gRight le_rfl

/-- **Math.** The left-hand Ricci-flow derivative extends to the joining time
when the metric coefficients and Ricci coefficients have their expected left
limits.  Smooth convergence on compact subsets supplies precisely these two
limits in the source proposition. -/
theorem patchedMetricFamily_hasDerivWithinAt_Iic_at_join
    {a b : ℝ} (hab : a < b)
    (gLeft gRight : ℝ → RiemannianMetric I M)
    (hLeft : IsRicciFlowEquationOn gLeft (Ico a b))
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x y) (𝓝[Ioo a b] b)
        (𝓝 ((gRight b).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gLeft t) p x y) (𝓝[Ioo a b] b)
        (𝓝 (ricciTensorAt (gRight b) p x y)))
    (p : M) (x y : TangentSpace I p) :
    HasDerivWithinAt
      (fun t => (patchedMetricFamily b gLeft gRight t).metricInner p x y)
      (-2 * ricciTensorAt (gRight b) p x y) (Iic b) b := by
  apply hasDerivWithinAt_Iic_of_deriv_tendsto_from_Ioo hab
      (df := fun t => -2 * ricciTensorAt (gLeft t) p x y)
  · intro t ht
    have hderiv := (hLeft t ⟨le_of_lt ht.1, ht.2⟩ p x y).hasDerivAt
      (Ico_mem_nhds ht.1 ht.2)
    apply hderiv.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht.2] with s hs
    have hsb : s < b := hs
    rw [patchedMetricFamily_of_lt b gLeft gRight hsb]
  · rw [patchedMetricFamily_at]
    apply (hMetric p x y).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htb : t < b := ht.2
    rw [patchedMetricFamily_of_lt b gLeft gRight htb]
  · exact (hRicci p x y).const_mul (-2)

/-- **Math.** The Ricci-flow equation patches across a joining time.  The left
flow is defined on `[a,b)`, the right flow on `[b,c)`, and convergence of the
metric and Ricci coefficients supplies the missing left derivative at `b`.

This is the equation half of Morgan--Tian's smooth-patching proposition; the
remaining half is the joint `C^∞` regularity of the patched horizontal metric
section, obtained in the source by bootstrapping all time derivatives from the
Ricci equation. -/
theorem isRicciFlowEquationOn_patchedMetricFamily
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (gLeft gRight : ℝ → RiemannianMetric I M)
    (hLeft : IsRicciFlowEquationOn gLeft (Ico a b))
    (hRight : IsRicciFlowEquationOn gRight (Ico b c))
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x y) (𝓝[Ioo a b] b)
        (𝓝 ((gRight b).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gLeft t) p x y) (𝓝[Ioo a b] b)
        (𝓝 (ricciTensorAt (gRight b) p x y))) :
    IsRicciFlowEquationOn (patchedMetricFamily b gLeft gRight) (Ico a c) := by
  intro t ht p x y
  rcases lt_trichotomy t b with htb | htb | hbt
  · have hset : (Ico a b : Set ℝ) =ᶠ[𝓝 t] Ico a c := by
      filter_upwards [Iio_mem_nhds htb] with s hs
      have hsb : s < b := hs
      apply propext
      constructor
      · intro h
        exact ⟨h.1, h.2.trans hbc⟩
      · intro h
        exact ⟨h.1, hsb⟩
    have hderiv := (hLeft t ⟨ht.1, htb⟩ p x y).congr_set hset
    have heq :
        (fun s => (patchedMetricFamily b gLeft gRight s).metricInner p x y) =ᶠ[𝓝[Ico a c] t]
          fun s => (gLeft s).metricInner p x y := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds htb)] with s hs
      have hsb : s < b := hs
      rw [patchedMetricFamily_of_lt b gLeft gRight hsb]
    rw [patchedMetricFamily_of_lt b gLeft gRight htb]
    exact hderiv.congr_of_eventuallyEq heq
      (by rw [patchedMetricFamily_of_lt b gLeft gRight htb])
  · subst t
    rw [patchedMetricFamily_at]
    have hleftAt := patchedMetricFamily_hasDerivWithinAt_Iic_at_join
      hab gLeft gRight hLeft hMetric hRicci p x y
    have hleftOn : HasDerivWithinAt
        (fun s => (patchedMetricFamily b gLeft gRight s).metricInner p x y)
        (-2 * ricciTensorAt (gRight b) p x y) (Icc a b) b :=
      hleftAt.mono (fun _ hs => hs.2)
    have hrightOn : HasDerivWithinAt
        (fun s => (patchedMetricFamily b gLeft gRight s).metricInner p x y)
        (-2 * ricciTensorAt (gRight b) p x y) (Ico b c) b := by
      apply (hRight b ⟨le_rfl, hbc⟩ p x y).congr
      · intro s hs
        rw [patchedMetricFamily_of_le b gLeft gRight hs.1]
      · rw [patchedMetricFamily_at]
    have hunion := hleftOn.union hrightOn
    rwa [Set.Icc_union_Ico_eq_Ico (le_of_lt hab) hbc] at hunion
  · have hset : (Ico b c : Set ℝ) =ᶠ[𝓝 t] Ico a c := by
      filter_upwards [Ioi_mem_nhds hbt] with s hs
      have hbs : b < s := hs
      apply propext
      constructor
      · intro h
        exact ⟨(le_of_lt hab).trans h.1, h.2⟩
      · intro h
        exact ⟨le_of_lt hbs, h.2⟩
    have hderiv := (hRight t ⟨le_of_lt hbt, ht.2⟩ p x y).congr_set hset
    have heq :
        (fun s => (patchedMetricFamily b gLeft gRight s).metricInner p x y) =ᶠ[𝓝[Ico a c] t]
          fun s => (gRight s).metricInner p x y := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hbt)] with s hs
      have hbs : b ≤ s := le_of_lt hs
      rw [patchedMetricFamily_of_le b gLeft gRight hbs]
    rw [patchedMetricFamily_of_le b gLeft gRight (le_of_lt hbt)]
    exact hderiv.congr_of_eventuallyEq heq
      (by rw [patchedMetricFamily_of_le b gLeft gRight (le_of_lt hbt)])

end MorganTianLib

end
