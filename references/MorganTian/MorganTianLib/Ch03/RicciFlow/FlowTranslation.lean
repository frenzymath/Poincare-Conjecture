import Mathlib.Analysis.Calculus.Deriv.Shift
import MorganTianLib.Ch03.RicciFlow.MetricVariation

/-!
# Time translation of Ricci flows

This module transports metric variations and the Ricci-flow equation through
the affine time map `s \mapsto s - T`.  Joint space-time smoothness is kept as
an explicit input to the full-flow adapter because it is a dependent-bundle
regularity statement, not a consequence of the coefficientwise chain rule.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A metric variation pulls back through a translation of the time
variable, with no scaling of the variation because the translation has
derivative one. -/
theorem isMetricVariationOn_comp_sub_const
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hvar : MorganTianLib.IsMetricVariationOn g h J) (T : ℝ) :
    MorganTianLib.IsMetricVariationOn
      (fun s => g (s - T))
      (fun s p v w => h (s - T) p v w)
      ((fun s : ℝ => s - T) ⁻¹' J) := by
  intro s hs p v w
  have hderiv := hvar (s - T) hs p v w
  have hshift : HasDerivAt (fun u : ℝ => u - T) 1 s := by
    simpa using (hasDerivAt_id s).sub_const T
  have hcomp := hderiv.comp s hshift.hasDerivWithinAt (by
    intro u hu
    exact hu)
  convert hcomp using 1
  all_goals try rfl
  all_goals try simp [mul_one]

/-- **Math.** Translating the preimage of a half-open interval translates
both endpoints. -/
theorem preimage_sub_const_Ico (a b T : ℝ) :
    (fun s : ℝ => s - T) ⁻¹' Ico a b = Ico (a + T) (b + T) := by
  ext s
  constructor
  · intro hs
    constructor <;> linarith [hs.1, hs.2]
  · intro hs
    constructor <;> linarith [hs.1, hs.2]

/-- **Math.** The Ricci-flow equation is invariant under translation of the
time variable. -/
theorem isRicciFlowEquationOn_comp_sub_const
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowEquationOn g J) (T : ℝ) :
    MorganTianLib.IsRicciFlowEquationOn
      (fun s => g (s - T)) ((fun s : ℝ => s - T) ⁻¹' J) := by
  exact isMetricVariationOn_comp_sub_const
    (h := fun t p v w =>
      -2 * MorganTianLib.ricciTensorAt (g t) p v w)
    hflow T

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** If a family `f` agrees with `g` after translating time by `T`,
then the metric variation of `f` is obtained by translating the variation of
`g`.  The equality is bundled-metric equality, so this adapter is useful for a
family specified by a shift equation rather than by a definitional
reparametrization. -/
theorem isMetricVariationOn_of_timeShift_eq
    {f g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hvar : MorganTianLib.IsMetricVariationOn g h J)
    (T : ℝ) (hfg : ∀ u : ℝ, f (T + u) = g u) :
    MorganTianLib.IsMetricVariationOn
      f (fun s p v w => h (s - T) p v w)
      ((fun s : ℝ => s - T) ⁻¹' J) := by
  intro s hs p v w
  have hderiv := isMetricVariationOn_comp_sub_const hvar T s hs p v w
  have hpoint : ∀ u : ℝ,
      (f u).metricInner p v w =
        ((g (u - T)).metricInner p v w) := by
    intro u
    have h := congrArg (fun q : RiemannianMetric I M => q.metricInner p v w)
      (hfg (u - T))
    simpa [add_sub_cancel_left] using h
  apply hderiv.congr
  · intro u hu
    exact hpoint u
  · exact hpoint s

/-- **Math.** The Ricci-flow equation transports through a family equality of
the form `f (T + s) = g s`; the Ricci tensor is rewritten using the same
bundled-metric equality. -/
theorem isRicciFlowEquationOn_of_timeShift_eq
    {f g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowEquationOn g J)
    (T : ℝ) (hfg : ∀ u : ℝ, f (T + u) = g u) :
    MorganTianLib.IsRicciFlowEquationOn
      f ((fun s : ℝ => s - T) ⁻¹' J) := by
  intro s hs p v w
  have hv := isMetricVariationOn_of_timeShift_eq
    (g := g) (f := f)
    (h := fun t p v w =>
      -2 * MorganTianLib.ricciTensorAt (g t) p v w)
    hflow T hfg s hs p v w
  have hmetric : f s = g (s - T) := by
    have h := hfg (s - T)
    simpa [add_sub_cancel_left] using h
  simpa [hmetric] using hv

/-- **Math.** A flow on `Ico 0 S` can be shifted to any shorter interval
`Ico T (T + epsilon)` when `epsilon ≤ S`, provided the shifted family agrees
with the original family. -/
theorem isRicciFlowEquationOn_of_timeShift_eq_Ico
    {f g : ℝ → RiemannianMetric I M} {T epsilon S : ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 S))
    (_hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ S)
    (hfg : ∀ u : ℝ, f (T + u) = g u) :
    MorganTianLib.IsRicciFlowEquationOn f (Ico T (T + epsilon)) := by
  have htranslated := isRicciFlowEquationOn_of_timeShift_eq
    (f := f) (g := g) (J := Ico 0 S) hflow.equation T hfg
  intro t ht p v w
  have htpre : t ∈ ((fun s : ℝ => s - T) ⁻¹' (Ico 0 S)) := by
    change 0 ≤ t - T ∧ t - T < S
    constructor <;> linarith [ht.1, ht.2, hepsilon_le]
  exact (htranslated t htpre p v w).mono (by
    intro u hu
    change 0 ≤ u - T ∧ u - T < S
    constructor <;> linarith [hu.1, hu.2, hepsilon_le])

/-- **Math.** The preceding shifted equation, together with an explicit joint
smoothness certificate for the shifted family, assembles into a genuine
`IsRicciFlowOn` certificate. -/
theorem isRicciFlowOn_of_timeShift_eq_Ico_of_smooth
    {f g : ℝ → RiemannianMetric I M} {T epsilon S : ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 S))
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ S)
    (hfg : ∀ u : ℝ, f (T + u) = g u)
    (hSmooth : MorganTianLib.IsSmoothMetricFamilyOn f (Ico T (T + epsilon))) :
    MorganTianLib.IsRicciFlowOn f (Ico T (T + epsilon)) := by
  refine
    { ordConnected := ordConnected_Ico
      nontrivial := ?_
      smooth := hSmooth
      equation := isRicciFlowEquationOn_of_timeShift_eq_Ico
        hflow hepsilon hepsilon_le hfg }
  apply nontrivial_of_mem_mem_ne
    (show T ∈ (Ico T (T + epsilon) : Set ℝ) by
      exact ⟨le_rfl, by linarith⟩)
    (show T + epsilon / 2 ∈ (Ico T (T + epsilon) : Set ℝ) by
      constructor <;> linarith)
    (by linarith)

/-- **Math.** A translated Ricci-flow equation, together with the translated
joint smoothness statement, gives a Ricci flow on the translated half-open
interval. -/
theorem isRicciFlowOn_comp_sub_const_of_smooth
    {g : ℝ → RiemannianMetric I M} {a b : ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico a b)) (T : ℝ)
    (hSmooth : MorganTianLib.IsSmoothMetricFamilyOn
      (fun s => g (s - T)) (Ico (a + T) (b + T))) :
    MorganTianLib.IsRicciFlowOn
      (fun s => g (s - T)) (Ico (a + T) (b + T)) := by
  have heq := preimage_sub_const_Ico a b T
  have hequation := isRicciFlowEquationOn_comp_sub_const
    (g := g) (J := Ico a b) hflow.equation T
  rw [heq] at hequation
  refine
    { ordConnected := ordConnected_Ico
      nontrivial := ?_
      smooth := hSmooth
      equation := hequation }
  have hsurj : Function.Surjective (fun s : ℝ => s - T) := by
    intro u
    exact ⟨u + T, by ring⟩
  rw [← heq]
  exact hflow.nontrivial.preimage hsurj

end MorganTianLib

end
