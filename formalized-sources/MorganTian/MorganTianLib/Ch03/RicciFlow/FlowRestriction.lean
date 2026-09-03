import MorganTianLib.Ch03.RicciFlow.HamiltonGauge

/-!
# Restriction and conditional uniqueness for Ricci flows

The local-existence and endpoint arguments repeatedly pass to smaller time
intervals.  This file records that bookkeeping once and isolates the elementary
one-dimensional uniqueness principle used after a common right-hand side has
been identified.  The latter is deliberately conditional: equality of the
Ricci tensors is a geometric input, not a disguised Ricci-flow uniqueness
axiom.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## Restriction -/

/-- **Math.** A Ricci flow remains a Ricci flow after restriction to a
nontrivial order-connected time subset.  The smooth section and within
derivative are both transported by monotonicity of `ContMDiffOn` and
`HasDerivWithinAt`.
-/
theorem IsRicciFlowOn.restrict
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (h : IsRicciFlowOn g J) (hKJ : K ⊆ J)
    (hKord : K.OrdConnected) (hKnontrivial : K.Nontrivial) :
    IsRicciFlowOn g K := by
  refine
    { ordConnected := hKord
      nontrivial := hKnontrivial
      smooth := h.smooth.mono (Set.prod_mono subset_rfl hKJ)
      equation := ?_ }
  intro t ht p x y
  exact (h.equation t (hKJ ht) p x y).mono hKJ

/-- **Math.** The common interval restriction used by endpoint estimates. -/
theorem isRicciFlowOn_Icc_of_isRicciFlowOn_Ico
    {g : ℝ → RiemannianMetric I M} {a b s : ℝ}
    (h : IsRicciFlowOn g (Ico a b)) (has : a < s) (hsb : s < b) :
    IsRicciFlowOn g (Icc a s) := by
  apply h.restrict
    (K := Icc a s)
    (J := Ico a b)
  · intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hsb⟩
  · exact ordConnected_Icc
  · apply nontrivial_of_mem_mem_ne
      (show a ∈ (Icc a s : Set ℝ) from ⟨le_rfl, has.le⟩)
      (show s ∈ (Icc a s : Set ℝ) from ⟨has.le, le_rfl⟩)
      (ne_of_lt has)

/-- **Math.** A flow on a closed interval restricts to a nontrivial half-open
subinterval with the same left endpoint. -/
theorem isRicciFlowOn_Ico_of_isRicciFlowOn_Icc
    {g : ℝ → RiemannianMetric I M} {a b : ℝ}
    (h : IsRicciFlowOn g (Icc a b)) (hab : a < b) :
    IsRicciFlowOn g (Ico a b) := by
  apply h.restrict
    (K := Ico a b)
    (J := Icc a b)
  · intro t ht
    exact ⟨ht.1, le_of_lt ht.2⟩
  · exact ordConnected_Ico
  · apply nontrivial_of_mem_mem_ne
      (show a ∈ (Ico a b : Set ℝ) from ⟨le_rfl, hab⟩)
      (show (a + b) / 2 ∈ (Ico a b : Set ℝ) by constructor <;> linarith)
      (by linarith)

/-! ## Shared-variation uniqueness on an interval -/

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
private theorem metricInner_eq_of_sharedVariation_Icc
    {g₁ g₂ : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {a b : ℝ} (hab : a < b)
    (h₁ : IsMetricVariationOn g₁ h (Icc a b))
    (h₂ : IsMetricVariationOn g₂ h (Icc a b))
    {r : ℝ} (hr : r ∈ Icc a b) (hinit : g₁ r = g₂ r)
    (t : ℝ) (ht : t ∈ Icc a b)
    (p : M) (v w : TangentSpace I p) :
    (g₁ t).metricInner p v w = (g₂ t).metricInner p v w := by
  let f : ℝ → ℝ :=
    (fun s => (g₁ s).metricInner p v w) -
      (fun s => (g₂ s).metricInner p v w)
  have hdiff : DifferentiableOn ℝ f (Icc a b) := by
    intro s hs
    exact ((h₁ s hs p v w).sub (h₂ s hs p v w)).differentiableWithinAt
  have hzero : ∀ s ∈ Ico a b, derivWithin f (Icc a b) s = 0 := by
    intro s hs
    have huniq : UniqueDiffWithinAt ℝ (Icc a b) s :=
      uniqueDiffOn_Icc hab s ⟨hs.1, le_of_lt hs.2⟩
    have hd := (h₁ s ⟨hs.1, le_of_lt hs.2⟩ p v w).sub
      (h₂ s ⟨hs.1, le_of_lt hs.2⟩ p v w)
    have hd0 : HasDerivWithinAt f 0 (Icc a b) s := by
      simpa [f] using hd
    exact hd0.derivWithin huniq
  have hconst : f t = f a :=
    constant_of_derivWithin_zero hdiff hzero t ht
  have hconst_r : f r = f a :=
    constant_of_derivWithin_zero hdiff hzero r hr
  have hfzero : f r = 0 := by
    simp [f, hinit]
  have hfa : f a = 0 := hconst_r.symm.trans hfzero
  exact sub_eq_zero.mp (hconst.trans hfa)

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Two metric families with the same variation field and one common
endpoint value agree coefficientwise on an interval. -/
theorem metricFamilyAgreementOn_of_sharedMetricVariation
    {g₁ g₂ : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hJord : J.OrdConnected)
    (h₁ : IsMetricVariationOn g₁ h J)
    (h₂ : IsMetricVariationOn g₂ h J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hinit : g₁ t₀ = g₂ t₀) :
    MetricFamilyAgreementOn g₁ g₂ J := by
  intro t ht p v w
  by_cases hteq : t = t₀
  · subst t
    exact congrArg (fun q : RiemannianMetric I M => q.metricInner p v w) hinit
  by_cases hlt : t < t₀
  · have hsub : Icc t t₀ ⊆ J := hJord.out ht ht₀
    have h₁' : IsMetricVariationOn g₁ h (Icc t t₀) := by
      intro s hs q x y
      exact (h₁ s (hsub hs) q x y).mono hsub
    have h₂' : IsMetricVariationOn g₂ h (Icc t t₀) := by
      intro s hs q x y
      exact (h₂ s (hsub hs) q x y).mono hsub
    exact metricInner_eq_of_sharedVariation_Icc hlt h₁' h₂'
      (r := t₀) ⟨hlt.le, le_rfl⟩ hinit t ⟨le_rfl, hlt.le⟩ p v w
  · have ht0lt : t₀ < t := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hteq)
    have hsub : Icc t₀ t ⊆ J := hJord.out ht₀ ht
    have h₁' : IsMetricVariationOn g₁ h (Icc t₀ t) := by
      intro s hs q x y
      exact (h₁ s (hsub hs) q x y).mono hsub
    have h₂' : IsMetricVariationOn g₂ h (Icc t₀ t) := by
      intro s hs q x y
      exact (h₂ s (hsub hs) q x y).mono hsub
    exact metricInner_eq_of_sharedVariation_Icc ht0lt h₁' h₂'
      (r := t₀) ⟨le_rfl, ht0lt.le⟩ hinit t ⟨ht0lt.le, le_rfl⟩ p v w

/-- **Math.** A Ricci-tensor agreement hypothesis turns the preceding shared
variation result into a conditional uniqueness theorem for Ricci flows. -/
theorem metricFamilyAgreementOn_of_equal_ricci_on_shared_initial
    {g₁ g₂ : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hJord : J.OrdConnected)
    (h₁ : IsRicciFlowOn g₁ J) (h₂ : IsRicciFlowOn g₂ J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hinit : g₁ t₀ = g₂ t₀)
    (hRicci : ∀ t ∈ J, ∀ (p : M) (v w : TangentSpace I p),
      ricciTensorAt (g₁ t) p v w = ricciTensorAt (g₂ t) p v w) :
    MetricFamilyAgreementOn g₁ g₂ J := by
  let h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ :=
    fun t p v w => -2 * ricciTensorAt (g₁ t) p v w
  have h₁' : IsMetricVariationOn g₁ h J := h₁.equation
  have h₂' : IsMetricVariationOn g₂ h J := by
    intro t ht p v w
    have hderiv := h₂.equation t ht p v w
    have heq : (-2 * ricciTensorAt (g₂ t) p v w) = h t p v w := by
      dsimp [h]
      rw [hRicci t ht p v w]
    rw [heq] at hderiv
    exact hderiv
  exact metricFamilyAgreementOn_of_sharedMetricVariation hJord h₁' h₂'
    ht₀ hinit

/-- **Math.** Bundled equality follows from the coefficientwise conditional
uniqueness theorem. -/
theorem metricFamily_eq_of_equal_ricci_on_shared_initial
    {g₁ g₂ : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hJord : J.OrdConnected)
    (h₁ : IsRicciFlowOn g₁ J) (h₂ : IsRicciFlowOn g₂ J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hinit : g₁ t₀ = g₂ t₀)
    (hRicci : ∀ t ∈ J, ∀ (p : M) (v w : TangentSpace I p),
      ricciTensorAt (g₁ t) p v w = ricciTensorAt (g₂ t) p v w) :
    ∀ t ∈ J, g₁ t = g₂ t := by
  have hAgree := metricFamilyAgreementOn_of_equal_ricci_on_shared_initial
    hJord h₁ h₂ ht₀ hinit hRicci
  intro t ht
  apply riemannianMetric_eq_of_metricInner_eq
  intro p v w
  exact hAgree t ht p v w

#print axioms IsRicciFlowOn.restrict
#print axioms metricFamilyAgreementOn_of_sharedMetricVariation
#print axioms metricFamilyAgreementOn_of_equal_ricci_on_shared_initial
#print axioms metricFamily_eq_of_equal_ricci_on_shared_initial

end MorganTianLib

end
