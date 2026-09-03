import MorganTianLib.Ch03.RicciFlow.SmoothPatching

/-!
# Morgan--Tian Ch. 3 - smooth endpoint bootstrap

This module supplies the analytic producer which is deliberately left open by
the coefficient-level patching theorem.  Two globally smooth horizontal
sections are glued with `ContMDiff.piecewise`; the primitive endpoint fields
record the local agreement needed at the frontier and the restrictions that
identify each extension with its metric family on its own time interval.
-/

open scoped ContDiff ContMDiff Manifold Topology Bundle RealInnerProductSpace
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

/-- **Math.** Primitive global extensions used to bootstrap smoothness across a joining
time.  The fields are section-level data, rather than a pre-packaged
`IsSmoothMetricFamilyOn` assertion. -/
structure SmoothEndpointExtension
    {a b c : ℝ} (gLeft gRight : ℝ → RiemannianMetric I M) where
  leftExtension : (z : M × ℝ) →
    TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (fun q : M × ℝ =>
        HorizontalTangentSpace I M q →L[ℝ]
          HorizontalTangentSpace I M q →L[ℝ] ℝ)
  rightExtension : (z : M × ℝ) →
    TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (fun q : M × ℝ =>
        HorizontalTangentSpace I M q →L[ℝ]
          HorizontalTangentSpace I M q →L[ℝ] ℝ)
  left_smooth :
    ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      leftExtension
  right_smooth :
    ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      rightExtension
  left_agrees :
    ∀ ⦃p : M⦄ ⦃t : ℝ⦄, a ≤ t → t < b →
      leftExtension (p, t) = horizontalMetricSection gLeft (p, t)
  right_agrees :
    ∀ ⦃p : M⦄ ⦃t : ℝ⦄, b ≤ t → t < c →
      rightExtension (p, t) = horizontalMetricSection gRight (p, t)
  join_eventuallyEq :
    ∀ p : M, leftExtension =ᶠ[𝓝 (p, b)] rightExtension

/-- **Math.** A single ambient smooth section supplies both sides of an endpoint join.

This is the primitive interface produced by a genuine compact-open smooth
bootstrap: the two restrictions are recorded separately, while agreement at
the joining slice is immediate because both extensions are the same function.
-/
def SmoothEndpointExtension.of_common
    {a b c : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (F : (z : M × ℝ) →
      TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun q : M × ℝ =>
          HorizontalTangentSpace I M q →L[ℝ]
            HorizontalTangentSpace I M q →L[ℝ] ℝ))
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞ F)
    (hLeft : ∀ ⦃p : M⦄ ⦃t : ℝ⦄, a ≤ t → t < b →
      F (p, t) = horizontalMetricSection gLeft (p, t))
    (hRight : ∀ ⦃p : M⦄ ⦃t : ℝ⦄, b ≤ t → t < c →
      F (p, t) = horizontalMetricSection gRight (p, t)) :
    SmoothEndpointExtension (I := I) (a := a) (b := b) (c := c)
      gLeft gRight :=
  { leftExtension := F
    rightExtension := F
    left_smooth := hF
    right_smooth := hF
    left_agrees := hLeft
    right_agrees := hRight
    join_eventuallyEq := fun _ => Filter.Eventually.of_forall (fun _ => rfl) }

theorem smoothMetricFamilyOn_patchedMetricFamily_of_extension
    {a b c : ℝ} (_hab : a < b) (_hbc : b < c)
    {gLeft gRight : ℝ → RiemannianMetric I M}
    (h : SmoothEndpointExtension (I := I) (a := a) (b := b) (c := c)
      gLeft gRight) :
    IsSmoothMetricFamilyOn
      (patchedMetricFamily b gLeft gRight) (Ico a c) := by
  classical
  let s : Set (M × ℝ) := (Set.univ : Set M) ×ˢ Iio b
  let glued : (z : M × ℝ) →
      TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun q : M × ℝ =>
          HorizontalTangentSpace I M q →L[ℝ]
            HorizontalTangentSpace I M q →L[ℝ] ℝ) :=
    Set.piecewise s h.leftExtension h.rightExtension
  have hfrontier : ∀ x ∈ frontier s,
      h.leftExtension =ᶠ[𝓝 x] h.rightExtension := by
    intro x hx
    rcases x with ⟨p, t⟩
    have hx' : (p, t) ∈ (Set.univ : Set M) ×ˢ frontier (Iio b) := by
      simpa [s, frontier_univ_prod_eq] using hx
    have ht : t = b := by simpa [frontier_Iio] using hx'.2
    subst t
    exact h.join_eventuallyEq p
  have hglued : ContMDiff
      (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞ glued := by
    exact ContMDiff.piecewise h.left_smooth h.right_smooth hfrontier
  have heq : ∀ z ∈ (Set.univ : Set M) ×ˢ Ico a c,
      horizontalMetricSection (patchedMetricFamily b gLeft gRight) z = glued z := by
    rintro ⟨p, t⟩ ⟨_, ht⟩
    by_cases htb : t < b
    · have hleft := h.left_agrees (p := p) (t := t) ht.1 htb
      simpa [horizontalMetricSection, glued, s, htb,
        patchedMetricFamily_of_lt b gLeft gRight htb] using hleft.symm
    · have hbt : b ≤ t := le_of_not_gt htb
      have hright := h.right_agrees (p := p) (t := t) hbt ht.2
      simpa [horizontalMetricSection, glued, s, htb, hbt,
        patchedMetricFamily_of_le b gLeft gRight hbt] using hright.symm
  exact hglued.contMDiffOn.congr heq

end MorganTianLib

end

#print axioms MorganTianLib.smoothMetricFamilyOn_patchedMetricFamily_of_extension
