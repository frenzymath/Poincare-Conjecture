import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3GeodesicLocal

set_option linter.unusedSectionVars false

/-!
# A fixed time window for the local geodesic family (do Carmo Ch. 3, Prop. 2.7)

The local flow theorem supplies a smooth family on a small symmetric interval.
This file records the affine reparametrisation needed to normalize that interval
to `(-2, 2)`.  The chart-level reparametrisation lemma is kept separate because
it is useful wherever a fixed-chart geodesic is rescaled.
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Affine rescaling in a fixed chart -/

/-- **Math.** Restrict a fixed-chart geodesic equation to a smaller time set. -/
theorem IsChartGeodesicOn.mono
    {g : RiemannianMetric I M} {α : M} {γ : ℝ → M} {J K : Set ℝ}
    (h : IsChartGeodesicOn (I := I) g α γ K) (hJK : J ⊆ K) :
    IsChartGeodesicOn (I := I) g α γ J := by
  rcases h with ⟨hmem, hfirst, hsecond⟩
  exact ⟨fun t ht => hmem t (hJK ht), fun t ht => hfirst t (hJK ht),
    fun t ht => hsecond t (hJK ht)⟩

theorem IsChartGeodesicOn.comp_mul_left
    {g : RiemannianMetric I M} {α : M} {γ : ℝ → M} {J : Set ℝ} {a : ℝ}
    (h : IsChartGeodesicOn (I := I) g α γ J) :
    IsChartGeodesicOn (I := I) g α (fun t => γ (a * t))
      ((fun t : ℝ => a * t) ⁻¹' J) := by
  rcases h with ⟨hmem, hfirst, hsecond⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact hmem (a * t) ht
  · intro t ht
    have h' := (hfirst (a * t) ht).scomp t (hasDerivAt_const_mul a)
    have hderiv : deriv (fun s : ℝ => extChartAt I α (γ (a * s))) t =
        a • deriv (fun s : ℝ => extChartAt I α (γ s)) (a * t) := by
      exact deriv_comp_mul_left a (fun s => extChartAt I α (γ s)) t
    convert h' using 1
    rfl
  · intro t ht
    have h' := (hsecond (a * t) ht).scomp t (hasDerivAt_const_mul a)
    have h'' := h'.const_smul a
    have hderiv : (fun s : ℝ =>
        deriv (fun r => extChartAt I α (γ (a * r))) s) =
        (fun s : ℝ => a • deriv (fun r => extChartAt I α (γ r)) (a * s)) := by
      funext s
      exact deriv_comp_mul_left a (fun r => extChartAt I α (γ r)) s
    change HasDerivAt
      (fun s : ℝ => deriv (fun r => extChartAt I α (γ (a * r))) s)
      (- Geodesic.chartChristoffelContraction (I := I) g α
        (deriv (fun r => extChartAt I α (γ (a * r))) t)
        (deriv (fun r => extChartAt I α (γ (a * r))) t)
        (extChartAt I α (γ (a * t)))) t
    rw [hderiv]
    convert h'' using 1
    · rfl
    · have hdt : deriv (fun r : ℝ => extChartAt I α (γ (a * r))) t =
          a • deriv (fun r : ℝ => extChartAt I α (γ r)) (a * t) := by
        exact deriv_comp_mul_left a (fun r => extChartAt I α (γ r)) t
      rw [hdt]
      rw [Geodesic.chartChristoffelContraction_smul_smul (I := I) g α a
        (deriv (fun r : ℝ => extChartAt I α (γ r)) (a * t))
        (extChartAt I α (γ (a * t)))]
      simp only [smul_neg, smul_smul]

namespace GeodesicLocal

/-- **Math.** The chart-local geodesic family can be normalized to the fixed
time window `(-2, 2)` by shrinking its model-space velocity neighborhood. -/
theorem geodesic_local_existence_fixedInterval
    (g : RiemannianMetric I M) [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] (p : M) :
    ∃ V₁ ∈ 𝓝 p, ∃ V₂ ∈ 𝓝 (0 : E), ∃ c : M → E → ℝ → M,
      (∀ q ∈ V₁, ∀ w ∈ V₂,
        IsChartGeodesicOn (I := I) g p (c q w) (Ioo (-2) 2) ∧
        c q w 0 = q ∧
        HasDerivAt (fun s => extChartAt I p (c q w s)) w 0) ∧
      ContDiffOn ℝ ∞
        (fun xwt : (E × E) × ℝ =>
          extChartAt I p
            (c ((extChartAt I p).symm xwt.1.1) xwt.1.2 xwt.2))
        (((extChartAt I p '' V₁) ×ˢ V₂) ×ˢ Ioo (-2) 2) := by
  obtain ⟨ε, hε, V₁, hV₁, V₂, hV₂, c, hc, hcsmooth⟩ :=
    geodesic_local_existence (I := I) g p (0 : E)
  let a : ℝ := ε / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  let scale : E → E := fun w => a⁻¹ • w
  let V₂' : Set E := scale ⁻¹' V₂
  have hV₂E : V₂ ∈ 𝓝 (0 : E) := by
    convert hV₂ using 1
  have hV₂' : V₂' ∈ 𝓝 (0 : E) := by
    have hcont : ContinuousAt scale (0 : E) := by
      dsimp [scale]
      exact (continuous_const_smul (T := E) a⁻¹).continuousAt
    apply hcont.preimage_mem_nhds
    simpa [scale] using hV₂E
  let c' : M → E → ℝ → M := fun q w t => c q (scale w) (a * t)
  refine ⟨V₁, hV₁, V₂', hV₂', c', ?_, ?_⟩
  · intro q hq w hw
    have hwV₂ : scale w ∈ V₂ := hw
    have hmain := hc q hq (scale w) hwV₂
    have hpre : Ioo (-2 : ℝ) 2 ⊆ (fun t : ℝ => a * t) ⁻¹' Ioo (-ε) ε := by
      intro t ht
      constructor
      · calc
          -ε = a * (-2) := by dsimp [a]; ring
          _ < a * t := mul_lt_mul_of_pos_left ht.1 ha
      · calc
          a * t < a * 2 := mul_lt_mul_of_pos_left ht.2 ha
          _ = ε := by dsimp [a]; ring
    have hgeo := (hmain.1.comp_mul_left).mono hpre
    refine ⟨?_, ?_, ?_⟩
    · simpa [c'] using hgeo
    · simpa [c'] using hmain.2.1
    · have hvel0 : HasDerivAt
          (fun s => extChartAt I p (c q (scale w) s)) (scale w) (a * 0) := by
        simpa using hmain.2.2
      have hv := hvel0.scomp (0 : ℝ) (hasDerivAt_const_mul a)
      convert hv using 1
      · rfl
      · simp [scale, smul_smul, ha.ne']
  · let rescale : ((E × E) × ℝ) → ((E × E) × ℝ) := fun xwt =>
      ((xwt.1.1, scale xwt.1.2), a * xwt.2)
    have hrescale : ContDiff ℝ ∞ rescale := by
      dsimp [rescale, scale]
      exact ((contDiff_fst.fst).prodMk
        (contDiff_fst.snd.const_smul a⁻¹)).prodMk
        (contDiff_snd.const_smul a)
    have hmaps : MapsTo rescale
        (((extChartAt I p '' V₁) ×ˢ V₂') ×ˢ Ioo (-2) 2)
        (((extChartAt I p '' V₁) ×ˢ V₂) ×ˢ Ioo (-ε) ε) := by
      rintro ⟨⟨x, w⟩, t⟩ ⟨⟨hx, hw⟩, ht⟩
      refine ⟨⟨hx, hw⟩, ?_⟩
      constructor
      · calc
          -ε = a * (-2) := by dsimp [a]; ring
          _ < a * t := mul_lt_mul_of_pos_left ht.1 ha
      · calc
          a * t < a * 2 := mul_lt_mul_of_pos_left ht.2 ha
          _ = ε := by dsimp [a]; ring
    have hcomp := hcsmooth.comp hrescale.contDiffOn hmaps
    apply hcomp.congr
    rintro ⟨⟨x, w⟩, t⟩ ⟨⟨hx, hw⟩, ht⟩
    rfl

end GeodesicLocal

end Riemannian
