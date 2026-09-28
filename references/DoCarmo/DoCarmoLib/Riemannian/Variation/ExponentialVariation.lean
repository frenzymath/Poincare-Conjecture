import DoCarmoLib.Riemannian.Variation.Basic
import DoCarmoLib.Riemannian.Exponential.MovingBaseExpGlobalSmooth

/-!
# Exponential variations

This file isolates the part of do Carmo's variation-existence argument that is
available from the complete exponential map.  The family

`f(s,t) = exp_{c(t)} (s V(t))`

has the prescribed zero slice, endpoint values, and variational field.  The
remaining finite-cover argument which supplies piecewise surface regularity
for an arbitrary curve and field is deliberately an explicit hypothesis in the
last packaging theorem.
-/

open Set
open scoped ContDiff Manifold Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- **Math.** The complete-exponential family used in do Carmo's existence
argument for a variational field. -/
def exponentialVariation (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (c : ℝ → M) (V : ℝ → E) (x : ℝ × ℝ) : M :=
  Riemannian.Exponential.expMapGlobal (I := I) g hg (c x.2) (x.1 • V x.2)

/-- **Math.** The zero member of an exponential variation is the original
curve. -/
@[simp] theorem exponentialVariation_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) (t : ℝ) :
    exponentialVariation (I := I) g hg c V (0, t) = c t := by
  rw [exponentialVariation, zero_smul]
  exact Riemannian.Exponential.expMapGlobal_zero (I := I) g hg (c t)

/-- **Math.** Vanishing endpoint values of the field make the exponential
variation proper. -/
theorem exponentialVariation_isProperVariation
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) {a ε : ℝ}
    (hV0 : V 0 = 0) (hVa : V a = 0) :
    IsProperVariation c a ε (exponentialVariation (I := I) g hg c V) := by
  intro s hs
  constructor
  · rw [exponentialVariation, hV0, smul_zero]
    exact Riemannian.Exponential.expMapGlobal_zero (I := I) g hg (c 0)
  · rw [exponentialVariation, hVa, smul_zero]
    exact Riemannian.Exponential.expMapGlobal_zero (I := I) g hg (c a)

/-- **Math.** The radial derivative of the exponential family, read in the
chart centered at its foot, is the prescribed field. -/
theorem hasDerivAt_extChartAt_exponentialVariation_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => extChartAt I (c t)
      (exponentialVariation (I := I) g hg c V (s, t))) (V t) 0 := by
  change HasDerivAt (fun s : ℝ => extChartAt I (c t)
    (Riemannian.Exponential.expMapGlobal (I := I) g hg (c t)
      (s • ((V t : E) : TangentSpace I (c t))))) (V t) 0
  exact Riemannian.Exponential.hasDerivAt_extChartAt_expMapGlobal_smul
    (I := I) g hg (c t) ((V t : E) : TangentSpace I (c t))

/-- **Math.** The intrinsic variational field of the exponential family is
the prescribed field `V`. -/
theorem variationalField_exponentialVariation
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) :
    variationalField I (exponentialVariation (I := I) g hg c V) = V := by
  funext t
  have heq : (fun s : ℝ => exponentialVariation (I := I) g hg c V (s, t)) =
      Riemannian.Geodesic.globalGeodesic (I := I) g hg (c t) (V t) := by
    funext s
    exact Riemannian.Exponential.expMapGlobal_smul
      (I := I) g hg (c t) (V t) s
  have hcont : ContinuousAt
      (fun s : ℝ => exponentialVariation (I := I) g hg c V (s, t)) 0 := by
    rw [heq]
    exact (Riemannian.Geodesic.continuous_globalGeodesic
      (I := I) g hg (c t) (V t)).continuousAt
  have hsrc :
      exponentialVariation (I := I) g hg c V (0, t) ∈ (chartAt H (c t)).source := by
    rw [exponentialVariation_zero]
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) (I := I)]
    exact mem_extChartAt_source (I := I) (c t)
  rw [variationalField_apply]
  change mfderiv 𝓘(ℝ, ℝ) I
    (fun s : ℝ => exponentialVariation (I := I) g hg c V (s, t)) 0 1 = V t
  rw [Riemannian.Geodesic.mfderiv_eq_of_hasDerivAt_extChartAt
    (I := I) hcont hsrc
    (hasDerivAt_extChartAt_exponentialVariation_zero (I := I) g hg c V t)]
  rw [exponentialVariation_zero]
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) (c t))

/-- **Math.** If the complete-exponential family has order-`r` regularity on
the parameter rectangle, it is an order-`r` variation with one time strip. -/
theorem exponentialVariation_isVariationOfOrder_of_contMDiffOn
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) {r : ℕ∞ω} {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε)
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I r
      (exponentialVariation (I := I) g hg c V)
      (Ioo (-ε) ε ×ˢ Icc 0 a)) :
    IsVariationOfOrder I r c a ε (exponentialVariation (I := I) g hg c V) := by
  exact IsDifferentiableVariationOfOrder.isVariationOfOrder hregular ha hε
    (fun t _ => exponentialVariation_zero (I := I) g hg c V t)

/-- **Math.** Package finite-subdivision regularity of the complete-exponential
family as an order-`r` variation.  The continuity hypothesis is stated
separately because continuity at subdivision points is part of the variation
definition, while the segment regularity is supplied by the finite-cover
argument in do Carmo's proof. -/
theorem exponentialVariation_isVariationOfOrder_of_piecewise_contMDiffOn
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) {r : ℕ∞ω} {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε)
    (hcontinuous : ContinuousOn
      (exponentialVariation (I := I) g hg c V)
      (Ioo (-ε) ε ×ˢ Icc 0 a))
    (hpieces : ∃ (n : ℕ) (τ : ℕ → ℝ),
      0 < n ∧ τ 0 = 0 ∧ τ n = a ∧
        (∀ i < n, τ i < τ (i + 1)) ∧
        ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I r
          (exponentialVariation (I := I) g hg c V)
          (Ioo (-ε) ε ×ˢ Icc (τ i) (τ (i + 1)))) :
    IsVariationOfOrder I r c a ε
      (exponentialVariation (I := I) g hg c V) := by
  refine ⟨hε, hcontinuous, ?_, hpieces⟩
  intro t _
  exact exponentialVariation_zero (I := I) g hg c V t

/-- **Math.** Legacy `C¹` projection of the finite-subdivision packaging
theorem for a complete-exponential family. -/
theorem exponentialVariation_isVariation_of_piecewise_contMDiffOn
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε)
    (hcontinuous : ContinuousOn
      (exponentialVariation (I := I) g hg c V)
      (Ioo (-ε) ε ×ˢ Icc 0 a))
    (hpieces : ∃ (n : ℕ) (τ : ℕ → ℝ),
      0 < n ∧ τ 0 = 0 ∧ τ n = a ∧
        (∀ i < n, τ i < τ (i + 1)) ∧
        ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1
          (exponentialVariation (I := I) g hg c V)
          (Ioo (-ε) ε ×ˢ Icc (τ i) (τ (i + 1)))) :
    IsVariation I c a ε
      (exponentialVariation (I := I) g hg c V) := by
  exact (exponentialVariation_isVariationOfOrder_of_piecewise_contMDiffOn
    (I := I) g hg c V ha hε hcontinuous hpieces).isVariation (by norm_num)

/-- **Math.** Finite-subdivision existence of a proper variation with a
prescribed field, once continuity and segment regularity of the complete-
exponential family have been extracted. -/
theorem exists_properVariation_with_variationalField_of_piecewise_contMDiffOn
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hV0 : V 0 = 0) (hVa : V a = 0)
    (hcontinuous : ContinuousOn
      (exponentialVariation (I := I) g hg c V)
      (Ioo (-ε) ε ×ˢ Icc 0 a))
    (hpieces : ∃ (n : ℕ) (τ : ℕ → ℝ),
      0 < n ∧ τ 0 = 0 ∧ τ n = a ∧
        (∀ i < n, τ i < τ (i + 1)) ∧
        ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1
          (exponentialVariation (I := I) g hg c V)
          (Ioo (-ε) ε ×ˢ Icc (τ i) (τ (i + 1)))) :
    ∃ f : ℝ × ℝ → M,
      IsVariation I c a ε f ∧
      IsProperVariation c a ε f ∧
      variationalField I f = V := by
  let f : ℝ × ℝ → M := exponentialVariation (I := I) g hg c V
  refine ⟨f, ?_, ?_, ?_⟩
  · exact exponentialVariation_isVariation_of_piecewise_contMDiffOn
      (I := I) g hg c V ha hε hcontinuous hpieces
  · exact exponentialVariation_isProperVariation
      (I := I) g hg c V hV0 hVa
  · exact variationalField_exponentialVariation (I := I) g hg c V

/-- **Math.** If the complete-exponential family has the regularity required
by the legacy `C¹` interface on a strip, then it is a variation. -/
theorem exponentialVariation_isVariation_of_contMDiffOn
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε)
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1
      (exponentialVariation (I := I) g hg c V)
      (Ioo (-ε) ε ×ˢ Icc 0 a)) :
    IsVariation I c a ε (exponentialVariation (I := I) g hg c V) := by
  exact (exponentialVariation_isVariationOfOrder_of_contMDiffOn
    (I := I) g hg c V ha hε hregular).isVariation (by norm_num)

/-- **Math.** Bundled complete-exponential construction of a proper variation
with a prescribed field, conditional only on the strip regularity needed by
the definition of variation. -/
theorem exists_properVariation_with_variationalField_of_contMDiffOn
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hV0 : V 0 = 0) (hVa : V a = 0)
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1
      (exponentialVariation (I := I) g hg c V)
      (Ioo (-ε) ε ×ˢ Icc 0 a)) :
    ∃ f : ℝ × ℝ → M,
      IsVariation I c a ε f ∧
      IsProperVariation c a ε f ∧
      variationalField I f = V := by
  let f : ℝ × ℝ → M := exponentialVariation (I := I) g hg c V
  refine ⟨f, ?_, ?_, ?_⟩
  · exact exponentialVariation_isVariation_of_contMDiffOn
      (I := I) g hg c V ha hε hregular
  · exact exponentialVariation_isProperVariation
      (I := I) g hg c V hV0 hVa
  · exact variationalField_exponentialVariation (I := I) g hg c V

/-! ### Public Proposition 2.2 wrapper -/

/-- **Math.** do Carmo Ch. 9, Proposition 2.2 (`prop:dc-ch9-2-2`), in the
regularity form exposed by the complete-exponential construction.

The book obtains the strip regularity from a finite subdivision and a finite
normal-neighborhood argument.  The present API makes that analytic input
explicit: once the exponential family is `C¹` on the parameter strip, it is a
variation with the prescribed variational field, and vanishing endpoint field
values make it proper.  This wrapper gives downstream first- and second-
variation arguments a stable proposition-level entry point while leaving the
finite-cover extraction as a separate theorem. -/
theorem exists_properVariation_with_variationalField
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hV0 : V 0 = 0) (hVa : V a = 0)
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1
      (exponentialVariation (I := I) g hg c V)
      (Ioo (-ε) ε ×ˢ Icc 0 a)) :
    ∃ f : ℝ × ℝ → M,
      IsVariation I c a ε f ∧
      IsProperVariation c a ε f ∧
      variationalField I f = V := by
  exact exists_properVariation_with_variationalField_of_contMDiffOn
    (I := I) g hg c V ha hε hV0 hVa hregular

/-! ### Prescribed fields without endpoint constraints -/

/-- **Math.** A complete-exponential family realizes an arbitrary prescribed
variational field as soon as its parameter rectangle has the regularity required
by the definition of a variation.  Endpoint conditions are deliberately absent
here; adding `V 0 = V a = 0` gives the proper-variation companion above.

This is the direct existence slice of do Carmo Ch. 9, Proposition 2.2.  The
remaining finite-cover argument for an arbitrary piecewise differentiable curve
and field is represented by the explicit strip-regularity hypothesis.
-/
theorem exists_variation_with_variationalField_of_contMDiffOn
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (c : ℝ → M) (V : ℝ → E) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε)
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1
      (exponentialVariation (I := I) g hg c V)
      (Ioo (-ε) ε ×ˢ Icc 0 a)) :
    ∃ f : ℝ × ℝ → M,
      IsVariation I c a ε f ∧ variationalField I f = V := by
  let f : ℝ × ℝ → M := exponentialVariation (I := I) g hg c V
  refine ⟨f, ?_, ?_⟩
  · exact exponentialVariation_isVariation_of_contMDiffOn
      (I := I) g hg c V ha hε hregular
  · exact variationalField_exponentialVariation (I := I) g hg c V

/-- **Math.** Along a complete geodesic, the sine multiple of a parallel field
is the variational field of a proper smooth variation. The common product
strip is supplied by smooth moving-base dependence of the exponential map. -/
theorem exists_proper_sine_smoothExponentialVariation [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {e : ℝ → E} {a b : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hγc : Continuous γ)
    (he : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ e a b)
    (hsegment : Icc (0 : ℝ) 1 ⊆ Ioo a b) :
    ∃ ε : ℝ, 0 < ε ∧
      IsSmoothVariation I γ 1 ε
        (exponentialVariation (I := I) g hg γ
          (fun t => Real.sin (Real.pi * t) • e t)) ∧
      IsProperVariation γ 1 ε
        (exponentialVariation (I := I) g hg γ
          (fun t => Real.sin (Real.pi * t) • e t)) ∧
      variationalField I
        (exponentialVariation (I := I) g hg γ
          (fun t => Real.sin (Real.pi * t) • e t)) =
        fun t => Real.sin (Real.pi * t) • e t := by
  obtain ⟨ε, hε, J, _hJopen, hIJ, hsmooth⟩ :=
    Riemannian.Exponential.exists_contMDiffOn_infty_expMapGlobal_sine_parallel_strip
      (I := I) g hg hgeo hγc he hsegment
  have hsub : Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1 ⊆ Ioo (-ε) ε ×ˢ J :=
    prod_mono_right hIJ
  have hregular : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (exponentialVariation (I := I) g hg γ
        (fun t => Real.sin (Real.pi * t) • e t))
      (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1) := by
    unfold exponentialVariation
    exact hsmooth.mono hsub
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · exact exponentialVariation_isVariationOfOrder_of_contMDiffOn
      (I := I) g hg γ (fun t => Real.sin (Real.pi * t) • e t)
      one_pos hε hregular
  · apply exponentialVariation_isProperVariation
      (I := I) g hg γ (fun t => Real.sin (Real.pi * t) • e t)
    · simp
    · simp
  · exact variationalField_exponentialVariation
      (I := I) g hg γ (fun t => Real.sin (Real.pi * t) • e t)

/-- **Math.** Along a complete geodesic, the sine multiple of a parallel field
is the variational field of a proper variation. This is the `C¹` projection of
`exists_proper_sine_smoothExponentialVariation` and the concrete instance
of do Carmo's variation-existence proposition used in the Bonnet--Myers
argument. -/
theorem exists_proper_sine_exponentialVariation [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {e : ℝ → E} {a b : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hγc : Continuous γ)
    (he : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ e a b)
    (hsegment : Icc (0 : ℝ) 1 ⊆ Ioo a b) :
    ∃ ε : ℝ, 0 < ε ∧
      IsVariation I γ 1 ε
        (exponentialVariation (I := I) g hg γ
          (fun t => Real.sin (Real.pi * t) • e t)) ∧
      IsProperVariation γ 1 ε
        (exponentialVariation (I := I) g hg γ
          (fun t => Real.sin (Real.pi * t) • e t)) ∧
      variationalField I
        (exponentialVariation (I := I) g hg γ
          (fun t => Real.sin (Real.pi * t) • e t)) =
        fun t => Real.sin (Real.pi * t) • e t := by
  obtain ⟨ε, hε, hsmooth, hproper, hfield⟩ :=
    exists_proper_sine_smoothExponentialVariation
      (I := I) g hg hgeo hγc he hsegment
  exact ⟨ε, hε, hsmooth.isVariation (by simp), hproper, hfield⟩

end Riemannian.Variation
