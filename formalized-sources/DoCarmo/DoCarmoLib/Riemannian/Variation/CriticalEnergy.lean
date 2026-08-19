import DoCarmoLib.Riemannian.Variation.FirstVariationFormula

/-!
# Proper geodesic variations are energy-critical

This file ties the endpoint condition in do Carmo Ch. 9, Definition 2.1 to the
segment first-variation formula.  The analytic and covariant-derivative data
remain explicit, but a proper `IsVariation` now supplies the two vanishing
endpoint values of its variational field automatically.
-/

open Set Riemannian Filter MeasureTheory
open scoped ContDiff Manifold Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** do Carmo Ch. 9, Proposition 2.5, the forward implication on a
segment: a geodesic is critical for energy under every proper variation.

The covariant-pair and domination hypotheses are precisely those of the
segment first-variation formula (`prop:dc-ch9-2-4`).  The geodesic equation is
encoded by `hW`, which says that the velocity field has covariant derivative
zero.  Unlike `hasDerivAt_dcEnergy_zero_of_geodesic`, the endpoint hypotheses
are not supplied separately: properness from `def:dc-ch9-2-1` forces the
variational field to vanish at `0` and `a`. -/
theorem IsVariation.hasDerivAt_dcEnergy_zero_of_proper_geodesic
    {g : RiemannianMetric I M} {c : ℝ → M} {f : ℝ × ℝ → M}
    {S T DsT DtS : ℝ × ℝ → E} {a ε : ℝ} {bound : ℝ → ℝ}
    (hvar : IsVariation I c a ε f) (hproper : IsProperVariation c a ε f)
    (ha : 0 ≤ a)
    (hS : ∀ t, S (0, t) = variationalField I f t)
    (hvel : ∀ σ t, T (σ, t) = DCVelocity (I := I) (fun τ => f (σ, τ)) t)
    (hslice : ∀ t ∈ uIoc 0 a, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => T (σ, t)) (fun σ => DsT (σ, t)) (-ε) ε)
    (hsdiff : ∀ t ∈ uIoc 0 a, IsChartDifferentiableOn (I := I)
      (fun σ => f (σ, t)) (-ε) ε)
    (hscont : ∀ t ∈ uIoc 0 a, ∀ σ ∈ Icc (-ε) ε,
      ContinuousAt (fun σ' => f (σ', t)) σ)
    (hF_meas : ∀ᶠ σ in nhds 0, AEStronglyMeasurable
      (fun t => g.metricInner (f (σ, t))
        (T (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)))
      (volume.restrict (uIoc 0 a)))
    (hF_int : IntervalIntegrable
      (fun t => g.metricInner (f (0, t))
        (T (0, t) : TangentSpace I (f (0, t))) (T (0, t))) volume 0 a)
    (hF'_meas : AEStronglyMeasurable
      (fun t => 2 * g.metricInner (f (0, t))
        (DsT (0, t) : TangentSpace I (f (0, t))) (T (0, t)))
      (volume.restrict (uIoc 0 a)))
    (h_bound : ∀ t ∈ uIoc 0 a, ∀ σ ∈ Ioo (-ε) ε,
      ‖2 * g.metricInner (f (σ, t))
        (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))‖ ≤ bound t)
    (hbound_int : IntervalIntegrable bound volume 0 a)
    (hsymm : ∀ t ∈ Ioo 0 a, DsT (0, t) = DtS (0, t))
    (hV : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (0, τ))
      (fun τ => S (0, τ)) (fun τ => DtS (0, τ)) 0 a)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (0, τ))
      (fun τ => T (0, τ)) (fun _ => 0) 0 a)
    (htdiff : IsChartDifferentiableOn (I := I) (fun τ => f (0, τ)) 0 a)
    (htcont : ∀ t ∈ Icc 0 a, ContinuousAt (fun τ => f (0, τ)) t)
    (hint₁ : IntervalIntegrable
      (fun t => g.metricInner (f (0, t))
        (DtS (0, t) : TangentSpace I (f (0, t))) (T (0, t))) volume 0 a)
    (hint₂ : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 a) :
    HasDerivAt (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) 0 a) 0 0 := by
  obtain ⟨hV0, hVa⟩ := hvar.variationalField_eq_zero_endpoints hproper
  have hS0 : S (0, 0) = 0 := by rw [hS]; exact hV0
  have hSa : S (0, a) = 0 := by rw [hS]; exact hVa
  have hslice' : ∀ t ∈ uIoc 0 a, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => T (σ, t)) (fun σ => DsT (σ, t))
        (0 - ε) (0 + ε) := by
    simpa only [zero_sub, zero_add] using hslice
  have hsdiff' : ∀ t ∈ uIoc 0 a, IsChartDifferentiableOn (I := I)
      (fun σ => f (σ, t)) (0 - ε) (0 + ε) := by
    simpa only [zero_sub, zero_add] using hsdiff
  have hscont' : ∀ t ∈ uIoc 0 a, ∀ σ ∈ Icc (0 - ε) (0 + ε),
      ContinuousAt (fun σ' => f (σ', t)) σ := by
    simpa only [zero_sub, zero_add] using hscont
  have hbound' : ∀ t ∈ uIoc 0 a, ∀ σ ∈ Ioo (0 - ε) (0 + ε),
      ‖2 * g.metricInner (f (σ, t))
        (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))‖ ≤ bound t := by
    simpa only [zero_sub, zero_add] using h_bound
  have hint₂' : IntervalIntegrable
      (fun t => g.metricInner (f (0, t))
        (S (0, t) : TangentSpace I (f (0, t))) (0 : E)) volume 0 a := by
    have hz : (fun t => g.metricInner (f (0, t))
        (S (0, t) : TangentSpace I (f (0, t))) (0 : E)) =
        (fun _ : ℝ => (0 : ℝ)) := by
      funext t
      exact g.metricInner_zero_right _ _
    rw [hz]
    exact hint₂
  exact hasDerivAt_dcEnergy_zero_of_geodesic (I := I) (g := g) (f := f)
      (T := T) (S := S) (DsT := DsT)
      (DtS := DtS) (s₀ := 0) (a := 0) (b := a) (ε := ε) (bound := bound)
      ha hvar.epsilon_pos hvel hslice' hsdiff' hscont' hF_meas hF_int hF'_meas
      hbound' hbound_int hsymm hV hW htdiff htcont hint₁
      hint₂' hS0 hSa

end Riemannian.Variation
