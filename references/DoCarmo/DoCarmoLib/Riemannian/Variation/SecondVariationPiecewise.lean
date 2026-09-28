import DoCarmoLib.Riemannian.Variation.SecondVariationFormula
import DoCarmoLib.Riemannian.Variation.IndexForm

/-!
# Finite-subdivision assembly of the second variation

This file performs the finite-subdivision step in do Carmo, Ch. 9, Prop. 2.8.  Its input is
the second-variation formula on each smooth segment.  Finite additivity of energy identifies
the derivative of the total energy with the sum of the segment derivatives, and the endpoint
pairings telescope to the jump term in formula (3).
-/

open Set Riemannian Filter MeasureTheory
open scoped BigOperators ContDiff Manifold Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Finite-subdivision assembly of do Carmo's second-variation formula.

For the subdivision `tau 0, ..., tau (k + 1)`, let `bulk i` be
`integral <V, V'' + R(gamma', V) gamma'>` on segment `i`.  At a subdivision point,
`minus i` and `plus i` are the pairings `<V, DV/dt>` with the left and right one-sided
covariant derivatives.  Thus the second variation on segment `i` has derivative

`2 * ((minus (i + 1) - plus i) - bulk i)`.

The hypotheses separate the two genuine analytic requirements of the assembly:

* `hint` gives finite additivity of energy on a neighbourhood of `s0`;
* `hfirst` says the segment energy functions are differentiable there, so differentiating
  their finite sum really is the sum of their derivatives.

Together with the per-segment second-variation identities `hsegment`, these imply the global
second variation, including the outer endpoint terms and all internal jumps. -/
theorem hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {bulk minus plus : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((minus (i + 1) - plus i) - bulk i)) s0) :
    HasDerivAt
      (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
        (tau 0) (tau (k + 1))))
      (2 * (minus (k + 1) - plus 0
        - ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1))
        - ∑ i ∈ Finset.range (k + 1), bulk i)) s0 := by
  have henergy :
      (fun s => DCEnergy (I := I) g (fun t => f (s, t)) (tau 0) (tau (k + 1)))
        =ᶠ[nhds s0]
      (fun s => ∑ i ∈ Finset.range (k + 1),
        DCEnergy (I := I) g (fun t => f (s, t)) (tau i) (tau (i + 1))) := by
    filter_upwards [hint] with s hs
    exact dcEnergy_eq_sum_subdivision (I := I) g (fun t => f (s, t)) tau (k + 1) hs
  have hderivSum :
      deriv (fun s => ∑ i ∈ Finset.range (k + 1),
        DCEnergy (I := I) g (fun t => f (s, t)) (tau i) (tau (i + 1)))
        =ᶠ[nhds s0]
      (fun s => ∑ i ∈ Finset.range (k + 1),
        deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))) s) := by
    filter_upwards [hfirst] with s hs
    exact deriv_fun_sum (u := Finset.range (k + 1))
      (fun i hi => hs i (Finset.mem_range.mp hi))
  have htotal :
      deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
        (tau 0) (tau (k + 1))) =ᶠ[nhds s0]
      (fun s => ∑ i ∈ Finset.range (k + 1),
        deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))) s) :=
    henergy.deriv.trans hderivSum
  have hsum := hasDerivAt_sum_segments_of_first_variation k
    (fun i s => deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
      (tau i) (tau (i + 1))) s)
    bulk minus plus s0 hsegment
  exact hsum.congr_of_eventuallyEq htotal

/-! ### Formula (5): non-proper finite-subdivision form -/

/-- **Math.** do Carmo Ch. 9, Remark 2.9 (`rem:dc-ch9-2-9`), formula (5)
assembled over a finite subdivision.

Unlike the proper specialization below, the two outer endpoint pairings are
retained.  On each segment `minus (i + 1) - plus i` is the sum of the
transverse-acceleration and `⟨V,DV/dt⟩` boundary terms from
`deriv_deriv_dcEnergy_eq_second_variation_nonproper`; telescoping them leaves
the outer boundary contribution and the internal one-sided jumps. -/
theorem hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation_nonproper
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {bulk minus plus : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((minus (i + 1) - plus i) - bulk i)) s0) :
    HasDerivAt
      (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
        (tau 0) (tau (k + 1))))
      (2 * (minus (k + 1) - plus 0
        - ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1))
        - ∑ i ∈ Finset.range (k + 1), bulk i)) s0 :=
  hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation
    (I := I) hint hfirst hsegment

/-- **Math.** Value form of formula (5) on a finite subdivision, retaining
both outer endpoint terms and every internal jump. -/
theorem deriv_deriv_dcEnergy_eq_piecewise_second_variation_nonproper
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {bulk minus plus : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((minus (i + 1) - plus i) - bulk i)) s0) :
    deriv (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
      (tau 0) (tau (k + 1)))) s0
      = 2 * (minus (k + 1) - plus 0
        - ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1))
        - ∑ i ∈ Finset.range (k + 1), bulk i) :=
  (hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation_nonproper
    (I := I) hint hfirst hsegment).deriv

/-! ### Formula (6): piecewise index-form assembly -/

/-- **Math.** do Carmo Ch. 9, Remark 2.10, formula (6) over a finite
subdivision.  Suppose each segment has already been reorganized into its index
form plus the transverse-acceleration boundary pairing.  The internal boundary
pairings telescope, and finite additivity of `indexForm` identifies the sum of
the segment index forms with the index form on the whole interval.

For a proper variation the two remaining values of `accel` are zero, reducing
the conclusion to `E''(s0) = 2 I(V,V)`. -/
theorem hasDerivAt_deriv_dcEnergy_eq_piecewise_indexForm
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {γ : ℝ → M} {V DV : ℝ → E} {accel : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hindex : ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t)
        - g.leviCivitaConnection.curvatureFormAt g (γ t)
            (DCVelocity (I := I) γ t) (V t : TangentSpace I (γ t))
            (DCVelocity (I := I) γ t) (V t))
      volume (tau i) (tau (i + 1)))
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((accel (i + 1) - accel i)
          + indexForm (I := I) g γ V DV (tau i) (tau (i + 1)))) s0) :
    HasDerivAt
      (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
        (tau 0) (tau (k + 1))))
      (2 * (accel (k + 1) - accel 0
        + indexForm (I := I) g γ V DV (tau 0) (tau (k + 1)))) s0 := by
  let bulk : ℕ → ℝ := fun i =>
    -indexForm (I := I) g γ V DV (tau i) (tau (i + 1))
  have hassembled :=
    hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation_nonproper
      (I := I) (g := g) (f := f) (tau := tau) (k := k) (s0 := s0)
      (bulk := bulk) (minus := accel) (plus := accel) hint hfirst (by
        intro i hi
        simpa [bulk, sub_neg_eq_add] using hsegment i hi)
  have hsum := indexForm_eq_sum_subdivision (I := I) g γ V DV tau (k + 1) hindex
  apply hassembled.congr_deriv
  simp only [sub_self, Finset.sum_const_zero, sub_zero, bulk,
    Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [← hsum]

/-- **Math.** Value form of the piecewise index-form identity. -/
theorem deriv_deriv_dcEnergy_eq_piecewise_indexForm
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {γ : ℝ → M} {V DV : ℝ → E} {accel : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hindex : ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t)
        - g.leviCivitaConnection.curvatureFormAt g (γ t)
            (DCVelocity (I := I) γ t) (V t : TangentSpace I (γ t))
            (DCVelocity (I := I) γ t) (V t))
      volume (tau i) (tau (i + 1)))
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((accel (i + 1) - accel i)
          + indexForm (I := I) g γ V DV (tau i) (tau (i + 1)))) s0) :
    deriv (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
      (tau 0) (tau (k + 1)))) s0
      = 2 * (accel (k + 1) - accel 0
        + indexForm (I := I) g γ V DV (tau 0) (tau (k + 1))) :=
  (hasDerivAt_deriv_dcEnergy_eq_piecewise_indexForm
    (I := I) hint hfirst hindex hsegment).deriv

/-- **Math.** do Carmo's formula (6) for a proper piecewise variation:
after the transverse-acceleration pairings vanish at both outer endpoints,
the second derivative of energy is twice the index form on the whole interval. -/
theorem hasDerivAt_deriv_dcEnergy_eq_piecewise_indexForm_of_proper
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {γ : ℝ → M} {V DV : ℝ → E} {accel : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hindex : ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t)
        - g.leviCivitaConnection.curvatureFormAt g (γ t)
            (DCVelocity (I := I) γ t) (V t : TangentSpace I (γ t))
            (DCVelocity (I := I) γ t) (V t))
      volume (tau i) (tau (i + 1)))
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((accel (i + 1) - accel i)
          + indexForm (I := I) g γ V DV (tau i) (tau (i + 1)))) s0)
    (haccel0 : accel 0 = 0) (haccelEnd : accel (k + 1) = 0) :
    HasDerivAt
      (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
        (tau 0) (tau (k + 1))))
      (2 * indexForm (I := I) g γ V DV (tau 0) (tau (k + 1))) s0 := by
  simpa [haccel0, haccelEnd] using
    hasDerivAt_deriv_dcEnergy_eq_piecewise_indexForm
      (I := I) hint hfirst hindex hsegment

/-- **Math.** Value form of the proper piecewise index-form identity. -/
theorem deriv_deriv_dcEnergy_eq_piecewise_indexForm_of_proper
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {γ : ℝ → M} {V DV : ℝ → E} {accel : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hindex : ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t)
        - g.leviCivitaConnection.curvatureFormAt g (γ t)
            (DCVelocity (I := I) γ t) (V t : TangentSpace I (γ t))
            (DCVelocity (I := I) γ t) (V t))
      volume (tau i) (tau (i + 1)))
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((accel (i + 1) - accel i)
          + indexForm (I := I) g γ V DV (tau i) (tau (i + 1)))) s0)
    (haccel0 : accel 0 = 0) (haccelEnd : accel (k + 1) = 0) :
    deriv (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
      (tau 0) (tau (k + 1)))) s0
      = 2 * indexForm (I := I) g γ V DV (tau 0) (tau (k + 1)) :=
  (hasDerivAt_deriv_dcEnergy_eq_piecewise_indexForm_of_proper
    (I := I) hint hfirst hindex hsegment haccel0 haccelEnd).deriv

/-- **Math.** Formula (3) at the finite-subdivision assembly level when the two outer
endpoint pairings vanish.

For a proper variation those endpoint pairings vanish; here their vanishing is exposed as
explicit scalar hypotheses rather than being derived from `IsProperVariation`. Consequently
the second derivative of the total energy is minus twice the sum of the segment bulk
integrals and the one-sided derivative jumps at all internal subdivision points. -/
theorem hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation_of_proper
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {bulk minus plus : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((minus (i + 1) - plus i) - bulk i)) s0)
    (hplus0 : plus 0 = 0) (hminusEnd : minus (k + 1) = 0) :
    HasDerivAt
      (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
        (tau 0) (tau (k + 1))))
      (-2 * ((∑ i ∈ Finset.range (k + 1), bulk i)
        + ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1)))) s0 := by
  have hglobal := hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation
    (I := I) hint hfirst hsegment
  apply hglobal.congr_deriv
  rw [hplus0, hminusEnd]
  ring

/-- **Math.** The value form of the finite-subdivision second-variation formula
when the two outer endpoint pairings vanish. -/
theorem deriv_deriv_dcEnergy_eq_piecewise_second_variation_of_proper
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {bulk minus plus : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((minus (i + 1) - plus i) - bulk i)) s0)
    (hplus0 : plus 0 = 0) (hminusEnd : minus (k + 1) = 0) :
    deriv (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
      (tau 0) (tau (k + 1)))) s0
      = -2 * ((∑ i ∈ Finset.range (k + 1), bulk i)
        + ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1))) :=
  (hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation_of_proper
    (I := I) hint hfirst hsegment hplus0 hminusEnd).deriv

end Riemannian.Variation
