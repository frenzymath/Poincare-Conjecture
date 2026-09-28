import Topping.RicciFlow.Existence.EndpointMetric

/-!
# Regularity of endpoint coefficient limits

Pointwise endpoint limits do not by themselves preserve regularity in the base
point.  This module isolates the elementary compactness-free bridge used in a
chartwise endpoint argument: a uniform Lipschitz estimate along a nontrivial
filter passes to the pointwise limit.  The bilinear specialization is the form
needed for metric coefficients in a fixed trivialization.

The result is deliberately a coefficient-level producer.  It does not assert
that the tangent fibres have been globally trivialized, nor that a Lipschitz
field is smooth.
-/

open scoped Topology NNReal
open Set Filter

noncomputable section

namespace Topping

/-! ## Limits of uniformly Lipschitz fields -/

/- The metric target in the basic limit argument need not be the real line.
This is useful when a coefficient is kept bundled in a finite-dimensional
tensor or operator space before its chart components are extracted. -/

/-- **Math.** A pointwise filter limit of a uniformly Lipschitz family with
values in any pseudo-metric space is Lipschitz.

The eventual hypothesis is useful for one-sided endpoint filters: estimates are
only required on the part of the flow sufficiently close to the endpoint. -/
theorem LipschitzWith.of_tendsto_nhds_of_pseudoMetric
    {X Y ι : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {l : Filter ι} [NeBot l]
    {f : ι → X → Y} {g : X → Y} {C : ℝ≥0}
    (hlim : ∀ x : X, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hLip : ∀ᶠ i in l, LipschitzWith C (f i)) :
    LipschitzWith C g := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdist : Tendsto (fun i => dist (f i x) (f i y)) l
      (𝓝 (dist (g x) (g y))) := (hlim x).dist (hlim y)
  have hev : ∀ᶠ i in l, dist (f i x) (f i y) ≤
      (C : ℝ) * dist x y :=
    hLip.mono (fun i hi => hi.dist_le_mul x y)
  exact le_of_tendsto hdist hev

/-- **Math.** One-sided endpoint form of
`LipschitzWith.of_tendsto_nhds_of_pseudoMetric`. -/
theorem LipschitzWith.of_tendsto_nhdsWithin_endpoint_of_pseudoMetric
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X → Y} {g : X → Y} {T : ℝ} {C : ℝ≥0}
    (hT : 0 < T)
    (hlim : ∀ x : X,
      Tendsto (fun t => f t x) (nhdsWithin T (Iio T)) (𝓝 (g x)))
    (hLip : ∀ᶠ t in nhdsWithin T (Iio T), LipschitzWith C (f t)) :
    LipschitzWith C g := by
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact LipschitzWith.of_tendsto_nhds_of_pseudoMetric hlim hLip

/-! ## Limits of uniformly Lipschitz scalar fields -/

/-- **Math.** A pointwise filter limit of a uniformly Lipschitz family is Lipschitz.

The eventual hypothesis is useful for one-sided endpoint filters: estimates are
only required on the part of the flow sufficiently close to the endpoint.
-/
theorem LipschitzWith.of_tendsto_nhds
    {X ι : Type*} [PseudoMetricSpace X]
    {l : Filter ι} [NeBot l]
    {f : ι → X → ℝ} {g : X → ℝ} {C : ℝ≥0}
    (hlim : ∀ x : X, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hLip : ∀ᶠ i in l, LipschitzWith C (f i)) :
    LipschitzWith C g := by
  exact LipschitzWith.of_tendsto_nhds_of_pseudoMetric hlim hLip

/-- **Math.** One-sided endpoint form of `LipschitzWith.of_tendsto_nhds`. -/
theorem LipschitzWith.of_tendsto_nhdsWithin_endpoint
    {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X → ℝ} {g : X → ℝ} {T : ℝ} {C : ℝ≥0}
    (hT : 0 < T)
    (hlim : ∀ x : X,
      Tendsto (fun t => f t x) (nhdsWithin T (Iio T)) (𝓝 (g x)))
    (hLip : ∀ᶠ t in nhdsWithin T (Iio T), LipschitzWith C (f t)) :
    LipschitzWith C g := by
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact LipschitzWith.of_tendsto_nhdsWithin_endpoint_of_pseudoMetric hT hlim hLip

/-! ## Fixed-trivialization bilinear coefficients -/

/-- **Math.** Uniform endpoint Lipschitz control for a family of bilinear coefficients.

The estimate may depend on the two fixed fibre vectors, as it does for a
coordinate coefficient of a metric tensor. -/
theorem bilinearCoefficient_lipschitz_of_tendsto_nhds
    {X V ι : Type*} [PseudoMetricSpace X]
    [AddCommGroup V] [Module ℝ V]
    {l : Filter ι} [NeBot l]
    {f : ι → X → V → V → ℝ} {g : X → V → V → ℝ}
    {C : V → V → ℝ≥0}
    (hlim : ∀ (v w : V) (x : X),
      Tendsto (fun i => f i x v w) l (𝓝 (g x v w)))
    (hLip : ∀ᶠ i in l, ∀ (v w : V),
      LipschitzWith (C v w) (fun x => f i x v w)) :
    ∀ (v w : V), LipschitzWith (C v w) (fun x => g x v w) := by
  intro v w
  apply LipschitzWith.of_tendsto_nhds
    (hlim := fun x => hlim v w x)
    (hLip := hLip.mono (fun i hi => hi v w))

/-- **Math.** Endpoint-filter specialization of the bilinear coefficient bridge. -/
theorem bilinearCoefficient_lipschitz_of_tendsto_nhdsWithin_endpoint
    {X V : Type*} [PseudoMetricSpace X]
    [AddCommGroup V] [Module ℝ V]
    {f : ℝ → X → V → V → ℝ} {g : X → V → V → ℝ}
    {T : ℝ} {C : V → V → ℝ≥0}
    (hT : 0 < T)
    (hlim : ∀ (v w : V) (x : X),
      Tendsto (fun t => f t x v w) (nhdsWithin T (Iio T)) (𝓝 (g x v w)))
    (hLip : ∀ᶠ t in nhdsWithin T (Iio T), ∀ (v w : V),
      LipschitzWith (C v w) (fun x => f t x v w)) :
    ∀ (v w : V), LipschitzWith (C v w) (fun x => g x v w) := by
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact bilinearCoefficient_lipschitz_of_tendsto_nhds hlim hLip

/-- **Math.** The endpoint coefficient field is continuous in the base point under the
same uniform Lipschitz hypothesis. -/
theorem continuous_bilinearCoefficient_of_tendsto_nhdsWithin_endpoint
    {X V : Type*} [PseudoMetricSpace X]
    [AddCommGroup V] [Module ℝ V]
    {f : ℝ → X → V → V → ℝ} {g : X → V → V → ℝ}
    {T : ℝ} {C : V → V → ℝ≥0}
    (hT : 0 < T)
    (hlim : ∀ (v w : V) (x : X),
      Tendsto (fun t => f t x v w) (nhdsWithin T (Iio T)) (𝓝 (g x v w)))
    (hLip : ∀ᶠ t in nhdsWithin T (Iio T), ∀ (v w : V),
      LipschitzWith (C v w) (fun x => f t x v w)) :
    ∀ (v w : V), Continuous (fun x => g x v w) := by
  intro v w
  exact (bilinearCoefficient_lipschitz_of_tendsto_nhdsWithin_endpoint
    hT hlim hLip v w).continuous

/-! The preceding theorem controls each fixed pair of fibre vectors.  In a
finite-dimensional fixed trivialization, bilinearity upgrades that pointwise
control to continuity of the joint coefficient evaluator. -/

/-- **Math.** Uniform filter-Lipschitz control and bilinearity give joint
continuity of the limiting coefficient in the base point and both fibre
vectors.  The conclusion is explicitly fixed-trivialization; it makes no
claim about a global bundle tensor or smoothness. -/
theorem continuous_joint_bilinearCoefficient_of_tendsto_nhds
    {X V ι : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {l : Filter ι} [NeBot l]
    {f : ι → X → V → V → ℝ} {g : X → V → V → ℝ}
    {C : V → V → ℝ≥0}
    (hlim : ∀ (v w : V) (x : X),
      Tendsto (fun i => f i x v w) l (𝓝 (g x v w)))
    (hLip : ∀ᶠ i in l, ∀ (v w : V),
      LipschitzWith (C v w) (fun x => f i x v w))
    (hbilin : ∀ x : X, IsBilinearMap ℝ (g x)) :
    Continuous (fun q : (X × V) × V => g q.1.1 q.1.2 q.2) := by
  let G : X → V →L[ℝ] V →L[ℝ] ℝ :=
    fun x => (hbilin x).toContinuousBilinearMap
  have hG : Continuous G := by
    refine continuous_clm_apply.mpr ?_
    intro v
    refine continuous_clm_apply.mpr ?_
    intro w
    simpa [G] using
      (bilinearCoefficient_lipschitz_of_tendsto_nhds hlim hLip v w).continuous
  have hGV : Continuous (fun q : X × V => G q.1 q.2) :=
    (hG.comp continuous_fst).clm_apply continuous_snd
  have hGVprod :
      Continuous (fun q : (X × V) × V => G q.1.1 q.1.2) :=
    hGV.comp continuous_fst
  have hGvw :
      Continuous (fun q : (X × V) × V => G q.1.1 q.1.2 q.2) :=
    hGVprod.clm_apply continuous_snd
  simpa [G] using hGvw

/-- **Math.** Uniform endpoint Lipschitz control and bilinearity give joint
continuity of the limiting coefficient in the base point and both fibre
vectors.  The conclusion is explicitly fixed-trivialization; it makes no
claim about a global bundle tensor or smoothness. -/
theorem continuous_joint_bilinearCoefficient_of_tendsto_nhdsWithin_endpoint
    {X V : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {f : ℝ → X → V → V → ℝ} {g : X → V → V → ℝ}
    {T : ℝ} {C : V → V → ℝ≥0}
    (hT : 0 < T)
    (hlim : ∀ (v w : V) (x : X),
      Tendsto (fun t => f t x v w) (nhdsWithin T (Iio T)) (𝓝 (g x v w)))
    (hLip : ∀ᶠ t in nhdsWithin T (Iio T), ∀ (v w : V),
      LipschitzWith (C v w) (fun x => f t x v w))
    (hbilin : ∀ x : X, IsBilinearMap ℝ (g x)) :
    Continuous (fun q : (X × V) × V => g q.1.1 q.1.2 q.2) := by
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact continuous_joint_bilinearCoefficient_of_tendsto_nhds hlim hLip hbilin

#print axioms LipschitzWith.of_tendsto_nhds
#print axioms LipschitzWith.of_tendsto_nhdsWithin_endpoint
#print axioms LipschitzWith.of_tendsto_nhds_of_pseudoMetric
#print axioms LipschitzWith.of_tendsto_nhdsWithin_endpoint_of_pseudoMetric
#print axioms bilinearCoefficient_lipschitz_of_tendsto_nhds
#print axioms bilinearCoefficient_lipschitz_of_tendsto_nhdsWithin_endpoint
#print axioms continuous_bilinearCoefficient_of_tendsto_nhdsWithin_endpoint
#print axioms continuous_joint_bilinearCoefficient_of_tendsto_nhds
#print axioms continuous_joint_bilinearCoefficient_of_tendsto_nhdsWithin_endpoint

end Topping

end
