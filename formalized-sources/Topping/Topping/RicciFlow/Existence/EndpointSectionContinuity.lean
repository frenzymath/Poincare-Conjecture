import Topping.RicciFlow.Existence.EndpointCoefficientRegularity

/-!
# Endpoint coefficients evaluated on continuous sections

The coefficient-limit module proves joint continuity in a fixed
trivialization.  This file records the direct section-space consumer: once
the two fibre arguments vary continuously in the base point, the limiting
coefficient remains continuous.  The set and endpoint-filter variants are
kept explicit so chartwise patching can use the same producer without
repeating product-space bookkeeping.
-/

open scoped Topology NNReal
open Set Filter

noncomputable section

namespace Topping

/-! ## General filter limits -/

/-- **Math.** A jointly continuous fixed-trivialization coefficient evaluated
on two continuous section fields is continuous in the base point. -/
theorem continuous_bilinearCoefficient_comp_of_tendsto_nhds
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
    (hbilin : ∀ x : X, IsBilinearMap ℝ (g x))
    {u v : X → V} (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => g x (u x) (v x)) := by
  have hjoint := continuous_joint_bilinearCoefficient_of_tendsto_nhds
    hlim hLip hbilin
  have hargs : Continuous (fun x : X => ((x, u x), v x)) :=
    (continuous_id.prodMk hu).prodMk hv
  have hcomp := hjoint.comp hargs
  change Continuous (fun x => g x (u x) (v x)) at hcomp
  exact hcomp

/-- **Math.** The same section-evaluation bridge on an arbitrary subset of the
base. -/
theorem continuousOn_bilinearCoefficient_comp_of_tendsto_nhds
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
    (hbilin : ∀ x : X, IsBilinearMap ℝ (g x))
    {u v : X → V} {s : Set X}
    (hu : ContinuousOn u s) (hv : ContinuousOn v s) :
    ContinuousOn (fun x => g x (u x) (v x)) s := by
  have hjoint := continuous_joint_bilinearCoefficient_of_tendsto_nhds
    hlim hLip hbilin
  have hargs : ContinuousOn (fun x : X => ((x, u x), v x)) s :=
    (continuousOn_id.prodMk hu).prodMk hv
  have hcomp := hjoint.comp_continuousOn hargs
  change ContinuousOn (fun x => g x (u x) (v x)) s at hcomp
  exact hcomp

/-! ## Map-valued and bounded-section consumers -/

/-- **Math.** The joint endpoint argument also yields continuity of the
continuous-bilinear-map valued coefficient field itself. -/
theorem continuous_bilinearCoefficientMap_of_tendsto_nhds
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
    Continuous (fun x => (hbilin x).toContinuousBilinearMap) := by
  let G : X → V →L[ℝ] V →L[ℝ] ℝ :=
    fun x => (hbilin x).toContinuousBilinearMap
  have hG : Continuous G := by
    refine continuous_clm_apply.mpr ?_
    intro v
    refine continuous_clm_apply.mpr ?_
    intro w
    simpa [G] using
      (bilinearCoefficient_lipschitz_of_tendsto_nhds hlim hLip v w).continuous
  change Continuous G
  exact hG

/-- **Math.** Endpoint-filter specialization of the map-valued coefficient
continuity producer. -/
theorem continuous_bilinearCoefficientMap_of_tendsto_nhdsWithin_endpoint
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
    Continuous (fun x => (hbilin x).toContinuousBilinearMap) := by
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact continuous_bilinearCoefficientMap_of_tendsto_nhds hlim hLip hbilin

/-- **Math.** On a compact base, the continuous coefficient-map field can be
regarded as a bounded continuous section.  The equality records its pointwise
value so later chartwise constructions can consume the bounded wrapper. -/
theorem exists_boundedContinuousCoefficientMap_of_tendsto_nhds
    {X V ι : Type*} [PseudoMetricSpace X] [CompactSpace X]
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
    ∃ G : BoundedContinuousFunction X (V →L[ℝ] V →L[ℝ] ℝ),
      ∀ x, G x = (hbilin x).toContinuousBilinearMap := by
  have hG : Continuous (fun x => (hbilin x).toContinuousBilinearMap) :=
    continuous_bilinearCoefficientMap_of_tendsto_nhds hlim hLip hbilin
  let Gc : C(X, V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousMap.mk (fun x => (hbilin x).toContinuousBilinearMap) hG
  refine ⟨BoundedContinuousFunction.mkOfCompact Gc, ?_⟩
  intro x
  rfl

/-- **Math.** Compact-base bounded-section packaging for endpoint limits. -/
theorem exists_boundedContinuousCoefficientMap_of_tendsto_nhdsWithin_endpoint
    {X V : Type*} [PseudoMetricSpace X] [CompactSpace X]
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
    ∃ G : BoundedContinuousFunction X (V →L[ℝ] V →L[ℝ] ℝ),
      ∀ x, G x = (hbilin x).toContinuousBilinearMap := by
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact exists_boundedContinuousCoefficientMap_of_tendsto_nhds
    hlim hLip hbilin

/-! ## Endpoint-filter specializations -/

/-- **Math.** Endpoint limits of uniformly Lipschitz coefficients remain
continuous after evaluation on two continuous section fields. -/
theorem continuous_bilinearCoefficient_comp_of_tendsto_nhdsWithin_endpoint
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
    (hbilin : ∀ x : X, IsBilinearMap ℝ (g x))
    {u v : X → V} (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => g x (u x) (v x)) := by
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact continuous_bilinearCoefficient_comp_of_tendsto_nhds
    hlim hLip hbilin hu hv

/-- **Math.** Endpoint section evaluation is continuous on any chosen base
subset. -/
theorem continuousOn_bilinearCoefficient_comp_of_tendsto_nhdsWithin_endpoint
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
    (hbilin : ∀ x : X, IsBilinearMap ℝ (g x))
    {u v : X → V} {s : Set X}
    (hu : ContinuousOn u s) (hv : ContinuousOn v s) :
    ContinuousOn (fun x => g x (u x) (v x)) s := by
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact continuousOn_bilinearCoefficient_comp_of_tendsto_nhds
    hlim hLip hbilin hu hv

/-! ## Diagonal evaluations -/

/-- **Math.** The quadratic coefficient obtained by evaluating both slots on
one continuous section is continuous. -/
theorem continuous_bilinearCoefficient_diag_of_tendsto_nhds
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
    (hbilin : ∀ x : X, IsBilinearMap ℝ (g x))
    {u : X → V} (hu : Continuous u) :
    Continuous (fun x => g x (u x) (u x)) := by
  exact continuous_bilinearCoefficient_comp_of_tendsto_nhds
    hlim hLip hbilin hu hu

/-- **Math.** Endpoint quadratic coefficient evaluation on one continuous
section is continuous. -/
theorem continuous_bilinearCoefficient_diag_of_tendsto_nhdsWithin_endpoint
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
    (hbilin : ∀ x : X, IsBilinearMap ℝ (g x))
    {u : X → V} (hu : Continuous u) :
    Continuous (fun x => g x (u x) (u x)) := by
  exact continuous_bilinearCoefficient_comp_of_tendsto_nhdsWithin_endpoint
    hT hlim hLip hbilin hu hu

#print axioms continuous_bilinearCoefficient_comp_of_tendsto_nhds
#print axioms continuousOn_bilinearCoefficient_comp_of_tendsto_nhds
#print axioms continuous_bilinearCoefficientMap_of_tendsto_nhds
#print axioms continuous_bilinearCoefficientMap_of_tendsto_nhdsWithin_endpoint
#print axioms exists_boundedContinuousCoefficientMap_of_tendsto_nhds
#print axioms exists_boundedContinuousCoefficientMap_of_tendsto_nhdsWithin_endpoint
#print axioms continuous_bilinearCoefficient_comp_of_tendsto_nhdsWithin_endpoint
#print axioms continuousOn_bilinearCoefficient_comp_of_tendsto_nhdsWithin_endpoint
#print axioms continuous_bilinearCoefficient_diag_of_tendsto_nhds
#print axioms continuous_bilinearCoefficient_diag_of_tendsto_nhdsWithin_endpoint

end Topping

end
