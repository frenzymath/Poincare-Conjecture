import Mathlib.Topology.MetricSpace.HolderNorm

/-!
# Parabolic Holder control

This file packages the two estimates used by a short-time parabolic
iteration: a spatial Holder estimate on every time slice and a temporal
Holder estimate on a prescribed time set.  The package is deliberately
independent of charts and bundles, so it can be consumed by later section
space and DeTurck constructions.
-/

namespace Topping
namespace ParabolicPDE

open Set Filter Function
open scoped NNReal ENNReal Topology

noncomputable section

/-- Spatial Holder control of a space-time map on one time slice. -/
def SpatialHolderWith {X T V : Type*}
    [PseudoEMetricSpace X] [PseudoEMetricSpace T] [PseudoEMetricSpace V]
    (u : X × T → V) (C r : ℝ≥0) (t : T) : Prop :=
  HolderWith C r (fun x : X => u (x, t))

/-- Temporal Holder control of a space-time map at one spatial point. -/
def TemporalHolderOnWith {X T V : Type*}
    [PseudoEMetricSpace X] [PseudoEMetricSpace T] [PseudoEMetricSpace V]
    (u : X × T → V) (C r : ℝ≥0) (x : X) (J : Set T) : Prop :=
  HolderOnWith C r (fun t : T => u (x, t)) J

/-- Separate spatial and temporal Holder estimates on a time set. -/
structure ParabolicHolderControl {X T V : Type*}
    [PseudoEMetricSpace X] [PseudoEMetricSpace T] [PseudoEMetricSpace V]
    (u : X × T → V) (J : Set T)
    (Cs α Ct β : ℝ≥0) : Prop where
  spatial : ∀ t ∈ J, SpatialHolderWith u Cs α t
  temporal : ∀ x, TemporalHolderOnWith u Ct β x J

namespace ParabolicHolderControl

variable {X T V W : Type*}
  [PseudoEMetricSpace X] [PseudoEMetricSpace T]
  [PseudoEMetricSpace V] [PseudoEMetricSpace W]
  {u : X × T → V} {J : Set T}
  {Cs α Ct β : ℝ≥0}

/-! ## Closure under uniform limits -/

/- A Holder estimate is an order-closed condition in the target distance.  The
   filter form below is useful for Picard limits and avoids making a section
   solver part of the Holder-space API. -/

/-- Uniform filter limits of parabolically Holder-controlled fields retain the
    same spatial and temporal constants. -/
theorem of_tendsto
    {ι : Type*} {l : Filter ι} [NeBot l]
    {f : ι → X × T → V} {g : X × T → V}
    (hlim : ∀ z : X × T, Tendsto (fun i => f i z) l (𝓝 (g z)))
    (hcontrol : ∀ᶠ i in l,
      ParabolicHolderControl (f i) J Cs α Ct β) :
    ParabolicHolderControl g J Cs α Ct β := by
  refine ⟨?_, ?_⟩
  · intro t ht x y
    have hdist : Tendsto
        (fun i => edist (f i (x, t)) (f i (y, t))) l
        (𝓝 (edist (g (x, t)) (g (y, t)))) :=
      (hlim (x, t)).edist (hlim (y, t))
    have hev : ∀ᶠ i in l,
        edist (f i (x, t)) (f i (y, t)) ≤
          (Cs : ℝ≥0∞) * edist x y ^ (α : ℝ) :=
      hcontrol.mono (fun i hi => hi.spatial t ht x y)
    exact le_of_tendsto hdist hev
  · intro x s hs t ht
    have hdist : Tendsto
        (fun i => edist (f i (x, s)) (f i (x, t))) l
        (𝓝 (edist (g (x, s)) (g (x, t)))) :=
      (hlim (x, s)).edist (hlim (x, t))
    have hev : ∀ᶠ i in l,
        edist (f i (x, s)) (f i (x, t)) ≤
          (Ct : ℝ≥0∞) * edist s t ^ (β : ℝ) :=
      hcontrol.mono (fun i hi => hi.temporal x s hs t ht)
    exact le_of_tendsto hdist hev

/-- One-sided endpoint specialization of `of_tendsto`. -/
theorem of_tendsto_nhdsWithin_endpoint
    {X T V : Type*}
    [PseudoEMetricSpace X] [PseudoEMetricSpace T]
    [PseudoEMetricSpace V]
    {f : ℝ → X × T → V} {g : X × T → V}
    {J : Set T} {T₀ : ℝ} {Cs α Ct β : ℝ≥0} (hT : 0 < T₀)
    (hlim : ∀ z : X × T,
      Tendsto (fun t => f t z) (nhdsWithin T₀ (Iio T₀)) (𝓝 (g z)))
    (hcontrol : ∀ᶠ t in nhdsWithin T₀ (Iio T₀),
      ParabolicHolderControl (f t) J Cs α Ct β) :
    ParabolicHolderControl g J Cs α Ct β := by
  letI : NeBot (nhdsWithin T₀ (Iio T₀)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact of_tendsto hlim hcontrol

/-- Increasing either Holder constant preserves parabolic control. -/
theorem mono
    (h : ParabolicHolderControl u J Cs α Ct β)
    {Ds Dt : ℝ≥0} (hCs : Cs ≤ Ds) (hCt : Ct ≤ Dt) :
    ParabolicHolderControl u J Ds α Dt β := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (h.spatial t ht).mono hCs
  · intro x s hs t ht
    exact (h.temporal x s hs t ht).trans
      (mul_le_mul_left (ENNReal.coe_le_coe.mpr hCt) _)

/- A pair of explicit Lipschitz estimates is the basic exponent-one input
   used when a section-space construction supplies separate space and time
   bounds. -/
theorem of_lipschitz
    {u : X × T → V} {J : Set T} {Cs Ct : ℝ≥0}
    (hsp : ∀ t ∈ J, LipschitzWith Cs (fun x : X => u (x, t)))
    (htm : ∀ x, LipschitzOnWith Ct (fun t : T => u (x, t)) J) :
    ParabolicHolderControl u J Cs 1 Ct 1 := by
  refine ⟨?_, ?_⟩
  · intro t ht
    simpa [SpatialHolderWith] using (hsp t ht).holderWith
  · intro x
    simpa [TemporalHolderOnWith] using (htm x).holderOnWith

/-- Holder maps preserve the parabolic control package, with the expected
    composition constants and exponents. -/
theorem comp
    {F : V → W} {CF γ : ℝ≥0}
    (hF : HolderWith CF γ F)
    (h : ParabolicHolderControl u J Cs α Ct β) :
    ParabolicHolderControl (fun z => F (u z)) J
      (CF * Cs ^ (γ : ℝ)) (γ * α)
      (CF * Ct ^ (γ : ℝ)) (γ * β) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    simpa [SpatialHolderWith, Function.comp_def] using
      hF.comp (h.spatial t ht)
  · intro x
    simpa [TemporalHolderOnWith, Function.comp_def] using
      (hF.holderOnWith univ).comp (h.temporal x) (by
        intro t ht
        trivial)

/-- The separate estimates give a two-point estimate on the parabolic
rectangle.  The intermediate point is `(y,s)`, so no product metric or chart
choice is needed. -/
theorem edist_le_split
    (h : ParabolicHolderControl u J Cs α Ct β)
    {x y : X} {s t : T} (hs : s ∈ J) (ht : t ∈ J) :
    edist (u (x, s)) (u (y, t)) ≤
      (Cs : ℝ≥0∞) * edist x y ^ (α : ℝ) +
        (Ct : ℝ≥0∞) * edist s t ^ (β : ℝ) := by
  calc
    edist (u (x, s)) (u (y, t)) ≤
        edist (u (x, s)) (u (y, s)) +
          edist (u (y, s)) (u (y, t)) := edist_triangle _ _ _
    _ ≤ (Cs : ℝ≥0∞) * edist x y ^ (α : ℝ) +
          (Ct : ℝ≥0∞) * edist s t ^ (β : ℝ) :=
      add_le_add ((h.spatial s hs).edist_le x y)
        ((h.temporal y).edist_le hs ht)

/-- Positive spatial Holder control makes each fixed-time slice continuous. -/
theorem continuous_spatial_slice
    (h : ParabolicHolderControl u J Cs α Ct β)
    {t : T} (ht : t ∈ J) (hα : 0 < α) :
    Continuous (fun x : X => u (x, t)) := by
  simpa only [SpatialHolderWith] using (h.spatial t ht).continuous hα

/-- Positive temporal Holder control makes each fixed-space trace continuous
on the prescribed time set. -/
theorem continuous_temporal_slice
    (h : ParabolicHolderControl u J Cs α Ct β)
    (x : X) (hβ : 0 < β) :
    ContinuousOn (fun t : T => u (x, t)) J := by
  simpa only [TemporalHolderOnWith] using (h.temporal x).continuousOn hβ

end ParabolicHolderControl

end
end ParabolicPDE
end Topping
