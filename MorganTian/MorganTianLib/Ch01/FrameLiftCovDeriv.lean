import MorganTianLib.Ch01.ChartIndexSeam
import MorganTianLib.Ch01.FrameRadialBridge

/-!
# Poincaré Ch. 1 — in a parallel frame the covariant derivative is the coordinate derivative

Along a geodesic `γ` we have a **parallel** `g`-orthonormal frame
`e : Fin (dim M) → ℝ → E` (`FrameRadialBridge`). A field along `γ` may be given by its
coefficient vector `W : ℝ → 𝔼` (`𝔼 = EuclideanSpace ℝ (Fin (dim M))`), lifted to the manifold
by `frameLift g γ e t x = ∑ᵢ ⟪𝔟 i, x⟫ • e i t`. This file proves the fact that makes the whole
frame-coefficient calculus of `FrameJacobiSystem`/`FrameRadialBridge` legitimate: **in a
parallel frame the (chart) covariant derivative of the lift is just the coordinate derivative
of the coefficients**,

`covariantDerivCoord g α (φ_α ∘ γ) (chartVectorRep γ α (frameLift ∘ W)) t
  = chartVectorRep γ α (frameLift ∘ (deriv-of-)W) t`,

stated with `DW` an arbitrary `HasDerivAt` witness for `W` at `t` (so no global differentiability
of `W` is required).

**Proof shape.** Three ingredients, each isolated below:

* `chartVectorRep_frameLift_eq` — the lift, read through the chart at `α`, is the sum
  `∑ᵢ fᵢ • Êᵢ` of the *scalar* coefficient functions `fᵢ s = ⟪𝔟 i, W s⟫` against the chart
  readings `Êᵢ = chartVectorRep γ α (e i)` of the frame. Pure algebra: `tangentCoordChange` is
  a continuous linear map, so it commutes with the finite sum defining `frameLift`.
* `covariantDerivCoord_sum` / `covariantDerivCoord_sum_smul` — `covariantDerivCoord` is
  additive over a finite sum and obeys the Leibniz rule against a scalar function, the
  `Finset`-indexed generalization of OpenGALib's `covariantDerivCoord_add` /
  `covariantDerivCoord_smul` (do Carmo Prop. 2.2 (a), (b)).
* The frame being **parallel** kills the `Êᵢ` term: `IsParallelAlongOn.isParallelSolOn_of_mem_source`
  localizes the patchwork parallelism to a single-chart certificate, and
  `IsParallelSolOn.covariantDerivCoord_eq_zero` (`ParallelFrame`) reads off
  `covariantDerivCoord g α (φ_α ∘ γ) Êᵢ t = 0` there, so only the `fᵢ' • Êᵢ` terms of the
  Leibniz expansion survive — exactly the coefficients of `DW`.

Blueprint: `prop:minimal-geodesic-no-conjugate`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4;
do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.2.
-/

open Set Filter Riemannian Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The standard orthonormal basis of the coefficient space (as in `FrameRadialBridge`). -/
local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-! ### Step 1: the chart reading of the lift is a sum of scalar functions times frame
readings -/

/-- **Math.** **The lift, read through a chart, expands in the frame.** For any coefficient
curve `X : ℝ → 𝔼`,

`chartVectorRep γ α (frameLift g γ e · (X ·)) = fun s => ∑ᵢ ⟪𝔟 i, X s⟫ • chartVectorRep γ α (e i) s`.

`frameLift` is by definition `∑ᵢ ⟪𝔟 i, x⟫ • e i t`, and `chartVectorRep γ α · s` is
`tangentCoordChange I (γ s) α (γ s)`, a **continuous linear map**, so it commutes with the
finite sum and the scalar multiples. -/
theorem chartVectorRep_frameLift_eq (g : RiemannianMetric I M) (γ : ℝ → M) (α : M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (X : ℝ → 𝔼) :
    chartVectorRep (I := I) γ α (fun s => frameLift (I := I) g γ e s (X s))
      = fun s => ∑ i, ⟪(𝔟 i : 𝔼), X s⟫ • chartVectorRep (I := I) γ α (e i) s := by
  funext s
  rw [chartVectorRep_apply]
  show tangentCoordChange I (γ s) α (γ s)
      (∑ i, ⟪(𝔟 i : 𝔼), X s⟫ • (e i s : TangentSpace I (γ s))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← chartVectorRep_apply]

/-! ### Step 2: `covariantDerivCoord` is additive over a finite sum, and obeys Leibniz -/

/-- **Math.** do Carmo Ch. 2, Prop. 2.2 (a), the `Finset`-indexed generalization: the
covariant derivative along a curve is additive over a finite sum of vector fields,

`D/dt (∑ᵢ Vᵢ) = ∑ᵢ D/dt Vᵢ`.

`deriv` distributes over the finite sum (`HasDerivAt.sum`), and the Christoffel contraction
distributes over it because `w ↦ Γ(v, w)(y)` is a continuous linear map
(`chartChristoffelContractionRight`, `map_sum`). -/
theorem covariantDerivCoord_sum {g : RiemannianMetric I M} {α : M} {u : ℝ → E}
    {ι : Type*} (s : Finset ι) (V : ι → ℝ → E) {t : ℝ}
    (hV : ∀ i ∈ s, DifferentiableAt ℝ (V i) t) :
    covariantDerivCoord (I := I) g α u (fun τ => ∑ i ∈ s, V i τ) t
      = ∑ i ∈ s, covariantDerivCoord (I := I) g α u (V i) t := by
  classical
  have hsum_eq : (∑ i ∈ s, V i) = fun τ => ∑ i ∈ s, V i τ := by
    funext τ; rw [Finset.sum_apply]
  have hderiv : HasDerivAt (fun τ => ∑ i ∈ s, V i τ) (∑ i ∈ s, deriv (V i) t) t := by
    rw [← hsum_eq]
    exact HasDerivAt.sum fun i hi => (hV i hi).hasDerivAt
  have hcontr : Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
      (∑ i ∈ s, V i t) (u t)
      = ∑ i ∈ s, Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V i t) (u t) := by
    have h := map_sum (chartChristoffelContractionRight (I := I) g α (deriv u t) (u t))
      (fun i => V i t) s
    simpa only [chartChristoffelContractionRight_apply] using h
  simp only [covariantDerivCoord_def, hderiv.deriv, hcontr, Finset.sum_add_distrib]

/-- **Math.** do Carmo Ch. 2, Prop. 2.2 (a) + (b), combined and generalized to a `Finset`-indexed
sum of scalar multiples: for scalar functions `fᵢ` and vector fields `Vᵢ` along `u`, all
differentiable at `t`,

`D/dt (∑ᵢ fᵢ Vᵢ) t = ∑ᵢ (fᵢ'(t) Vᵢ(t) + fᵢ(t) D/dt Vᵢ(t))`.

`covariantDerivCoord_sum` reduces this to the single-term Leibniz rule
(`covariantDerivCoord_smul`, do Carmo Prop. 2.2 (b)), applied termwise. -/
theorem covariantDerivCoord_sum_smul {g : RiemannianMetric I M} {α : M} {u : ℝ → E}
    {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (V : ι → ℝ → E) {t : ℝ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) t) (hV : ∀ i ∈ s, DifferentiableAt ℝ (V i) t) :
    covariantDerivCoord (I := I) g α u (fun τ => ∑ i ∈ s, f i τ • V i τ) t
      = ∑ i ∈ s, (deriv (f i) t • V i t + f i t • covariantDerivCoord (I := I) g α u (V i) t) := by
  classical
  rw [covariantDerivCoord_sum (I := I) s (fun i τ => f i τ • V i τ)
    (fun i hi => (hf i hi).smul (hV i hi))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hsmul := covariantDerivCoord_smul (I := I) g α u (f i) (V i) (hf i hi) (hV i hi)
  have heq : (f i • V i) = fun τ => f i τ • V i τ := by funext τ; rw [Pi.smul_apply']
  rwa [heq] at hsmul

/-! ### The main theorem -/

/-- **Math.** **In a parallel frame the covariant derivative is the coordinate derivative.**
Let `γ` be a geodesic on `[a, b]` carrying a parallel `g`-orthonormal frame `e`, and let
`[c, d] ⊆ [a, b]` be a subinterval whose `γ`-image lies in the chart at `α`. For a coefficient
curve `W : ℝ → 𝔼` with `HasDerivAt W (DW t) t` at an interior time `t ∈ (c, d)`, the covariant
derivative (`covariantDerivCoord`, read in the chart at `α`) of the chart reading of the lift
`frameLift g γ e · (W ·)` is the chart reading of the lift of `DW`:

`covariantDerivCoord g α (φ_α ∘ γ) (chartVectorRep γ α (frameLift ∘ W)) t
  = chartVectorRep γ α (frameLift ∘ DW) t`.

**Proof.** Expand both sides through `chartVectorRep_frameLift_eq` as sums
`∑ᵢ fᵢ • Êᵢ` (`fᵢ s = ⟪𝔟 i, W s⟫`, `Êᵢ = chartVectorRep γ α (e i)`) and `∑ᵢ ⟪𝔟 i, DW t⟫ • Êᵢ t`.
Localize the parallelism of `e i` to the chart at `α`
(`IsParallelAlongOn.isParallelSolOn_of_mem_source`), which hands us both differentiability of
`Êᵢ` at `t` and the vanishing of its covariant derivative there
(`IsParallelSolOn.differentiableAt`, `IsParallelSolOn.covariantDerivCoord_eq_zero`). The
`Finset`-Leibniz rule `covariantDerivCoord_sum_smul` then reduces the left side to
`∑ᵢ (fᵢ'(t) • Êᵢ(t) + fᵢ(t) • 0)`, and `fᵢ'(t) = ⟪𝔟 i, DW t⟫` because `x ↦ ⟪𝔟 i, x⟫` is a
continuous linear map composed with `W`, matching the right side termwise.

This is what legitimizes reading off the covariant derivative of a frame-coefficient field
purely from the coordinate derivative of its coefficients, throughout `FrameJacobiSystem` /
`FrameRadialBridge`.

Blueprint: `prop:minimal-geodesic-no-conjugate`. -/
theorem covariantDerivCoord_chartVectorRep_frameLift
    {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {a b : ℝ}
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {α : M} {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (hsrc : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H α).source)
    {W DW : ℝ → 𝔼} {t : ℝ} (ht : t ∈ Ioo c d)
    (hW : HasDerivAt W (DW t) t) :
    covariantDerivCoord (I := I) g α (fun s => extChartAt I α (γ s))
        (chartVectorRep (I := I) γ α (fun s => frameLift (I := I) g γ e s (W s))) t
      = chartVectorRep (I := I) γ α (fun s => frameLift (I := I) g γ e s (DW s)) t := by
  classical
  have hsol : ∀ i, IsParallelSolOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (chartVectorRep (I := I) γ α (e i)) c d :=
    fun i => (hPar i).isParallelSolOn_of_mem_source hgeo hγc hsub hsrc
  have hEzero : ∀ i, covariantDerivCoord (I := I) g α (fun s => extChartAt I α (γ s))
      (chartVectorRep (I := I) γ α (e i)) t = 0 :=
    fun i => (hsol i).covariantDerivCoord_eq_zero ht
  have hEdiff : ∀ i, DifferentiableAt ℝ (chartVectorRep (I := I) γ α (e i)) t :=
    fun i => (hsol i).differentiableAt ht
  have hf : ∀ i, HasDerivAt (fun s => ⟪(𝔟 i : 𝔼), W s⟫) (⟪(𝔟 i : 𝔼), DW t⟫) t := fun i => by
    have h := (innerSL ℝ (𝔟 i : 𝔼)).hasFDerivAt.comp_hasDerivAt t hW
    simpa only [Function.comp_def, innerSL_apply_apply] using h
  have hfdiff : ∀ i, DifferentiableAt ℝ (fun s => ⟪(𝔟 i : 𝔼), W s⟫) t :=
    fun i => (hf i).differentiableAt
  rw [chartVectorRep_frameLift_eq (I := I) g γ α e W,
    chartVectorRep_frameLift_eq (I := I) g γ α e DW]
  dsimp only
  rw [covariantDerivCoord_sum_smul (I := I) Finset.univ
    (fun i s => ⟪(𝔟 i : 𝔼), W s⟫) (fun i => chartVectorRep (I := I) γ α (e i))
    (fun i _ => hfdiff i) (fun i _ => hEdiff i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hf i).deriv, hEzero i, smul_zero, add_zero]

end MorganTianLib

end

#print axioms MorganTianLib.chartVectorRep_frameLift_eq
#print axioms MorganTianLib.covariantDerivCoord_sum
#print axioms MorganTianLib.covariantDerivCoord_sum_smul
#print axioms MorganTianLib.covariantDerivCoord_chartVectorRep_frameLift
