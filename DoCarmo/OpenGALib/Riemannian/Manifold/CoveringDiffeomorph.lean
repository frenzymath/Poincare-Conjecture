import OpenGALib.Riemannian.Manifold.CoveringMapConclusion
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Covering map + simply connected ⟹ diffeomorphism (do Carmo Ch. 7, §3, proof of Thm 3.1)

`CoveringMapConclusion.lean` proved do Carmo's Lemma 3.3: a metric-expanding smooth
local diffeomorphism `f : M → M'` out of a complete manifold `M` is a **covering
map**. The proof of the Hadamard theorem (do Carmo Ch. 7, §3.4) closes with the
sentence

> From Lemma 3.3, `exp_p` is a covering map. Since `M` is simply connected, `exp_p`
> is a diffeomorphism.

This file formalises that final topological+smooth step, independently of the
Jacobi-field input `lem:dc-ch7-3-2` (which supplies "`exp_p` is a local
diffeomorphism") and independently of the exponential map itself: it is a fact
about an **abstract** metric-expanding local diffeomorphism.

* `IsCoveringMap.bijective_of_simplyConnected` — the classical covering-space fact:
  a covering map out of a **preconnected, nonempty** total space `E` onto a
  **simply connected, locally path connected** base `X` is **bijective**. Proof:
  the identity `X → X` lifts (uniquely, mathlib's
  `IsCoveringMap.existsUnique_continuousMap_lifts`) to a continuous global section
  `s`; `f ∘ s = id` gives surjectivity, and `s ∘ f = id` follows because `s ∘ f`
  and `id` are two continuous lifts of `f` through the same point of the connected
  space `E`, hence equal (`IsCoveringMap.eq_of_comp_eq`), giving injectivity.
* `IsCoveringMap.homeomorphOfSimplyConnected` — packages it as a homeomorphism
  `E ≃ₜ X` (a continuous open bijection).
* `DCExpandsMetric.diffeomorphOfSimplyConnected` — the do Carmo Ch. 7 assembly:
  Lemma 3.3 (`isCoveringMap`) + bijectivity + the smooth upgrade
  `IsLocalDiffeomorph.diffeomorphOfBijective` produce a `Diffeomorph I I' M M' ∞`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3, proof of Theorem 3.1
(Hadamard).
-/

open Bundle Manifold Set Function
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

/-! ### The topological core: covering + simply connected ⟹ bijective -/

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

/-- **Math.** A covering map `f : E → X` out of a **preconnected, nonempty** total
space `E`, onto a **simply connected, locally path connected** base `X`, is
**bijective**. This is the covering-space fact do Carmo invokes at the end of the
proof of the Hadamard theorem ("since `M` is simply connected, the covering map
`exp_p` is a diffeomorphism"). -/
theorem IsCoveringMap.bijective_of_simplyConnected
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (hf : IsCoveringMap f) : Function.Bijective f := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  -- The identity `X → X` lifts uniquely to a global continuous section `s`.
  obtain ⟨s, ⟨hs0, hsp⟩, -⟩ :=
    hf.existsUnique_continuousMap_lifts (ContinuousMap.id X) (f e₀) e₀ rfl
  -- `hs0 : s (f e₀) = e₀`,  `hsp : f ∘ ⇑s = ⇑(ContinuousMap.id X) = id`.
  have hfs : Function.RightInverse s f := by
    intro x
    have := congrFun hsp x
    simpa using this
  refine ⟨?_, hfs.surjective⟩
  -- Injectivity: `s ∘ f` and `id` are two continuous lifts of `f` agreeing at `e₀`.
  have hsf : (⇑s ∘ f) = id := by
    refine hf.eq_of_comp_eq (g₁ := ⇑s ∘ f) (g₂ := id) (s.continuous.comp hf.continuous)
      continuous_id ?_ e₀ ?_
    · funext e; simp [Function.comp, hfs (f e)]
    · simp [Function.comp, hs0]
  have hli : Function.LeftInverse s f := fun e => congrFun hsf e
  exact hli.injective

/-- **Math.** The homeomorphism packaging of
`IsCoveringMap.bijective_of_simplyConnected`: a covering map out of a preconnected
nonempty space onto a simply connected, locally path connected base is a
**homeomorphism** (a continuous open bijection). -/
def IsCoveringMap.homeomorphOfSimplyConnected
    [PreconnectedSpace E] [Nonempty E]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (hf : IsCoveringMap f) : E ≃ₜ X :=
  (Equiv.ofBijective f hf.bijective_of_simplyConnected).toHomeomorphOfContinuousOpen
    hf.continuous hf.isOpenMap

namespace Riemannian

/-! ### The do Carmo Ch. 7 assembly: metric-expanding local diffeo + simply connected -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** do Carmo Ch. 7, §3, final step of the proof of Theorem 3.1
(Hadamard). Let `f : M → M'` be a smooth local diffeomorphism between Riemannian
manifolds which **expands the metric** (`|df_p(v)| ≥ |v|`), out of a **complete**
(proper) manifold `M`, onto a **simply connected** manifold `M'`. Then `f` is a
**diffeomorphism**.

Assembly: `f` is a covering map by Lemma 3.3
(`DCExpandsMetric.isCoveringMap`); a covering map onto a simply connected base is
bijective (`IsCoveringMap.bijective_of_simplyConnected`); a bijective local
diffeomorphism is a diffeomorphism (`IsLocalDiffeomorph.diffeomorphOfBijective`).

Applied to `f = exp_p : T_pM → M` (once `lem:dc-ch7-3-2` provides the
local-diffeomorphism input and the pulled-back metric makes `exp_p` a local
isometry out of the complete flat `T_pM`), this is exactly the Hadamard
conclusion. -/
def DCExpandsMetric.diffeomorphOfSimplyConnected [ProperSpace M] [T2Space M']
    [I'.Boundaryless] [PreconnectedSpace M] [Nonempty M]
    [SimplyConnectedSpace M'] [LocPathConnectedSpace M']
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : IsLocalDiffeomorph I I' ∞ f) : Diffeomorph I I' M M' ∞ :=
  hf.diffeomorphOfBijective (hexp.isCoveringMap hgM hf).bijective_of_simplyConnected

/-- **Math.** The underlying map of `DCExpandsMetric.diffeomorphOfSimplyConnected`
is `f` itself: the constructed diffeomorphism is `f`, upgraded, not a new map. -/
theorem DCExpandsMetric.diffeomorphOfSimplyConnected_coe [ProperSpace M] [T2Space M']
    [I'.Boundaryless] [PreconnectedSpace M] [Nonempty M]
    [SimplyConnectedSpace M'] [LocPathConnectedSpace M']
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : IsLocalDiffeomorph I I' ∞ f) :
    ⇑(hexp.diffeomorphOfSimplyConnected hgM hf) = f := rfl

end Riemannian
