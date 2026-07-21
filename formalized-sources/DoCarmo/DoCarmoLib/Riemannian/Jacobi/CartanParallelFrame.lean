import DoCarmoLib.Riemannian.Jacobi.ParallelFieldAlong
import DoCarmoLib.Riemannian.Jacobi.ParallelTransport

/-!
# The parallel orthonormal frame along a geodesic, and its transport by a linear isometry

do Carmo, *Riemannian Geometry*, Ch. 8, Theorem 2.1 (E. Cartan).  do Carmo's proof
runs in a **parallel orthonormal frame** `e₁(t), …, eₙ(t)` along a geodesic `γ` of
`M`, and compares it with the frame `ẽⱼ(t) = φ_t(eⱼ(t))` along the corresponding
geodesic `γ̃` of `M̃`, where

  `φ_t = P̃_t ∘ i ∘ P_t⁻¹ : T_{γ(t)}M → T_{γ̃(t)}M̃`

is the parallel-transport conjugate of the linear isometry `i : T_pM → T_{p̃}M̃`
(`P_t`, `P̃_t` the parallel transports along `γ`, `γ̃` from time `a`).

Because `P_t` is parallel transport, the composite `φ_t` applied to the *parallel*
frame `e` is nothing but **the parallel field seeded by `i(eⱼ(a))`**:
`φ_t(eⱼ(t)) = P̃_t(i(P_t⁻¹(eⱼ(t)))) = P̃_t(i(eⱼ(a)))`.  So `φ_t` itself **is not needed**
to build the transported frame: seeding the parallel field on `M̃` with `i(eⱼ(a))`
produces it directly.  That is what the first half of this file does, and it is the
"basis `→ i`" step that Ch. 8 §2 was missing.

`φ_t` *is* available now, and the last section builds it
(`parallelTransportConjugate`), so the displayed identity
`ẽⱼ(t) = φ_t(eⱼ(t))` is a theorem here
(`eq_parallelTransportConjugate_of_isParallelFieldAlongOn`) rather than a reading
imposed on an existential statement.  It rests on manifold-level uniqueness of
parallel transport (`IsParallelFieldAlongOn.eqOn_of_initial`) and on `P_t` bundled
as an invertible linear map (`parallelTransportAlongEquiv`), both supplied by
`ParallelTransport.lean`.

## Contents

* `exists_parallelOrthoFrameAlongOn` — along a geodesic `γ` on `[a, b]`, an
  orthonormal basis `e₀` of `T_{γ(a)}M` extends to a frame `e` that is parallel
  along `γ` and **orthonormal at every time**.  The frame is the parallel transport
  of `e₀` (`exists_parallelFieldAlongOn`); orthonormality is preserved because
  parallel transport is an isometry (`IsParallelFieldAlongOn.metricInner_const`),
  so the Gram matrix is constant in `t` and equals its value `δᵢⱼ` at `a`.
* `exists_transportedParallelOrthoFrame` — do Carmo's `ẽⱼ(t) = φ_t(eⱼ(t))`: given a
  linear isometry `i : T_pM → T_{p̃}M̃` and a geodesic `γ̃` of `M̃` issuing from `p̃`,
  the frame on `M̃` seeded by `i(e₀ⱼ)` is parallel along `γ̃` and orthonormal at
  every time.  Orthonormality of the seed is immediate from `i` being a linear
  isometry, so this is the previous theorem applied on `M̃`.
* `exists_transportedParallelOrthoFrame_pair` — both frames at once, the shape
  do Carmo's proof consumes: `e` on `M`, `ẽ` on `M̃`, matched at time `a` by
  `ẽⱼ(a) = i(eⱼ(a))`.
* `parallelTransportConjugate` — do Carmo's `φ_t = P̃_t ∘ i ∘ P_t⁻¹` itself, with
  `parallelTransportConjugate_left` (`φ_a = i`) and
  `metricInner_parallelTransportConjugate` (`φ_t` is a linear isometry
  `T_{γ(t)}M → T_{γ̃(t)}M̃` when `i` is one — the property do Carmo's curvature
  hypothesis is stated against).
* `eq_parallelTransportConjugate_of_isParallelFieldAlongOn` — **`ẽ(t) = φ_t(e(t))`**
  at every `t`, the identity the transported-frame statements above can only assert
  at `t = a`.

Note this file is **curvature-free**: no constant-curvature and no curvature-matching
hypothesis appears.  The curvature hypothesis of E. Cartan's theorem enters one level
up, where these frames are fed to `jacobiFrameTransfer`'s `hmatch`.

Blueprint: `lem:dc-ch8-2-1-parallel-ortho-frame`, `lem:dc-ch8-2-1-transported-frame`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8, Thm. 2.1; Ch. 2, Prop. 2.6.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-! ### The parallel orthonormal frame -/

/-- **Math.** **The parallel orthonormal frame along a geodesic** (do Carmo Ch. 8,
Thm. 2.1: "let `e₁, …, eₙ` be an orthonormal basis of `T_pM` and let `eᵢ(t)` be the
parallel transport of `eᵢ` along `γ`").

Along a geodesic `γ : [a, b] → M`, an orthonormal family `e₀ : ι → T_{γ(a)}M` extends
to a family `e : ι → ℝ → E` of own-foot fields with

* `eᵢ(a) = e₀ᵢ` — the frame is seeded by `e₀`;
* each `eᵢ` is parallel along `γ`;
* `⟨eᵢ(t), eⱼ(t)⟩_{γ(t)} = δᵢⱼ` for **every** `t ∈ [a, b]`, not just at `a`.

Proof: parallel-transport each `e₀ᵢ` (`exists_parallelFieldAlongOn`).  Parallel
transport is an isometry (`IsParallelFieldAlongOn.metricInner_const`: the pairing of
two parallel fields is constant along `γ`), so the Gram matrix at time `t` equals the
Gram matrix at time `a`, which is `δᵢⱼ` by hypothesis.

This is the manifold-level counterpart of the chart-fixed `exists_parallelOrthoFrame`
(`ParallelFrame.lean`); being chart-local, it applies to a geodesic that leaves any
single chart.

Blueprint: `lem:dc-ch8-2-1-parallel-ortho-frame`. -/
theorem exists_parallelOrthoFrameAlongOn {ι : Type*} [DecidableEq ι]
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (e₀ : ι → E)
    (horth : ∀ i j, g.metricInner (γ a) (e₀ i) (e₀ j) = if i = j then (1 : ℝ) else 0) :
    ∃ e : ι → ℝ → E,
      (∀ i, e i a = e₀ i) ∧
      (∀ i, IsParallelFieldAlongOn (I := I) g γ (e i) a b) ∧
      (∀ t ∈ Icc a b, ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
        = if i = j then (1 : ℝ) else 0) := by
  classical
  -- parallel-transport each seed vector
  have H : ∀ i : ι, ∃ w : ℝ → E, IsParallelFieldAlongOn (I := I) g γ w a b ∧ w a = e₀ i :=
    fun i => exists_parallelFieldAlongOn (I := I) hab hgeo hγc (e₀ i)
  choose e hePar he0 using H
  refine ⟨e, he0, hePar, fun t ht i j => ?_⟩
  -- parallel transport is an isometry: the Gram matrix is constant, hence `δᵢⱼ` throughout
  rw [IsParallelFieldAlongOn.metricInner_const (I := I) hab.le (hePar i) (hePar j) hgeo hγc ht,
    he0 i, he0 j]
  exact horth i j

/-! ### The frame transported by a linear isometry -/

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [SigmaCompactSpace M'] [T2Space M'] [I'.Boundaryless]

/-- **Math.** **do Carmo's transported frame `ẽⱼ(t) = φ_t(eⱼ(t))`** (Ch. 8, Thm. 2.1).

Let `i : T_pM → T_{p̃}M̃` be a linear isometry (`hi`), let `e₀` be an orthonormal family
at `p = γ(a)`, and let `γ̃` be a geodesic of `M̃` with `γ̃(a) = p̃`.  Then there is a
family `ẽ : ι → ℝ → E` of own-foot fields along `γ̃` with

* `ẽⱼ(a) = i(e₀ⱼ)`,
* each `ẽⱼ` parallel along `γ̃`,
* `⟨ẽⱼ(t), ẽₖ(t)⟩_{γ̃(t)} = δⱼₖ` for every `t ∈ [a, b]`.

**What this delivers.**  `ẽ` is *a* parallel field on `M̃` seeded by `i(e₀ⱼ)`.  That is do
Carmo's `ẽⱼ(t) = φ_t(eⱼ(t))`: since `e` is parallel with `eⱼ(a) = e₀ⱼ` we have
`P_t⁻¹(eⱼ(t)) = e₀ⱼ`, hence `φ_t(eⱼ(t)) = P̃_t(i(e₀ⱼ))`, the parallel field seeded by
`i(e₀ⱼ)`.

The statement below is nevertheless **existential**: it gives a parallel orthonormal frame
with the right seed, and the proposition `ẽⱼ(t) = φ_t(eⱼ(t))` is proved separately, as
`eq_parallelTransportConjugate_of_isParallelFieldAlongOn` at the end of this file.  The
identification needs **uniqueness of parallel transport at the manifold level** — that two
`IsParallelFieldAlongOn` fields agreeing at `a` agree on `[a, b]` — which is now available
as `IsParallelFieldAlongOn.eqOn_of_initial` (`ParallelTransport.lean`); it was missing when
this statement was first written, which is why the existential form is the one the frame
consumers below are phrased against.

What the seed buys *without* uniqueness is what the Cartan argument actually consumes:
orthonormality of `ẽ` at every time, matched to `e` at time `a` through `i`.

Proof: `i` is a linear isometry, so `⟨i(e₀ⱼ), i(e₀ₖ)⟩_{p̃} = ⟨e₀ⱼ, e₀ₖ⟩_p = δⱼₖ`: the
transported seed is orthonormal at `p̃`.  Apply `exists_parallelOrthoFrameAlongOn` on `M̃`.

Blueprint: `lem:dc-ch8-2-1-transported-frame`. -/
theorem exists_transportedParallelOrthoFrame {ι : Type*} [DecidableEq ι]
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    {γ : ℝ → M} {γbar : ℝ → M'} {a b : ℝ} (hab : a < b)
    (hgeobar : IsGeodesicOn (I := I') g' γbar (Icc a b))
    (hγcbar : ∀ t ∈ Icc a b, ContinuousAt γbar t)
    (e₀ : ι → E) (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner (γbar a) (i u) (i w) = g.metricInner (γ a) u w)
    (horth : ∀ j k, g.metricInner (γ a) (e₀ j) (e₀ k) = if j = k then (1 : ℝ) else 0) :
    ∃ ebar : ι → ℝ → E,
      (∀ j, ebar j a = i (e₀ j)) ∧
      (∀ j, IsParallelFieldAlongOn (I := I') g' γbar (ebar j) a b) ∧
      (∀ t ∈ Icc a b, ∀ j k, g'.metricInner (γbar t) (ebar j t : TangentSpace I' (γbar t)) (ebar k t)
        = if j = k then (1 : ℝ) else 0) :=
  exists_parallelOrthoFrameAlongOn (I := I') hab hgeobar hγcbar (fun j => i (e₀ j))
    (fun j k => by rw [hi (e₀ j) (e₀ k)]; exact horth j k)

/-- **Math.** **The two frames of do Carmo Ch. 8, Thm. 2.1, packaged together**: the
parallel orthonormal frame `e` along `γ` seeded by an orthonormal family `e₀` at `p`, and
the frame `ẽ` along `γ̃` seeded by `i(e₀)`, matched at time `a` by

  `ẽⱼ(a) = i(eⱼ(a))`,

which is do Carmo's `ẽⱼ(t) = φ_t(eⱼ(t))` at `t = a`, where `φ_a = i`.

**One gap remains between this and do Carmo's frame pair**, to be closed by later work
rather than assumed by readers of this statement:

* `γ̃` here is an **arbitrary** geodesic of `M̃`; the only hypothesis touching it is `hi`,
  which merely names `γ̃(a)` as the foot of `i`'s codomain.  do Carmo additionally requires
  `γ̃'(a) = i(γ'(a))`, and his frames carry the distinguished member `eₙ = γ'`,
  `ẽₙ = γ̃'` (cf. `exists_velocitySeededParallelOrthoFrame`, which does supply
  `e_{n₀}(t) = γ'(t)`, in the chart-fixed setting).  Neither is concluded here.

The other gap this statement used to carry — the extension of `ẽⱼ(a) = i(eⱼ(a))` to
`ẽⱼ(t) = φ_t(eⱼ(t))` at every `t` — is **closed**: it needed manifold-level uniqueness of
parallel transport, and `eq_parallelTransportConjugate_of_isParallelFieldAlongOn` (below)
now proves the identity from the two `IsParallelFieldAlongOn` clauses and `ẽⱼ(a) = i(eⱼ(a))`
that this statement already returns.

Blueprint: `lem:dc-ch8-2-1-transported-frame`. -/
theorem exists_transportedParallelOrthoFrame_pair {ι : Type*} [DecidableEq ι]
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    {γ : ℝ → M} {γbar : ℝ → M'} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hgeobar : IsGeodesicOn (I := I') g' γbar (Icc a b))
    (hγcbar : ∀ t ∈ Icc a b, ContinuousAt γbar t)
    (e₀ : ι → E) (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner (γbar a) (i u) (i w) = g.metricInner (γ a) u w)
    (horth : ∀ j k, g.metricInner (γ a) (e₀ j) (e₀ k) = if j = k then (1 : ℝ) else 0) :
    ∃ (e ebar : ι → ℝ → E),
      (∀ j, e j a = e₀ j) ∧
      (∀ j, IsParallelFieldAlongOn (I := I) g γ (e j) a b) ∧
      (∀ t ∈ Icc a b, ∀ j k, g.metricInner (γ t) (e j t : TangentSpace I (γ t)) (e k t)
        = if j = k then (1 : ℝ) else 0) ∧
      (∀ j, ebar j a = i (e j a)) ∧
      (∀ j, IsParallelFieldAlongOn (I := I') g' γbar (ebar j) a b) ∧
      (∀ t ∈ Icc a b, ∀ j k, g'.metricInner (γbar t) (ebar j t : TangentSpace I' (γbar t)) (ebar k t)
        = if j = k then (1 : ℝ) else 0) := by
  obtain ⟨e, he0, hePar, heorth⟩ :=
    exists_parallelOrthoFrameAlongOn (I := I) hab hgeo hγc e₀ horth
  obtain ⟨ebar, hebar0, hebarPar, hebarorth⟩ :=
    exists_transportedParallelOrthoFrame (I := I) (I' := I') (g := g) (g' := g') (γ := γ)
      hab hgeobar hγcbar e₀ i hi horth
  exact ⟨e, ebar, he0, hePar, heorth,
    fun j => by rw [hebar0 j, he0 j], hebarPar, hebarorth⟩

/-! ### do Carmo's `φ_t`, and the transported frame as a theorem rather than a reading

`ParallelTransport.lean` supplies manifold-level uniqueness of parallel transport, and with
it `P_t` as an invertible linear map.  So `φ_t = P̃_t ∘ i ∘ P_t⁻¹` can now be *written down*,
and do Carmo's `ẽⱼ(t) = φ_t(eⱼ(t))` — which the statements above could only assert at `t = a`
— becomes a theorem at every `t`. -/

/-- **Math.** **do Carmo's `φ_t = P̃_t ∘ i ∘ P_t⁻¹`** (Ch. 8, Thm. 2.1): the parallel-transport
conjugate of a linear map `i : T_pM → T_{p̃}M̃`, carrying `T_{γ(t)}M → T_{γ̃(t)}M̃`.  Transport
back to `p` along `γ`, apply `i`, transport forward to `γ̃(t)` along `γ̃`.

At `t = a` both transports are the identity, so `φ_a = i` (`parallelTransportConjugate_left`).

Blueprint: `lem:dc-ch8-2-1-transported-frame`. -/
def parallelTransportConjugate {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    {γ : ℝ → M} {γbar : ℝ → M'} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hgeobar : IsGeodesicOn (I := I') g' γbar (Icc a b))
    (hγcbar : ∀ t ∈ Icc a b, ContinuousAt γbar t)
    (i : E →ₗ[ℝ] E) {t : ℝ} (ht : t ∈ Icc a b) : E →ₗ[ℝ] E :=
  (parallelTransportAlong (I := I') hab hgeobar hγcbar ht).comp
    (i.comp (parallelTransportAlongEquiv (I := I) hab hgeo hγc ht).symm.toLinearMap)

/-- **Math.** **`ẽ(t) = φ_t(e(t))`, do Carmo's transported field, as a theorem.**

Let `v` be parallel along `γ` and let `v̄` be parallel along `γ̃` with the seed matched by
`i`, i.e. `v̄(a) = i(v(a))` — exactly the data `exists_transportedParallelOrthoFrame_pair`
produces.  Then `v̄(t) = φ_t(v(t))` for **every** `t ∈ [a, b]`, not merely at `a`.

This is what the `exists_transportedParallelOrthoFrame*` statements above could not say.
The proof is do Carmo's own one-line computation, now available because each step is a
map: `P_t⁻¹(v(t)) = v(a)` since `v` is the parallel field seeded by `v(a)`
(`parallelTransportAlongEquiv_symm_apply_of_isParallelFieldAlongOn`), so
`φ_t(v(t)) = P̃_t(i(v(a))) = P̃_t(v̄(a)) = v̄(t)`, the last step because `v̄` is the parallel
field seeded by `v̄(a)`.

Blueprint: `lem:dc-ch8-2-1-transported-frame`. -/
theorem eq_parallelTransportConjugate_of_isParallelFieldAlongOn
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    {γ : ℝ → M} {γbar : ℝ → M'} {a b : ℝ} {hab : a < b}
    {hgeo : IsGeodesicOn (I := I) g γ (Icc a b)}
    {hγc : ∀ t ∈ Icc a b, ContinuousAt γ t}
    {hgeobar : IsGeodesicOn (I := I') g' γbar (Icc a b)}
    {hγcbar : ∀ t ∈ Icc a b, ContinuousAt γbar t}
    {i : E →ₗ[ℝ] E} {v vbar : ℝ → E}
    (hv : IsParallelFieldAlongOn (I := I) g γ v a b)
    (hvbar : IsParallelFieldAlongOn (I := I') g' γbar vbar a b)
    (hseed : vbar a = i (v a)) {t : ℝ} (ht : t ∈ Icc a b) :
    vbar t = parallelTransportConjugate (I := I) (I' := I') hab hgeo hγc hgeobar hγcbar i ht
      (v t) := by
  show vbar t = parallelTransportAlong (I := I') hab hgeobar hγcbar ht
    (i ((parallelTransportAlongEquiv (I := I) hab hgeo hγc ht).symm (v t)))
  rw [parallelTransportAlongEquiv_symm_apply_of_isParallelFieldAlongOn hv ht, ← hseed,
    parallelTransportAlong_apply]
  exact (parallelFieldSeed_eq (hab := hab) (hgeo := hgeobar) (hγc := hγcbar) hvbar rfl t ht).symm

/-- **Math.** `φ_a = i`: at the initial time both parallel transports are the identity. -/
theorem parallelTransportConjugate_left {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    {γ : ℝ → M} {γbar : ℝ → M'} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hgeobar : IsGeodesicOn (I := I') g' γbar (Icc a b))
    (hγcbar : ∀ t ∈ Icc a b, ContinuousAt γbar t)
    (i : E →ₗ[ℝ] E) (w : E) :
    parallelTransportConjugate (I := I) (I' := I') hab hgeo hγc hgeobar hγcbar i
      (left_mem_Icc.2 hab.le) w = i w := by
  show parallelTransportAlong (I := I') hab hgeobar hγcbar (left_mem_Icc.2 hab.le)
    (i ((parallelTransportAlongEquiv (I := I) hab hgeo hγc (left_mem_Icc.2 hab.le)).symm w))
      = i w
  rw [show (parallelTransportAlongEquiv (I := I) hab hgeo hγc (left_mem_Icc.2 hab.le)).symm w
      = w from by
    rw [LinearEquiv.symm_apply_eq, parallelTransportAlongEquiv_apply,
      parallelTransportAlong_left]]
  exact parallelTransportAlong_left (I := I') hab hgeobar hγcbar (i w)

/-- **Math.** **`φ_t` is a linear isometry `T_{γ(t)}M → T_{γ̃(t)}M̃`** whenever `i` is one at
the base point.  Both parallel transports preserve the metric
(`metricInner_parallelTransportAlong`) and `i` is an isometry by `hi`, so the composite is.
This is the property do Carmo's curvature hypothesis is stated against. -/
theorem metricInner_parallelTransportConjugate {g : RiemannianMetric I M}
    {g' : RiemannianMetric I' M'} {γ : ℝ → M} {γbar : ℝ → M'} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hgeobar : IsGeodesicOn (I := I') g' γbar (Icc a b))
    (hγcbar : ∀ t ∈ Icc a b, ContinuousAt γbar t)
    (i : E →ₗ[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner (γbar a) (i u) (i w) = g.metricInner (γ a) u w)
    {t : ℝ} (ht : t ∈ Icc a b) (u w : E) :
    g'.metricInner (γbar t)
        (parallelTransportConjugate (I := I) (I' := I') hab hgeo hγc hgeobar hγcbar i ht u
          : TangentSpace I' (γbar t))
        (parallelTransportConjugate (I := I) (I' := I') hab hgeo hγc hgeobar hγcbar i ht w)
      = g.metricInner (γ t) (u : TangentSpace I (γ t)) w := by
  show g'.metricInner (γbar t)
      (parallelTransportAlong (I := I') hab hgeobar hγcbar ht
        (i ((parallelTransportAlongEquiv (I := I) hab hgeo hγc ht).symm u)))
      (parallelTransportAlong (I := I') hab hgeobar hγcbar ht
        (i ((parallelTransportAlongEquiv (I := I) hab hgeo hγc ht).symm w))) = _
  rw [metricInner_parallelTransportAlong (I := I') hab hgeobar hγcbar ht, hi,
    ← metricInner_parallelTransportAlong (I := I) hab hgeo hγc ht
      ((parallelTransportAlongEquiv (I := I) hab hgeo hγc ht).symm u)
      ((parallelTransportAlongEquiv (I := I) hab hgeo hγc ht).symm w)]
  simp only [← parallelTransportAlongEquiv_apply, LinearEquiv.apply_symm_apply]

end Riemannian.Jacobi

end
