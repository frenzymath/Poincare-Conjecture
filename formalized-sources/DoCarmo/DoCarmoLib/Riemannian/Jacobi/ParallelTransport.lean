import DoCarmoLib.Riemannian.Jacobi.ParallelFieldAlong

/-!
# The parallel transport map at the manifold level — do Carmo's `φ_t`

`ParallelFieldAlong.lean` lifts the parallel-transport ODE to the manifold level
(`IsParallelFieldAlongOn`) and supplies **existence** (`exists_parallelFieldAlongOn`) and
the **isometry** property (`IsParallelFieldAlongOn.metricInner_const`).  What it does not
supply is **uniqueness**, and without uniqueness there is no *map*: a parallel field seeded
at `a` is only ever produced existentially, so do Carmo's parallel transport `P_t` — and
with it the conjugated isometry `φ_t = P̃_t ∘ i ∘ P_t⁻¹` of Ch. 8, Thm. 2.1 — cannot be
written down.  This file closes that gap.

## The uniqueness argument

Not a supremum walk.  Parallel fields are **linear** in their seed, so the difference of two
parallel fields is parallel; and the intrinsic pairing of two parallel fields is *constant*
(`metricInner_const`).  Hence if `v`, `w` are parallel with `v a = w a`, the difference
`d = v - w` is parallel with `d a = 0`, so

  `⟨d t, d t⟩_{γ t} = ⟨d a, d a⟩_{γ a} = 0`,

and positive-definiteness of `g` at `γ t` gives `d t = 0`.  The chart-fixed Grönwall
uniqueness `isParallelSol_eqOn_Icc` is never invoked: the *energy* is doing the work, so no
chart window, no coefficient bound, and no continuation argument appear.  This is do Carmo's
own reason that parallel transport is an isometry, run backwards.

The linearity that this rests on is itself cheap at the manifold level, because
`isParallelSolOn_of_mem_source` lets the second field be localized into the chart window
*produced by the first* — so, unlike `IsJacobiFieldAlongOn.add`/`.sub`, no common refinement
of two independent chart windows is needed.

## Contents

* `IsParallelSolOn.add`, `.sub`, `.const_smul` — chart-level linearity of the certificate,
  from linearity of `Γ(u̇, ·)(u)` (`chartChristoffelContractionRight`, a `E →L[ℝ] E`).
* `IsParallelFieldAlongOn.add`, `.sub`, `.smul` — the same, manifold level.
* `IsParallelFieldAlongOn.eqOn_of_initial` — **uniqueness**: two parallel fields agreeing at
  `a` agree on `[a, b]`.
* `parallelFieldSeed`, `parallelFieldSeed_eq` — the parallel field seeded by `w₀`, and the
  characterization that *any* parallel field with that seed is it.  The only place uniqueness
  is consumed; everything below is a corollary.
* `parallelTransportAlong` — do Carmo's `P_t`: the parallel transport `E →ₗ[ℝ] E` along a
  geodesic, a genuine map, linear in the seed.
* `parallelTransportAlong_apply`, `parallelTransportAlong_left` — its defining property: it is
  the time-`t` value of the parallel field it seeds, and `P_a = id`.
* `metricInner_parallelTransportAlong` — `P_t` is an isometry for the **Riemannian** pairings,
  carrying `g.metricInner (γ a)` to `g.metricInner (γ t)`.  It is *not* an isometry for the
  ambient inner product of the model space `E`, which carries no geometric meaning here — so
  `P_t` is bundled as a `LinearMap`, not a `LinearIsometry`.
* `parallelTransportAlong_injective`, `parallelTransportAlongEquiv` — `P_t` as a linear
  automorphism `E ≃ₗ[ℝ] E` (injectivity from metric preservation, plus `E` finite-dimensional).
  This is what lets `P_t⁻¹`, and hence `φ_t`, be written.

Blueprint: `lem:dc-ch8-2-1-transported-frame` (do Carmo's `ẽⱼ(t) = φ_t(eⱼ(t))`).

Reference: do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.6 and Cor. 3.3; Ch. 8, Thm. 2.1.
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

/-! ### Chart-level linearity of the parallel certificate

The parallel ODE `ẇ = −Γ(u̇, w)(u)` is linear in `w`, because `Γ(u̇, ·)(u)` is the
continuous linear map `chartChristoffelContractionRight g α u̇ u`. -/

/-- **Math.** The sum of two chart-level parallel solutions is a parallel solution. -/
theorem IsParallelSolOn.add {g : RiemannianMetric I M} {α : M} {u v w : ℝ → E} {a b : ℝ}
    (hv : IsParallelSolOn (I := I) g α u v a b)
    (hw : IsParallelSolOn (I := I) g α u w a b) :
    IsParallelSolOn (I := I) g α u (fun τ => v τ + w τ) a b := by
  intro t ht
  have key := map_add (chartChristoffelContractionRight (I := I) g α (deriv u t) (u t))
    (v t) (w t)
  simp only [chartChristoffelContractionRight_apply] at key
  show HasDerivWithinAt (fun τ => v τ + w τ)
    (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (v t + w t) (u t))
    (Icc a b) t
  rw [key, neg_add]
  exact (hv t ht).add (hw t ht)

/-- **Math.** The difference of two chart-level parallel solutions is a parallel solution. -/
theorem IsParallelSolOn.sub {g : RiemannianMetric I M} {α : M} {u v w : ℝ → E} {a b : ℝ}
    (hv : IsParallelSolOn (I := I) g α u v a b)
    (hw : IsParallelSolOn (I := I) g α u w a b) :
    IsParallelSolOn (I := I) g α u (fun τ => v τ - w τ) a b := by
  intro t ht
  have key := map_sub (chartChristoffelContractionRight (I := I) g α (deriv u t) (u t))
    (v t) (w t)
  simp only [chartChristoffelContractionRight_apply] at key
  show HasDerivWithinAt (fun τ => v τ - w τ)
    (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (v t - w t) (u t))
    (Icc a b) t
  rw [key]
  have h := (hv t ht).sub (hw t ht)
  convert h using 1
  abel

/-- **Math.** A scalar multiple of a chart-level parallel solution is a parallel solution. -/
theorem IsParallelSolOn.const_smul {g : RiemannianMetric I M} {α : M} {u v : ℝ → E} {a b : ℝ}
    (r : ℝ) (hv : IsParallelSolOn (I := I) g α u v a b) :
    IsParallelSolOn (I := I) g α u (fun τ => r • v τ) a b := by
  intro t ht
  have key := map_smul (chartChristoffelContractionRight (I := I) g α (deriv u t) (u t))
    r (v t)
  simp only [chartChristoffelContractionRight_apply] at key
  show HasDerivWithinAt (fun τ => r • v τ)
    (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (r • v t) (u t))
    (Icc a b) t
  rw [key, ← smul_neg]
  exact (hv t ht).const_smul r

/-! ### Manifold-level linearity

Each proof takes the chart window produced by the *first* field's certificate and localizes
the second field into it with `isParallelSolOn_of_mem_source` — so no common refinement of
two chart windows is needed. -/

section Algebra

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Superposition**: the sum of two parallel fields along `γ` is parallel. -/
theorem IsParallelFieldAlongOn.add
    {g : RiemannianMetric I M} {γ : ℝ → M} {v w : ℝ → E} {a b : ℝ}
    (hv : IsParallelFieldAlongOn (I := I) g γ v a b)
    (hw : IsParallelFieldAlongOn (I := I) g γ w a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    IsParallelFieldAlongOn (I := I) g γ (fun τ => v τ + w τ) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hcertv⟩ := hv t₀ ht₀
  have hcertw := hw.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc (β := α)
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, (hcertv.add hcertw).congr ?_⟩
  intro τ _
  show chartVectorRep (I := I) γ α (fun σ => v σ + w σ) τ
    = chartVectorRep (I := I) γ α v τ + chartVectorRep (I := I) γ α w τ
  simp only [chartVectorRep_apply, map_add]

/-- **Math.** The difference of two parallel fields along `γ` is parallel — the engine of
`IsParallelFieldAlongOn.eqOn_of_initial`. -/
theorem IsParallelFieldAlongOn.sub
    {g : RiemannianMetric I M} {γ : ℝ → M} {v w : ℝ → E} {a b : ℝ}
    (hv : IsParallelFieldAlongOn (I := I) g γ v a b)
    (hw : IsParallelFieldAlongOn (I := I) g γ w a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    IsParallelFieldAlongOn (I := I) g γ (fun τ => v τ - w τ) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hcertv⟩ := hv t₀ ht₀
  have hcertw := hw.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc (β := α)
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, (hcertv.sub hcertw).congr ?_⟩
  intro τ _
  show chartVectorRep (I := I) γ α (fun σ => v σ - w σ) τ
    = chartVectorRep (I := I) γ α v τ - chartVectorRep (I := I) γ α w τ
  simp only [chartVectorRep_apply, map_sub]

/-- **Math.** A scalar multiple of a parallel field along `γ` is parallel.  Only one chart
window is involved, so — unlike `add`/`sub` — neither `hgeo` nor `hγc` is needed. -/
theorem IsParallelFieldAlongOn.smul
    {g : RiemannianMetric I M} {γ : ℝ → M} {v : ℝ → E} {a b : ℝ} (r : ℝ)
    (hv : IsParallelFieldAlongOn (I := I) g γ v a b) :
    IsParallelFieldAlongOn (I := I) g γ (fun τ => r • v τ) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hcertv⟩ := hv t₀ ht₀
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, (hcertv.const_smul r).congr ?_⟩
  intro τ _
  show chartVectorRep (I := I) γ α (fun σ => r • v σ) τ
    = r • chartVectorRep (I := I) γ α v τ
  simp only [chartVectorRep_apply, map_smul]

end Algebra

/-! ### Uniqueness of parallel transport, at the manifold level -/

section Uniqueness

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Uniqueness of the parallel field with prescribed initial value** along a
geodesic (do Carmo Ch. 2, Prop. 2.6, uniqueness half, manifold form).  Two parallel fields
along `γ` that agree at the left endpoint agree on all of `[a, b]`.

The proof is the *energy* argument, not a Grönwall continuation: `d = v - w` is parallel
(`IsParallelFieldAlongOn.sub`) with `d a = 0`, so `⟨d t, d t⟩` is constant
(`metricInner_const`) and equal to `⟨d a, d a⟩ = 0`; positive-definiteness of `g` at `γ t`
then forces `d t = 0`.  In particular no chart window, coefficient bound, or supremum walk
occurs anywhere.

This is what upgrades `exists_transportedParallelOrthoFrame` from an existential statement
to do Carmo's actual reading `ẽⱼ(t) = φ_t(eⱼ(t))`, and it is what makes the transport map
`parallelTransportAlong` well defined.

Blueprint: `lem:dc-ch8-2-1-transported-frame`. -/
theorem IsParallelFieldAlongOn.eqOn_of_initial
    {g : RiemannianMetric I M} {γ : ℝ → M} {v w : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hv : IsParallelFieldAlongOn (I := I) g γ v a b)
    (hw : IsParallelFieldAlongOn (I := I) g γ w a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (h₀ : v a = w a) :
    ∀ t ∈ Icc a b, v t = w t := by
  intro t ht
  have hd : IsParallelFieldAlongOn (I := I) g γ (fun τ => v τ - w τ) a b :=
    hv.sub hw hgeo hγc
  -- the energy of the difference is constant, and vanishes at `a`
  have hconst := hd.metricInner_const hab hd hgeo hγc ht
  have hda : v a - w a = 0 := sub_eq_zero.2 h₀
  simp only [hda] at hconst
  -- `TangentSpace I (γ a)` is only semireducibly `E`, so bridge the vanishing pairing with
  -- `.trans` rather than `simp`/`rw`, which cannot see through the fibre identification
  have hz : g.metricInner (γ a) (0 : TangentSpace I (γ a)) 0 = 0 :=
    g.metricInner_zero_left (γ a) 0
  have hconst' : g.metricInner (γ t) ((v t - w t : E) : TangentSpace I (γ t)) (v t - w t) = 0 :=
    hconst.trans hz
  -- positive-definiteness at `γ t`
  by_contra hne
  have hdt : (v t - w t : TangentSpace I (γ t)) ≠ 0 := sub_ne_zero.2 hne
  exact absurd hconst' (g.metricInner_self_pos (γ t) _ hdt).ne'

end Uniqueness

/-! ### The parallel transport map `P_t`

With uniqueness available, the parallel field seeded by `w₀` is *the* parallel field seeded
by `w₀`, and evaluating it at time `t` is a well-defined function of `w₀`.  That function is
do Carmo's parallel transport `P_t : T_{γ a}M → T_{γ t}M`. -/

section Transport

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
variable {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ}

/-- **Math.** The parallel field along `γ` seeded by `w₀` at time `a`, chosen by
`exists_parallelFieldAlongOn`.  By `IsParallelFieldAlongOn.eqOn_of_initial` the choice is
immaterial: `parallelFieldSeed_eq` identifies it with *any* parallel field having that
seed. -/
def parallelFieldSeed (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) (w₀ : E) : ℝ → E :=
  Classical.choose (exists_parallelFieldAlongOn (I := I) hab hgeo hγc w₀)

theorem isParallelFieldAlongOn_parallelFieldSeed (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) (w₀ : E) :
    IsParallelFieldAlongOn (I := I) g γ (parallelFieldSeed (I := I) hab hgeo hγc w₀) a b :=
  (Classical.choose_spec (exists_parallelFieldAlongOn (I := I) hab hgeo hγc w₀)).1

@[simp] theorem parallelFieldSeed_left (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) (w₀ : E) :
    parallelFieldSeed (I := I) hab hgeo hγc w₀ a = w₀ :=
  (Classical.choose_spec (exists_parallelFieldAlongOn (I := I) hab hgeo hγc w₀)).2

/-- **Math.** **The characterization**: any parallel field along `γ` with seed `w₀` at `a`
*is* `parallelFieldSeed w₀` on `[a, b]`.  This is the only place uniqueness is used, and
everything below is a corollary of it. -/
theorem parallelFieldSeed_eq {hab : a < b} {hgeo : IsGeodesicOn (I := I) g γ (Icc a b)}
    {hγc : ∀ t ∈ Icc a b, ContinuousAt γ t} {w : ℝ → E} {w₀ : E}
    (hw : IsParallelFieldAlongOn (I := I) g γ w a b) (hw₀ : w a = w₀) :
    ∀ t ∈ Icc a b, parallelFieldSeed (I := I) hab hgeo hγc w₀ t = w t :=
  IsParallelFieldAlongOn.eqOn_of_initial hab.le
    (isParallelFieldAlongOn_parallelFieldSeed (I := I) hab hgeo hγc w₀) hw hgeo hγc
    (by rw [parallelFieldSeed_left, hw₀])

/-- **Math.** **do Carmo's parallel transport `P_t`** along a geodesic `γ`, as a genuine
linear map `T_{γ a}M → T_{γ t}M` (both read in the model space `E`): `P_t(w₀)` is the value
at time `t` of the parallel field seeded by `w₀`.

Additivity and homogeneity are immediate from uniqueness: `parallelFieldSeed w₀ +
parallelFieldSeed w₁` is parallel (`IsParallelFieldAlongOn.add`) with seed `w₀ + w₁`, so by
`parallelFieldSeed_eq` it *is* `parallelFieldSeed (w₀ + w₁)`.

Blueprint: `lem:dc-ch8-2-1-transported-frame`. -/
def parallelTransportAlong (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) {t : ℝ} (ht : t ∈ Icc a b) : E →ₗ[ℝ] E where
  toFun w₀ := parallelFieldSeed (I := I) hab hgeo hγc w₀ t
  map_add' w₀ w₁ := by
    refine parallelFieldSeed_eq (hab := hab) (hgeo := hgeo) (hγc := hγc)
      ((isParallelFieldAlongOn_parallelFieldSeed (I := I) hab hgeo hγc w₀).add
        (isParallelFieldAlongOn_parallelFieldSeed (I := I) hab hgeo hγc w₁) hgeo hγc)
      (by simp) t ht
  map_smul' r w₀ := by
    refine parallelFieldSeed_eq (hab := hab) (hgeo := hgeo) (hγc := hγc)
      ((isParallelFieldAlongOn_parallelFieldSeed (I := I) hab hgeo hγc w₀).smul r)
      (by simp) t ht

@[simp] theorem parallelTransportAlong_apply (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) {t : ℝ} (ht : t ∈ Icc a b) (w₀ : E) :
    parallelTransportAlong (I := I) hab hgeo hγc ht w₀
      = parallelFieldSeed (I := I) hab hgeo hγc w₀ t := rfl

/-- **Math.** `P_a = id`: transporting to the initial time returns the seed. -/
@[simp] theorem parallelTransportAlong_left (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) (w₀ : E) :
    parallelTransportAlong (I := I) hab hgeo hγc (left_mem_Icc.2 hab.le) w₀ = w₀ :=
  parallelFieldSeed_left (I := I) hab hgeo hγc w₀

/-- **Math.** **Parallel transport is an isometry** (do Carmo Ch. 2, Cor. 3.3): `P_t` carries
the metric at `γ a` to the metric at `γ t`.  Note this is an isometry for the *Riemannian*
pairings `g.metricInner (γ a)` and `g.metricInner (γ t)` — **not** for the ambient inner
product of the model space `E`, which carries no geometric meaning here.  So `P_t` is bundled
as a `LinearMap`, not a `LinearIsometry`. -/
theorem metricInner_parallelTransportAlong (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) {t : ℝ} (ht : t ∈ Icc a b) (v w : E) :
    g.metricInner (γ t)
        (parallelTransportAlong (I := I) hab hgeo hγc ht v : TangentSpace I (γ t))
        (parallelTransportAlong (I := I) hab hgeo hγc ht w)
      = g.metricInner (γ a) (v : TangentSpace I (γ a)) w := by
  have h := (isParallelFieldAlongOn_parallelFieldSeed (I := I) hab hgeo hγc v).metricInner_const
    hab.le (isParallelFieldAlongOn_parallelFieldSeed (I := I) hab hgeo hγc w) hgeo hγc ht
  simpa only [parallelTransportAlong_apply, parallelFieldSeed_left] using h

/-- **Math.** `P_t` is injective: it preserves the metric, and the metric is
positive-definite.  (With `E` finite-dimensional this makes `P_t` a linear automorphism —
the invertibility do Carmo's `φ_t = P̃_t ∘ i ∘ P_t⁻¹` needs.) -/
theorem parallelTransportAlong_injective (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Injective (parallelTransportAlong (I := I) hab hgeo hγc ht) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  by_contra hne
  have hpos : 0 < g.metricInner (γ a) (v : TangentSpace I (γ a)) v :=
    g.metricInner_self_pos (γ a) v hne
  rw [← metricInner_parallelTransportAlong (I := I) hab hgeo hγc ht v v, hv] at hpos
  exact absurd (g.metricInner_zero_left (γ t) 0) hpos.ne'

/-- **Math.** `P_t` as a linear **automorphism** of `E`: injective (`
parallelTransportAlong_injective`) plus `E` finite-dimensional.  This is what lets do Carmo
write `P_t⁻¹`, and hence `φ_t = P̃_t ∘ i ∘ P_t⁻¹`. -/
def parallelTransportAlongEquiv (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) {t : ℝ} (ht : t ∈ Icc a b) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofInjectiveEndo (parallelTransportAlong (I := I) hab hgeo hγc ht)
    (parallelTransportAlong_injective (I := I) hab hgeo hγc ht)

@[simp] theorem parallelTransportAlongEquiv_apply (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) {t : ℝ} (ht : t ∈ Icc a b) (w₀ : E) :
    parallelTransportAlongEquiv (I := I) hab hgeo hγc ht w₀
      = parallelTransportAlong (I := I) hab hgeo hγc ht w₀ := rfl

/-- **Math.** The defining property in inverse form: `P_t⁻¹` sends the time-`t` value of a
parallel field back to its seed. -/
theorem parallelTransportAlongEquiv_symm_apply_of_isParallelFieldAlongOn {hab : a < b}
    {hgeo : IsGeodesicOn (I := I) g γ (Icc a b)}
    {hγc : ∀ t ∈ Icc a b, ContinuousAt γ t} {v : ℝ → E}
    (hv : IsParallelFieldAlongOn (I := I) g γ v a b) {t : ℝ} (ht : t ∈ Icc a b) :
    (parallelTransportAlongEquiv (I := I) hab hgeo hγc ht).symm (v t) = v a := by
  rw [LinearEquiv.symm_apply_eq, parallelTransportAlongEquiv_apply,
    parallelTransportAlong_apply]
  exact (parallelFieldSeed_eq (hab := hab) (hgeo := hgeo) (hγc := hγc) hv rfl t ht).symm

end Transport

end Riemannian.Jacobi

end
