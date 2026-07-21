/-
Copyright (c) 2026 Archon Horizon. All rights reserved.
Released under Apache 2.0 license.
-/
import MorganTianLib.Ch01.BrokenVariationGlue
import MorganTianLib.Ch01.ChartPartitionCorner
import MorganTianLib.Ch01.PieceEnergyDeriv
import MorganTianLib.Ch01.SecondVariationPrep
import MorganTianLib.Ch01.FrameLiftCovDeriv
import MorganTianLib.Ch01.FrameIndexSeam
import MorganTianLib.Ch01.JunctionGeodesic
import MorganTianLib.Ch01.GeodesicSpeed
import MorganTianLib.Ch01.IndexFormNegativeSmooth
import MorganTianLib.Ch01.SmoothExtension

/-!
# Poincaré Ch. 1 — the broken chart variation of a geodesic: the data package

This file **constructs** the broken chart variation that half 2 of
`prop:minimal-geodesic-no-conjugate` (*a minimizing geodesic has nonnegative index form*)
computes with.  Every analytic ingredient already existed; what was missing was the
construction itself, and that is what `exists_brokenVariationData` supplies.

## The input

A geodesic `γ` on `[a, b] ⊇ [0, 1]` (with room at both ends), a parallel frame `e` along
it, and a test field given by its **frame coefficients**, split at a corner `c ∈ (0, 1)`
into two globally-`C³` halves `W₀`, `W₁` with `W₀ c = W₁ c`.  This is *exactly* the output
of `exists_indexForm_neg_smooth_of_isConjugatePointAt` (`Ch01/IndexFormNegativeSmooth.lean`),
so the interface is demonstrably not vacuous.

The manifold field is the lift of the glued coefficient curve,
`V = frameFieldOf g γ e (glueCoeff c W₀ W₁)`, and the field *of the `i`-th piece* is the
lift of the **smooth half** that owns that piece,
`frameFieldOf g γ e (if i < k then W₀ else W₁)`.

## The construction

1. **Partition through the corner.**  `exists_chart_partition_slack_through` partitions
   `[0, 1]` with `τ k = c`, chart centres `β i`, and a slack `r > 0` such that `γ` carries
   the enlarged *open* interval `Ioo (τ i - r) (τ (i+1) + r)` into `(chartAt H (β i)).source`.
   Routing the partition through `c` is what makes the field have **no corner inside any
   piece**: on the `i`-th piece the glued field agrees with the globally smooth half
   `if i < k then W₀ else W₁` (`glueCoeff_eq_half_on_piece`).

2. **Chart readings.**  On the enlarged piece, the chart reading `ŷᵢ = φ_{β i} ∘ γ` of the
   geodesic is `C³` (`contDiffOn_chartReading_of_isGeodesicOn`), and the chart reading
   `Ŷᵢ = chartVectorRep γ (β i) Vᵢ` of the piece field is `C³` — it expands in the frame as
   `∑ⱼ ⟪𝔟 ⱼ, W(s)⟫ • chartVectorRep γ (β i) (e j) s` (`chartVectorRep_frameLift_eq`), whose
   frame factors are `C³` by the parallel-transport bootstrap
   (`contDiffOn_chartVectorRep_of_isParallelAlongOn`).

3. **Junction curves.**  `cᵢ = globalGeodesic g hg (γ (τ i)) (V (τ i))` — a genuine manifold
   geodesic with prescribed initial data; its chart reading in the chart at `β i` is `C³`
   near `σ = 0` (`contDiffOn_chartReading_globalGeodesic`), with derivative
   `chartVectorRep γ (β i) V (τ i)` at `σ = 0`.

4. **Bump-extension and assembly.**  All four one-variable data are bump-extended to
   globally-`C³` functions agreeing with them on **open** sets
   (`exists_contDiff_eqOn_of_contDiffOn_Ioo`), and fed to `chartVariation`
   (`Ch01/ChartVariation.lean`).  The tube lemma
   (`exists_forall_mem_of_isCompact_of_continuous`) over the *compact* enlarged piece then
   confines the whole family to the chart target for small variation parameters, and the
   finitely many per-piece radii are minimized over `Finset.range N`.

## What is delivered

* `exists_brokenVariationData` — **the data package**, an existence statement, hence not
  vacuous: the chart families `u i`, their `C³` regularity, their confinement to the chart
  targets on an enlarged box, the identification of the `s = 0` line with `γ`, of the two
  junction curves with the prescribed global geodesics (and of their stay in the chart
  source, so that those readings may be read *back* into `M`), and of the `∂_s`-field with
  the chart reading of the piece field.  Every clause is proved.

* `hasDerivAt_deriv_pieceEnergy_indexIntegrand` — **the second variation of one piece IS the
  abstract index form of its coefficients**:

    `d²/ds² Eᵢ(0) = indexForm (frameCurvOp g γ e) (τ i) (τ (i+1)) W (W′) W (W′)`,

  with `W` the smooth half owning the piece.  Its hypotheses are, one for one, the clauses
  of the data package (the two junction hypotheses being routed through
  `covDerivAlong_fst_eq_zero_of_globalGeodesic_junction`), so it is directly composable
  with it.

* `hasDerivAt_pieceEnergy_chartMetricBilin` — the first `s`-derivative of a piece energy on a
  whole neighbourhood of `0`, which is what lets `deriv_deriv_sum_eq` split the *second*
  derivative of the total energy across the pieces.

* `isMetricCompatibleAt_chartMetricBilin_target` — the honest domain of the chart data is the
  whole chart target (the tangent-bundle trivialization's base set at `α` *is* the chart
  source at `α`), which is what makes the box clause of the data package the right one.

## What this feeds

`Ch01/MinimalGeodesicNoConjugate.lean` consumes the data package and closes half 2:
`s = 0` is a *local minimum* of the total energy `𝓔 (s) = ∑ᵢ Eᵢ(s)` (because `γ` is
minimizing and the endpoints of the varied curve are fixed by `globalGeodesic_zero_velocity`,
the outer junction curves having zero initial velocity), hence
`0 ≤ deriv (deriv 𝓔) 0 = ∑ᵢ Iᵢ`, hence `indexForm ≥ 0`.

A note for readers of the history: an earlier draft of this file reported the `∀ s` in the
junction hypothesis of `sq_dist_le_sum_chartFamily_energy` as a genuine obstruction, and
proposed a reparametrization clamp to work around it.  That was a misdiagnosis of an
*over-strong hypothesis*, not a real wall: every use of `hjunc` inside
`Ch01/BrokenVariationGlue.lean` was already at the single `s` in play, so the `∀ s` was pure
surplus and has been removed.  With the single-`s` form, the junction matching follows
directly from the eventual junction clauses below (intersect the finitely many
neighbourhoods with `Filter.eventually_all_finset`).  No clamp is needed.

Blueprint: `prop:minimal-geodesic-no-conjugate`,
`claim:second-variation-minimal-geodesic`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.3–§1.4.
-/

open Set Filter Riemannian Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

/-! ### The glued coefficient curve -/

section Glue

variable {F : Type*}

/-- **Math.** The coefficient curve of the test field, glued at the corner `c`: it is `W₀`
up to `c` and `W₁` after.  When `W₀ c = W₁ c` it is continuous, and it agrees with **one**
smooth half on every subinterval of `[·, c]` or of `[c, ·]` — which is the whole reason the
chart partition is routed through `c`. -/
def glueCoeff (c : ℝ) (W₀ W₁ : ℝ → F) : ℝ → F := fun s => if s ≤ c then W₀ s else W₁ s

theorem glueCoeff_of_le {c : ℝ} {W₀ W₁ : ℝ → F} {s : ℝ} (hs : s ≤ c) :
    glueCoeff c W₀ W₁ s = W₀ s := if_pos hs

theorem glueCoeff_of_lt {c : ℝ} {W₀ W₁ : ℝ → F} {s : ℝ} (hs : c < s) :
    glueCoeff c W₀ W₁ s = W₁ s := if_neg (not_le.mpr hs)

/-- **Math.** **On each piece of a partition through the corner, the glued curve *is* a
smooth half.**  If `τ` is strictly increasing with `τ k = c`, then on the closed piece
`[τ i, τ (i+1)]` the glued coefficient curve coincides with `W₀` when `i < k` and with `W₁`
when `k ≤ i`.

The only delicate point is the piece that *ends* at the corner (`i + 1 = k`) and the one
that *starts* there (`i = k`): at the single time `s = c` both halves are used, and they
agree there by `hmatch`. -/
theorem glueCoeff_eq_half_on_piece {c : ℝ} {W₀ W₁ : ℝ → F} (hmatch : W₀ c = W₁ c)
    {τ : ℕ → ℝ} {k i : ℕ} (hmono : ∀ j, τ j < τ (j + 1)) (hτk : τ k = c)
    {s : ℝ} (hs : s ∈ Icc (τ i) (τ (i + 1))) :
    glueCoeff c W₀ W₁ s = (if i < k then W₀ else W₁) s := by
  have hsm : StrictMono τ := strictMono_nat_of_lt_succ hmono
  by_cases hik : i < k
  · have hle : τ (i + 1) ≤ c := by rw [← hτk]; exact hsm.monotone (by omega)
    rw [glueCoeff_of_le (hs.2.trans hle), if_pos hik]
  · have hge : c ≤ τ i := by rw [← hτk]; exact hsm.monotone (by omega)
    have hcs : c ≤ s := hge.trans hs.1
    rw [if_neg hik]
    rcases eq_or_lt_of_le hcs with heq | hlt
    · rw [← heq, glueCoeff_of_le le_rfl, hmatch]
    · rw [glueCoeff_of_lt hlt]

end Glue

/-! ### The manifold setting -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-- **Math.** The field along `γ` with prescribed frame coefficients `W`: the pointwise lift
`s ↦ ∑ᵢ Wᵢ(s) · eᵢ(s)` of the coefficient curve through the frame. Its frame coordinates are
`W` again (`frameVec_frameLift_apply`), so no information is lost. -/
def frameFieldOf (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (W : ℝ → 𝔼) : ℝ → E :=
  fun s => frameLift (I := I) g γ e s (W s)

/-- **Math.** The frame coordinates of a frame-coefficient field are the coefficients again:
`frameVec ∘ frameFieldOf = id`.  Restatement of `frameVec_frameLift_apply` for `frameFieldOf`
(the two are definitionally the same field). -/
theorem frameVec_frameFieldOf {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {t : ℝ}
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0) (W : ℝ → 𝔼) :
    frameVec (I := I) g γ e (frameFieldOf (I := I) g γ e W) t = W t :=
  frameVec_frameLift_apply (I := I) horth W

/-- **Math.** The chart reading of a frame-coefficient field is `C^n` wherever the
coefficients are `C^n` and the geodesic stays in the chart.

By `chartVectorRep_frameLift_eq` the reading expands as
`∑ⱼ ⟪𝔟 ⱼ, W s⟫ • chartVectorRep γ α (e j) s`; the scalar factors are `C^n` because
`x ↦ ⟪𝔟 ⱼ, x⟫` is a continuous linear map, and the frame factors are `C^n` by the
parallel-transport bootstrap `contDiffOn_chartVectorRep_of_isParallelAlongOn`. -/
theorem contDiffOn_chartVectorRep_frameFieldOf {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {a b : ℝ}
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {α : M} {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (hsrc : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H α).source)
    {W : ℝ → 𝔼} {n : ℕ} (hW : ContDiffOn ℝ n W (Ioo c d)) :
    ContDiffOn ℝ n (chartVectorRep (I := I) γ α (frameFieldOf (I := I) g γ e W)) (Ioo c d) := by
  classical
  have hE : ∀ j, ContDiffOn ℝ n (chartVectorRep (I := I) γ α (e j)) (Ioo c d) := fun j =>
    contDiffOn_chartVectorRep_of_isParallelAlongOn (I := I) (hPar j) hgeo hγc hsub hsrc n
  have hexp : chartVectorRep (I := I) γ α (frameFieldOf (I := I) g γ e W)
      = fun s => ∑ j, ⟪(𝔟 j : 𝔼), W s⟫ • chartVectorRep (I := I) γ α (e j) s :=
    chartVectorRep_frameLift_eq (I := I) g γ α e W
  rw [hexp]
  refine ContDiffOn.sum fun j _ => ContDiffOn.smul ?_ (hE j)
  have h := ((innerSL ℝ (𝔟 j : 𝔼)).contDiff (n := n)).comp_contDiffOn hW
  simpa only [Function.comp_def, innerSL_apply_apply] using h

/-! ### The data package -/

set_option maxHeartbeats 1600000 in
set_option maxSynthPendingDepth 6 in
/-- **Math.** **The broken chart variation of a minimizing geodesic: the data.**

Let `γ` be a geodesic on `[a, b] ⊇ [0, 1]` (`a < 0 < 1 < b`), `e` a parallel frame along it,
and let a test field be given by its frame coefficients, split at a corner `c ∈ (0, 1)` into
two halves `W₀` (of class `C³` on `(a, b)`) and `W₁` (of class `C³` on `ℝ`) matching at `c`.
Write `V = frameFieldOf g γ e (glueCoeff c W₀ W₁)` for the resulting field along `γ`.

Then there exist a partition `0 = τ 0 < ⋯ < τ N = 1` **through the corner** (`τ k = c`,
`0 < k < N`), chart centres `β i`, chart families `u i : ℝ × ℝ → E`, and radii `ρ, ε > 0`
with `ε ≤ ρ`, such that:

* each `u i` is `C³` on the whole parameter plane;
* `u i` maps the enlarged box `(-ε, ε) × (τ i - ρ, τ (i+1) + ρ)` into the chart target — so
  every consumer that reads `u i` back into `M` through the chart at `β i` is legitimate;
* the unvaried line `s = 0` of `u i` **is** `γ` read in the chart at `β i`, on a
  neighbourhood of every time of the `i`-th closed piece;
* the two junction curves `σ ↦ u i (σ, τ i)` and `σ ↦ u i (σ, τ (i+1))` **are** the global
  geodesics with initial data `(γ (τ j), V (τ j))`, read in the chart at `β i`, for `σ` near
  `0` — this is what makes the assembled broken path a genuine curve *and* kills each piece's
  second-variation boundary term inside its own chart;
* the `∂_s`-field of `u i` on the unvaried line is the chart reading of the **piece field**
  `frameFieldOf g γ e (if i < k then W₀ else W₁)` — the globally smooth half that owns the
  piece, which on the piece agrees with `V` (`glueCoeff_eq_half_on_piece`);
* `γ` stays in the `i`-th chart source over the enlarged piece.

**Note on the `∂_s` clause.** It is stated with the *piece* field, not with the glued field
`V`.  This is forced, and is not a weakening in practice: the clause is an *eventual* identity
on a neighbourhood of each `t` of the piece, and at `t = c` any neighbourhood straddles the
corner, where `V` switches halves while `u (k-1)` — a `C³` object — cannot.  On the piece
itself the two fields agree, which is all a consumer needs (`glueCoeff_eq_half_on_piece`, and
`frameVec_frameLift_apply` turns the piece field's frame coordinates back into `W₀`/`W₁`).

Blueprint: `prop:minimal-geodesic-no-conjugate`. -/
theorem exists_brokenVariationData [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b c : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E} {W₀ W₁ : ℝ → 𝔼}
    (ha : a < 0) (hb : 1 < b) (hc₀ : 0 < c) (hc₁ : c < 1)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hW₀ : ContDiffOn ℝ 3 W₀ (Ioo a b)) (hW₁ : ContDiff ℝ 3 W₁)
    (hmatch : W₀ c = W₁ c) :
    ∃ (N : ℕ) (τ : ℕ → ℝ) (β : ℕ → M) (u : ℕ → ℝ × ℝ → E) (ρ ε : ℝ) (k : ℕ),
      0 < N ∧ 0 < ρ ∧ 0 < ε ∧ ε ≤ ρ ∧ 0 < k ∧ k < N ∧
      τ 0 = 0 ∧ τ N = 1 ∧ τ k = c ∧ (∀ i, τ i < τ (i + 1)) ∧
      (∀ i ≤ N, τ i ∈ Icc (0 : ℝ) 1) ∧
      -- regularity of each piece's chart family
      (∀ i < N, ContDiff ℝ 3 (u i)) ∧
      -- each piece stays in its chart's (extended) target on the enlarged box
      (∀ i < N, ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (τ i - ρ) (τ (i + 1) + ρ),
        u i p ∈ (extChartAt I (β i)).target) ∧
      -- the unvaried line IS `γ` read in the chart, near every time of the piece
      (∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)),
        ∀ᶠ s in 𝓝 t, u i ((0 : ℝ), s) = extChartAt I (β i) (γ s)) ∧
      -- the junction curves are the global geodesics with the prescribed initial data
      (∀ i < N, ∀ᶠ σ in 𝓝 (0 : ℝ), u i (σ, τ i) = extChartAt I (β i)
        (globalGeodesic (I := I) g hg (γ (τ i))
          ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ i) : E)) σ)) ∧
      (∀ i < N, ∀ᶠ σ in 𝓝 (0 : ℝ), u i (σ, τ (i + 1)) = extChartAt I (β i)
        (globalGeodesic (I := I) g hg (γ (τ (i + 1)))
          ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ (i + 1)) : E)) σ)) ∧
      -- the `∂_s`-field of the unvaried line is the piece field, read in the chart
      (∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), ∀ᶠ s in 𝓝 t,
        fderiv ℝ (u i) ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ))
          = chartVectorRep (I := I) γ (β i)
              (frameFieldOf (I := I) g γ e (if i < k then W₀ else W₁)) s) ∧
      -- the junction geodesics stay in the chart source for small `σ` (so the chart readings
      -- above may be read *back* into `M`)
      (∀ i < N, ∀ᶠ σ in 𝓝 (0 : ℝ),
        globalGeodesic (I := I) g hg (γ (τ i))
          ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ i) : E)) σ
            ∈ (chartAt H (β i)).source) ∧
      (∀ i < N, ∀ᶠ σ in 𝓝 (0 : ℝ),
        globalGeodesic (I := I) g hg (γ (τ (i + 1)))
          ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ (i + 1)) : E)) σ
            ∈ (chartAt H (β i)).source) ∧
      -- `γ`'s foot stays in `(a, b)` and in the chart source over the enlarged **closed** piece
      (∀ i < N, ∀ t ∈ Icc (τ i - ρ) (τ (i + 1) + ρ),
        t ∈ Ioo a b ∧ γ t ∈ (chartAt H (β i)).source) := by
  classical
  have hab : a < b := ha.trans (by linarith)
  have hIcc01 : Icc (0 : ℝ) 1 ⊆ Ioo a b := fun t ht =>
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hγOn : ContinuousOn γ (Ioo a b) := fun t ht =>
    (hγc t (Ioo_subset_Icc_self ht)).continuousWithinAt
  -- ### Step 1: the partition through the corner
  obtain ⟨N, τ, β, r, k, hN, hr, hτ0, hτN, hk0, hkN, hτk, hmono, hτmem, hslack⟩ :=
    exists_chart_partition_slack_through (I := I) (γ := γ) (O := Ioo a b)
      hc₀ hc₁ isOpen_Ioo hIcc01 hγOn
  set V : ℝ → E := frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) with hVdef
  -- ### Step 2: the per-piece construction
  have hpiece : ∀ i : ℕ, ∃ (uu : ℝ × ℝ → E) (ρ' ε' : ℝ), i < N →
      (0 < ρ' ∧ 0 < ε' ∧ ε' ≤ ρ' ∧
        ContDiff ℝ 3 uu ∧
        (∀ t ∈ Icc (τ i - ρ') (τ (i + 1) + ρ'),
          t ∈ Ioo a b ∧ γ t ∈ (chartAt H (β i)).source) ∧
        (∀ p ∈ Ioo (-ε') ε' ×ˢ Ioo (τ i - ρ') (τ (i + 1) + ρ'),
          uu p ∈ (extChartAt I (β i)).target) ∧
        (∀ t ∈ Icc (τ i) (τ (i + 1)),
          ∀ᶠ s in 𝓝 t, uu ((0 : ℝ), s) = extChartAt I (β i) (γ s)) ∧
        (∀ᶠ σ in 𝓝 (0 : ℝ), uu (σ, τ i)
          = extChartAt I (β i) (globalGeodesic (I := I) g hg (γ (τ i)) (V (τ i)) σ)) ∧
        (∀ᶠ σ in 𝓝 (0 : ℝ), uu (σ, τ (i + 1))
          = extChartAt I (β i)
              (globalGeodesic (I := I) g hg (γ (τ (i + 1))) (V (τ (i + 1))) σ)) ∧
        (∀ t ∈ Icc (τ i) (τ (i + 1)), ∀ᶠ s in 𝓝 t,
          fderiv ℝ uu ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ))
            = chartVectorRep (I := I) γ (β i)
                (frameFieldOf (I := I) g γ e (if i < k then W₀ else W₁)) s) ∧
        (∀ᶠ σ in 𝓝 (0 : ℝ), globalGeodesic (I := I) g hg (γ (τ i)) (V (τ i)) σ
          ∈ (chartAt H (β i)).source) ∧
        (∀ᶠ σ in 𝓝 (0 : ℝ), globalGeodesic (I := I) g hg (γ (τ (i + 1))) (V (τ (i + 1))) σ
          ∈ (chartAt H (β i)).source)) := by
    intro i
    by_cases hi : i < N
    swap
    · exact ⟨fun _ => 0, 1, 1, fun hc => absurd hc hi⟩
    -- the enlarged open piece, and its half-size closed companion
    set L : ℝ := τ i with hL
    set R : ℝ := τ (i + 1) with hR
    have hLR : L < R := hmono i
    have hEnl : ∀ t ∈ Ioo (L - r) (R + r),
        t ∈ Ioo a b ∧ γ t ∈ (chartAt H (β i)).source ∧
          extChartAt I (β i) (γ t) ∈ interior (extChartAt I (β i)).target :=
      hslack i hi
    have hr2 : 0 < r / 2 := by linarith
    have hJsub : Ioo (L - r / 2) (R + r / 2) ⊆ Ioo (L - r) (R + r) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    have hJclsub : Icc (L - r / 2) (R + r / 2) ⊆ Ioo (L - r) (R + r) := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hJclab : Icc (L - r / 2) (R + r / 2) ⊆ Icc a b := fun t ht =>
      Ioo_subset_Icc_self ((hEnl t (hJclsub ht)).1)
    have hJclsrc : ∀ t ∈ Icc (L - r / 2) (R + r / 2), γ t ∈ (chartAt H (β i)).source :=
      fun t ht => (hEnl t (hJclsub ht)).2.1
    -- (a) the chart reading of the geodesic is `C³` on the open enlarged piece
    have hŷ : ContDiffOn ℝ 3 (fun t => extChartAt I (β i) (γ t))
        (Ioo (L - r / 2) (R + r / 2)) := by
      have := contDiffOn_chartReading_of_isGeodesicOn (I := I) g
        (J := Ioo (L - r / 2) (R + r / 2)) (β := β i) isOpen_Ioo
        (fun t ht => hgeo t (hJclab (Ioo_subset_Icc_self ht)))
        (fun t ht => hγc t (hJclab (Ioo_subset_Icc_self ht)))
        (fun t ht => hJclsrc t (Ioo_subset_Icc_self ht)) 3
      exact this
    -- (b) the chart reading of the piece field is `C³` there
    have hWhalf : ContDiffOn ℝ 3 (if i < k then W₀ else W₁) (Ioo (L - r / 2) (R + r / 2)) := by
      by_cases hik : i < k
      · rw [if_pos hik]
        exact hW₀.mono (fun t ht => (hEnl t (hJsub ht)).1)
      · rw [if_neg hik]
        exact hW₁.contDiffOn
    have hŶ : ContDiffOn ℝ 3
        (chartVectorRep (I := I) γ (β i)
          (frameFieldOf (I := I) g γ e (if i < k then W₀ else W₁)))
        (Ioo (L - r / 2) (R + r / 2)) :=
      contDiffOn_chartVectorRep_frameFieldOf (I := I) hPar hgeo hγc hJclab hJclsrc hWhalf
    -- (c) bump-extend both
    obtain ⟨ŷE, Vy, hŷE, hVyopen, hIccVy, hVysub, hEqy⟩ :=
      exists_contDiff_eqOn_of_contDiffOn_Ioo (n := 3) hŷ
        (by linarith : L - r / 2 < L) hLR.le (by linarith : R < R + r / 2)
    obtain ⟨ŶE, VY, hŶE, hVYopen, hIccVY, hVYsub, hEqY⟩ :=
      exists_contDiff_eqOn_of_contDiffOn_Ioo (n := 3) hŶ
        (by linarith : L - r / 2 < L) hLR.le (by linarith : R < R + r / 2)
    -- (d) the two junction geodesics, their chart readings, and their bump extensions
    have hjunc : ∀ (T : ℝ), T ∈ Ioo (L - r) (R + r) →
        ∃ (ĉ : ℝ → E) (Vc : Set ℝ), ContDiff ℝ 3 ĉ ∧ IsOpen Vc ∧ (0 : ℝ) ∈ Vc ∧
          EqOn ĉ (fun σ => extChartAt I (β i)
            (globalGeodesic (I := I) g hg (γ T) (V T) σ)) Vc ∧
          (∀ σ ∈ Vc, globalGeodesic (I := I) g hg (γ T) (V T) σ
            ∈ (chartAt H (β i)).source) := by
      intro T hT
      have hTsrc : γ T ∈ (chartAt H (β i)).source := (hEnl T hT).2.1
      set cT : ℝ → M := globalGeodesic (I := I) g hg (γ T) (V T) with hcT
      have hcT0 : cT 0 = γ T := globalGeodesic_zero (I := I) g hg (γ T) (V T)
      have hcTcont : Continuous cT := continuous_globalGeodesic (I := I) g hg (γ T) (V T)
      have hpre : cT ⁻¹' (chartAt H (β i)).source ∈ 𝓝 (0 : ℝ) :=
        (((chartAt H (β i)).open_source).preimage hcTcont).mem_nhds
          (show cT 0 ∈ (chartAt H (β i)).source by rw [hcT0]; exact hTsrc)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
      have hballIoo : Ioo (-δ) δ ⊆ cT ⁻¹' (chartAt H (β i)).source := by
        intro σ hσ
        refine hball ?_
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        exact ⟨hσ.1, hσ.2⟩
      have hsm : ContDiffOn ℝ 3 (fun σ => extChartAt I (β i) (cT σ)) (Ioo (-δ) δ) :=
        contDiffOn_chartReading_globalGeodesic (I := I) g hg (γ T) (V T) isOpen_Ioo
          (fun σ hσ => hballIoo hσ) 3
      obtain ⟨ĉ, Vc, hĉ, hVcopen, hIccVc, hVcsub, hEqc⟩ :=
        exists_contDiff_eqOn_of_contDiffOn_Ioo (n := 3) hsm
          (by linarith : -δ < (0 : ℝ)) (le_refl (0 : ℝ)) (by linarith : (0 : ℝ) < δ)
      exact ⟨ĉ, Vc, hĉ, hVcopen, hIccVc ⟨le_rfl, le_rfl⟩, hEqc,
        fun σ hσ => hballIoo (hVcsub hσ)⟩
    have hLmem : L ∈ Ioo (L - r) (R + r) := ⟨by linarith, by linarith⟩
    have hRmem : R ∈ Ioo (L - r) (R + r) := ⟨by linarith, by linarith⟩
    obtain ⟨ĉ₀, V₀, hĉ₀, hV₀open, hV₀0, hEq₀, hV₀src⟩ := hjunc L hLmem
    obtain ⟨ĉ₁, V₁, hĉ₁, hV₁open, hV₁0, hEq₁, hV₁src⟩ := hjunc R hRmem
    -- (e) the chart family
    set uu : ℝ × ℝ → E := chartVariation L R ŷE ŶE ĉ₀ ĉ₁ with huu
    have hne : L ≠ R := hLR.ne
    -- the chart reading of the piece field at the two endpoints is the reading of `V`
    have hVpiece : ∀ T ∈ Icc L R,
        chartVectorRep (I := I) γ (β i)
            (frameFieldOf (I := I) g γ e (if i < k then W₀ else W₁)) T
          = chartVectorRep (I := I) γ (β i) V T := by
      intro T hT
      have h := glueCoeff_eq_half_on_piece (F := 𝔼) (c := c) (W₀ := W₀) (W₁ := W₁) hmatch
        (τ := τ) (k := k) (i := i) hmono hτk (s := T) hT
      simp only [chartVectorRep_apply, hVdef, frameFieldOf, h]
    -- (f) the four hypotheses of `chartVariation`
    have hLVy : L ∈ Vy := hIccVy ⟨le_rfl, hLR.le⟩
    have hRVy : R ∈ Vy := hIccVy ⟨hLR.le, le_rfl⟩
    have hLVY : L ∈ VY := hIccVY ⟨le_rfl, hLR.le⟩
    have hRVY : R ∈ VY := hIccVY ⟨hLR.le, le_rfl⟩
    have hjunc0 : ∀ (T : ℝ), T ∈ Icc L R → T ∈ Ioo (L - r) (R + r) → ∀ (ĉ : ℝ → E)
        (Vc : Set ℝ), IsOpen Vc → (0 : ℝ) ∈ Vc →
        EqOn ĉ (fun σ => extChartAt I (β i)
          (globalGeodesic (I := I) g hg (γ T) (V T) σ)) Vc →
        ĉ 0 = extChartAt I (β i) (γ T) ∧
          HasDerivAt ĉ (chartVectorRep (I := I) γ (β i) V T) 0 := by
      intro T _ hTe ĉ Vc hVcopen hVc0 hEqc
      have hTsrc : γ T ∈ (chartAt H (β i)).source := (hEnl T hTe).2.1
      set cT : ℝ → M := globalGeodesic (I := I) g hg (γ T) (V T) with hcT
      have hcT0 : cT 0 = γ T := globalGeodesic_zero (I := I) g hg (γ T) (V T)
      have hev : ĉ =ᶠ[𝓝 (0 : ℝ)] fun σ => extChartAt I (β i) (cT σ) := by
        filter_upwards [hVcopen.mem_nhds hVc0] with σ hσ using hEqc hσ
      constructor
      · rw [hev.eq_of_nhds, hcT0]
      · -- the chart-`β i` velocity of the junction geodesic at `σ = 0`
        have hgeoT : HasGeodesicEquationAt (I := I) g cT 0 :=
          (isGeodesic_globalGeodesic (I := I) g hg (γ T) (V T)).hasGeodesicEquationAt 0
        have hcont : ContinuousAt cT 0 :=
          (continuous_globalGeodesic (I := I) g hg (γ T) (V T)).continuousAt
        have hsrc0 : cT 0 ∈ (chartAt H (β i)).source := by rw [hcT0]; exact hTsrc
        have hD := (hgeoT.eventually_hasDerivAt_extChartAt hcont hsrc0).self_of_nhds
        have hlocal : deriv (chartLocalCurve (I := I) cT 0) 0 = V T := by
          have hread : chartLocalCurve (I := I) cT 0
              = chartReading (I := I) (γ T) cT := by
            funext σ
            simp only [chartLocalCurve, chartReading, hcT0]
          rw [hread]
          exact (hasDerivAt_chartReading_globalGeodesic (I := I) g hg (γ T) (V T)).deriv
        rw [hlocal, hcT0] at hD
        have hrep : tangentCoordChange I (γ T) (β i) (γ T) (V T)
            = chartVectorRep (I := I) γ (β i) V T := (chartVectorRep_apply _ _ _ _).symm
        rw [hrep] at hD
        exact hD.congr_of_eventuallyEq hev
    obtain ⟨hĉ₀0, hĉ₀'⟩ := hjunc0 L ⟨le_rfl, hLR.le⟩ hLmem ĉ₀ V₀ hV₀open hV₀0 hEq₀
    obtain ⟨hĉ₁0, hĉ₁'⟩ := hjunc0 R ⟨hLR.le, le_rfl⟩ hRmem ĉ₁ V₁ hV₁open hV₁0 hEq₁
    have hc₀y : ĉ₀ 0 = ŷE L := by rw [hĉ₀0, hEqy hLVy]
    have hc₁y : ĉ₁ 0 = ŷE R := by rw [hĉ₁0, hEqy hRVy]
    have hc₀Y : HasDerivAt ĉ₀ (ŶE L) 0 := by
      have : ŶE L = chartVectorRep (I := I) γ (β i) V L := by
        rw [hEqY hLVY]; exact hVpiece L ⟨le_rfl, hLR.le⟩
      rw [this]; exact hĉ₀'
    have hc₁Y : HasDerivAt ĉ₁ (ŶE R) 0 := by
      have : ŶE R = chartVectorRep (I := I) γ (β i) V R := by
        rw [hEqY hRVY]; exact hVpiece R ⟨hLR.le, le_rfl⟩
      rw [this]; exact hĉ₁'
    -- (g) regularity, and the three identification clauses
    have hcd : ContDiff ℝ 3 uu := contDiff_chartVariation hne hŷE hŶE hĉ₀ hĉ₁
    have hzero : ∀ t : ℝ, uu ((0 : ℝ), t) = ŷE t := fun t =>
      chartVariation_zero (ŷ := ŷE) (Ŷ := ŶE) hc₀y hc₁y t
    have hleft : ∀ s : ℝ, uu (s, L) = ĉ₀ s := fun s => chartVariation_left hne s
    have hright : ∀ s : ℝ, uu (s, R) = ĉ₁ s := fun s => chartVariation_right hne s
    have hfd : ∀ t : ℝ, fderiv ℝ uu ((0 : ℝ), t) ((1 : ℝ), (0 : ℝ)) = ŶE t := fun t =>
      fderiv_chartVariation_snd_zero hne hc₀y hc₁y hc₀Y hc₁Y
        ((hŷE.differentiable (by norm_num)).differentiableAt)
        ((hŶE.differentiable (by norm_num)).differentiableAt)
    -- (h) the slack radius: an enlarged closed piece inside the common agreement set
    set Vi : Set ℝ := Vy ∩ VY with hVi
    have hViopen : IsOpen Vi := hVyopen.inter hVYopen
    have hIccVi : Icc L R ⊆ Vi := fun t ht => ⟨hIccVy ht, hIccVY ht⟩
    obtain ⟨ρ', hρ', hρsub⟩ := exists_Icc_enlarged_subset hViopen hLR.le hIccVi
    have hViJ : Vi ⊆ Ioo (L - r / 2) (R + r / 2) := fun t ht => hVysub ht.1
    have hρr : ρ' < r / 2 := by
      have hmem : L - ρ' ∈ Ioo (L - r / 2) (R + r / 2) :=
        hViJ (hρsub ⟨le_rfl, by linarith⟩)
      have := hmem.1
      linarith
    have hIooρ : Ioo (L - ρ') (R + ρ') ⊆ Ioo (L - r) (R + r) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    -- (i) the tube radius
    have hmem0 : ∀ t ∈ Icc (L - ρ') (R + ρ'), uu ((0 : ℝ), t) ∈ (extChartAt I (β i)).target := by
      intro t ht
      have htVi : t ∈ Vi := hρsub ht
      rw [hzero t, hEqy htVi.1]
      have : t ∈ Ioo (L - r) (R + r) := hJsub (hViJ htVi)
      exact interior_subset (hEnl t this).2.2
    obtain ⟨ε₀, hε₀, htube⟩ :=
      exists_forall_mem_of_isCompact_of_continuous (u := uu)
        (U := (extChartAt I (β i)).target) (K := Icc (L - ρ') (R + ρ'))
        isCompact_Icc (isOpen_extChartAt_target (I := I) (β i)) hcd.continuous hmem0
    have hIccρ : Icc (L - ρ') (R + ρ') ⊆ Ioo (L - r) (R + r) := fun t ht =>
      hJsub (hViJ (hρsub ht))
    refine ⟨uu, ρ', min ε₀ ρ', fun _ => ⟨hρ', lt_min hε₀ hρ', min_le_right _ _, hcd, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩⟩
    · -- `γ` in `(a, b)` and in the chart source over the enlarged closed piece
      exact fun t ht => ⟨(hEnl t (hIccρ ht)).1, (hEnl t (hIccρ ht)).2.1⟩
    · -- the box
      rintro ⟨s, t⟩ ⟨hs, ht⟩
      have hs' : s ∈ Ioo (-ε₀) ε₀ :=
        ⟨lt_of_le_of_lt (neg_le_neg (min_le_left ε₀ ρ')) hs.1,
          hs.2.trans_le (min_le_left ε₀ ρ')⟩
      exact htube s hs' t (Ioo_subset_Icc_self ht)
    · -- the unvaried line
      intro t ht
      filter_upwards [hVyopen.mem_nhds (hIccVy ht)] with s hs
      rw [hzero s, hEqy hs]
    · -- the left junction
      filter_upwards [hV₀open.mem_nhds hV₀0] with σ hσ
      rw [hleft σ, hEq₀ hσ]
    · -- the right junction
      filter_upwards [hV₁open.mem_nhds hV₁0] with σ hσ
      rw [hright σ, hEq₁ hσ]
    · -- the `∂_s` field
      intro t ht
      filter_upwards [hVYopen.mem_nhds (hIccVY ht)] with s hs
      rw [hfd s, hEqY hs]
    · -- the left junction geodesic stays in the chart source
      filter_upwards [hV₀open.mem_nhds hV₀0] with σ hσ using hV₀src σ hσ
    · -- the right junction geodesic stays in the chart source
      filter_upwards [hV₁open.mem_nhds hV₁0] with σ hσ using hV₁src σ hσ
  -- ### Step 3: choose the per-piece data and take the minimal radii
  choose uf ρf εf hpf using hpiece
  have hrangeNE : (Finset.range N).Nonempty := ⟨0, Finset.mem_range.mpr hN⟩
  set ρ : ℝ := (Finset.range N).inf' hrangeNE ρf with hρdef
  set ε : ℝ := (Finset.range N).inf' hrangeNE εf with hεdef
  have hρle : ∀ i < N, ρ ≤ ρf i := fun i hi =>
    Finset.inf'_le _ (Finset.mem_range.mpr hi)
  have hεle : ∀ i < N, ε ≤ εf i := fun i hi =>
    Finset.inf'_le _ (Finset.mem_range.mpr hi)
  have hρpos : 0 < ρ := by
    rw [hρdef, Finset.lt_inf'_iff]
    exact fun i hi => (hpf i (Finset.mem_range.mp hi)).1
  have hεpos : 0 < ε := by
    rw [hεdef, Finset.lt_inf'_iff]
    exact fun i hi => (hpf i (Finset.mem_range.mp hi)).2.1
  have hερ : ε ≤ ρ := by
    rw [hρdef]
    refine Finset.le_inf' _ _ fun i hi => ?_
    exact (hεle i (Finset.mem_range.mp hi)).trans (hpf i (Finset.mem_range.mp hi)).2.2.1
  refine ⟨N, τ, β, uf, ρ, ε, k, hN, hρpos, hεpos, hερ, hk0, hkN, hτ0, hτN, hτk, hmono, hτmem,
    fun i hi => (hpf i hi).2.2.2.1, ?_, fun i hi => (hpf i hi).2.2.2.2.2.2.1,
    fun i hi => (hpf i hi).2.2.2.2.2.2.2.1, fun i hi => (hpf i hi).2.2.2.2.2.2.2.2.1,
    fun i hi => (hpf i hi).2.2.2.2.2.2.2.2.2.1,
    fun i hi => (hpf i hi).2.2.2.2.2.2.2.2.2.2.1,
    fun i hi => (hpf i hi).2.2.2.2.2.2.2.2.2.2.2, ?_⟩
  · -- the box, with the global radii
    rintro i hi ⟨s, t⟩ ⟨hs, ht⟩
    refine (hpf i hi).2.2.2.2.2.1 (s, t) ⟨?_, ?_⟩
    · exact ⟨lt_of_le_of_lt (neg_le_neg (hεle i hi)) hs.1, hs.2.trans_le (hεle i hi)⟩
    · exact ⟨by linarith [hρle i hi, ht.1], by linarith [hρle i hi, ht.2]⟩
  · -- `γ` in `(a, b)` and in the chart source, with the global radius
    intro i hi t ht
    refine (hpf i hi).2.2.2.2.1 t ⟨?_, ?_⟩
    · linarith [hρle i hi, ht.1]
    · linarith [hρle i hi, ht.2]

/-! ### The second variation of one piece, as the abstract index form of the coefficients -/

/-- **Math.** **The genuine chart data is metric-compatible on the whole chart target.**
`isMetricCompatibleAt_chartMetricBilin` (`Ch01/ChartMetricCompatible.lean`) asks for two
things: the chart point in the *interior* of the chart target (which, the model being
boundaryless, is the target itself), and its readback in the trivialization base set — but
the base set of the tangent-bundle trivialization at `α` **is** the chart source at `α`
(`symm_extChartAt_mem_baseSet`), and the readback of a target point lies there by
`PartialEquiv.map_target`.  So the honest domain of the chart data is simply
`(extChartAt I α).target`, which is exactly the open set `U` that the piece
second-variation lemma wants. -/
theorem isMetricCompatibleAt_chartMetricBilin_target (g : RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    IsMetricCompatibleAt (chartMetricBilin (I := I) g α)
      (chartChristoffelBilin (I := I) g α) y := by
  refine isMetricCompatibleAt_chartMetricBilin (I := I) g α ?_ ?_
  · rwa [(isOpen_extChartAt_target (I := I) α).interior_eq]
  · show (extChartAt I α).symm y ∈ (chartAt H α).source
    rw [← extChartAt_source (I := I) α]
    exact (extChartAt I α).map_target hy

set_option maxHeartbeats 1600000 in
/-- **Math.** **The second variation of one piece of the broken variation IS the index form
of the piece's frame coefficients.**

Let `γ` be a geodesic on `[a, b]` with a parallel `g`-orthonormal frame `e`, let
`[τ₀ - ρ, τ₁ + ρ] ⊆ [a, b]` be an enlarged piece whose `γ`-image lies in the chart at `α`,
and let `u` be a `C³` chart family satisfying exactly the clauses that
`exists_brokenVariationData` produces:

* `u` maps the enlarged box into the chart target (`hbox`);
* the `s = 0` line reads `γ` in the chart near every time of the piece (`hline`);
* its `∂_s`-field reads the frame-coefficient field `W` (`hvar`);
* the two junction curves are geodesics in the chart (`hj₀`, `hj₁` — discharge these with
  `covDerivAlong_fst_eq_zero_of_globalGeodesic_junction` from the junction clauses of the
  data package).

Then the energy of this piece is twice differentiable at `s = 0` and

`d²/ds² Eᵢ(0) = ∫_{τ₀}^{τ₁} (⟪W′, W′⟫ − ⟪ℛ(t) W, W⟫) dt = I_{[τ₀,τ₁]}(W, W)`,

the **abstract index form** of the coefficient curve `W` in which half 1 of
`prop:minimal-geodesic-no-conjugate` (`exists_indexForm_neg_smooth_of_isConjugatePointAt`)
delivers its strictly negative direction.

The two seams doing the translation are `chartIndexIntegrand_eq_indexIntegrand_frameVec`
(chart integrand `=` abstract integrand of the frame coordinates) and
`frameVec_frameLift_apply` (the frame coordinates of the lift of `W` are `W` again), with
the covariant-derivative hypothesis discharged by
`covariantDerivCoord_chartVectorRep_frameLift` — in a *parallel* frame the covariant
derivative of the lift is the coordinate derivative of the coefficients.

Blueprint: `prop:minimal-geodesic-no-conjugate`,
`claim:second-variation-minimal-geodesic`. -/
theorem hasDerivAt_deriv_pieceEnergy_indexIntegrand
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E} {α : M} {u : ℝ × ℝ → E} {τ₀ τ₁ ρ : ℝ} {W : ℝ → 𝔼}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    (hτ : τ₀ < τ₁) (hρ : 0 < ρ)
    (hEnl : ∀ t ∈ Icc (τ₀ - ρ) (τ₁ + ρ), t ∈ Icc a b ∧ γ t ∈ (chartAt H α).source)
    (hWd : ∀ t ∈ Ioo (τ₀ - ρ) (τ₁ + ρ), DifferentiableAt ℝ W t)
    (hu : ContDiff ℝ 3 u)
    (hbox : ∀ p ∈ Ioo (-ρ) ρ ×ˢ Ioo (τ₀ - ρ) (τ₁ + ρ), u p ∈ (extChartAt I α).target)
    (hline : ∀ t ∈ Icc τ₀ τ₁, ∀ᶠ s in 𝓝 t, u ((0 : ℝ), s) = extChartAt I α (γ s))
    (hvar : ∀ t ∈ Icc τ₀ τ₁, ∀ᶠ s in 𝓝 t,
      fderiv ℝ u ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ))
        = chartVectorRep (I := I) γ α (frameFieldOf (I := I) g γ e W) s)
    (hj₀ : covDerivAlong (chartChristoffelBilin (I := I) g α) u
      (fun q => fderiv ℝ u q ((1 : ℝ), (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), τ₀) = 0)
    (hj₁ : covDerivAlong (chartChristoffelBilin (I := I) g α) u
      (fun q => fderiv ℝ u q ((1 : ℝ), (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), τ₁) = 0) :
    HasDerivAt (deriv (fun s => ∫ t in τ₀..τ₁,
        energyDensity (chartMetricBilin (I := I) g α) u ((0 : ℝ), (1 : ℝ)) (s, t)))
      (indexForm (frameCurvOp (I := I) g γ e) τ₀ τ₁ W (deriv W) W (deriv W)) 0 := by
  have hU : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have hcompat : ∀ y ∈ (extChartAt I α).target,
      IsMetricCompatibleAt (chartMetricBilin (I := I) g α)
        (chartChristoffelBilin (I := I) g α) y := fun y hy =>
    isMetricCompatibleAt_chartMetricBilin_target (I := I) g α hy
  have hG : ContDiffOn ℝ 2 (chartMetricBilin (I := I) g α) (extChartAt I α).target :=
    contDiffOn_infty.mp (contDiffOn_chartMetricBilin (I := I) g α) 2
  have hΓ : ContDiffOn ℝ 1 (chartChristoffelBilin (I := I) g α) (extChartAt I α).target := by
    have h := contDiffOn_infty.mp (contDiffOn_chartChristoffelBilin (I := I) g α) 1
    rwa [(isOpen_extChartAt_target (I := I) α).interior_eq] at h
  have hIccIoo : Icc τ₀ τ₁ ⊆ Ioo (τ₀ - ρ) (τ₁ + ρ) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIccab : Icc (τ₀ - ρ) (τ₁ + ρ) ⊆ Icc a b := fun t ht => (hEnl t ht).1
  have hsrc : ∀ t ∈ Icc (τ₀ - ρ) (τ₁ + ρ), γ t ∈ (chartAt H α).source := fun t ht => (hEnl t ht).2
  -- the `t`-lines at `s = 0` are geodesic in the chart
  have hgeoT : ∀ t ∈ Icc τ₀ τ₁,
      covDerivAlong (chartChristoffelBilin (I := I) g α) u
        (fun q => fderiv ℝ u q ((0 : ℝ), (1 : ℝ))) ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), t) = 0 := by
    intro t ht
    have htI : t ∈ Icc (τ₀ - ρ) (τ₁ + ρ) := Ioo_subset_Icc_self (hIccIoo ht)
    exact covDerivAlong_snd_eq_zero_of_geodesic_tline (I := I) (hu.of_le (by norm_num))
      (hgeo t (hIccab htI)) (hγc t (hIccab htI)) (hsrc t htI) (hline t ht)
  have hkey := hasDerivAt_deriv_pieceEnergy_chartIndexIntegrand
    (G := chartMetricBilin (I := I) g α) (Γ := chartChristoffelBilin (I := I) g α) (u := u)
    (τ₀ := τ₀) (τ₁ := τ₁) (r := ρ) (U := (extChartAt I α).target)
    hτ.le hρ hU (fun x X Y => chartMetricBilin_symm (I := I) g α x X Y)
    (fun x X Y => chartChristoffelBilin_symm (I := I) g α x X Y) hcompat hG hΓ hu hbox
    hgeoT hj₀ hj₁
  -- the chart integrand is the abstract index integrand of the coefficient curve `W`
  have hcongr : ∀ t ∈ uIcc τ₀ τ₁,
      chartIndexIntegrand (chartMetricBilin (I := I) g α)
          (chartChristoffelBilin (I := I) g α) u t
        = indexIntegrand (frameCurvOp (I := I) g γ e) W (deriv W) W (deriv W) t := by
    intro t ht
    rw [uIcc_of_le hτ.le] at ht
    have htIoo : t ∈ Ioo (τ₀ - ρ) (τ₁ + ρ) := hIccIoo ht
    have htI : t ∈ Icc (τ₀ - ρ) (τ₁ + ρ) := Ioo_subset_Icc_self htIoo
    have htab : t ∈ Icc a b := hIccab htI
    have hDV := covariantDerivCoord_chartVectorRep_frameLift (I := I) (g := g) (γ := γ)
      (e := e) (a := a) (b := b) hPar hgeo hγc (α := α) (c := τ₀ - ρ) (d := τ₁ + ρ)
      hIccab hsrc (W := W) (DW := deriv W) htIoo ((hWd t htIoo).hasDerivAt)
    have hseam := chartIndexIntegrand_eq_indexIntegrand_frameVec (I := I) g
      (γ := γ) (α := α) (V := frameFieldOf (I := I) g γ e W)
      (DV := frameFieldOf (I := I) g γ e (deriv W)) (e := e) (u := u) (t := t)
      (horth t htab) (hsrc t htI) (hgeo t htab) (hγc t htab)
      (hu.of_le (by norm_num)) (hline t ht) (hvar t ht) hDV
    rw [hseam]
    simp only [indexIntegrand]
    rw [frameVec_frameFieldOf (I := I) (horth t htab) W,
      frameVec_frameFieldOf (I := I) (horth t htab) (deriv W)]
  rw [intervalIntegral.integral_congr hcongr] at hkey
  exact hkey

/-- **Math.** **The first `s`-derivative of one piece's energy, on a whole neighbourhood of
`0`.**  The companion of `hasDerivAt_deriv_pieceEnergy_indexIntegrand`: `deriv` of a finite
sum only splits where *every* summand is differentiable, and — for the *second* derivative of
the sum — that has to hold on a whole neighbourhood of `0`, not just at `0`.  This is
`hasDerivAt_pieceEnergy` (`Ch01/PieceEnergyDeriv.lean`) with the abstract metric `G`
instantiated at the genuine chart Gram data, whose `C²` regularity on the chart target is
`contDiffOn_chartMetricBilin`.

Together with `hasDerivAt_deriv_pieceEnergy_indexIntegrand` these are exactly the two
hypotheses `hd`, `hd2` of `deriv_deriv_sum_eq`. -/
theorem hasDerivAt_pieceEnergy_chartMetricBilin (g : RiemannianMetric I M) {α : M}
    {u : ℝ × ℝ → E} {τ₀ τ₁ ρ : ℝ} (hτ : τ₀ ≤ τ₁) (hρ : 0 < ρ) (hu : ContDiff ℝ 3 u)
    (hbox : ∀ p ∈ Ioo (-ρ) ρ ×ˢ Ioo (τ₀ - ρ) (τ₁ + ρ), u p ∈ (extChartAt I α).target)
    {s : ℝ} (hs : s ∈ Ioo (-ρ) ρ) :
    HasDerivAt (fun σ => ∫ t in τ₀..τ₁,
        energyDensity (chartMetricBilin (I := I) g α) u ((0 : ℝ), (1 : ℝ)) (σ, t))
      (∫ t in τ₀..τ₁, deriv (fun r =>
        energyDensity (chartMetricBilin (I := I) g α) u ((0 : ℝ), (1 : ℝ)) (r, t)) s) s :=
  hasDerivAt_pieceEnergy hτ hρ
    (contDiffOn_infty.mp (contDiffOn_chartMetricBilin (I := I) g α) 2) hu hbox hs

end MorganTianLib

end

#print axioms MorganTianLib.glueCoeff_eq_half_on_piece
#print axioms MorganTianLib.contDiffOn_chartVectorRep_frameFieldOf
#print axioms MorganTianLib.exists_brokenVariationData
#print axioms MorganTianLib.frameVec_frameFieldOf
#print axioms MorganTianLib.isMetricCompatibleAt_chartMetricBilin_target
#print axioms MorganTianLib.hasDerivAt_deriv_pieceEnergy_indexIntegrand
#print axioms MorganTianLib.hasDerivAt_pieceEnergy_chartMetricBilin
