/-
Copyright (c) 2026 Archon Horizon. All rights reserved.
Released under Apache 2.0 license.
-/
import MorganTianLib.Ch01.BrokenVariationData
import MorganTianLib.Ch01.BrokenVariationGlue
import MorganTianLib.Ch01.IndexFormNegativeSmooth
import MorganTianLib.Ch01.GeodesicSpeed
import MorganTianLib.Ch01.PieceEnergyDeriv
import MorganTianLib.Ch01.SecondVariationPrep

/-!
# Poincaré Ch. 1 — a minimizing geodesic has no conjugate point in `[0, 1)`

This file **closes** `prop:minimal-geodesic-no-conjugate` by assembling half 2 — *a minimizing
geodesic has nonnegative index form* — and colliding it with half 1
(`exists_indexForm_neg_smooth_of_isConjugatePointAt`, `Ch01/IndexFormNegativeSmooth.lean`),
which produces a strictly negative index form at a conjugate point.

## Half 2, in six moves

Let `γ` be a geodesic on `[a, b] ⊇ [0, 1]` whose restriction to `[0, 1]` is minimizing, `e` a
parallel orthonormal frame along it, and let a test field be given by its frame coefficients,
split at a corner `c ∈ (0, 1)` into `C³` halves `W₀`, `W₁` matching at `c`, with `W₀ 0 = 0` and
`W₁ 1 = 0`.

1. **The variation.**  `exists_brokenVariationData` (`Ch01/BrokenVariationData.lean`) builds the
   broken chart variation: a partition `0 = τ 0 < ⋯ < τ N = 1` through the corner (`τ k = c`),
   chart centres `β i`, and `C³` chart families `u i` whose `s = 0` line reads `γ`, whose
   junction curves are the *global geodesics* with initial data `(γ (τ j), V (τ j))`, and whose
   `∂_s`-field reads the piece half-field.

2. **The total energy** `𝓔 (s) = ∑ᵢ ∫_{τ i}^{τ (i+1)} energyDensity (chartMetricBilin g (β i))
   (u i) ∂ₜ (s, t)`.

3. **`s = 0` is a local minimum of `𝓔`.**  For `|s|` small the glued path
   `brokenPath β u τ N s` is a genuine curve of `M` — the two chart readings at a junction are
   the *same manifold point*, being two readings of one global geodesic, and the finitely many
   junction neighbourhoods are intersected with `Filter.eventually_all_finset` — so
   `sq_dist_le_sum_chartFamily_energy` (`Ch01/BrokenVariationGlue.lean`) bounds
   `d(Φ_s 0, Φ_s 1)² ≤ 2 𝓔 (s)`.  Its endpoints are **fixed**: the field vanishes at `0` and
   `1` (`W₀ 0 = 0`, `W₁ 1 = 0`), so the outer junction curves are geodesics with zero initial
   velocity, i.e. constant (`globalGeodesic_zero_velocity`).  And at `s = 0` the bound is an
   *equality*, `2 𝓔 (0) = d(γ 0, γ 1)²`, because `γ` is a minimizing geodesic
   (`sum_chart_energy_eq_sq_dist_of_minimizing`, `Ch01/GeodesicSpeed.lean`).  The factor `2` and
   the `derivWithin`/`fderiv` mismatch are absorbed by `two_mul_pieceEnergy_eq_chartMetricInner`
   and `derivWithin_eq_deriv_of_eqOn_Icc`.

4. **The second-derivative test.**  `deriv_deriv_nonneg_of_isLocalMin`
   (`Ch01/EnergyVariation.lean`) gives `0 ≤ 𝓔″(0)`.

5. **Splitting `𝓔″(0)` over the pieces.**  `deriv_deriv_sum_eq` (`Ch01/PieceEnergyDeriv.lean`),
   fed with the first derivative of each piece on a whole neighbourhood of `0`
   (`hasDerivAt_pieceEnergy_chartMetricBilin`) and the second derivative at `0`
   (`hasDerivAt_deriv_pieceEnergy_indexIntegrand`, which *is* the abstract index form of the
   piece's coefficients), gives `0 ≤ ∑ᵢ I_{[τ i, τ (i+1)]}(Wᵢ, Wᵢ)`.

6. **Recombining.**  The index form is an interval integral of `indexIntegrand`, whose
   continuity comes from `continuousOn_frameCurvOp` and the smoothness of the halves, so
   `intervalIntegral.sum_integral_adjacent_intervals` telescopes the pieces below the corner
   into `I_{[0, c]}(W₀, W₀)` and those above it into `I_{[c, 1]}(W₁, W₁)`.

## What is delivered

* `indexForm_nonneg_of_minimizing` — **half 2**: for a minimizing geodesic, the index form of
  any broken test field vanishing at both endpoints is `≥ 0`.
* `not_isConjugatePointAt_of_minimizing` — **the proposition**: a minimizing geodesic has no
  conjugate point at any `t₀ ∈ (0, 1)`.

Blueprint: `prop:minimal-geodesic-no-conjugate`, `claim:second-variation-minimal-geodesic`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.3–§1.4.
-/

open Set Filter Riemannian Module MeasureTheory
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
  [CompleteSpace E] [T2Space (TangentBundle I M)]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ### Two small bridges -/

/-- **Math.** The `t`-slice derivative of a vector-valued family on the parameter square:
`∂_t u (s, t) = (d/dr) u (s, r) |_{r = t}`.  (`PieceSecondVariation.deriv_slice_snd` is the
same statement for scalar-valued families; the proof is verbatim the chain rule along the
affine line `r ↦ (s, r)`.) -/
theorem deriv_slice_snd_vec {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    deriv (fun r => f (s, r)) t = fderiv ℝ f (s, t) ((0 : ℝ), (1 : ℝ)) :=
  (hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))).deriv

/-- **Math.** The lift of the zero coefficient vector is the zero tangent vector: the lift is
the finite sum `∑ᵢ ⟪𝔟 ᵢ, x⟫ • eᵢ`, linear in `x`. -/
theorem frameFieldOf_eq_zero {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (finrank ℝ E) → ℝ → E} {W : ℝ → 𝔼} {t : ℝ} (hW : W t = 0) :
    (frameFieldOf (I := I) g γ e W t : E) = 0 := by
  show (∑ i, ⟪(EuclideanSpace.basisFun (Fin (finrank ℝ E)) ℝ i : 𝔼), W t⟫ • (e i t : E)) = 0
  simp [hW]

/-! ### The chart energy of one piece, doubled -/

/-- **Math.** Twice the `energyDensity`-energy of a piece is its `chartMetricInner`-energy —
the normalisation in which `sq_dist_le_sum_chartFamily_energy` states the lower bound
`d(p, q)² ≤ ∑ᵢ ∫ᵢ ⟨∂ₜu, ∂ₜu⟩`.  Two identifications: `chartMetricBilin_apply`
(`chartMetricBilin = chartMetricInner`) and `deriv_slice_snd_vec` (`fderiv u (s,t) (0,1)` is
the `t`-slice derivative). -/
theorem two_mul_pieceEnergy_eq_chartMetricInner (g : RiemannianMetric I M) (α : M)
    {u : ℝ × ℝ → E} (hu : Differentiable ℝ u) (s τ₀ τ₁ : ℝ) :
    2 * ∫ t in τ₀..τ₁, energyDensity (chartMetricBilin (I := I) g α) u ((0 : ℝ), (1 : ℝ)) (s, t)
      = ∫ t in τ₀..τ₁, chartMetricInner (I := I) g α (u (s, t))
          (deriv (fun r => u (s, r)) t) (deriv (fun r => u (s, r)) t) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [energyDensity]
  rw [deriv_slice_snd_vec (hu (s, t)), ← chartMetricBilin_apply (I := I) g α]
  ring

/-! ### The primary target -/

set_option maxHeartbeats 1600000 in
set_option maxSynthPendingDepth 6 in
/-- **Math.** **Half 2 of `prop:minimal-geodesic-no-conjugate`: a minimizing geodesic has
nonnegative index form.**

Let `γ` be a geodesic on `[a, b] ⊇ [0, 1]` (`a < 0 < 1 < b`) whose restriction to `[0, 1]` is
**minimizing** — in the workspace's official normalisation (`Ch01/GeodesicSpeed.lean`), its
speed, which for a unit-time geodesic *is* its length, is at most `d(γ 0, γ 1)`.  Let `e` be a
parallel `g`-orthonormal frame along `γ`, and let a test field be given by its frame
coefficients, split at a corner `c ∈ (0, 1)` into two `C³` halves `W₀`, `W₁` matching at `c`
and **vanishing at the two endpoints** (`W₀ 0 = 0`, `W₁ 1 = 0`).  Then

`I_{[0,c]}(W₀, W₀) + I_{[c,1]}(W₁, W₁) ≥ 0`.

*Proof.*  The two index forms are the second `s`-derivative at `s = 0` of the energy of the
broken chart variation of `γ` in the direction of the field (`exists_brokenVariationData`,
`hasDerivAt_deriv_pieceEnergy_indexIntegrand`, `deriv_deriv_sum_eq`).  The varied curve has the
same endpoints as `γ` (the field vanishes there, so the outer junction geodesics are constant),
and `γ` is minimizing, so `2 𝓔 (s) ≥ d(γ 0, γ 1)² = 2 𝓔 (0)` for all small `s`
(`sq_dist_le_sum_chartFamily_energy`, `sum_chart_energy_eq_sq_dist_of_minimizing`): `s = 0` is a
local minimum, and a local minimum has nonnegative second derivative
(`deriv_deriv_nonneg_of_isLocalMin`). ∎

The corner `c` and the two halves are exactly the shape in which half 1
(`exists_indexForm_neg_smooth_of_isConjugatePointAt`) delivers a strictly *negative* index form
at a conjugate point, so the two statements collide directly — see
`not_isConjugatePointAt_of_minimizing`.

Blueprint: `prop:minimal-geodesic-no-conjugate`,
`claim:second-variation-minimal-geodesic`. -/
theorem indexForm_nonneg_of_minimizing [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b c : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E} {W₀ W₁ : ℝ → 𝔼}
    (ha : a < 0) (hb : 1 < b) (hc₀ : 0 < c) (hc₁ : c < 1)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1))
    (hW₀ : ContDiffOn ℝ 3 W₀ (Ioo a b)) (hW₁ : ContDiff ℝ 3 W₁)
    (hW₀0 : W₀ 0 = 0) (hW₁1 : W₁ 1 = 0) (hmatch : W₀ c = W₁ c) :
    0 ≤ indexForm (frameCurvOp (I := I) g γ e) 0 c W₀ (deriv W₀) W₀ (deriv W₀)
      + indexForm (frameCurvOp (I := I) g γ e) c 1 W₁ (deriv W₁) W₁ (deriv W₁) := by
  classical
  obtain ⟨N, τ, β, u, ρ, ε, k, hN, hρ, hε, hερ, hk0, hkN, hτ0, hτN, hτk, hmono, hτmem,
    hCD, hbox, hline, hjL, hjR, hvar, hsrcL, hsrcR, hEnl⟩ :=
    exists_brokenVariationData (I := I) g hg ha hb hc₀ hc₁ hgeo hγc hPar hW₀ hW₁ hmatch
  have hab : a < b := ha.trans (by linarith)
  have hIcc01 : Icc (0 : ℝ) 1 ⊆ Ioo a b := fun t ht =>
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hsm : StrictMono τ := strictMono_nat_of_lt_succ hmono
  -- the enlarged data, with the *smaller* radius `ε ≤ ρ`, which is what the piece lemmas want
  have hboxε : ∀ i < N, ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (τ i - ε) (τ (i + 1) + ε),
      u i p ∈ (extChartAt I (β i)).target := fun i hi p hp =>
    hbox i hi p ⟨hp.1, Ioo_subset_Ioo (by linarith) (by linarith) hp.2⟩
  have hEnlε : ∀ i < N, ∀ t ∈ Icc (τ i - ε) (τ (i + 1) + ε),
      t ∈ Ioo a b ∧ γ t ∈ (chartAt H (β i)).source := fun i hi t ht =>
    hEnl i hi t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the piece energies, their first derivatives, and their second derivatives
  set f : ℕ → ℝ → ℝ := fun i s => ∫ t in (τ i)..(τ (i + 1)),
    energyDensity (chartMetricBilin (I := I) g (β i)) (u i) ((0 : ℝ), (1 : ℝ)) (s, t) with hfdef
  set f' : ℕ → ℝ → ℝ := fun i s => ∫ t in (τ i)..(τ (i + 1)),
    deriv (fun r =>
      energyDensity (chartMetricBilin (I := I) g (β i)) (u i) ((0 : ℝ), (1 : ℝ)) (r, t)) s
    with hf'def
  set L : ℕ → ℝ := fun i => indexForm (frameCurvOp (I := I) g γ e) (τ i) (τ (i + 1))
    (if i < k then W₀ else W₁) (deriv (if i < k then W₀ else W₁))
    (if i < k then W₀ else W₁) (deriv (if i < k then W₀ else W₁)) with hLdef
  -- ### the first derivative of each piece energy, on a whole neighbourhood of `0`
  have hd : ∀ i < N, ∀ s ∈ Ioo (-ε) ε, HasDerivAt (f i) (f' i s) s := fun i hi s hs =>
    hasDerivAt_pieceEnergy_chartMetricBilin (I := I) g (hmono i).le hε (hCD i hi)
      (hboxε i hi) hs
  -- ### the second derivative of each piece energy IS the index form of its coefficients
  have hd2 : ∀ i < N, HasDerivAt (f' i) (L i) 0 := by
    intro i hi
    have hWd : ∀ t ∈ Ioo (τ i - ε) (τ (i + 1) + ε),
        DifferentiableAt ℝ (if i < k then W₀ else W₁) t := by
      intro t ht
      have htab : t ∈ Ioo a b := (hEnlε i hi t (Ioo_subset_Icc_self ht)).1
      by_cases hik : i < k
      · rw [if_pos hik]
        exact (hW₀.differentiableOn (by norm_num)).differentiableAt
          (isOpen_Ioo.mem_nhds htab)
      · rw [if_neg hik]
        exact (hW₁.differentiable (by norm_num)).differentiableAt
    have hsrc₀ : γ (τ i) ∈ (chartAt H (β i)).source :=
      (hEnlε i hi (τ i) ⟨by linarith, by linarith [hmono i]⟩).2
    have hsrc₁ : γ (τ (i + 1)) ∈ (chartAt H (β i)).source :=
      (hEnlε i hi (τ (i + 1)) ⟨by linarith [hmono i], by linarith⟩).2
    have hj₀ := covDerivAlong_fst_eq_zero_of_globalGeodesic_junction (I := I) (α := β i)
      (u := u i) g hg ((hCD i hi).of_le (by norm_num)) hsrc₀ (hjL i hi)
    have hj₁ := covDerivAlong_fst_eq_zero_of_globalGeodesic_junction (I := I) (α := β i)
      (u := u i) g hg ((hCD i hi).of_le (by norm_num)) hsrc₁ (hjR i hi)
    have hkey := hasDerivAt_deriv_pieceEnergy_indexIntegrand (I := I) g (α := β i)
      (u := u i) (W := if i < k then W₀ else W₁) hgeo hγc hPar horth (hmono i) hε
      (fun t ht => ⟨Ioo_subset_Icc_self (hEnlε i hi t ht).1, (hEnlε i hi t ht).2⟩)
      hWd (hCD i hi) (hboxε i hi) (hline i hi) (hvar i hi) hj₀ hj₁
    -- `deriv (f i)` and `f' i` agree on a neighbourhood of `0`
    refine hkey.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by linarith : (-ε : ℝ) < 0) hε] with s hs
    exact ((hd i hi s hs).deriv).symm
  -- ### the varied curve has fixed endpoints, because the field vanishes there
  have hV0 : (frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ 0) : E) = 0 := by
    refine frameFieldOf_eq_zero (I := I) ?_
    rw [hτ0, glueCoeff_of_le hc₀.le, hW₀0]
  have hV1 : (frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ N) : E) = 0 := by
    refine frameFieldOf_eq_zero (I := I) ?_
    rw [hτN, glueCoeff_of_lt hc₁, hW₁1]
  have hgg0 : ∀ s : ℝ, globalGeodesic (I := I) g hg (γ (τ 0))
      ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ 0) : E)) s = γ (τ 0) := by
    have hconst : globalGeodesic (I := I) g hg (γ (τ 0))
        ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ 0) : E)) = fun _ => γ (τ 0) := by
      rw [show ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ 0) : E)) = 0 from hV0]
      exact globalGeodesic_zero_velocity (I := I) g hg (γ (τ 0))
    intro s; rw [hconst]
  have hggN : ∀ s : ℝ, globalGeodesic (I := I) g hg (γ (τ N))
      ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ N) : E)) s = γ (τ N) := by
    have hconst : globalGeodesic (I := I) g hg (γ (τ N))
        ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ N) : E)) = fun _ => γ (τ N) := by
      rw [show ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ N) : E)) = 0 from hV1]
      exact globalGeodesic_zero_velocity (I := I) g hg (γ (τ N))
    intro s; rw [hconst]
  -- ### the finitely many junction neighbourhoods, intersected
  have hEv : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i ∈ Finset.range N,
      (u i (s, τ i) = extChartAt I (β i) (globalGeodesic (I := I) g hg (γ (τ i))
        ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ i) : E)) s)) ∧
      (u i (s, τ (i + 1)) = extChartAt I (β i) (globalGeodesic (I := I) g hg (γ (τ (i + 1)))
        ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ (i + 1)) : E)) s)) ∧
      (globalGeodesic (I := I) g hg (γ (τ i))
        ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ i) : E)) s
          ∈ (chartAt H (β i)).source) ∧
      (globalGeodesic (I := I) g hg (γ (τ (i + 1)))
        ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ (i + 1)) : E)) s
          ∈ (chartAt H (β i)).source) := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact (hjL i hi').and ((hjR i hi').and ((hsrcL i hi').and (hsrcR i hi')))
  -- ### the chart families are smooth in time, and stay in the chart targets
  have hu1 : ∀ (s : ℝ), ∀ i < N, ContDiff ℝ 1 (fun t => u i (s, t)) := fun s i hi =>
    ((hCD i hi).comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)
  have hmemT : ∀ s ∈ Ioo (-ε) ε, ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)),
      u i (s, t) ∈ (extChartAt I (β i)).target := fun s hs i hi t ht =>
    hboxε i hi (s, t) ⟨hs, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  -- ### `2 𝓔 (s)` is the energy of the glued broken path, hence `≥ d(γ 0, γ 1)²`
  have hE0mem : γ (τ 0) ∈ (chartAt H (β 0)).source :=
    (hEnlε 0 hN (τ 0) ⟨by linarith, by linarith [hmono 0]⟩).2
  have hm : (N - 1) + 1 = N := Nat.succ_pred_eq_of_pos hN
  have hmN : N - 1 < N := by omega
  have hENmem : γ (τ N) ∈ (chartAt H (β (N - 1))).source := by
    have := (hEnlε (N - 1) hmN (τ ((N - 1) + 1))
      ⟨by linarith [hmono (N - 1)], by linarith⟩).2
    rwa [hm] at this
  have hEnergy : ∀ s ∈ Ioo (-ε) ε, (∀ i ∈ Finset.range N,
      (u i (s, τ i) = extChartAt I (β i) (globalGeodesic (I := I) g hg (γ (τ i))
        ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ i) : E)) s)) ∧
      (u i (s, τ (i + 1)) = extChartAt I (β i) (globalGeodesic (I := I) g hg (γ (τ (i + 1)))
        ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ (i + 1)) : E)) s)) ∧
      (globalGeodesic (I := I) g hg (γ (τ i))
        ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ i) : E)) s
          ∈ (chartAt H (β i)).source) ∧
      (globalGeodesic (I := I) g hg (γ (τ (i + 1)))
        ((frameFieldOf (I := I) g γ e (glueCoeff c W₀ W₁) (τ (i + 1)) : E)) s
          ∈ (chartAt H (β i)).source)) →
      dist (γ 0) (γ 1) ^ 2 ≤ 2 * ∑ i ∈ Finset.range N, f i s := by
    intro s hsε hs
    -- the two chart readings at a junction are the same manifold point
    have hjuncS : ∀ i, i + 1 < N →
        (extChartAt I (β (i + 1))).symm (u (i + 1) (s, τ (i + 1)))
          = (extChartAt I (β i)).symm (u i (s, τ (i + 1))) := by
      intro i hi1
      obtain ⟨-, h2, -, h4⟩ := hs i (Finset.mem_range.mpr (by omega))
      obtain ⟨h1', -, h3', -⟩ := hs (i + 1) (Finset.mem_range.mpr hi1)
      rw [h1', h2, (extChartAt I (β (i + 1))).left_inv (by rwa [extChartAt_source]),
        (extChartAt I (β i)).left_inv (by rwa [extChartAt_source])]
    -- the endpoints of the glued path are those of `γ`
    have h01 : (0 : ℝ) < τ 1 := by rw [← hτ0]; exact hmono 0
    have hE0 : brokenPath (I := I) β u τ N s 0 = γ 0 := by
      rw [brokenPath_eq_of_mem_Icc (I := I) hmono hN hjuncS hN ⟨hτ0.le, h01.le⟩]
      obtain ⟨h1, -, -, -⟩ := hs 0 (Finset.mem_range.mpr hN)
      rw [← hτ0, h1, hgg0 s]
      exact (extChartAt I (β 0)).left_inv (by rw [extChartAt_source]; exact hE0mem)
    have hE1 : brokenPath (I := I) β u τ N s 1 = γ 1 := by
      have hτle : τ (N - 1) ≤ (1 : ℝ) := by
        have := hsm.monotone (show N - 1 ≤ N by omega)
        rw [hτN] at this; exact this
      rw [brokenPath_eq_of_mem_Icc (I := I) hmono hN hjuncS hmN
        (by rw [hm, hτN]; exact ⟨hτle, le_rfl⟩)]
      obtain ⟨-, h2, -, -⟩ := hs (N - 1) (Finset.mem_range.mpr hmN)
      rw [hm] at h2
      rw [← hτN, h2, hggN s]
      exact (extChartAt I (β (N - 1))).left_inv (by rw [extChartAt_source]; exact hENmem)
    have hkey := sq_dist_le_sum_chartFamily_energy (I := I) g hg hmono hN hτ0 hτN hjuncS
      (fun i hi t ht => hmemT s hsε i hi t ht) (fun i hi => hu1 s i hi)
    rw [hE0, hE1] at hkey
    have hRHS : ∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)),
          chartMetricInner (I := I) g (β i) (u i (s, t))
            (deriv (fun r => u i (s, r)) t) (deriv (fun r => u i (s, r)) t)
        = 2 * ∑ i ∈ Finset.range N, f i s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      exact (two_mul_pieceEnergy_eq_chartMetricInner (I := I) g (β i)
        ((hCD i (Finset.mem_range.mp hi)).differentiable (by norm_num)) s
        (τ i) (τ (i + 1))).symm
    rwa [hRHS] at hkey
  -- ### at `s = 0` the energy of the (unvaried) minimizing geodesic is exactly `d²`
  have hZero : 2 * ∑ i ∈ Finset.range N, f i 0 = dist (γ 0) (γ 1) ^ 2 := by
    have hRHS0 : 2 * ∑ i ∈ Finset.range N, f i 0
        = ∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)),
            chartMetricInner (I := I) g (β i) (extChartAt I (β i) (γ t))
              (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t)
              (derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [two_mul_pieceEnergy_eq_chartMetricInner (I := I) g (β i)
        ((hCD i hi').differentiable (by norm_num)) 0 (τ i) (τ (i + 1))]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le (hmono i).le] at ht
      have heq : EqOn (fun r => extChartAt I (β i) (γ r)) (fun r => u i ((0 : ℝ), r))
          (Icc (τ i) (τ (i + 1))) := fun r hr => ((hline i hi' r hr).self_of_nhds).symm
      have heq' : extChartAt I (β i) (γ t) = u i ((0 : ℝ), t) := heq ht
      have hdw : derivWithin (fun r => extChartAt I (β i) (γ r)) (Icc (τ i) (τ (i + 1))) t
          = deriv (fun r => u i ((0 : ℝ), r)) t :=
        derivWithin_eq_deriv_of_eqOn_Icc (hmono i) heq ht
          (((hu1 0 i hi').differentiable (by norm_num)).differentiableAt)
      rw [hdw, heq']
    rw [hRHS0]
    exact sum_chart_energy_eq_sq_dist_of_minimizing (I := I) g hg
      (hgeo.mono Ioo_subset_Icc_self) isOpen_Ioo isPreconnected_Ioo
      (fun t ht => (hγc t (Ioo_subset_Icc_self ht)).continuousWithinAt) hIcc01
      (fun i _ => (hmono i).le) hτ0 hτN
      (fun i hi t ht => (hEnl i hi t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2) hmin
  -- ### hence `s = 0` is a local minimum of the total energy
  have hLocMin : IsLocalMin (fun s => ∑ i ∈ Finset.range N, f i s) 0 := by
    filter_upwards [hEv, Ioo_mem_nhds (by linarith : (-ε : ℝ) < 0) hε] with s hs hsε
    have h1 := hEnergy s hsε hs
    linarith
  -- ### the second-derivative test
  have hnn : 0 ≤ ∑ i ∈ Finset.range N, L i := by
    rw [← deriv_deriv_sum_eq hε hd hd2]
    exact deriv_deriv_nonneg_of_isLocalMin hLocMin (continuousAt_sum hε hd)
  -- ### recombine the sum of piece index forms into the two half index forms
  have hcontI : ∀ W : ℝ → 𝔼, ContDiffOn ℝ 3 W (Ioo a b) →
      ContinuousOn (indexIntegrand (frameCurvOp (I := I) g γ e) W (deriv W) W (deriv W))
        (Ioo a b) := by
    intro W hW
    have hW0 : ContinuousOn W (Ioo a b) := hW.continuousOn
    have hW1 : ContinuousOn (deriv W) (Ioo a b) :=
      (hW.deriv_of_isOpen (m := 2) isOpen_Ioo (by norm_num)).continuousOn
    have hRc : ContinuousOn (frameCurvOp (I := I) g γ e) (Ioo a b) :=
      (continuousOn_frameCurvOp (I := I) hPar hgeo hγc).mono Ioo_subset_Icc_self
    show ContinuousOn (fun t => (⟪deriv W t, deriv W t⟫ : ℝ)
      - ⟪frameCurvOp (I := I) g γ e t (W t), W t⟫) (Ioo a b)
    exact (hW1.inner hW1).sub ((hRc.clm_apply hW0).inner hW0)
  have hii : ∀ W : ℝ → 𝔼, ContDiffOn ℝ 3 W (Ioo a b) → ∀ i < N,
      IntervalIntegrable (indexIntegrand (frameCurvOp (I := I) g γ e) W (deriv W) W (deriv W))
        volume (τ i) (τ (i + 1)) := by
    intro W hW i hi
    refine ContinuousOn.intervalIntegrable ((hcontI W hW).mono ?_)
    rw [uIcc_of_le (hmono i).le]
    exact fun t ht => hIcc01 ⟨(hτmem i hi.le).1.trans ht.1, ht.2.trans (hτmem (i + 1) hi).2⟩
  have hsum₀ : ∑ i ∈ Finset.range k, L i
      = indexForm (frameCurvOp (I := I) g γ e) 0 c W₀ (deriv W₀) W₀ (deriv W₀) := by
    have hcongr : ∀ i ∈ Finset.range k, L i = ∫ t in (τ i)..(τ (i + 1)),
        indexIntegrand (frameCurvOp (I := I) g γ e) W₀ (deriv W₀) W₀ (deriv W₀) t := by
      intro i hi
      simp only [hLdef, if_pos (Finset.mem_range.mp hi), indexForm_def]
    rw [Finset.sum_congr rfl hcongr,
      intervalIntegral.sum_integral_adjacent_intervals
        (fun i hik => hii W₀ hW₀ i (lt_trans hik hkN)),
      indexForm_def, hτ0, hτk]
  have hsum₁ : ∑ i ∈ Finset.Ico k N, L i
      = indexForm (frameCurvOp (I := I) g γ e) c 1 W₁ (deriv W₁) W₁ (deriv W₁) := by
    have hcongr : ∀ i ∈ Finset.Ico k N, L i = ∫ t in (τ i)..(τ (i + 1)),
        indexIntegrand (frameCurvOp (I := I) g γ e) W₁ (deriv W₁) W₁ (deriv W₁) t := by
      intro i hi
      have hik : ¬ i < k := by
        have := (Finset.mem_Ico.mp hi).1
        omega
      simp only [hLdef, if_neg hik, indexForm_def]
    rw [Finset.sum_congr rfl hcongr,
      intervalIntegral.sum_integral_adjacent_intervals_Ico hkN.le
        (fun i hi => hii W₁ hW₁.contDiffOn i hi.2),
      indexForm_def, hτk, hτN]
  have hsplit : ∑ i ∈ Finset.range N, L i
      = (∑ i ∈ Finset.range k, L i) + ∑ i ∈ Finset.Ico k N, L i := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) hkN.le,
      Finset.range_eq_Ico]
  rw [hsplit, hsum₀, hsum₁] at hnn
  exact hnn

/-! ### The proposition -/

/-- **Math.** **`prop:minimal-geodesic-no-conjugate`: a minimizing geodesic has no conjugate
point in `[0, 1)`.**

Let `γ` be a geodesic on `[a, b] ⊇ [0, 1]` (with room at both ends) whose restriction to
`[0, 1]` is minimizing, i.e. its length `√⟨γ′, γ′⟩` is at most `d(γ 0, γ 1)`.  Then no
`t₀ ∈ (0, 1)` is conjugate to `0` along `γ`.

*Proof.*  Suppose `t₀` were conjugate.  Half 1
(`exists_indexForm_neg_smooth_of_isConjugatePointAt`) produces a parallel orthonormal frame
`e` along `γ` and two `C³` coefficient halves `W₀`, `W₁` matching at `t₀`, vanishing at the
two endpoints, whose index forms over `[0, t₀]` and `[t₀, 1]` sum to a **strictly negative**
number: the conjugate Jacobi field, cut at `t₀`, is a *broken* field whose index form is `0`,
and a corner-smoothing variation makes it negative.  Half 2
(`indexForm_nonneg_of_minimizing`) says the same sum is **nonnegative**, because `s = 0` is a
local minimum of the energy of the corresponding broken chart variation of the minimizing
geodesic, so its second derivative — which *is* that sum of index forms — is `≥ 0`.
Contradiction. ∎

The `t₀ = 1` case is excluded, as it must be: the endpoint of a minimizing geodesic *may* be
conjugate (the antipode of a round sphere).

Blueprint: `prop:minimal-geodesic-no-conjugate`. -/
theorem not_isConjugatePointAt_of_minimizing [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b t₀ : ℝ}
    (ha : a < 0) (hb : 1 < b) (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1)) :
    ¬ IsConjugatePointAt (I := I) g γ t₀ := by
  intro hconj
  obtain ⟨e, W₀, W₁, hPar, horth, hW₀, hW₁, hW₀0, hW₁1, hmatch, hneg⟩ :=
    exists_indexForm_neg_smooth_of_isConjugatePointAt (I := I) ha hb ht₀ ht₁ hgeo hγc hconj
  have hnn := indexForm_nonneg_of_minimizing (I := I) g hg ha hb ht₀ ht₁ hgeo hγc hPar horth
    hmin hW₀ hW₁ hW₀0 hW₁1 hmatch
  linarith

end MorganTianLib

end

#print axioms MorganTianLib.deriv_slice_snd_vec
#print axioms MorganTianLib.frameFieldOf_eq_zero
#print axioms MorganTianLib.two_mul_pieceEnergy_eq_chartMetricInner
#print axioms MorganTianLib.indexForm_nonneg_of_minimizing
#print axioms MorganTianLib.not_isConjugatePointAt_of_minimizing
