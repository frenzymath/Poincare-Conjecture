import PetersenLib.Ch05.PuncturedPlane
import PetersenLib.Ch05.GeodesicCompleteness

/-!
# Petersen Ch. 5, §5.2 — Example 5.2.7: maximal geodesic intervals jump in the punctured plane

Petersen's Example 5.2.7: in `ℝ² − {(0,0)}` with the induced flat metric, the
unit-speed geodesic from `p = (-1, 0)` with tangent `(1, 0)` runs straight into
the deleted origin and is therefore defined only on `(-∞, 1)`; but *every* nearby
geodesic from `p` with tangent `(1 + ε₁, ε₂)`, `ε₂ ≠ 0`, misses the origin and is
defined on all of `ℝ`.  So maximal intervals of existence can **jump up** in size
under an arbitrarily small perturbation of the initial velocity (they cannot jump
*down*, by the uniform neighbourhood lemma `lem:pet-ch5-uniform-neighborhood`).

The chart-free `geodesicMaximalDomain` of `Ch05/GeodesicCompleteness.lean` — the
union of all open order-connected time sets carrying a continuous geodesic with
the prescribed initial datum — is used throughout; the *chart artifacts*
`expDomain` / `injectivityRadius` would not express Petersen's claim.

Contents:

* `lineOpens`, `coe_lineOpens` — the straight curve `t ↦ p + t • v` regarded as a
  curve into an open set `s ⊆ F` (junk value where the line leaves `s`);
* `chartChristoffelContraction_opensFlatMetric` — the Christoffel contraction of
  the flat metric on an open set vanishes (from `chartChristoffel_opensFlatMetric`);
* `isGeodesicOn_lineOpens`, `isGeodesicWithInitialOn_lineOpens`,
  `subset_geodesicMaximalDomain_lineOpens` — **straight lines are geodesics of
  `opensFlatMetric`**, on every open time set where they stay inside `s`.  This is
  the "separate work" that `Ch05/OpenSubmanifoldFlat.lean` left open;
* `geodesicMaximalDomain_pLeft_horizontal` — the domain of the `(1, 0)` geodesic
  from `(-1, 0)` is **exactly** `(-∞, 1)`;
* `geodesicMaximalDomain_pLeft_tilted` — the domain of the `(1 + ε₁, ε₂)`
  geodesic, `ε₂ ≠ 0`, is **all of `ℝ`**;
* `example_punctured_plane_geodesic_interval` — **Example 5.2.7**.

The `⊆` half of `geodesicMaximalDomain_pLeft_horizontal` is the only real work:
an admissible geodesic reaching time `1` would, by global uniqueness
(`geodesicWithInitialOn_eqOn`), agree with the straight line on `(-∞, 1)`, hence
by continuity take the value `(0, 0)` at time `1` — not a point of `ℝ² − {0}`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §5.2, Example 5.2.7.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Bornology TopologicalSpace Set
open scoped ContDiff Manifold Topology

namespace PetersenLib

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)]

open Classical in
/-- The straight curve `t ↦ p + t • v` regarded as a curve into an open set. -/
def lineOpens (s : Opens F) (base : s) (p v : F) : ℝ → s := fun t =>
  if h : p + t • v ∈ s then ⟨p + t • v, h⟩ else base

theorem coe_lineOpens (s : Opens F) (base : s) (p v : F) {t : ℝ}
    (h : p + t • v ∈ s) : (lineOpens s base p v t : F) = p + t • v := by
  rw [lineOpens, dif_pos h]

theorem chartChristoffelContraction_opensFlatMetric (s : Opens F) (a : s) (v w y : F) :
    Geodesic.chartChristoffelContraction (I := 𝓘(ℝ, F)) (opensFlatMetric F s) a v w y = 0 := by
  simp only [Geodesic.chartChristoffelContraction, chartChristoffel_opensFlatMetric,
    zero_mul, Finset.sum_const_zero, zero_smul]

theorem isGeodesicOn_lineOpens (s : Opens F) (base : s) (p v : F) {J : Set ℝ}
    (hJ : IsOpen J) (hmem : ∀ t ∈ J, p + t • v ∈ s) :
    Geodesic.IsGeodesicOn (I := 𝓘(ℝ, F)) (opensFlatMetric F s) (lineOpens s base p v) J := by
  set γ : ℝ → s := lineOpens s base p v with hγdef
  have hline : ∀ t : ℝ, HasDerivAt (fun r : ℝ => p + r • v) v t := by
    intro t
    simpa using (((hasDerivAt_id t).smul_const v).const_add p)
  intro t ht
  have hcl : Geodesic.chartLocalCurve (I := 𝓘(ℝ, F)) γ t = fun r => (γ r : F) := by
    funext r; exact extChartAt_opens_apply s (γ t) (γ r)
  have hev : Geodesic.chartLocalCurve (I := 𝓘(ℝ, F)) γ t =ᶠ[𝓝 t] fun r : ℝ => p + r • v := by
    rw [hcl]
    filter_upwards [hJ.mem_nhds ht] with r hr
    exact coe_lineOpens s base p v (hmem r hr)
  have hderiv : deriv (Geodesic.chartLocalCurve (I := 𝓘(ℝ, F)) γ t) =ᶠ[𝓝 t] fun _ : ℝ => v := by
    filter_upwards [hev.eventually_nhds] with r hr
    have hr' : Geodesic.chartLocalCurve (I := 𝓘(ℝ, F)) γ t =ᶠ[𝓝 r] fun r : ℝ => p + r • v := hr
    rw [hr'.deriv_eq, (hline r).deriv]
  refine ⟨v, 0, (hline t).congr_of_eventuallyEq hev, ?_, ?_, ?_⟩
  · filter_upwards [hev.eventually_nhds, hderiv] with r h1 h2
    rw [h2]
    exact (hline r).congr_of_eventuallyEq h1
  · exact (hasDerivAt_const t v).congr_of_eventuallyEq hderiv
  · rw [chartChristoffelContraction_opensFlatMetric]
    simp

theorem lineOpens_zero (s : Opens F) (base : s) (p v : F) (q : s) (hq : (q : F) = p)
    (hp : p ∈ s) : lineOpens s base p v 0 = q := by
  apply Subtype.ext
  rw [coe_lineOpens s base p v (by simpa using hp), hq]
  simp

theorem isGeodesicWithInitialOn_lineOpens (s : Opens F) (base : s) (p v : F) {J : Set ℝ}
    (hJ : IsOpen J) (h0 : (0 : ℝ) ∈ J) (hmem : ∀ t ∈ J, p + t • v ∈ s)
    (q : s) (hq : (q : F) = p) :
    IsGeodesicWithInitialOn (I := 𝓘(ℝ, F)) (opensFlatMetric F s)
      (lineOpens s base p v) J 0 q v := by
  set γ : ℝ → s := lineOpens s base p v with hγdef
  have hline : ∀ t : ℝ, HasDerivAt (fun r : ℝ => p + r • v) v t := by
    intro t
    simpa using (((hasDerivAt_id t).smul_const v).const_add p)
  have hcoe : ∀ r ∈ J, (γ r : F) = p + r • v := fun r hr =>
    coe_lineOpens s base p v (hmem r hr)
  have hp : p ∈ s := by simpa using hmem 0 h0
  have hval : γ 0 = q := lineOpens_zero s base p v q hq hp
  refine ⟨?_, hval, ?_, isGeodesicOn_lineOpens s base p v hJ hmem⟩
  · -- continuity on `J`
    have hcont : ContinuousOn (fun r => (γ r : F)) J := by
      apply ContinuousOn.congr (f := fun r : ℝ => p + r • v) _ hcoe
      exact (Continuous.continuousOn (by fun_prop))
    exact Topology.IsInducing.subtypeVal.continuousOn_iff.mpr hcont
  · -- initial velocity
    have hfun : (fun r => extChartAt 𝓘(ℝ, F) q (γ r)) =ᶠ[𝓝 (0 : ℝ)] fun r : ℝ => p + r • v := by
      filter_upwards [hJ.mem_nhds h0] with r hr
      rw [extChartAt_opens_apply s q (γ r)]
      exact hcoe r hr
    exact (hline 0).congr_of_eventuallyEq hfun

/-- **Math.** Any admissible straight-line interval sits inside the maximal domain. -/
theorem subset_geodesicMaximalDomain_lineOpens (s : Opens F) (base : s) (p v : F) {J : Set ℝ}
    (hJ : IsOpen J) (hJc : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    (hmem : ∀ t ∈ J, p + t • v ∈ s) (q : s) (hq : (q : F) = p) :
    J ⊆ geodesicMaximalDomain (I := 𝓘(ℝ, F)) (opensFlatMetric F s) q v := fun _ ht =>
  ⟨J, ⟨hJ, hJc, h0, _, isGeodesicWithInitialOn_lineOpens s base p v hJ h0 hmem q hq⟩, ht⟩

/-! ## The punctured plane -/

/-- The line `t ↦ (-1, 0) + t · (a, b)` in coordinates. -/
theorem pLeft_add_smul_vec (a b t : ℝ) :
    (pLeft : E2) + t • vec a b = vec (-1 + t * a) (t * b) := by
  rw [coe_pLeft, vec_smul, vec_add]
  norm_num

/-- **Math.** The straight ray from `(-1, 0)` with tangent `(1 + ε₁, ε₂)`,
`ε₂ ≠ 0`, **never meets the origin**: at time `t` its second coordinate is
`t ε₂`, which vanishes only at `t = 0`, where the first coordinate is `-1`. -/
theorem tilted_ray_ne_zero {ε₁ ε₂ : ℝ} (hε : ε₂ ≠ 0) (t : ℝ) :
    (pLeft : E2) + t • vec (1 + ε₁) ε₂ ∈ puncturedPlane := by
  rw [mem_puncturedPlane, pLeft_add_smul_vec]
  refine vec_ne_zero (sq_add_sq_ne_zero ?_)
  rcases eq_or_ne t 0 with rfl | ht
  · exact Or.inl (by norm_num)
  · exact Or.inr (mul_ne_zero ht hε)

/-- **Math.** The straight ray from `(-1, 0)` with tangent `(1, 0)` misses the
origin exactly for `t < 1`: at time `t` it sits at `(t - 1, 0)`. -/
theorem horizontal_ray_ne_zero {t : ℝ} (ht : t < 1) :
    (pLeft : E2) + t • vec 1 0 ∈ puncturedPlane := by
  rw [mem_puncturedPlane, pLeft_add_smul_vec]
  exact vec_ne_zero (sq_add_sq_ne_zero (Or.inl (by intro h; simp at h; linarith)))

/-- **Math.** **Example 5.2.7, jumped-up half.** For `ε₂ ≠ 0` the geodesic of the
punctured plane from `(-1, 0)` with tangent `(1 + ε₁, ε₂)` is defined on **all of
`ℝ`**: the straight line it follows misses the deleted origin at every time
(`tilted_ray_ne_zero`), and a straight line is a geodesic of the flat metric
because all Christoffel symbols of `opensFlatMetric` vanish. -/
theorem geodesicMaximalDomain_pLeft_tilted (ε₁ ε₂ : ℝ) (hε : ε₂ ≠ 0) :
    geodesicMaximalDomain (I := 𝓘(ℝ, E2)) puncturedPlaneMetric pLeft (vec (1 + ε₁) ε₂)
      = univ :=
  eq_univ_of_univ_subset <|
    subset_geodesicMaximalDomain_lineOpens puncturedPlane pLeft (pLeft : E2)
      (vec (1 + ε₁) ε₂) isOpen_univ ordConnected_univ (mem_univ 0)
      (fun t _ => tilted_ray_ne_zero hε t) pLeft rfl

/-- **Math.** **Example 5.2.7, truncated half.** The geodesic of the punctured
plane from `(-1, 0)` with tangent `(1, 0)` is defined on **exactly `(-∞, 1)`**.

`⊇` is `horizontal_ray_ne_zero` plus `isGeodesicOn_lineOpens`.  For `⊆`: if the
maximal domain reached time `1`, an admissible geodesic `γ` on an open
order-connected `J ∋ 0, 1` would, by uniqueness (`geodesicWithInitialOn_eqOn`),
agree on `(-∞, 1) ∩ J` with the straight line `t ↦ (t - 1, 0)`.  That line tends
to the *origin* as `t ↑ 1`, while `γ` is continuous at `1` with value in the
punctured plane — so `γ(1) = (0, 0)`, which is not a point of `ℝ² − {0}`. -/
theorem geodesicMaximalDomain_pLeft_horizontal :
    geodesicMaximalDomain (I := 𝓘(ℝ, E2)) puncturedPlaneMetric pLeft (vec 1 0) = Iio 1 := by
  set L : ℝ → puncturedPlane := lineOpens puncturedPlane pLeft (pLeft : E2) (vec 1 0) with hL
  have hLgeo : IsGeodesicWithInitialOn (I := 𝓘(ℝ, E2)) puncturedPlaneMetric L (Iio 1) 0 pLeft
      (vec 1 0) :=
    isGeodesicWithInitialOn_lineOpens puncturedPlane pLeft (pLeft : E2) (vec 1 0) isOpen_Iio
      (by norm_num) (fun t ht => horizontal_ray_ne_zero ht) pLeft rfl
  refine le_antisymm ?_ ?_
  · -- `⊆`: time `1` is unreachable
    intro t ht
    by_contra hcon
    have hcon' : (1 : ℝ) ≤ t := not_lt.mp hcon
    have h1 : (1 : ℝ) ∈ geodesicMaximalDomain (I := 𝓘(ℝ, E2)) puncturedPlaneMetric pLeft
        (vec 1 0) :=
      (ordConnected_geodesicMaximalDomain _ _ _).out
        (zero_mem_geodesicMaximalDomain _ _ _) ht ⟨by norm_num, hcon'⟩
    obtain ⟨γ, J, hJo, hJc, h0J, h1J, hγ⟩ := exists_geodesicWitness_of_mem_maximalDomain _ h1
    have heqon : Set.EqOn L γ (Iio 1 ∩ J) :=
      geodesicWithInitialOn_eqOn (I := 𝓘(ℝ, E2)) puncturedPlaneMetric isOpen_Iio
        ordConnected_Iio hJo hJc hLgeo hγ (by norm_num) h0J
    -- `γ` is continuous at `1`
    have hlim1 : Filter.Tendsto (fun r => (γ r : E2)) (𝓝[<] (1 : ℝ)) (𝓝 ((γ 1 : E2))) := by
      have hca : ContinuousAt γ 1 := hγ.1.continuousAt (hJo.mem_nhds h1J)
      exact (continuous_subtype_val.continuousAt.comp hca).tendsto.mono_left nhdsWithin_le_nhds
    -- but along `(-∞, 1)` it is the straight line, which tends to the origin
    have hmemf : Iio 1 ∩ J ∈ 𝓝[<] (1 : ℝ) :=
      Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (hJo.mem_nhds h1J))
    have hlim2 : Filter.Tendsto (fun r => (γ r : E2)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : E2)) := by
      have hcont : Filter.Tendsto (fun r : ℝ => (pLeft : E2) + r • vec 1 0) (𝓝[<] (1 : ℝ))
          (𝓝 ((pLeft : E2) + (1 : ℝ) • vec 1 0)) :=
        ((by fun_prop : Continuous fun r : ℝ => (pLeft : E2) + r • vec 1 0)).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      have hz : (pLeft : E2) + (1 : ℝ) • vec 1 0 = 0 := by
        rw [pLeft_add_smul_vec]; norm_num
      rw [hz] at hcont
      refine hcont.congr' ?_
      filter_upwards [hmemf] with r hr
      rw [← heqon hr, hL, coe_lineOpens puncturedPlane pLeft (pLeft : E2) (vec 1 0)
        (horizontal_ray_ne_zero hr.1)]
    have : (γ 1 : E2) = 0 := tendsto_nhds_unique hlim1 hlim2
    exact (γ 1).2 this
  · exact subset_geodesicMaximalDomain_lineOpens puncturedPlane pLeft (pLeft : E2) (vec 1 0)
      isOpen_Iio ordConnected_Iio (by norm_num)
      (fun _ ht => horizontal_ray_ne_zero ht) pLeft rfl

/-- **Math.** **Example 5.2.7** (Petersen §5.2, `ex:pet-ch5-punctured-plane-geodesic`).
In the punctured plane `ℝ² − {(0,0)}` with the induced flat metric, the
unit-speed geodesic from `(-1, 0)` with tangent `(1, 0)` is defined only on
`(-∞, 1)` — it runs into the deleted origin — whereas every nearby geodesic from
`(-1, 0)` with tangent `(1 + ε₁, ε₂)`, `ε₂ ≠ 0`, is defined on all of `ℝ`.  So
maximal intervals of existence can **jump up** in size under arbitrarily small
perturbations of the initial velocity (they cannot jump *down*, by the uniform
neighbourhood lemma). -/
theorem example_punctured_plane_geodesic_interval :
    geodesicMaximalDomain (I := 𝓘(ℝ, E2)) puncturedPlaneMetric pLeft (vec 1 0) = Iio 1 ∧
      ∀ ε₁ ε₂ : ℝ, ε₂ ≠ 0 →
        geodesicMaximalDomain (I := 𝓘(ℝ, E2)) puncturedPlaneMetric pLeft (vec (1 + ε₁) ε₂)
          = univ :=
  ⟨geodesicMaximalDomain_pLeft_horizontal, fun ε₁ ε₂ hε =>
    geodesicMaximalDomain_pLeft_tilted ε₁ ε₂ hε⟩

end PetersenLib
