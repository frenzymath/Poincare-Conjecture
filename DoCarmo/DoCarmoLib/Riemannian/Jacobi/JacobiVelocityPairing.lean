import DoCarmoLib.Riemannian.Jacobi.JacobiNonpositiveManifold
import DoCarmoLib.Riemannian.Geodesic.EquationTransfer

/-!
# do Carmo Ch. 5, §3, Proposition 3.6 and Corollaries 3.7, 3.8 — the pairing `⟨J, γ'⟩`

For a Jacobi field `J` along a geodesic `γ`, the tangential component `⟨J(t), γ'(t)⟩`
is an **affine** function of `t`:

  `⟨J(t), γ'(t)⟩ = ⟨J'(0), γ'(0)⟩·t + ⟨J(0), γ'(0)⟩`   (do Carmo Prop. 3.6).

We formalize the coordinate form: read in a chart `α` whose source contains the piece of
`γ`, with `u = φ_α ∘ γ` the chart curve and `u̇ = deriv u` the chart velocity (the chart
reading of `γ'`), the chart Gram pairing `P(t) = ⟨J^α(t), u̇(t)⟩_G` satisfies the affine law.
The chart Gram pairing equals the intrinsic `⟨J, γ'⟩_g` (`chartMetricInner_tangentCoordChange`),
so this is do Carmo's statement read in the chart.

## The two analytic inputs

* `covariantDerivCoord_extChartAt_velocity_eq_zero` — the geodesic velocity is **parallel** in
  any fixed chart: `∇_{u̇} u̇ = covariantDerivCoord g α u u̇ = 0`. This is do Carmo's `Dγ'/dt = 0`
  read in a *non-centered* chart, obtained from the fixed-chart geodesic ODE
  `HasGeodesicEquationAt.solvesGeodesicODEAt` (the Christoffel transformation law).
* `chartMetricInner_chartCurvature_velocity_eq_zero` — the curvature antisymmetry
  `⟨R(J, u̇)u̇, u̇⟩_G = 0`, from the pointwise algebraic-curvature antisymmetry in the last pair
  (`IsAlgCurvatureForm.antisymm₃₄`) via the frame realization `curvatureFormAt_chartFrame`.

Then the metric-compatibility product rule `hasDerivAt_chartMetricInner_along` with the Jacobi
pair system `∇J = DJ`, `∇DJ = -R(J, u̇)u̇` gives `P' = ⟨DJ, u̇⟩ =: Pd` and `Pd' = 0`, so `Pd` is
constant and `P` is affine.

Blueprint: `prop:dc-ch5-3-6`, `cor:dc-ch5-3-7`, `cor:dc-ch5-3-8`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 5, Proposition 3.6 and Corollaries 3.7, 3.8.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### The geodesic velocity is parallel in a fixed chart -/

/-- **Math.** **The geodesic velocity is parallel in any fixed chart.** For a geodesic `γ`
whose foot `γ t` lies in the source of the chart at `α`, the chart velocity `u̇ = deriv u`
(`u = φ_α ∘ γ`) has vanishing coordinate covariant derivative
`∇_{u̇} u̇ = covariantDerivCoord g α u u̇ = 0`.

This is do Carmo's `Dγ'/dt = 0` read in a *non-centered* chart. The moving-foot geodesic
equation `HasGeodesicEquationAt` gives the second-order geodesic ODE
`u̇' + Γ_α(u̇, u̇)(u) = 0` in the fixed chart `α` via the Christoffel transformation law
(`HasGeodesicEquationAt.solvesGeodesicODEAt`), and `covariantDerivCoord` is exactly that
operator. -/
theorem covariantDerivCoord_extChartAt_velocity_eq_zero
    (g : RiemannianMetric I M) (α : M) {γ : ℝ → M} {t : ℝ}
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ t) (hcont : ContinuousAt γ t)
    (hsrc : γ t ∈ (chartAt H α).source) :
    covariantDerivCoord (I := I) g α (Geodesic.chartReading (I := I) α γ)
        (deriv (Geodesic.chartReading (I := I) α γ)) t = 0 := by
  obtain ⟨_hev, a, ha, heq⟩ := hgeo.solvesGeodesicODEAt hcont hsrc
  rw [covariantDerivCoord_def, ha.deriv]
  exact heq

/-! ### The curvature antisymmetry `⟨R(J, u̇)u̇, u̇⟩ = 0` -/

/-- **Math.** **Curvature antisymmetry paired with the velocity.** For any chart vectors
`w, v`, the chart curvature contraction paired with `v` vanishes:
`⟨R_chart(w, v)v, v⟩_G = 0`. This is do Carmo's `⟨R(γ', J)γ', γ'⟩ = 0` (antisymmetry of the
curvature `(0,4)`-form in its last pair): the frame realization `curvatureFormAt_chartFrame`
turns the chart pairing into the pointwise `(0,4)` form, which is an algebraic curvature form,
hence antisymmetric in the last two slots (`IsAlgCurvatureForm.antisymm₃₄`); with both slots
equal to `v` it is `0`. -/
theorem chartMetricInner_chartCurvature_velocity_eq_zero
    (g : RiemannianMetric I M) {α p : M} (hp : p ∈ (chartAt H α).source) (w v : E) :
    chartMetricInner (I := I) g α (extChartAt I α p)
        (chartCurvature (I := I) g α (extChartAt I α p) w v v) v = 0 := by
  classical
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  obtain ⟨_hsym, hcompat⟩ := hLC
  -- the frame realization: `curvatureFormAt p (Fw)(Fv)(Fv)(Fv) = -⟨R_chart(w,v)v, v⟩_G`
  have hbridge := curvatureFormAt_chartFrame (I := I) g hp w v v v
  -- `⟨R(Fw, Fv)Fv, Fv⟩ = 0`: the curvature `(0,4)` form vanishes with its last pair equal
  have hzero : g.leviCivitaConnection.curvatureFormAt g p
      (∑ a, Geodesic.chartCoord (E := E) a w • chartBasisVecFiber (I := I) α a p)
      (∑ b, Geodesic.chartCoord (E := E) b v • chartBasisVecFiber (I := I) α b p)
      (∑ c, Geodesic.chartCoord (E := E) c v • chartBasisVecFiber (I := I) α c p)
      (∑ d, Geodesic.chartCoord (E := E) d v • chartBasisVecFiber (I := I) α d p) = 0 := by
    rw [g.leviCivitaConnection.curvatureFormAt_eq g p
      (AffineConnection.extendField_apply p _) (AffineConnection.extendField_apply p _)
      (AffineConnection.extendField_apply p _) (AffineConnection.extendField_apply p _)]
    exact g.leviCivitaConnection.curvature_inner_self g hcompat _ _ _ p
  rw [hzero] at hbridge
  linarith [hbridge]

/-! ### Proposition 3.6 — the pairing `⟨J, γ'⟩` is affine (coordinate form) -/

/-- **Math.** **do Carmo Ch. 5, Proposition 3.6 (coordinate form).** Let `J` (with covariant
derivative `DJ`) be a Jacobi field along a geodesic `γ`, read in a chart `α` whose source
contains `γ([a, b])`, with chart curve `u = φ_α ∘ γ` and chart velocity `u̇ = deriv u` (the chart
reading of `γ'`). Then the chart Gram pairing `⟨J, u̇⟩_G` is an **affine** function of `t`:

  `⟨J(t), u̇(t)⟩ = ⟨DJ(a), u̇(a)⟩·(t - a) + ⟨J(a), u̇(a)⟩`.

Since the chart Gram pairing equals the intrinsic `⟨·, ·⟩_g` and `u̇` is the chart reading of
`γ'`, this is do Carmo's `⟨J(t), γ'(t)⟩ = ⟨J'(0), γ'(0)⟩·t + ⟨J(0), γ'(0)⟩`.

The proof follows do Carmo: `P(t) = ⟨J, u̇⟩` has `P' = ⟨DJ, u̇⟩ =: Pd` (metric compatibility,
`∇J = DJ`, and the velocity is parallel `∇u̇ = 0`), and `Pd' = -⟨R(J, u̇)u̇, u̇⟩ = 0` (curvature
antisymmetry), so `Pd` is constant and `P` is affine. -/
theorem chartMetricInner_jacobi_velocity_affine
    (g : RiemannianMetric I M) (α : M) {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H α).source)
    (hJF : IsJacobiFieldOn (I := I) g α (Geodesic.chartReading (I := I) α γ) J DJ a b) :
    ∀ t ∈ Icc a b,
      chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ t) (J t)
          (deriv (Geodesic.chartReading (I := I) α γ) t)
        = chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ a) (DJ a)
            (deriv (Geodesic.chartReading (I := I) α γ) a) * (t - a)
          + chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ a) (J a)
            (deriv (Geodesic.chartReading (I := I) α γ) a) := by
  classical
  set u : ℝ → E := Geodesic.chartReading (I := I) α γ with hu_def
  set P : ℝ → ℝ := fun t => chartMetricInner (I := I) g α (u t) (J t) (deriv u t) with hP_def
  set Pd : ℝ → ℝ := fun t => chartMetricInner (I := I) g α (u t) (DJ t) (deriv u t) with hPd_def
  -- chart-independent regularity inputs at an interior time
  have hcore : ∀ t ∈ Ioo a b, HasDerivAt Pd 0 t ∧ HasDerivAt P (Pd t) t := by
    intro t ht
    have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have hsrct : γ t ∈ (chartAt H α).source := hsrc t htIcc
    have hnhdsW : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    -- differentiability of the chart curve, its velocity, and the Jacobi pair
    have hu_diff : DifferentiableAt ℝ u t :=
      hgeo.differentiableAt_extChartAt htIcc (hγc t htIcc) hsrct
    obtain ⟨_hev, aa, hderiv2, _heq⟩ :=
      (hgeo.hasGeodesicEquationAt htIcc).solvesGeodesicODEAt (hγc t htIcc) hsrct
    have hudot_diff : DifferentiableAt ℝ (deriv u) t := hderiv2.differentiableAt
    have hJd : DifferentiableAt ℝ J t :=
      ((hJF.hasDerivWithinAt_fst t htIcc).hasDerivAt hnhdsW).differentiableAt
    have hDJd : DifferentiableAt ℝ DJ t :=
      ((hJF.hasDerivWithinAt_snd t htIcc).hasDerivAt hnhdsW).differentiableAt
    have hymem : u t ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrct)
    have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t) := fun i j =>
      differentiableAt_chartGramOnE (I := I) g α hymem i j
    have hbase : (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      symm_extChartAt_mem_baseSet (I := I) hsrct
    -- covariant identities: `∇J = DJ`, `∇DJ = -R(J, u̇)u̇`, `∇u̇ = 0`
    have hfst : covariantDerivCoord (I := I) g α u J t = DJ t := hJF.covariantDerivCoord_fst ht
    have hsnd : covariantDerivCoord (I := I) g α u DJ t
        = -(chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t)) :=
      hJF.covariantDerivCoord_snd ht
    have hvel : covariantDerivCoord (I := I) g α u (deriv u) t = 0 :=
      covariantDerivCoord_extChartAt_velocity_eq_zero (I := I) g α
        (hgeo.hasGeodesicEquationAt htIcc) (hγc t htIcc) hsrct
    refine ⟨?_, ?_⟩
    · -- `Pd' = ⟨∇DJ, u̇⟩ + ⟨DJ, ∇u̇⟩ = -⟨R(J, u̇)u̇, u̇⟩ + 0 = 0`
      have hraw := hasDerivAt_chartMetricInner_along (I := I) g α u DJ (deriv u)
        hu_diff hDJd hudot_diff hG hbase
      rw [hsnd, hvel] at hraw
      have hut : u t = extChartAt I α (γ t) := by rw [hu_def, Geodesic.chartReading_def]
      have hcurv : chartMetricInner (I := I) g α (u t)
          (-(chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t))) (deriv u t) = 0 := by
        rw [chartMetricInner_neg_left, neg_eq_zero, hut]
        exact chartMetricInner_chartCurvature_velocity_eq_zero (I := I) g hsrct (J t) (deriv u t)
      rw [hcurv, chartMetricInner_zero_right, add_zero] at hraw
      exact hraw
    · -- `P' = ⟨∇J, u̇⟩ + ⟨J, ∇u̇⟩ = ⟨DJ, u̇⟩ + 0 = Pd t`
      have hraw := hasDerivAt_chartMetricInner_along (I := I) g α u J (deriv u)
        hu_diff hJd hudot_diff hG hbase
      rw [hfst, hvel, chartMetricInner_zero_right, add_zero] at hraw
      exact hraw
  -- continuity of `P`, `Pd` on `[a, b]`
  have hu_cont : ContinuousOn u (Icc a b) := fun t ht =>
    (hgeo.differentiableAt_extChartAt ht (hγc t ht) (hsrc t ht)).continuousAt.continuousWithinAt
  have hudot_cont : ContinuousOn (deriv u) (Icc a b) := fun t ht => by
    obtain ⟨_hev, aa, hderiv2, _heq⟩ :=
      (hgeo.hasGeodesicEquationAt ht).solvesGeodesicODEAt (hγc t ht) (hsrc t ht)
    exact hderiv2.continuousAt.continuousWithinAt
  have hmem : ∀ τ ∈ Icc a b, u τ ∈ (extChartAt I α).target := fun τ hτ =>
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc τ hτ)
  have hJcont : ContinuousOn J (Icc a b) := hJF.continuousOn_fst
  have hDJcont : ContinuousOn DJ (Icc a b) := hJF.continuousOn_snd
  have hP_cont : ContinuousOn P (Icc a b) :=
    continuousOn_chartMetricInner_pairing (I := I) g α hu_cont hmem hJcont hudot_cont
  have hPd_cont : ContinuousOn Pd (Icc a b) :=
    continuousOn_chartMetricInner_pairing (I := I) g α hu_cont hmem hDJcont hudot_cont
  -- `Pd` is constant on `[a, b]` (derivative zero, both monotone and antitone)
  have hPd_diff : DifferentiableOn ℝ Pd (interior (Icc a b)) := by
    rw [interior_Icc]; intro t ht; exact (hcore t ht).1.differentiableAt.differentiableWithinAt
  have hPd_deriv0 : ∀ t ∈ interior (Icc (a : ℝ) b), deriv Pd t = 0 := by
    rw [interior_Icc]; intro t ht; exact (hcore t ht).1.deriv
  have hPd_const : ∀ t ∈ Icc a b, Pd t = Pd a := by
    have hmono : MonotoneOn Pd (Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc a b) hPd_cont
      hPd_diff (fun t ht => by rw [hPd_deriv0 t ht])
    have hanti : AntitoneOn Pd (Icc a b) := antitoneOn_of_deriv_nonpos (convex_Icc a b) hPd_cont
      hPd_diff (fun t ht => by rw [hPd_deriv0 t ht])
    intro t ht
    exact le_antisymm (hanti ⟨le_rfl, hab.le⟩ ht ht.1) (hmono ⟨le_rfl, hab.le⟩ ht ht.1)
  -- `Q(t) = P(t) - Pd(a)·(t - a) - P(a)` has derivative zero, is continuous, and vanishes at `a`
  set Q : ℝ → ℝ := fun t => P t - Pd a * (t - a) - P a with hQ_def
  have hQ_cont : ContinuousOn Q (Icc a b) :=
    ((hP_cont.sub ((continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))).sub
      continuousOn_const)
  have hQ_deriv0 : ∀ t ∈ interior (Icc (a : ℝ) b), deriv Q t = 0 := by
    rw [interior_Icc]; intro t ht
    have hPderiv : HasDerivAt P (Pd a) t := by
      have := (hcore t ht).2; rwa [hPd_const t (Ioo_subset_Icc_self ht)] at this
    have hlin : HasDerivAt (fun t => Pd a * (t - a) + P a) (Pd a) t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul (Pd a) |>.add_const (P a)
    have : HasDerivAt Q 0 t := by
      have hQeq : Q = fun t => P t - (Pd a * (t - a) + P a) := by funext s; rw [hQ_def]; ring
      rw [hQeq]; simpa using hPderiv.sub hlin
    exact this.deriv
  have hQ_diff : DifferentiableOn ℝ Q (interior (Icc a b)) := by
    rw [interior_Icc]; intro t ht
    have hPderiv : HasDerivAt P (Pd a) t := by
      have := (hcore t ⟨ht.1, ht.2⟩).2; rwa [hPd_const t (Ioo_subset_Icc_self ⟨ht.1, ht.2⟩)] at this
    have hlin : HasDerivAt (fun t => Pd a * (t - a) + P a) (Pd a) t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul (Pd a) |>.add_const (P a)
    have hQeq : Q = fun t => P t - (Pd a * (t - a) + P a) := by funext s; rw [hQ_def]; ring
    rw [hQeq]; exact (hPderiv.sub hlin).differentiableAt.differentiableWithinAt
  have hQ_const : ∀ t ∈ Icc a b, Q t = Q a := by
    have hmono : MonotoneOn Q (Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc a b) hQ_cont
      hQ_diff (fun t ht => by rw [hQ_deriv0 t ht])
    have hanti : AntitoneOn Q (Icc a b) := antitoneOn_of_deriv_nonpos (convex_Icc a b) hQ_cont
      hQ_diff (fun t ht => by rw [hQ_deriv0 t ht])
    intro t ht
    exact le_antisymm (hanti ⟨le_rfl, hab.le⟩ ht ht.1) (hmono ⟨le_rfl, hab.le⟩ ht ht.1)
  -- unwind: `Q(a) = 0`, so `P(t) = Pd(a)·(t - a) + P(a)`
  intro t ht
  have hQa : Q a = 0 := by rw [hQ_def]; ring
  have := hQ_const t ht
  rw [hQa, hQ_def] at this
  have hPt : P t = Pd a * (t - a) + P a := by linarith [this]
  exact hPt

/-! ### Corollaries 3.7 and 3.8 -/

/-- **Math.** **do Carmo Ch. 5, Corollary 3.7 (coordinate form).** If the pairing `⟨J, γ'⟩`
takes the same value at two distinct times `t₁ ≠ t₂`, then it is constant. In particular, if
`J(a) = J(b) = 0` the pairing vanishes identically. -/
theorem chartMetricInner_jacobi_velocity_const_of_eq
    (g : RiemannianMetric I M) (α : M) {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H α).source)
    (hJF : IsJacobiFieldOn (I := I) g α (Geodesic.chartReading (I := I) α γ) J DJ a b)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) (hne : t₁ ≠ t₂)
    (heq : chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ t₁) (J t₁)
          (deriv (Geodesic.chartReading (I := I) α γ) t₁)
        = chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ t₂) (J t₂)
          (deriv (Geodesic.chartReading (I := I) α γ) t₂)) :
    ∀ t ∈ Icc a b,
      chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ t) (J t)
          (deriv (Geodesic.chartReading (I := I) α γ) t)
        = chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ a) (J a)
          (deriv (Geodesic.chartReading (I := I) α γ) a) := by
  have haff := chartMetricInner_jacobi_velocity_affine (I := I) g α hab hgeo hγc hsrc hJF
  set A : ℝ := chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ a) (DJ a)
    (deriv (Geodesic.chartReading (I := I) α γ) a) with hA_def
  rw [haff t₁ ht₁, haff t₂ ht₂] at heq
  have hA0 : A = 0 := by
    have hkey : A * (t₁ - t₂) = 0 := by linear_combination heq
    rcases mul_eq_zero.1 hkey with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  intro t ht
  rw [haff t ht, hA0]; ring

/-- **Math.** **do Carmo Ch. 5, Corollary 3.8 (coordinate form).** Suppose `J(a) = 0`. Then the
tangential initial velocity vanishes, `⟨J'(a), γ'(a)⟩ = 0`, if and only if the pairing
`⟨J, γ'⟩` vanishes identically on `[a, b]`. (do Carmo's further ``the space of such `J` has
dimension `n - 1`'' is the separate linear-algebra count of `rem:dc-ch5-3-2`.) -/
theorem chartMetricInner_jacobi_velocity_eq_zero_iff
    (g : RiemannianMetric I M) (α : M) {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H α).source)
    (hJF : IsJacobiFieldOn (I := I) g α (Geodesic.chartReading (I := I) α γ) J DJ a b)
    (hJ0 : J a = 0) :
    chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ a) (DJ a)
        (deriv (Geodesic.chartReading (I := I) α γ) a) = 0
      ↔ ∀ t ∈ Icc a b,
          chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ t) (J t)
            (deriv (Geodesic.chartReading (I := I) α γ) t) = 0 := by
  have haff := chartMetricInner_jacobi_velocity_affine (I := I) g α hab hgeo hγc hsrc hJF
  have hB : chartMetricInner (I := I) g α (Geodesic.chartReading (I := I) α γ a) (J a)
      (deriv (Geodesic.chartReading (I := I) α γ) a) = 0 := by
    rw [hJ0]; simp [chartMetricInner_def]
  constructor
  · intro hA t ht; rw [haff t ht, hA, hB]; ring
  · intro h
    have hb := h b ⟨hab.le, le_rfl⟩
    rw [haff b ⟨hab.le, le_rfl⟩, hB, add_zero] at hb
    rcases mul_eq_zero.1 hb with hA | hba
    · exact hA
    · exact absurd (sub_eq_zero.1 hba).symm (ne_of_lt hab)

end Riemannian.Jacobi

end
