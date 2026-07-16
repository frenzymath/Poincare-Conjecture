import OpenGALib.Riemannian.Jacobi.ConjugateDifferential
import OpenGALib.Riemannian.Jacobi.ChartCurvatureNaturality
import OpenGALib.Riemannian.Jacobi.ExpLocalDiffeo

/-!
# do Carmo Ch. 7, `lem:dc-ch7-3-2` — a manifold of nonpositive curvature has no conjugate points

This is the **one genuinely-new piece** of the Hadamard chain: the manifold-level statement that
under nonpositive sectional curvature no point of a geodesic is conjugate to its start.

`JacobiNonpositiveCurvature.lean` proved the analytic heart in a **parallel orthonormal frame in
a single chart** (`frameJacobi_ne_zero_of_nonpos`). Here we run the same energy argument
**intrinsically along the whole geodesic**, so it survives geodesics that leave any single chart:

* The energy `q(t) = ⟨J, J⟩_g` and its first derivative `q'(t) = 2⟨DJ, J⟩_g` are chart-independent
  scalars along `γ` (`metricInner_eq_chartMetricInner_rep`). In each chart the metric-compatibility
  product rule `hasDerivAt_chartMetricInner_along` gives their derivatives from the covariant pair
  system `∇J = DJ`, `∇DJ = -ℛ(J, u̇)u̇` (`IsJacobiFieldOn`).
* Nonpositive curvature makes `qd(t) := ⟨DJ, J⟩` have derivative
  `⟨DJ, DJ⟩ - ⟨ℛ(J, u̇)u̇, J⟩ ≥ 0`, so `qd` is monotone; with `qd(0) = 0` this gives `qd ≥ 0`, so
  `q' = 2 qd ≥ 0` and `q` is monotone.
* `q(0) = 0 = q(b)` (both endpoints of a conjugate arc kill `J`) then squeeze `q ≡ 0`, so `J ≡ 0`
  by positive-definiteness: no interior zero, hence no conjugate point.

The **curvature sign** is pinned by `curvatureFormAt_chartFrame`: `⟨ℛ_chart(J, u̇)u̇, J⟩ ≤ 0` is the
chart avatar of `⟨R(J, u̇)u̇, J⟩ = -K(u̇, J)|u̇ ∧ J|² ≥ 0` under `K ≤ 0`, expressed via the pointwise
curvature operator as `0 ≤ ⟨curvatureOperatorAt x a b b, a⟩` (Morgan–Tian sign; this is do Carmo's
`K ≤ 0`).

## Main results

* `Riemannian.Jacobi.chartMetricInner_chartCurvature_nonpos` — the curvature-sign bridge.
* `Riemannian.Jacobi.IsJacobiFieldAlongOn.forall_eq_zero_of_nonpos_of_endpoints` — the energy
  squeeze: a Jacobi field with `K ≤ 0`, `J(0) = 0 = J(b)` vanishes on `[0, b]`.
* `Riemannian.Jacobi.not_isConjugatePointAt_one_of_nonpos` — `K ≤ 0 ⟹ ¬IsConjugatePointAt γ_v 1`.

Blueprint: `lem:dc-ch7-3-2`, `lem:dc-ch7-3-2-no-conjugate`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7, Lemma 3.2.
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

/-! ### The curvature-sign bridge -/

/-- **Math.** **`K ≤ 0` in the chart.** Under nonpositive sectional curvature, expressed via the
pointwise curvature operator as `0 ≤ ⟨curvatureOperatorAt x a b b, a⟩` (do Carmo's `K ≤ 0`, in the
Morgan–Tian curvature sign), the chart curvature contraction `⟨ℛ_chart(w, v)v, w⟩` is nonpositive
for every chart vector `w` and every velocity `v`.

The bridge is `curvatureFormAt_chartFrame`:
`⟨ℛ_chart(w, v)v, w⟩_{G} = -⟨curvatureOperatorAt p (F w)(F v)(F v), F w⟩`, so the hypothesis makes
the left side `≤ 0`. -/
theorem chartMetricInner_chartCurvature_nonpos (g : RiemannianMetric I M) {α p : M}
    (hp : p ∈ (chartAt H α).source)
    (hK : ∀ a b : TangentSpace I p,
      0 ≤ g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p a b b) a)
    (w v : E) :
    chartMetricInner (I := I) g α (extChartAt I α p)
        (chartCurvature (I := I) g α (extChartAt I α p) w v v) w ≤ 0 := by
  have hbridge := curvatureFormAt_chartFrame (I := I) g hp w v v w
  -- `chartMetricInner(...) = - curvatureFormAt p (F w)(F v)(F v)(F w)`
  have heq : chartMetricInner (I := I) g α (extChartAt I α p)
      (chartCurvature (I := I) g α (extChartAt I α p) w v v) w
        = - g.leviCivitaConnection.curvatureFormAt g p
            (∑ a, Geodesic.chartCoord (E := E) a w • chartBasisVecFiber (I := I) α a p)
            (∑ b, Geodesic.chartCoord (E := E) b v • chartBasisVecFiber (I := I) α b p)
            (∑ c, Geodesic.chartCoord (E := E) c v • chartBasisVecFiber (I := I) α c p)
            (∑ d, Geodesic.chartCoord (E := E) d w • chartBasisVecFiber (I := I) α d p) := by
    rw [hbridge]; ring
  rw [heq, curvatureFormAt_eq_metricInner, neg_nonpos]
  exact hK _ _

/-! ### The energy squeeze -/

/-- **Math.** **do Carmo `lem:dc-ch7-3-2` — the energy squeeze.** Let `(J, DJ)` be a Jacobi field
along a geodesic `γ` on `[0, b]` (`b > 0`) in a manifold of nonpositive curvature (expressed
operatorwise as `0 ≤ ⟨curvatureOperatorAt x a c c, a⟩`). If `J(0) = 0` and `J(b) = 0`, then
`J ≡ 0` on `[0, b]`.

The energy `q = ⟨J, J⟩` is monotone nondecreasing (its derivative `q' = 2⟨DJ, J⟩` is itself
monotone from `q'' = 2|DJ|² - 2⟨R(J, γ')γ', J⟩ ≥ 0`, and `q'(0) = 0`), so `q(0) = 0 = q(b)`
squeezes `q ≡ 0`; positive-definiteness gives `J ≡ 0`. -/
theorem IsJacobiFieldAlongOn.forall_eq_zero_of_nonpos_of_endpoints
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {b : ℝ} (hb : 0 < b)
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 b))
    (hγc : ∀ t ∈ Icc (0 : ℝ) b, ContinuousAt γ t)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a)
    (hJ0 : J 0 = 0) (hJb : J b = 0) :
    ∀ t ∈ Icc (0 : ℝ) b, J t = 0 := by
  classical
  set q : ℝ → ℝ := fun t => g.metricInner (γ t) (J t : TangentSpace I (γ t)) (J t) with hqdef
  set qd : ℝ → ℝ := fun t => g.metricInner (γ t) (DJ t : TangentSpace I (γ t)) (J t) with hqddef
  -- Chart-local package at a time `τ` whose foot lies in the chart at `α`.
  -- the chart curve, and its readings of `J`, `DJ`
  -- `q` and `qd` agree with their chart expressions where the chart contains `γ`.
  have hq_chart : ∀ (α : M) (τ : ℝ), γ τ ∈ (chartAt H α).source →
      q τ = chartMetricInner (I := I) g α (extChartAt I α (γ τ))
        (chartVectorRep (I := I) γ α J τ) (chartVectorRep (I := I) γ α J τ) := by
    intro α τ hsrc
    exact metricInner_eq_chartMetricInner_rep (I := I) g hsrc J J
  have hqd_chart : ∀ (α : M) (τ : ℝ), γ τ ∈ (chartAt H α).source →
      qd τ = chartMetricInner (I := I) g α (extChartAt I α (γ τ))
        (chartVectorRep (I := I) γ α DJ τ) (chartVectorRep (I := I) γ α J τ) := by
    intro α τ hsrc
    exact metricInner_eq_chartMetricInner_rep (I := I) g hsrc DJ J
  -- At an interior time we get a chart with `τ` strictly inside its window.
  have hInterior : ∀ t ∈ Ioo (0 : ℝ) b, ∃ (α : M) (a' b' : ℝ), a' < b' ∧ t ∈ Ioo a' b' ∧
      Icc a' b' ⊆ Icc 0 b ∧ (∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H α).source) ∧
      IsJacobiFieldOn (I := I) g α (fun τ => extChartAt I α (γ τ))
        (chartVectorRep (I := I) γ α J) (chartVectorRep (I := I) γ α DJ) a' b' := by
    intro t ht
    obtain ⟨α, a', b', hab', htIcc, hsub, hnbhd, hsrc, hJF⟩ := hJac t ⟨ht.1.le, ht.2.le⟩
    have hnhds : Icc a' b' ∈ 𝓝 t := by
      have : 𝓝[Icc 0 b] t = 𝓝 t := nhdsWithin_eq_nhds.mpr (Icc_mem_nhds ht.1 ht.2)
      rwa [this] at hnbhd
    have htioo : t ∈ Ioo a' b' := by
      have := mem_interior_iff_mem_nhds.mpr hnhds
      rwa [interior_Icc] at this
    exact ⟨α, a', b', hab', htioo, hsub, hsrc, hJF⟩
  -- The derivative facts at an interior time.
  have hcore : ∀ t ∈ Ioo (0 : ℝ) b,
      (∃ d : ℝ, HasDerivAt qd d t ∧ 0 ≤ d) ∧ HasDerivAt q (2 * qd t) t := by
    intro t ht
    obtain ⟨α, a', b', hab', htioo, hsub, hsrc, hJF⟩ := hInterior t ht
    set uα : ℝ → E := fun s => extChartAt I α (γ s) with huαdef
    set VJ : ℝ → E := chartVectorRep (I := I) γ α J with hVJdef
    set VDJ : ℝ → E := chartVectorRep (I := I) γ α DJ with hVDJdef
    have htIcc' : t ∈ Icc a' b' := Ioo_subset_Icc_self htioo
    have htIcc0 : t ∈ Icc (0 : ℝ) b := hsub htIcc'
    have hsrct : γ t ∈ (chartAt H α).source := hsrc t htIcc'
    have hnhdsW : Icc a' b' ∈ 𝓝 t := Icc_mem_nhds htioo.1 htioo.2
    -- differentiability inputs for `hasDerivAt_chartMetricInner_along`
    have hu : DifferentiableAt ℝ uα t :=
      hgeo.differentiableAt_extChartAt htIcc0 (hγc t htIcc0) hsrct
    have hVJd : DifferentiableAt ℝ VJ t :=
      ((hJF.hasDerivWithinAt_fst t htIcc').hasDerivAt hnhdsW).differentiableAt
    have hVDJd : DifferentiableAt ℝ VDJ t :=
      ((hJF.hasDerivWithinAt_snd t htIcc').hasDerivAt hnhdsW).differentiableAt
    have hymem : uα t ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrct)
    have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (uα t) := fun i j =>
      differentiableAt_chartGramOnE (I := I) g α hymem i j
    have hbase : (extChartAt I α).symm (uα t) ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      symm_extChartAt_mem_baseSet (I := I) hsrct
    -- covariant pair identities at `t`
    have hfst : covariantDerivCoord (I := I) g α uα VJ t = VDJ t := hJF.covariantDerivCoord_fst htioo
    have hsnd : covariantDerivCoord (I := I) g α uα VDJ t
        = -(chartCurvature (I := I) g α (uα t) (VJ t) (deriv uα t) (deriv uα t)) :=
      hJF.covariantDerivCoord_snd htioo
    -- eventual equalities of `q`, `qd` with their chart expressions
    have hevq : q =ᶠ[𝓝 t] fun s => chartMetricInner (I := I) g α (uα s) (VJ s) (VJ s) := by
      filter_upwards [hnhdsW] with s hs
      exact hq_chart α s (hsrc s hs)
    have hevqd : qd =ᶠ[𝓝 t] fun s => chartMetricInner (I := I) g α (uα s) (VDJ s) (VJ s) := by
      filter_upwards [hnhdsW] with s hs
      exact hqd_chart α s (hsrc s hs)
    refine ⟨?_, ?_⟩
    · -- the `qd` derivative `-⟨R(J), J⟩ + |DJ|²` is nonnegative
      have hraw := hasDerivAt_chartMetricInner_along (I := I) g α uα VDJ VJ hu hVDJd hVJd hG hbase
      rw [hfst, hsnd] at hraw
      refine ⟨_, hraw.congr_of_eventuallyEq hevqd, ?_⟩
      rw [chartMetricInner_neg_left]
      have hcurv : chartMetricInner (I := I) g α (uα t)
          (chartCurvature (I := I) g α (uα t) (VJ t) (deriv uα t) (deriv uα t)) (VJ t) ≤ 0 :=
        chartMetricInner_chartCurvature_nonpos (I := I) g hsrct (hK (γ t)) (VJ t) (deriv uα t)
      have hDJsq : 0 ≤ chartMetricInner (I := I) g α (uα t) (VDJ t) (VDJ t) := by
        have h : chartMetricInner (I := I) g α (uα t) (VDJ t) (VDJ t)
            = g.metricInner (γ t) (DJ t) (DJ t) :=
          (metricInner_eq_chartMetricInner_rep (I := I) g hsrct DJ DJ).symm
        rw [h]; exact g.metricInner_self_nonneg (γ t) (DJ t)
      linarith
    · -- the `q` derivative is `2 qd t`
      have hraw := hasDerivAt_chartMetricInner_along (I := I) g α uα VJ VJ hu hVJd hVJd hG hbase
      rw [hfst] at hraw
      have hqderiv : HasDerivAt q
          (chartMetricInner (I := I) g α (uα t) (VDJ t) (VJ t)
            + chartMetricInner (I := I) g α (uα t) (VJ t) (VDJ t)) t :=
        hraw.congr_of_eventuallyEq hevq
      have hsymm : chartMetricInner (I := I) g α (uα t) (VJ t) (VDJ t)
          = chartMetricInner (I := I) g α (uα t) (VDJ t) (VJ t) :=
        chartMetricInner_symm (I := I) g α (uα t) (VJ t) (VDJ t)
      have hqd_val : chartMetricInner (I := I) g α (uα t) (VDJ t) (VJ t) = qd t := by
        rw [hqd_chart α t hsrct]
      rw [hsymm] at hqderiv
      have : chartMetricInner (I := I) g α (uα t) (VDJ t) (VJ t)
          + chartMetricInner (I := I) g α (uα t) (VDJ t) (VJ t) = 2 * qd t := by
        rw [hqd_val]; ring
      rwa [this] at hqderiv
  -- continuity of `q` and `qd` on `[0, b]`, patched from chart-local continuity
  have hcont_at : ∀ (F : ℝ → ℝ) (V : ℝ → E), (V = J ∨ V = DJ) →
      (∀ (α : M) (τ : ℝ), γ τ ∈ (chartAt H α).source →
        F τ = chartMetricInner (I := I) g α (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α V τ) (chartVectorRep (I := I) γ α J τ)) →
      ContinuousOn F (Icc 0 b) := by
    intro F V hV hFrep t ht
    obtain ⟨α, a', b', hab', htIcc, hsub, hnbhd, hsrc, hJF⟩ := hJac t ht
    set uα : ℝ → E := fun s => extChartAt I α (γ s) with huαdef
    have hucont : ContinuousOn uα (Icc a' b') := by
      intro τ hτ
      exact (hgeo.differentiableAt_extChartAt (hsub hτ) (hγc τ (hsub hτ))
        (hsrc τ hτ)).continuousAt.continuousWithinAt
    have hmem : ∀ τ ∈ Icc a' b', uα τ ∈ (extChartAt I α).target := fun τ hτ =>
      (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc τ hτ)
    have hVcont : ContinuousOn (chartVectorRep (I := I) γ α V) (Icc a' b') := by
      rcases hV with rfl | rfl
      · exact hJF.continuousOn_fst
      · exact hJF.continuousOn_snd
    have hchartcont : ContinuousOn (fun s => chartMetricInner (I := I) g α (uα s)
        (chartVectorRep (I := I) γ α V s) (chartVectorRep (I := I) γ α J s)) (Icc a' b') :=
      continuousOn_chartMetricInner_pairing (I := I) g α hucont hmem hVcont hJF.continuousOn_fst
    have hcwa : ContinuousWithinAt (fun s => chartMetricInner (I := I) g α (uα s)
        (chartVectorRep (I := I) γ α V s) (chartVectorRep (I := I) γ α J s)) (Icc 0 b) t :=
      (hchartcont t htIcc).mono_of_mem_nhdsWithin hnbhd
    refine hcwa.congr_of_eventuallyEq ?_ (hFrep α t (hsrc t htIcc))
    filter_upwards [hnbhd] with s hs using hFrep α s (hsrc s hs)
  have hqcont : ContinuousOn q (Icc 0 b) := hcont_at q J (Or.inl rfl) hq_chart
  have hqdcont : ContinuousOn qd (Icc 0 b) := hcont_at qd DJ (Or.inr rfl) hqd_chart
  -- `qd` is monotone nondecreasing
  have hqd_diff : DifferentiableOn ℝ qd (interior (Icc 0 b)) := by
    rw [interior_Icc]
    intro t ht
    obtain ⟨d, hd, _⟩ := (hcore t ht).1
    exact hd.differentiableAt.differentiableWithinAt
  have hqd_deriv_nonneg : ∀ t ∈ interior (Icc (0 : ℝ) b), 0 ≤ deriv qd t := by
    rw [interior_Icc]
    intro t ht
    obtain ⟨d, hd, hdnn⟩ := (hcore t ht).1
    rwa [hd.deriv]
  have hqd_mono : MonotoneOn qd (Icc 0 b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 b) hqdcont hqd_diff hqd_deriv_nonneg
  -- `qd 0 = 0`, so `qd ≥ 0` on `[0, b]`
  have hqd0 : qd 0 = 0 := by
    simp only [hqddef, hJ0]; exact g.metricInner_zero_right (γ 0) (DJ 0)
  have hqd_nonneg : ∀ t ∈ Icc (0 : ℝ) b, 0 ≤ qd t := by
    intro t ht
    have := hqd_mono ⟨le_rfl, hb.le⟩ ht ht.1
    rwa [hqd0] at this
  -- `q` is monotone nondecreasing, from `q' = 2 qd ≥ 0`
  have hq_diff : DifferentiableOn ℝ q (interior (Icc 0 b)) := by
    rw [interior_Icc]
    intro t ht
    exact (hcore t ht).2.differentiableAt.differentiableWithinAt
  have hq_deriv_nonneg : ∀ t ∈ interior (Icc (0 : ℝ) b), 0 ≤ deriv q t := by
    rw [interior_Icc]
    intro t ht
    rw [(hcore t ht).2.deriv]
    have := hqd_nonneg t (Ioo_subset_Icc_self ht)
    linarith
  have hq_mono : MonotoneOn q (Icc 0 b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 b) hqcont hq_diff hq_deriv_nonneg
  -- `q 0 = 0 = q b` squeezes `q ≡ 0`
  have hq0 : q 0 = 0 := by
    simp only [hqdef, hJ0]; exact g.metricInner_zero_right (γ 0) 0
  have hqb : q b = 0 := by
    simp only [hqdef, hJb]; exact g.metricInner_zero_right (γ b) 0
  intro t ht
  have hle : q t ≤ 0 := by rw [← hqb]; exact hq_mono ht ⟨hb.le, le_rfl⟩ ht.2
  have hge : 0 ≤ q t := by rw [← hq0]; exact hq_mono ⟨le_rfl, hb.le⟩ ht ht.1
  have hqt0 : q t = 0 := le_antisymm hle hge
  -- positive-definiteness: `⟨J, J⟩ = 0 ⟹ J = 0`
  by_contra hJne
  have : 0 < q t := g.metricInner_self_pos (γ t) (J t) hJne
  linarith

/-! ### No conjugate points -/

/-- **Math.** **do Carmo `lem:dc-ch7-3-2`.** In a manifold of nonpositive curvature, no point of a
geodesic `γ` is conjugate to `γ(0)`: a nontrivial Jacobi field along `γ|[0,b]` vanishing at both
endpoints would contradict the energy squeeze. -/
theorem not_isConjugatePointAt_of_nonpos (g : RiemannianMetric I M) {γ : ℝ → M} {b : ℝ}
    (hb : 0 < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 b))
    (hγc : ∀ t ∈ Icc (0 : ℝ) b, ContinuousAt γ t)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    ¬ IsConjugatePointAt (I := I) g γ b := by
  rintro ⟨J, DJ, hJac, ⟨t, ht, hJt⟩, hJ0, hJb⟩
  exact hJt (IsJacobiFieldAlongOn.forall_eq_zero_of_nonpos_of_endpoints
    (I := I) g hb hJac hgeo hγc hK hJ0 hJb t ht)

/-- **Math.** **do Carmo `lem:dc-ch7-3-2` (exponential form).** On a complete manifold of
nonpositive curvature, for every `p` and `v` the point `exp_p(v) = γ_v(1)` is not conjugate to
`p` along `γ_v`. Combined with `expDifferential_isEquiv_of_not_conjugate`
(`ExpLocalDiffeo.lean`), this makes `d(exp_p)_v` a linear isomorphism at every `v`, so
`exp_p` is a local diffeomorphism (the conjugate locus `C(p) = ∅`). -/
theorem not_isConjugatePointAt_one_of_nonpos (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1 :=
  not_isConjugatePointAt_of_nonpos (I := I) g one_pos
    (fun t _ => isGeodesic_globalGeodesic g hg p v t)
    (fun _ _ => (continuous_globalGeodesic g hg p v).continuousAt) hK

/-! ### `exp_p` is a local diffeomorphism under nonpositive curvature -/

/-- **Math.** **do Carmo `lem:dc-ch7-3-2` (differential form).** On a complete manifold of
nonpositive curvature, the differential `d(exp_p)_v` is a **continuous linear isomorphism** at
every `v ∈ T_pM`. This is the composition of the empty conjugate locus
(`not_isConjugatePointAt_one_of_nonpos`, do Carmo `lem:dc-ch7-3-2`) with the curvature-free
analytic core `expDifferential_isEquiv_of_not_conjugate`. It is the sense in which `exp_p` is a
local diffeomorphism used in the proof of the Hadamard theorem `thm:dc-ch7-3-1`.

Blueprint: `lem:dc-ch7-3-2`. -/
theorem expDifferential_isEquiv_of_nonpos (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    ∃ (ζ : M) (D : E ≃L[ℝ] E),
      expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasStrictFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
        (D : E →L[ℝ] E) v :=
  expDifferential_isEquiv_of_not_conjugate (I := I) g hg p
    (not_isConjugatePointAt_one_of_nonpos (I := I) g hg p v hK)

/-- **Math.** **do Carmo `lem:dc-ch7-3-2` (local injectivity).** On a complete manifold of
nonpositive curvature, `exp_p` is injective on a neighbourhood of every `v ∈ T_pM`.

Blueprint: `lem:dc-ch7-3-2`. -/
theorem expMapGlobal_locallyInjective_of_nonpos (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E)
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    ∃ U ∈ 𝓝 v, Set.InjOn (expMapGlobal (I := I) g hg p) U :=
  expMapGlobal_locallyInjective_of_not_conjugate (I := I) g hg p
    (not_isConjugatePointAt_one_of_nonpos (I := I) g hg p v hK)

end Riemannian.Jacobi

end
