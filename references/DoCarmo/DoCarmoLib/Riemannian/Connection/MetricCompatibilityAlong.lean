import DoCarmoLib.Riemannian.Connection.AffineCovariantDerivativeAlong
import DoCarmoLib.Riemannian.Connection.ParallelAlong
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-!
# Metric compatibility along curves

This file gives the intrinsic along-curve form of do Carmo Ch. 2, Proposition 3.2:
the Levi-Civita covariant derivative obeys the metric product rule.  It also relates
the product rule, constancy of the pairing of parallel fields (Definition 3.1), and
the ambient-vector-field formulation `AffineConnection.IsMetricCompatible`
(Corollary 3.3).
-/

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Reading a tangent field in a fixed chart and then reading it back at
the same foot recovers the original tangent vector. -/
theorem tangentCoordChange_chartFieldRep (c : ℝ → M) (alpha : M)
    (V : ∀ t, TangentSpace I (c t)) {t : ℝ}
    (h : c t ∈ (extChartAt I alpha).source) :
    tangentCoordChange I alpha (c t) (c t)
        (chartFieldRep (I := I) c alpha V t) = V t := by
  rw [chartFieldRep_apply,
    tangentCoordChange_comp (I := I) (w := c t) (x := alpha) (y := c t)
      (z := c t) ⟨⟨mem_extChartAt_source (I := I) (c t), h⟩,
        mem_extChartAt_source (I := I) (c t)⟩]
  exact tangentCoordChange_self (mem_extChartAt_source (I := I) (c t))

/-- **Math.** do Carmo Ch. 2, Proposition 3.2: the intrinsic metric product
rule along a curve,
`(d/dt) g(V,W) = g(DV/dt,W) + g(V,DW/dt)`.

The hypotheses are exactly the local chart hypotheses needed by the
two-sided derivative at `t`; smoothness of the metric supplies `hG`
automatically. -/
theorem hasDerivAt_metricInner_along (g : RiemannianMetric I M)
    {c : ℝ → M} {V W : ∀ t, TangentSpace I (c t)} (alpha : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H alpha).source)
    (hu : DifferentiableAt ℝ (fun s => extChartAt I alpha (c s)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c alpha V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c alpha W) t) :
    HasDerivAt (fun s => g.metricInner (c s) (V s) (W s))
      (g.metricInner (c t) (Riemannian.covDerivAlong (I := I) g c V t) (W t)
        + g.metricInner (c t) (V t) (Riemannian.covDerivAlong (I := I) g c W t)) t := by
  classical
  have hsrc' : c t ∈ (extChartAt I alpha).source := by
    rwa [extChartAt_source]
  have hev : ∀ᶠ s in 𝓝 t, c s ∈ (extChartAt I alpha).source :=
    hc.eventually_mem ((isOpen_extChartAt_source (I := I) alpha).mem_nhds hsrc')
  have heq : (fun s => g.metricInner (c s) (V s) (W s)) =ᶠ[𝓝 t]
      fun s => chartMetricInner (I := I) g alpha (extChartAt I alpha (c s))
        (chartFieldRep (I := I) c alpha V s)
        (chartFieldRep (I := I) c alpha W s) := by
    filter_upwards [hev] with s hs
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g alpha
        (by rwa [extChartAt_source] at hs),
      trivializationAt_symm_eq_tangentCoordChange (I := I) alpha
        (by rwa [extChartAt_source] at hs),
      trivializationAt_symm_eq_tangentCoordChange (I := I) alpha
        (by rwa [extChartAt_source] at hs),
      tangentCoordChange_chartFieldRep (I := I) c alpha V hs,
      tangentCoordChange_chartFieldRep (I := I) c alpha W hs]
  have hbase : (extChartAt I alpha).symm (extChartAt I alpha (c t))
      ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    rw [(extChartAt I alpha).left_inv hsrc',
      trivializationAt_baseSet_eq_chartAt_source]
    exact hsrc
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g alpha i j)
      (extChartAt I alpha (c t)) := fun i j =>
    ((chartGramOnE_contDiffOn (I := I) g alpha i j).contDiffAt
      (extChartAt_target_mem_nhds' (I := I)
        ((extChartAt I alpha).map_source hsrc'))).differentiableAt (by norm_num)
  have h := hasDerivAt_chartMetricInner_along (I := I) g alpha
    (fun s => extChartAt I alpha (c s))
    (chartFieldRep (I := I) c alpha V)
    (chartFieldRep (I := I) c alpha W) hu hV hW hG hbase
  have hreadV : (trivializationAt E (TangentSpace I) alpha).symm (c t)
      (chartFieldRep (I := I) c alpha V t) = V t := by
    rw [trivializationAt_symm_eq_tangentCoordChange (I := I) alpha hsrc]
    exact tangentCoordChange_chartFieldRep (I := I) c alpha V hsrc'
  have hreadW : (trivializationAt E (TangentSpace I) alpha).symm (c t)
      (chartFieldRep (I := I) c alpha W t) = W t := by
    rw [trivializationAt_symm_eq_tangentCoordChange (I := I) alpha hsrc]
    exact tangentCoordChange_chartFieldRep (I := I) c alpha W hsrc'
  have hcovV : (trivializationAt E (TangentSpace I) alpha).symm (c t)
      (covariantDerivCoord (I := I) g alpha
        (fun s => extChartAt I alpha (c s))
        (chartFieldRep (I := I) c alpha V) t) =
        Riemannian.covDerivAlong (I := I) g c V t := by
    rw [trivializationAt_symm_eq_tangentCoordChange (I := I) alpha hsrc]
    exact (covDerivAlong_eq_chart (I := I) g alpha hc hsrc hu hV).symm
  have hcovW : (trivializationAt E (TangentSpace I) alpha).symm (c t)
      (covariantDerivCoord (I := I) g alpha
        (fun s => extChartAt I alpha (c s))
        (chartFieldRep (I := I) c alpha W) t) =
        Riemannian.covDerivAlong (I := I) g c W t := by
    rw [trivializationAt_symm_eq_tangentCoordChange (I := I) alpha hsrc]
    exact (covDerivAlong_eq_chart (I := I) g alpha hc hsrc hu hW).symm
  rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g alpha hsrc,
    chartMetricInner_extChartAt_eq_metricInner (I := I) g alpha hsrc,
    hcovV, hreadW, hreadV, hcovW] at h
  exact h.congr_of_eventuallyEq heq

/-- **Math.** The metric pairing has zero derivative wherever both fields are parallel. -/
theorem hasDerivAt_metricInner_eq_zero_of_isParallelAt
    (g : RiemannianMetric I M) {c : ℝ → M}
    {V W : ∀ t, TangentSpace I (c t)} (alpha : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H alpha).source)
    (hu : DifferentiableAt ℝ (fun s => extChartAt I alpha (c s)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c alpha V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c alpha W) t)
    (hVp : Riemannian.covDerivAlong (I := I) g c V t = 0)
    (hWp : Riemannian.covDerivAlong (I := I) g c W t = 0) :
    HasDerivAt (fun s => g.metricInner (c s) (V s) (W s)) 0 t := by
  have h := hasDerivAt_metricInner_along (I := I) g alpha hc hsrc hu hV hW
  simpa only [hVp, hWp, g.metricInner_zero_left, g.metricInner_zero_right,
    zero_add] using h

/-- **Math.** The metric product rule with a chart-free curve hypothesis.  The field
regularity hypotheses still use the canonical chart at the moving foot, which
is the regularity notion built into `covDerivAlong`. -/
theorem hasDerivAt_metricInner_along_of_mdifferentiableAt
    (g : RiemannianMetric I M) {c : ℝ → M}
    {V W : ∀ t, TangentSpace I (c t)} {t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t) :
    HasDerivAt (fun s => g.metricInner (c s) (V s) (W s))
      (g.metricInner (c t) (Riemannian.covDerivAlong (I := I) g c V t) (W t)
        + g.metricInner (c t) (V t) (Riemannian.covDerivAlong (I := I) g c W t)) t := by
  have hu : DifferentiableAt ℝ (fun s => extChartAt I (c t) (c s)) t :=
    (hasDerivAt_extChartAt_comp_of_hasMFDerivAt_DC (I := I)
      (hasMFDerivAt_smulRight_DCVelocity (I := I) hc)
      (mem_extChartAt_source (I := I) (c t))).differentiableAt
  exact hasDerivAt_metricInner_along (I := I) g (c t) hc.continuousAt
    (mem_chart_source H (c t)) hu hV hW

/-- **Math.** Pointwise regularity of a tangent field along a curve in the moving-foot
chart used to define the intrinsic along derivative. -/
def IsRegularFieldAlong (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) : Prop :=
  ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t

/-- **Math.** Regularity of an along-field at every time in `s`. -/
def IsRegularFieldAlongOn (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t

/-- **Math.** The unguarded parallel equation for an affine connection on a
parameter set.

Because `covDerivAlong` is total, this predicate can be satisfied by irregular
fields whose coordinate derivatives default to zero.  It is meaningful for
parallel transport only together with `IsRegularFieldAlongOn`; for the
Levi-Civita connection the guarded notions are `IsParallelAlongWithinOn` and
`IsIntrinsicPiecewiseParallelAlongOn`. -/
def AffineConnection.IsParallelFieldAlongOn
    (nabla : AffineConnection I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, nabla.covDerivAlong c V t = 0

/-- **Math.** Setwise parallelism for the Levi-Civita affine connection is exactly the
intrinsic `IsParallelAlong` predicate. -/
theorem RiemannianMetric.leviCivita_isParallelFieldAlongOn_iff_isParallelAlong
    (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (s : Set ℝ) :
    g.leviCivitaConnection.IsParallelFieldAlongOn c V s ↔
      IsParallelAlong (I := I) g c V s := by
  simp only [AffineConnection.IsParallelFieldAlongOn, IsParallelAlong,
    g.leviCivita_covDerivAlong_eq]

private theorem isParallelWithinSolOn_of_isParallelAlong
    {g : RiemannianMetric I M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {alpha : M} {a b : ℝ}
    (hc : ∀ t ∈ Icc a b, ContinuousAt c t)
    (hdiff : Variation.IsChartDifferentiableOn (I := I) c a b)
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H alpha).source)
    (hreg : IsRegularFieldAlongOn (I := I) c V (Icc a b))
    (hpar : IsParallelAlong (I := I) g c V (Icc a b)) :
    IsParallelWithinSolOn (I := I) g alpha c V a b := by
  intro t ht
  have huSelf := hdiff t ht (c t) (mem_chart_source H (c t))
  have hu := hdiff t ht alpha (hsrc t ht)
  have hfield : DifferentiableAt ℝ (chartFieldRep (I := I) c alpha V) t :=
    differentiableAt_chartFieldRep_change (I := I) (c t) alpha
      (hc t ht) (mem_chart_source H (c t)) (hsrc t ht)
      huSelf (hreg t ht)
  have hzero := (covDerivAlong_eq_zero_iff_chart (I := I) g alpha
    (hc t ht) (hsrc t ht) hu hfield).1 (hpar t ht)
  refine ⟨deriv (fun s => extChartAt I alpha (c s)) t,
    hu.hasDerivAt.hasDerivWithinAt, ?_⟩
  rw [covariantDerivCoord_def] at hzero
  rw [← (eq_neg_of_add_eq_zero_left hzero)]
  exact hfield.hasDerivAt.hasDerivWithinAt

private theorem isParallelAlongWithinOn_of_isParallelAlong_Icc
    {g : RiemannianMetric I M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b : ℝ}
    (hab : a < b)
    (hc : ∀ t ∈ Icc a b, ContinuousAt c t)
    (hdiff : Variation.IsChartDifferentiableOn (I := I) c a b)
    (hreg : IsRegularFieldAlongOn (I := I) c V (Icc a b))
    (hpar : IsParallelAlong (I := I) g c V (Icc a b)) :
    IsParallelAlongWithinOn (I := I) g c V a b := by
  intro t ht
  have hpre : c ⁻¹' (chartAt H (c t)).source ∈ 𝓝 t :=
    (hc t ht).preimage_mem_nhds
      ((chartAt H (c t)).open_source.mem_nhds (mem_chart_source H (c t)))
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.1 hpre
  let l := max a (t - eps / 2)
  let r := min b (t + eps / 2)
  have htlr : t ∈ Icc l r :=
    ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩
  have hsub : Icc l r ⊆ Icc a b :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hnbhd : Icc l r ∈ 𝓝[Icc a b] t := by
    refine mem_nhdsWithin.2 ⟨Ioo (t - eps / 2) (t + eps / 2), isOpen_Ioo,
      ⟨by linarith, by linarith⟩, ?_⟩
    intro s hs
    exact ⟨max_le hs.2.1 hs.1.1.le, le_min hs.2.2 hs.1.2.le⟩
  have hsrc : ∀ s ∈ Icc l r, c s ∈ (chartAt H (c t)).source := by
    intro s hs
    have hlower : t - eps / 2 ≤ s :=
      (le_max_right a (t - eps / 2)).trans hs.1
    have hupper : s ≤ t + eps / 2 :=
      hs.2.trans (min_le_right b (t + eps / 2))
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hle : |s - t| ≤ eps / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hlr : l < r := by
    apply max_lt
    · exact lt_min hab (by linarith [ht.1])
    · exact lt_min (by linarith [ht.2]) (by linarith)
  refine ⟨c t, l, r, hlr, htlr, hsub, hnbhd, hsrc, ?_⟩
  exact isParallelWithinSolOn_of_isParallelAlong
    (fun s hs => hc s (hsub hs))
    (fun s hs => hdiff s (hsub hs))
    hsrc
    (fun s hs => hreg s (hsub hs))
    (fun s hs => hpar s (hsub hs))

/-- **Math.** On every compact subinterval of an open interval, continuity and
chart differentiability of the curve, regularity of the field, and the
unguarded parallel equation yield a genuine closed-interval certificate.  This
is the converse direction to the existing certificate-to-equation bridge. -/
theorem IsParallelAlong.isParallelAlongWithinOn_of_isRegularFieldAlongOn
    {g : RiemannianMetric I M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b l r : ℝ}
    (hpar : IsParallelAlong (I := I) g c V (Ioo a b))
    (hreg : IsRegularFieldAlongOn (I := I) c V (Ioo a b))
    (hc : ∀ t ∈ Ioo a b, ContinuousAt c t)
    (hdiff : ∀ t ∈ Ioo a b, ∀ alpha : M,
      c t ∈ (chartAt H alpha).source →
        DifferentiableAt ℝ (fun s => extChartAt I alpha (c s)) t)
    (hlr : l < r) (hsub : Icc l r ⊆ Ioo a b) :
    IsParallelAlongWithinOn (I := I) g c V l r := by
  exact isParallelAlongWithinOn_of_isParallelAlong_Icc hlr
    (fun t ht => hc t (hsub ht))
    (fun t ht alpha hsrc => hdiff t (hsub ht) alpha hsrc)
    (fun t ht => hreg t (hsub ht))
    (fun t ht => hpar t (hsub ht))

/-- **Math.** A closed-interval certificate implies the ordinary parallel
equation at every interior time. -/
theorem IsParallelAlongWithinOn.isParallelAlong_Ioo_of_contMDiffOn
    {g : RiemannianMetric I M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b : ℝ}
    (h : IsParallelAlongWithinOn (I := I) g c V a b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b)) :
    IsParallelAlong (I := I) g c V (Ioo a b) := by
  intro t ht
  obtain ⟨alpha, l, r, _hlr, ht', _hsub, hnbhd, hsrc, hcert⟩ :=
    h t (Ioo_subset_Icc_self ht)
  have hOuterN : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  rw [nhdsWithin_eq_nhds.2 hOuterN] at hnbhd
  obtain ⟨velocity, hu, hV⟩ := hcert t ht'
  have huAt := hu.hasDerivAt hnbhd
  have hVAt := hV.hasDerivAt hnbhd
  have hcoord : covariantDerivCoord (I := I) g alpha
      (fun s => extChartAt I alpha (c s))
      (chartFieldRep (I := I) c alpha V) t = 0 := by
    rw [covariantDerivCoord_def, huAt.deriv, hVAt.deriv]
    abel
  have hct : ContMDiffAt 𝓘(ℝ, ℝ) I 1 c t :=
    (hc t (Ioo_subset_Icc_self ht)).contMDiffAt hOuterN
  exact (covDerivAlong_eq_zero_iff_chart (I := I) g alpha
    hct.continuousAt (hsrc t ht')
    huAt.differentiableAt hVAt.differentiableAt).2 hcoord

/-- **Math.** A one-sided within-parallel certificate on a nontrivial closed
interval starting at `a` and contained in `[a,b]`. -/
def IsParallelAlongWithinAtLeft (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (a b : ℝ) : Prop :=
  ∃ r, a < r ∧ r ≤ b ∧ ∃ alpha : M,
    (∀ t ∈ Icc a r, c t ∈ (chartAt H alpha).source) ∧
    IsParallelWithinSolOn (I := I) g alpha c V a r

/-- **Math.** A one-sided within-parallel certificate on a nontrivial closed
interval ending at `b` and contained in `[a,b]`. -/
def IsParallelAlongWithinAtRight (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (a b : ℝ) : Prop :=
  ∃ l, a ≤ l ∧ l < b ∧ ∃ alpha : M,
    (∀ t ∈ Icc l b, c t ∈ (chartAt H alpha).source) ∧
    IsParallelWithinSolOn (I := I) g alpha c V l b

/-- **Math.** Closed-interval parallelism is exactly the regular interior
parallel equation together with its two one-sided endpoint certificates. -/
theorem isParallelAlongWithinOn_iff_isParallelAlong_Ioo_and_endpoints
    {g : RiemannianMetric I M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b : ℝ}
    (hab : a < b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    (hreg : IsRegularFieldAlongOn (I := I) c V (Ioo a b)) :
    IsParallelAlongWithinOn (I := I) g c V a b ↔
      IsParallelAlong (I := I) g c V (Ioo a b) ∧
      IsParallelAlongWithinAtLeft (I := I) g c V a b ∧
      IsParallelAlongWithinAtRight (I := I) g c V a b := by
  have hcAt : ∀ t ∈ Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) I 1 c t := by
    intro t ht
    exact (hc t (Ioo_subset_Icc_self ht)).contMDiffAt
      (Icc_mem_nhds ht.1 ht.2)
  constructor
  · intro h
    refine ⟨h.isParallelAlong_Ioo_of_contMDiffOn hc, ?_, ?_⟩
    · obtain ⟨alpha, l, r, hlr, ha, hsub, _hnbhd, hsrc, hcert⟩ :=
        h a (left_mem_Icc.2 hab.le)
      have hleq : l = a := le_antisymm ha.1
        (hsub (left_mem_Icc.2 hlr.le)).1
      subst l
      exact ⟨r, hlr, (hsub (right_mem_Icc.2 hlr.le)).2,
        alpha, hsrc, hcert⟩
    · obtain ⟨alpha, l, r, hlr, hb, hsub, _hnbhd, hsrc, hcert⟩ :=
        h b (right_mem_Icc.2 hab.le)
      have hre : r = b := le_antisymm
        (hsub (right_mem_Icc.2 hlr.le)).2 hb.2
      subst r
      exact ⟨l, (hsub (left_mem_Icc.2 hlr.le)).1, hlr,
        alpha, hsrc, hcert⟩
  · rintro ⟨hpar, hleft, hright⟩ t ht
    rcases eq_or_lt_of_le ht.1 with hta | hat
    · subst t
      obtain ⟨r, har, hrb, alpha, hsrc, hcert⟩ := hleft
      refine ⟨alpha, a, r, har, left_mem_Icc.2 har.le,
        Icc_subset_Icc le_rfl hrb, ?_, hsrc, hcert⟩
      refine mem_nhdsWithin.2 ⟨Iio r, isOpen_Iio, har, ?_⟩
      intro s hs
      exact ⟨hs.2.1, hs.1.le⟩
    · rcases eq_or_lt_of_le ht.2 with htb | htb
      · subst t
        obtain ⟨l, hal, hlb, alpha, hsrc, hcert⟩ := hright
        refine ⟨alpha, l, b, hlb, right_mem_Icc.2 hlb.le,
          Icc_subset_Icc hal le_rfl, ?_, hsrc, hcert⟩
        refine mem_nhdsWithin.2 ⟨Ioi l, isOpen_Ioi, hlb, ?_⟩
        intro s hs
        exact ⟨hs.1.le, hs.2.2⟩
      · let l := (a + t) / 2
        let r := (t + b) / 2
        have halt : a < l := by dsimp [l]; linarith
        have hltt : l < t := by dsimp [l]; linarith
        have httr : t < r := by dsimp [r]; linarith
        have hrtb : r < b := by dsimp [r]; linarith
        have hlr : l < r := lt_trans hltt httr
        have hsubOpen : Icc l r ⊆ Ioo a b := by
          intro s hs
          exact ⟨halt.trans_le hs.1, hs.2.trans_lt hrtb⟩
        have hsmall := hpar.isParallelAlongWithinOn_of_isRegularFieldAlongOn
          hreg
          (fun s hs => (hcAt s hs).continuousAt)
          (fun s hs alpha hsrc =>
            ((contMDiffAt_extChartAt' (I := I) (n := 1) hsrc).comp
              s (hcAt s hs)).contDiffAt.differentiableAt (by norm_num))
          hlr hsubOpen
        obtain ⟨alpha, l', r', hlr', ht', hsub', hnbhd', hsrc', hcert'⟩ :=
          hsmall t ⟨hltt.le, httr.le⟩
        have hlocalN : Icc l r ∈ 𝓝 t := Icc_mem_nhds hltt httr
        rw [nhdsWithin_eq_nhds.2 hlocalN] at hnbhd'
        exact ⟨alpha, l', r', hlr', ht',
          hsub'.trans (Icc_subset_Icc halt.le hrtb.le),
          mem_nhdsWithin_of_mem_nhds hnbhd', hsrc', hcert'⟩

/-- **Math.** The endpoint seam criterion, written with the arbitrary affine
parallel equation specialized to the Levi-Civita connection. -/
theorem isParallelAlongWithinOn_iff_leviCivita_isParallelFieldAlongOn_Ioo_and_endpoints
    {g : RiemannianMetric I M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b : ℝ}
    (hab : a < b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    (hreg : IsRegularFieldAlongOn (I := I) c V (Ioo a b)) :
    IsParallelAlongWithinOn (I := I) g c V a b ↔
      g.leviCivitaConnection.IsParallelFieldAlongOn c V (Ioo a b) ∧
      IsParallelAlongWithinAtLeft (I := I) g c V a b ∧
      IsParallelAlongWithinAtRight (I := I) g c V a b := by
  rw [isParallelAlongWithinOn_iff_isParallelAlong_Ioo_and_endpoints
    (I := I) hab hc hreg,
    g.leviCivita_isParallelFieldAlongOn_iff_isParallelAlong]

/-- **Math.** Prescribed fibre values are realized by regular parallel fields on `s`. -/
def AffineConnection.HasParallelFieldRealizationAlongOn
    (nabla : AffineConnection I M) (c : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ v : TangentSpace I (c t),
    ∃ V : ∀ r, TangentSpace I (c r),
      IsRegularFieldAlongOn (I := I) c V s ∧
      nabla.IsParallelFieldAlongOn c V s ∧ V t = v

/-- **Math.** The metric product rule at every time of a parameter set. -/
def AffineConnection.HasMetricProductRuleAlongOn
    (nabla : AffineConnection I M) (g : RiemannianMetric I M)
    (c : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I c t →
    ∀ (V W : ∀ r, TangentSpace I (c r)),
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t →
      HasDerivAt (fun r => g.metricInner (c r) (V r) (W r))
        (g.metricInner (c t) (nabla.covDerivAlong c V t) (W t)
          + g.metricInner (c t) (V t) (nabla.covDerivAlong c W t)) t

/-- **Math.** The connection term in a fixed chart, packaged as a continuous linear map
in the field variable. -/
noncomputable def AffineConnection.chartContractionRightAt
    (nabla : AffineConnection I M) (alpha p : M) (v : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => nabla.chartContractionAt alpha p v w
      map_add' := nabla.chartContractionAt_add_right alpha p v
      map_smul' := fun a w => nabla.chartContractionAt_smul_right alpha p v w a }

@[simp] theorem AffineConnection.chartContractionRightAt_apply
    (nabla : AffineConnection I M) (alpha p : M) (v w : E) :
    nabla.chartContractionRightAt alpha p v w =
      nabla.chartContractionAt alpha p v w := rfl

/-- **Math.** On a region where a fixed smooth frame agrees locally with the coordinate
frame, the chart connection endomorphism varies continuously with its foot and
direction. -/
theorem AffineConnection.continuousOn_chartContractionRightAt_of_frame
    (nabla : AffineConnection I M) (alpha : M)
    (Y : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    {s : Set ℝ} {c : ℝ → M} {v : ℝ → E}
    (hc : ContinuousOn c s) (hv : ContinuousOn v s)
    (hsrc : ∀ t ∈ s, c t ∈ (chartAt H alpha).source)
    (hY : ∀ t ∈ s, ∀ i, ⇑(Y i) =ᶠ[𝓝 (c t)]
      fun q => Tensor.chartBasisVecFiber (I := I) alpha i q) :
    ContinuousOn (fun t => nabla.chartContractionRightAt alpha (c t) (v t)) s := by
  classical
  let L : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E →L[ℝ] E :=
    fun j m => (Geodesic.chartCoordFunctional (E := E) j).smulRight
      (Module.finBasis ℝ E m)
  let B : ℝ → E →L[ℝ] E := fun t => ∑ i, ∑ j, ∑ m,
    (Geodesic.chartCoord (E := E) i (v t)
      * nabla.chartConnectionCoeff alpha Y i j m (c t)) • L j m
  have hcoord : ∀ i, ContinuousOn
      (fun t => Geodesic.chartCoord (E := E) i (v t)) s := fun i =>
    (Geodesic.chartCoordFunctional (E := E) i).continuous.comp_continuousOn hv
  have hcoeff : ∀ i j m, ContinuousOn
      (fun t => nabla.chartConnectionCoeff alpha Y i j m (c t)) s := by
    intro i j m
    exact (nabla.chartConnectionCoeff_contMDiffOn alpha Y i j m).continuousOn.comp
      hc (fun t ht => by
        rw [trivializationAt_baseSet_eq_chartAt_source]
        exact hsrc t ht)
  have hB : ContinuousOn B s := by
    dsimp only [B]
    exact continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      continuousOn_finsetSum _ fun m _ =>
        ((hcoord i).mul (hcoeff i j m)).smul continuousOn_const
  refine hB.congr fun t ht => ?_
  ext w
  rw [AffineConnection.chartContractionRightAt_apply,
    nabla.chartContractionAt_eq_sum_chartConnectionCoeff alpha (hsrc t ht) Y
      (hY t ht)]
  simp only [B, L, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Geodesic.chartCoordFunctional_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun m _ => ?_
  module

private theorem LinearODE.exists_isSolOn_value
    {A : ℝ → E →L[ℝ] E} {a b t₀ : ℝ} {K : NNReal}
    (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) (v : E) :
    ∃ V : ℝ → E, LinearODE.IsSolOn A a b V ∧ V t₀ = v := by
  have hsub : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc le_rfl ht₀.2
  have hcontL : ContinuousOn A (Icc a t₀) := hcont.mono hsub
  have hKL : ∀ t ∈ Icc a t₀, ‖A t‖₊ ≤ K := fun t ht => hK t (hsub ht)
  let P : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo
    (LinearODE.flowMap ht₀.1 hcontL hKL)
    (LinearODE.flowMap_injective ht₀.1 hcontL hKL)
  let w : E := P.symm v
  let V : ℝ → E := LinearODE.solOf hab hcont hK w
  let Vleft : ℝ → E := LinearODE.solOf ht₀.1 hcontL hKL w
  have heq : Set.EqOn V Vleft (Icc a t₀) :=
    LinearODE.IsSolOn.eqOn_of_left hKL
      (fun t ht =>
        (LinearODE.solOf_isSolOn hab hcont hK w t (hsub ht)).mono hsub)
      (LinearODE.solOf_isSolOn ht₀.1 hcontL hKL w)
      (by simp only [V, Vleft, LinearODE.solOf_left])
  have hVt₀ : V t₀ = v := by
    rw [heq ⟨ht₀.1, le_rfl⟩]
    change LinearODE.flowMap ht₀.1 hcontL hKL w = v
    change P w = v
    exact P.apply_symm_apply v
  exact ⟨V, LinearODE.solOf_isSolOn hab hcont hK w, hVt₀⟩

/-- **Math.** Prescribed-value existence for an affine-parallel field on a single chart
interval.  Continuity and a norm bound for the linear connection coefficient
are the exact analytic hypotheses consumed by the compact-interval ODE engine. -/
theorem AffineConnection.exists_isParallelFieldAlongOn_of_chart
    (nabla : AffineConnection I M) {c : ℝ → M} (alpha : M)
    {a b t₀ : ℝ} {K : NNReal} (ht₀ : t₀ ∈ Ioo a b)
    (hc : ∀ t ∈ Ioo a b, ContinuousAt c t)
    (hsrc : ∀ t ∈ Ioo a b, c t ∈ (chartAt H alpha).source)
    (hu : ∀ t ∈ Ioo a b,
      DifferentiableAt ℝ (fun s => extChartAt I alpha (c s)) t)
    (hcont : ContinuousOn
      (fun t => -nabla.chartContractionRightAt alpha (c t)
        (deriv (fun s => extChartAt I alpha (c s)) t)) (Icc a b))
    (hK : ∀ t ∈ Icc a b,
      ‖nabla.chartContractionRightAt alpha (c t)
        (deriv (fun s => extChartAt I alpha (c s)) t)‖₊ ≤ K)
    (v : TangentSpace I (c t₀)) :
    ∃ V : ∀ t, TangentSpace I (c t),
      IsRegularFieldAlongOn (I := I) c V (Ioo a b) ∧
      nabla.IsParallelFieldAlongOn c V (Ioo a b) ∧ V t₀ = v := by
  classical
  let u : ℝ → E := fun t => extChartAt I alpha (c t)
  let A : ℝ → E →L[ℝ] E := fun t =>
    -nabla.chartContractionRightAt alpha (c t) (deriv u t)
  have hab : a ≤ b := (lt_trans ht₀.1 ht₀.2).le
  have hKA : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K := fun t ht => by
    rw [show A t = -nabla.chartContractionRightAt alpha (c t) (deriv u t) from rfl]
    simpa only [u, nnnorm_neg] using hK t ht
  obtain ⟨Vcoord, hVsol, hVt₀⟩ := LinearODE.exists_isSolOn_value
    (E := E) hab (Ioo_subset_Icc_self ht₀) hcont hKA
      (tangentCoordChange I (c t₀) alpha (c t₀) v)
  let V : ∀ t, TangentSpace I (c t) := fun t =>
    tangentCoordChange I alpha (c t) (c t) (Vcoord t)
  have hrep : ∀ t ∈ Ioo a b,
      chartFieldRep (I := I) c alpha V t = Vcoord t := by
    intro t ht
    have halpha : c t ∈ (extChartAt I alpha).source := by
      rw [extChartAt_source]
      exact hsrc t ht
    have hself : c t ∈ (extChartAt I (c t)).source :=
      mem_extChartAt_source (I := I) (c t)
    show tangentCoordChange I (c t) alpha (c t)
        (tangentCoordChange I alpha (c t) (c t) (Vcoord t)) = Vcoord t
    rw [tangentCoordChange_comp (I := I) (w := alpha) (x := c t)
      (y := alpha) (z := c t) ⟨⟨halpha, hself⟩, halpha⟩]
    exact tangentCoordChange_self halpha
  have hev : ∀ t ∈ Ioo a b,
      chartFieldRep (I := I) c alpha V =ᶠ[𝓝 t] Vcoord := fun t ht => by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hrep s hs
  have hVcoord : ∀ t ∈ Ioo a b, HasDerivAt Vcoord (A t (Vcoord t)) t :=
    fun t ht => (hVsol t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hVfixed : ∀ t ∈ Ioo a b,
      HasDerivAt (chartFieldRep (I := I) c alpha V) (A t (Vcoord t)) t :=
    fun t ht => (hVcoord t ht).congr_of_eventuallyEq (hev t ht)
  refine ⟨V, ?_, ?_, ?_⟩
  · intro t ht
    exact differentiableAt_chartFieldRep_change (I := I) alpha (c t)
      (hc t ht) (hsrc t ht) (mem_chart_source H (c t)) (hu t ht)
      ((hVfixed t ht).differentiableAt)
  · intro t ht
    have hfixed := (hVfixed t ht).differentiableAt
    rw [nabla.covDerivAlong_eq_chart alpha (hc t ht) (hsrc t ht)
      (hu t ht) hfixed, AffineConnection.covDerivAlongInChart,
      (hVfixed t ht).deriv, hrep t ht]
    change tangentCoordChange I alpha (c t) (c t)
      (A t (Vcoord t) +
        nabla.chartContractionAt alpha (c t) (deriv u t) (Vcoord t)) = 0
    rw [show A t (Vcoord t) =
        -nabla.chartContractionAt alpha (c t) (deriv u t) (Vcoord t) by rfl,
      neg_add_cancel, map_zero]
  · change tangentCoordChange I alpha (c t₀) (c t₀) (Vcoord t₀) = v
    rw [hVt₀,
      tangentCoordChange_comp (I := I) (w := c t₀) (x := alpha)
        (y := c t₀) (z := c t₀)
        ⟨⟨mem_extChartAt_source (I := I) (c t₀),
          by rw [extChartAt_source]; exact hsrc t₀ ht₀⟩,
          mem_extChartAt_source (I := I) (c t₀)⟩]
    exact tangentCoordChange_self (mem_extChartAt_source (I := I) (c t₀))

/-- **Math.** The single-chart ODE construction realizes every prescribed fibre value
on the open interval. -/
theorem AffineConnection.hasParallelFieldRealizationAlongOn_of_chart
    (nabla : AffineConnection I M) {c : ℝ → M} (alpha : M)
    {a b : ℝ} {K : NNReal}
    (hc : ∀ t ∈ Ioo a b, ContinuousAt c t)
    (hsrc : ∀ t ∈ Ioo a b, c t ∈ (chartAt H alpha).source)
    (hu : ∀ t ∈ Ioo a b,
      DifferentiableAt ℝ (fun s => extChartAt I alpha (c s)) t)
    (hcont : ContinuousOn
      (fun t => -nabla.chartContractionRightAt alpha (c t)
        (deriv (fun s => extChartAt I alpha (c s)) t)) (Icc a b))
    (hK : ∀ t ∈ Icc a b,
      ‖nabla.chartContractionRightAt alpha (c t)
        (deriv (fun s => extChartAt I alpha (c s)) t)‖₊ ≤ K) :
    nabla.HasParallelFieldRealizationAlongOn c (Ioo a b) := by
  intro t ht v
  exact nabla.exists_isParallelFieldAlongOn_of_chart alpha ht hc hsrc hu hcont hK v

/-- **Math.** Every tangent direction admits a local integral-curve chart interval on
which the arbitrary affine connection has prescribed-value parallel fields.
This is the local ODE realization needed for the converse in Proposition 3.2. -/
theorem AffineConnection.exists_integralCurve_parallelFieldRealization
    (nabla : AffineConnection I M) (X : SmoothVectorField I M) (p : M) :
    ∃ (c : ℝ → M) (eps : ℝ), 0 < eps ∧ c 0 = p ∧
      (∀ t ∈ Icc (-eps) eps,
        HasMFDerivAt 𝓘(ℝ, ℝ) I c t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c t)))) ∧
      nabla.HasParallelFieldRealizationAlongOn c (Ioo (-eps) eps) := by
  classical
  obtain ⟨c, hc0, hcint⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I) (M := M) (v := X.toFun) (t₀ := (0 : ℝ)) (x₀ := p)
      ((X.smooth p).of_le (by norm_num))
  let Y : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun i => chartFrameFieldAt (I := I) p p i
  have hframe : ∀ᶠ q in 𝓝 p, ∀ i, Y i q =
      Tensor.chartBasisVecFiber (I := I) p i q :=
    Filter.eventually_all.mpr fun i =>
      chartFrameFieldAt_eventuallyEq (I := I) p (mem_chart_source H p) i
  have hgood : ∀ᶠ q in 𝓝 p,
      q ∈ (chartAt H p).source ∧
        ∀ i, Y i q = Tensor.chartBasisVecFiber (I := I) p i q :=
    ((chartAt H p).open_source.eventually_mem (mem_chart_source H p)).and hframe
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp hgood
  have hcU : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ U :=
    hcint.continuousAt.eventually_mem
      (hUopen.mem_nhds (by rwa [hc0]))
  have hcint' : {t | HasMFDerivAt 𝓘(ℝ, ℝ) I c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c t)))} ∈ 𝓝 (0 : ℝ) := hcint
  obtain ⟨eps₁, heps₁, heps₁sub⟩ := Metric.mem_nhds_iff.mp hcint'
  have hcU' : {t | c t ∈ U} ∈ 𝓝 (0 : ℝ) := hcU
  obtain ⟨eps₂, heps₂, heps₂sub⟩ := Metric.mem_nhds_iff.mp hcU'
  let eps : ℝ := min eps₁ eps₂ / 2
  have hepsMin : 0 < min eps₁ eps₂ := lt_min heps₁ heps₂
  have heps : 0 < eps := div_pos hepsMin (by norm_num)
  have heps_lt₁ : eps < eps₁ := by
    dsimp only [eps]
    have : min eps₁ eps₂ / 2 < min eps₁ eps₂ := by linarith
    exact this.trans_le (min_le_left _ _)
  have heps_lt₂ : eps < eps₂ := by
    dsimp only [eps]
    have : min eps₁ eps₂ / 2 < min eps₁ eps₂ := by linarith
    exact this.trans_le (min_le_right _ _)
  have hIcc_ball : ∀ {r : ℝ}, eps < r → Icc (-eps) eps ⊆ Metric.ball 0 r := by
    intro r her t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩).trans_lt her
  have hcurve : ∀ t ∈ Icc (-eps) eps,
      HasMFDerivAt 𝓘(ℝ, ℝ) I c t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c t))) :=
    fun t ht => heps₁sub (hIcc_ball heps_lt₁ ht)
  have hmemU : ∀ t ∈ Icc (-eps) eps, c t ∈ U :=
    fun t ht => heps₂sub (hIcc_ball heps_lt₂ ht)
  have hsrc : ∀ t ∈ Icc (-eps) eps, c t ∈ (chartAt H p).source :=
    fun t ht => (hUsub (hmemU t ht)).1
  have hY : ∀ t ∈ Icc (-eps) eps, ∀ i, ⇑(Y i) =ᶠ[𝓝 (c t)]
      fun q => Tensor.chartBasisVecFiber (I := I) p i q := by
    intro t ht i
    filter_upwards [hUopen.mem_nhds (hmemU t ht)] with q hq
    exact (hUsub hq).2 i
  let vel : ℝ → E := fun t => ∑ i,
    chartVectorFieldCoeff (I := I) p X i (c t) • (Module.finBasis ℝ E i : E)
  have hcOn : ContinuousOn c (Icc (-eps) eps) := fun t ht =>
    (hcurve t ht).continuousAt.continuousWithinAt
  have hvel : ContinuousOn vel (Icc (-eps) eps) := by
    dsimp only [vel]
    exact continuousOn_finsetSum _ fun i _ =>
      ((chartVectorFieldCoeff_contMDiffOn (I := I) p X i).continuousOn.comp
        hcOn (fun t ht => by
          rw [trivializationAt_baseSet_eq_chartAt_source]
          exact hsrc t ht)).smul continuousOn_const
  let u : ℝ → E := fun t => extChartAt I p (c t)
  have huDeriv : ∀ t ∈ Icc (-eps) eps, deriv u t = vel t := by
    intro t ht
    have hsrc' : c t ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hsrc t ht
    have hd := hasDerivAt_extChartAt_comp_of_hasMFDerivAt_DC
      (I := I) (hcurve t ht) hsrc'
    let L : TangentSpace I (c t) →L[ℝ] E :=
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (c t)
    have hL : L = tangentCoordChange I (c t) p (c t) := by
      dsimp [L]
      rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (hsrc t ht)]
    have hcoord : tangentCoordChange I (c t) p (c t) (X (c t)) = vel t := by
      calc
        tangentCoordChange I (c t) p (c t) (X (c t)) = L (X (c t)) := by
          exact (congrArg (fun F : TangentSpace I (c t) →L[ℝ] E => F (X (c t))) hL).symm
        _ = L (∑ i,
              chartVectorFieldCoeff (I := I) p X i (c t) •
                Tensor.chartBasisVecFiber (I := I) p i (c t)) :=
          congrArg L
            (vectorField_eq_sum_chartCoeff (I := I) p X (hsrc t ht))
        _ = ∑ i, L (chartVectorFieldCoeff (I := I) p X i (c t) •
              Tensor.chartBasisVecFiber (I := I) p i (c t)) :=
          map_sum L _ Finset.univ
        _ = ∑ i, chartVectorFieldCoeff (I := I) p X i (c t) •
              L (Tensor.chartBasisVecFiber (I := I) p i (c t)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact map_smul L _ _
        _ = vel t := by
          rw [show vel t = ∑ i, chartVectorFieldCoeff (I := I) p X i (c t) •
              (Module.finBasis ℝ E i : E) from rfl]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hLi : L (Tensor.chartBasisVecFiber (I := I) p i (c t)) =
              (Module.finBasis ℝ E i : E) := by
            calc
              L (Tensor.chartBasisVecFiber (I := I) p i (c t)) =
                  tangentCoordChange I (c t) p (c t)
                    (Tensor.chartBasisVecFiber (I := I) p i (c t)) :=
                congrArg (fun F : TangentSpace I (c t) →L[ℝ] E =>
                  F (Tensor.chartBasisVecFiber (I := I) p i (c t))) hL
              _ = (Module.finBasis ℝ E i : E) :=
                tangentCoordChange_chartBasisVecFiber (I := I) p (hsrc t ht) i
          exact congrArg (fun z : E =>
            chartVectorFieldCoeff (I := I) p X i (c t) • z) hLi
    exact hd.deriv.trans hcoord
  have hcont₀ := nabla.continuousOn_chartContractionRightAt_of_frame p Y hcOn hvel
    hsrc hY
  have hcontPos : ContinuousOn
      (fun t => nabla.chartContractionRightAt p (c t) (deriv u t))
      (Icc (-eps) eps) :=
    hcont₀.congr (fun t ht => by rw [huDeriv t ht])
  have hcont : ContinuousOn
      (fun t => -nabla.chartContractionRightAt p (c t) (deriv u t))
      (Icc (-eps) eps) := hcontPos.neg
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontPos
  let K : NNReal := ⟨max 1 C, le_trans zero_le_one (le_max_left _ _)⟩
  have hK : ∀ t ∈ Icc (-eps) eps,
      ‖nabla.chartContractionRightAt p (c t) (deriv u t)‖₊ ≤ K := by
    intro t ht
    rw [← NNReal.coe_le_coe]
    change ‖nabla.chartContractionRightAt p (c t) (deriv u t)‖ ≤ max 1 C
    exact (hC t ht).trans (le_max_right _ _)
  have hcInt : ∀ t ∈ Ioo (-eps) eps, ContinuousAt c t :=
    fun t ht => (hcurve t (Ioo_subset_Icc_self ht)).continuousAt
  have hsrcInt : ∀ t ∈ Ioo (-eps) eps,
      c t ∈ (chartAt H p).source :=
    fun t ht => hsrc t (Ioo_subset_Icc_self ht)
  have huInt : ∀ t ∈ Ioo (-eps) eps,
      DifferentiableAt ℝ (fun s => extChartAt I p (c s)) t := fun t ht =>
    (hasDerivAt_extChartAt_comp_of_hasMFDerivAt_DC (I := I)
      (hcurve t (Ioo_subset_Icc_self ht))
      (by rw [extChartAt_source]; exact hsrcInt t ht)).differentiableAt
  refine ⟨c, eps, heps, hc0, hcurve, ?_⟩
  exact nabla.hasParallelFieldRealizationAlongOn_of_chart p hcInt hsrcInt huInt
    hcont hK

/-- **Math.** The metric product rule for one fixed curve. -/
def AffineConnection.HasMetricProductRuleAlongCurve
    (nabla : AffineConnection I M) (g : RiemannianMetric I M)
    (c : ℝ → M) : Prop :=
  ∀ (t : ℝ), MDifferentiableAt 𝓘(ℝ, ℝ) I c t →
    ∀ (V W : ∀ s, TangentSpace I (c s)),
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t →
      DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t →
      HasDerivAt (fun s => g.metricInner (c s) (V s) (W s))
        (g.metricInner (c t) (nabla.covDerivAlong c V t) (W t)
          + g.metricInner (c t) (V t) (nabla.covDerivAlong c W t)) t

/-- **Math.** The intrinsic product-rule formulation of metric compatibility
for an arbitrary affine connection, quantified over all curves. -/
def AffineConnection.HasMetricProductRuleAlong
    (nabla : AffineConnection I M) (g : RiemannianMetric I M) : Prop :=
  ∀ c : ℝ → M, nabla.HasMetricProductRuleAlongCurve g c

/-- **Math.** do Carmo Ch. 2, Corollary 3.3: the ambient field identity
`X g(Y,Z) = g(nabla_X Y,Z) + g(Y,nabla_X Z)` is equivalent to the full
intrinsic product rule along curves.

For the forward implication, ambient fields extending the velocity and the two
along-field values are subtracted off.  The remainders vanish at the point, so
their along derivatives are independent of the connection.  The reverse
implication tests the curve rule on restrictions of ambient fields along a
local integral curve of `X`. -/
theorem AffineConnection.isMetricCompatible_iff_hasMetricProductRuleAlong
    (nabla : AffineConnection I M) (g : RiemannianMetric I M) :
    nabla.IsMetricCompatible g ↔ nabla.HasMetricProductRuleAlong g := by
  classical
  constructor
  · intro hcompat c t hc V W hV hW
    obtain ⟨X, hX⟩ :=
      exists_smoothVectorField_eq (I := I) (c t) (DCVelocity (I := I) c t)
    obtain ⟨Y, hY⟩ := exists_smoothVectorField_eq (I := I) (c t) (V t)
    obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eq (I := I) (c t) (W t)
    let P : ∀ s, TangentSpace I (c s) := fun s => Y (c s)
    let Q : ∀ s, TangentSpace I (c s) := fun s => Z (c s)
    let U : ∀ s, TangentSpace I (c s) := fun s => V s - P s
    let R : ∀ s, TangentSpace I (c s) := fun s => W s - Q s
    have hP : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) P) t :=
      differentiableAt_chartFieldRep_comp_smoothVectorField_of_mdifferentiableAt
        (I := I) Y hc
    have hQ : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) Q) t :=
      differentiableAt_chartFieldRep_comp_smoothVectorField_of_mdifferentiableAt
        (I := I) Z hc
    have hU : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) U) t := by
      rw [show U = fun s => V s - P s from rfl, chartFieldRep_sub]
      exact hV.sub hP
    have hR : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) R) t := by
      rw [show R = fun s => W s - Q s from rfl, chartFieldRep_sub]
      exact hW.sub hQ
    have hUt : U t = 0 := by
      change V t - Y (c t) = 0
      rw [hY, sub_self]
    have hRt : R t = 0 := by
      change W t - Z (c t) = 0
      rw [hZ, sub_self]
    have hnU := nabla.covDerivAlong_sub c V P hV hP
    have hnR := nabla.covDerivAlong_sub c W Q hW hQ
    have hlU := g.leviCivitaConnection.covDerivAlong_sub c V P hV hP
    have hlR := g.leviCivitaConnection.covDerivAlong_sub c W Q hW hQ
    simp only [g.leviCivita_covDerivAlong_eq] at hlU hlR
    have hzeroU : nabla.covDerivAlong c U t = Riemannian.covDerivAlong (I := I) g c U t := by
      calc
        nabla.covDerivAlong c U t =
            g.leviCivitaConnection.covDerivAlong c U t :=
          nabla.covDerivAlong_eq_of_field_eq_zero
            g.leviCivitaConnection c U hUt
        _ = Riemannian.covDerivAlong (I := I) g c U t :=
          g.leviCivita_covDerivAlong_eq c U t
    have hzeroR : nabla.covDerivAlong c R t = Riemannian.covDerivAlong (I := I) g c R t := by
      calc
        nabla.covDerivAlong c R t =
            g.leviCivitaConnection.covDerivAlong c R t :=
          nabla.covDerivAlong_eq_of_field_eq_zero
            g.leviCivitaConnection c R hRt
        _ = Riemannian.covDerivAlong (I := I) g c R t :=
          g.leviCivita_covDerivAlong_eq c R t
    have hnP := nabla.covDerivAlong_comp_smoothVectorField hc X Y hX
    have hnQ := nabla.covDerivAlong_comp_smoothVectorField hc X Z hX
    have hlP := Riemannian.covDerivAlong_comp_smoothVectorField (I := I) g hc X Y hX
    have hlQ := Riemannian.covDerivAlong_comp_smoothVectorField (I := I) g hc X Z hX
    have hDV : nabla.covDerivAlong c V t =
        Riemannian.covDerivAlong (I := I) g c V t
          + ((nabla.cov X Y) (c t)
            - (g.leviCivitaConnection.cov X Y) (c t)) := by
      calc
        nabla.covDerivAlong c V t =
            nabla.covDerivAlong c U t + nabla.covDerivAlong c P t := by
          rw [hnU]
          abel
        _ = Riemannian.covDerivAlong (I := I) g c U t
            + nabla.covDerivAlong c P t := by rw [hzeroU]
        _ = (Riemannian.covDerivAlong (I := I) g c V t
              - Riemannian.covDerivAlong (I := I) g c P t)
            + nabla.covDerivAlong c P t := by rw [hlU]
        _ = Riemannian.covDerivAlong (I := I) g c V t
            + (nabla.covDerivAlong c P t
              - Riemannian.covDerivAlong (I := I) g c P t) := by abel
        _ = _ := by rw [hnP, hlP]
    have hDW : nabla.covDerivAlong c W t =
        Riemannian.covDerivAlong (I := I) g c W t
          + ((nabla.cov X Z) (c t)
            - (g.leviCivitaConnection.cov X Z) (c t)) := by
      calc
        nabla.covDerivAlong c W t =
            nabla.covDerivAlong c R t + nabla.covDerivAlong c Q t := by
          rw [hnR]
          abel
        _ = Riemannian.covDerivAlong (I := I) g c R t
            + nabla.covDerivAlong c Q t := by rw [hzeroR]
        _ = (Riemannian.covDerivAlong (I := I) g c W t
              - Riemannian.covDerivAlong (I := I) g c Q t)
            + nabla.covDerivAlong c Q t := by rw [hlR]
        _ = Riemannian.covDerivAlong (I := I) g c W t
            + (nabla.covDerivAlong c Q t
              - Riemannian.covDerivAlong (I := I) g c Q t) := by abel
        _ = _ := by rw [hnQ, hlQ]
    have hLC : g.leviCivitaConnection.IsMetricCompatible g :=
      (g.leviCivitaConnection.isLeviCivita_of_koszulDual g
        (fun A B C p => g.koszulDualSection_dual A B C p)).2
    have hskew :
        g.metricInner (c t)
            ((nabla.cov X Y) (c t)
              - (g.leviCivitaConnection.cov X Y) (c t)) (W t)
          + g.metricInner (c t) (V t)
            ((nabla.cov X Z) (c t)
              - (g.leviCivitaConnection.cov X Z) (c t)) = 0 := by
      have hn := hcompat X Y Z (c t)
      have hl := hLC X Y Z (c t)
      rw [g.metricInner_sub_left, g.metricInner_sub_right, ← hY, ← hZ]
      linarith
    have hlevi := hasDerivAt_metricInner_along_of_mdifferentiableAt
      (I := I) g hc hV hW
    refine hlevi.congr_deriv ?_
    rw [hDV, hDW, g.metricInner_add_left, g.metricInner_add_right]
    linarith
  · intro hproduct X Y Z p
    obtain ⟨c, hc0, hcint⟩ :=
      exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
        (I := I) (M := M) (v := X.toFun) (t₀ := (0 : ℝ)) (x₀ := p)
        ((X.smooth p).of_le (by norm_num))
    have hcurve := hcint.hasMFDerivAt
    have hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c 0 := hcurve.mdifferentiableAt
    have hvel : X (c 0) = DCVelocity (I := I) c 0 := by
      have happ := congrArg (fun L => L (1 : ℝ)) hcurve.mfderiv
      calc
        X (c 0) = ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c 0))) (1 : ℝ) := by
          rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
        _ = DCVelocity (I := I) c 0 := by
          exact happ.symm
    have hY : DifferentiableAt ℝ
        (chartFieldRep (I := I) c (c 0) (fun s => Y (c s))) 0 :=
      differentiableAt_chartFieldRep_comp_smoothVectorField_of_mdifferentiableAt
        (I := I) Y hc
    have hZ : DifferentiableAt ℝ
        (chartFieldRep (I := I) c (c 0) (fun s => Z (c s))) 0 :=
      differentiableAt_chartFieldRep_comp_smoothVectorField_of_mdifferentiableAt
        (I := I) Z hc
    have hprod := hproduct c 0 hc (fun s => Y (c s)) (fun s => Z (c s)) hY hZ
    have hchain := hasDerivAt_comp_curve_DC (I := I)
      ((g.metricInner_field_contMDiff Y Z).mdifferentiableAt (by norm_num)) hc
    have huniq := hchain.unique hprod
    have hdir :
        mfderiv I 𝓘(ℝ, ℝ) (fun q => g.metricInner q (Y q) (Z q))
            (c 0) (DCVelocity (I := I) c 0)
          = X.dir (fun q => g.metricInner q (Y q) (Z q)) p := by
      rw [← hvel, hc0]
      rfl
    have hcovY := nabla.covDerivAlong_comp_smoothVectorField hc X Y hvel
    have hcovZ := nabla.covDerivAlong_comp_smoothVectorField hc X Z hvel
    rw [hdir, hcovY, hcovZ, hc0] at huniq
    exact huniq

/-- **Math.** A field is parallel for `nabla` along the whole parameter line when its
intrinsic affine covariant derivative vanishes everywhere. -/
def AffineConnection.IsParallelFieldAlong
    (nabla : AffineConnection I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) : Prop :=
  ∀ t, nabla.covDerivAlong c V t = 0

/-- **Math.** do Carmo Ch. 2, Definition 3.1 on a fixed curve: the pairing of
any two regular parallel fields is constant. -/
def AffineConnection.PreservesMetricAlongCurve
    (nabla : AffineConnection I M) (g : RiemannianMetric I M)
    (c : ℝ → M) : Prop :=
  ∀ (V W : ∀ t, TangentSpace I (c t)),
    IsRegularFieldAlong (I := I) c V → IsRegularFieldAlong (I := I) c W →
    nabla.IsParallelFieldAlong c V → nabla.IsParallelFieldAlong c W →
    ∀ s t, g.metricInner (c s) (V s) (W s) =
      g.metricInner (c t) (V t) (W t)

/-- **Math.** Prescribed values can be realized by regular parallel fields along `c`.
This is the precise ODE input in the reverse implication of do Carmo
Proposition 3.2. -/
def AffineConnection.HasParallelFieldRealizationAlong
    (nabla : AffineConnection I M) (c : ℝ → M) : Prop :=
  ∀ (t : ℝ) (v : TangentSpace I (c t)),
    ∃ V : ∀ s, TangentSpace I (c s),
      IsRegularFieldAlong (I := I) c V ∧
      nabla.IsParallelFieldAlong c V ∧ V t = v

/-- **Math.** do Carmo Definition 3.1, interval form: every pair of regular
parallel fields has constant metric pairing on `s`. -/
def AffineConnection.PreservesMetricAlongOn
    (nabla : AffineConnection I M) (g : RiemannianMetric I M)
    (c : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ (V W : ∀ t, TangentSpace I (c t)),
    IsRegularFieldAlongOn (I := I) c V s →
    IsRegularFieldAlongOn (I := I) c W s →
    nabla.IsParallelFieldAlongOn c V s →
    nabla.IsParallelFieldAlongOn c W s →
    ∀ u ∈ s, ∀ v ∈ s,
      g.metricInner (c u) (V u) (W u) = g.metricInner (c v) (V v) (W v)

/-- **Math.** do Carmo Definition 3.1 for an affine connection: parallel
translation preserves the metric on every open parameter interval. -/
def AffineConnection.PreservesMetricUnderParallelTransport
    (nabla : AffineConnection I M) (g : RiemannianMetric I M) : Prop :=
  ∀ (c : ℝ → M) (a b : ℝ),
    (∀ t ∈ Ioo a b, MDifferentiableAt 𝓘(ℝ, ℝ) I c t) →
    nabla.PreservesMetricAlongOn g c (Ioo a b)

/-- **Math.** The product rule implies interval-wise metric preservation for parallel
fields. -/
theorem AffineConnection.HasMetricProductRuleAlongCurve.preservesMetricAlongOn
    {nabla : AffineConnection I M} {g : RiemannianMetric I M} {c : ℝ → M}
    (hproduct : nabla.HasMetricProductRuleAlongCurve g c)
    {s : Set ℝ} (hsOpen : IsOpen s) (hsConn : IsPreconnected s)
    (hc : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    nabla.PreservesMetricAlongOn g c s := by
  intro V W hV hW hVp hWp u hu v hv
  let f : ℝ → ℝ := fun r => g.metricInner (c r) (V r) (W r)
  have hf : ∀ r ∈ s, HasDerivAt f 0 r := fun r hr => by
    have h := hproduct r (hc r hr) V W (hV r hr) (hW r hr)
    simpa only [hVp r hr, hWp r hr, g.metricInner_zero_left,
      g.metricInner_zero_right, zero_add] using h
  exact hsOpen.is_const_of_deriv_eq_zero hsConn
    (fun r hr => (hf r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hf r hr).deriv) hu hv

/-- **Math.** Interval form of do Carmo Proposition 3.2.  The only analytic input in the
reverse implication is prescribed-value realization for the parallel ODE. -/
theorem AffineConnection.preservesMetricAlongOn_iff_hasMetricProductRuleAlongOn_of_realization
    (nabla : AffineConnection I M) (g : RiemannianMetric I M)
    {c : ℝ → M} {s : Set ℝ} (hsOpen : IsOpen s)
    (hsConn : IsPreconnected s)
    (hc : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hrealize : nabla.HasParallelFieldRealizationAlongOn c s) :
    nabla.PreservesMetricAlongOn g c s ↔
      nabla.HasMetricProductRuleAlongOn g c s := by
  constructor
  · intro hpres t ht hct V W hV hW
    obtain ⟨P, hP, hPp, hPt⟩ := hrealize t ht (V t)
    obtain ⟨Q, hQ, hQp, hQt⟩ := hrealize t ht (W t)
    let U : ∀ r, TangentSpace I (c r) := fun r => V r - P r
    let R : ∀ r, TangentSpace I (c r) := fun r => W r - Q r
    have hU : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) U) t := by
      rw [show U = fun r => V r - P r from rfl, chartFieldRep_sub]
      exact hV.sub (hP t ht)
    have hR : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) R) t := by
      rw [show R = fun r => W r - Q r from rfl, chartFieldRep_sub]
      exact hW.sub (hQ t ht)
    have hUt : U t = 0 := by
      change V t - P t = 0
      rw [hPt, sub_self]
    have hRt : R t = 0 := by
      change W t - Q t = 0
      rw [hQt, sub_self]
    have hDU : Riemannian.covDerivAlong (I := I) g c U t =
        nabla.covDerivAlong c V t := by
      have hnU := nabla.covDerivAlong_sub c V P hV (hP t ht)
      calc
        Riemannian.covDerivAlong (I := I) g c U t =
            g.leviCivitaConnection.covDerivAlong c U t :=
          (g.leviCivita_covDerivAlong_eq c U t).symm
        _ = nabla.covDerivAlong c U t :=
          (nabla.covDerivAlong_eq_of_field_eq_zero
            g.leviCivitaConnection c U hUt).symm
        _ = nabla.covDerivAlong c V t - nabla.covDerivAlong c P t := hnU
        _ = nabla.covDerivAlong c V t := by rw [hPp t ht, sub_zero]
    have hDR : Riemannian.covDerivAlong (I := I) g c R t =
        nabla.covDerivAlong c W t := by
      have hnR := nabla.covDerivAlong_sub c W Q hW (hQ t ht)
      calc
        Riemannian.covDerivAlong (I := I) g c R t =
            g.leviCivitaConnection.covDerivAlong c R t :=
          (g.leviCivita_covDerivAlong_eq c R t).symm
        _ = nabla.covDerivAlong c R t :=
          (nabla.covDerivAlong_eq_of_field_eq_zero
            g.leviCivitaConnection c R hRt).symm
        _ = nabla.covDerivAlong c W t - nabla.covDerivAlong c Q t := hnR
        _ = nabla.covDerivAlong c W t := by rw [hQp t ht, sub_zero]
    have hPQ : HasDerivAt
        (fun r => g.metricInner (c r) (P r) (Q r)) 0 t := by
      have heq : (fun r => g.metricInner (c r) (P r) (Q r)) =ᶠ[𝓝 t]
          fun _ => g.metricInner (c t) (P t) (Q t) := by
        filter_upwards [hsOpen.mem_nhds ht] with r hr
        exact hpres P Q hP hQ hPp hQp r hr t ht
      exact (hasDerivAt_const t
        (g.metricInner (c t) (P t) (Q t))).congr_of_eventuallyEq heq
    have hUQ0 := hasDerivAt_metricInner_along_of_mdifferentiableAt
      (I := I) g hct hU (hQ t ht)
    have hUQ : HasDerivAt
        (fun r => g.metricInner (c r) (U r) (Q r))
        (g.metricInner (c t) (nabla.covDerivAlong c V t) (W t)) t := by
      simpa only [hDU, hUt, hQt, g.metricInner_zero_left, add_zero] using hUQ0
    have hVR0 := hasDerivAt_metricInner_along_of_mdifferentiableAt
      (I := I) g hct hV hR
    have hVR : HasDerivAt
        (fun r => g.metricInner (c r) (V r) (R r))
        (g.metricInner (c t) (V t) (nabla.covDerivAlong c W t)) t := by
      simpa only [hDR, hRt, g.metricInner_zero_right, zero_add] using hVR0
    have hsum := (hPQ.add hUQ).add hVR
    have heq : (fun r => g.metricInner (c r) (V r) (W r)) =
        fun r => (g.metricInner (c r) (P r) (Q r)
          + g.metricInner (c r) (U r) (Q r))
          + g.metricInner (c r) (V r) (R r) := by
      funext r
      simp only [U, R, g.metricInner_sub_left, g.metricInner_sub_right]
      ring
    exact (hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun r => congrFun heq r))).congr_deriv (by
        simp)
  · intro hproduct V W hV hW hVp hWp u hu v hv
    let f : ℝ → ℝ := fun r => g.metricInner (c r) (V r) (W r)
    have hf : ∀ r ∈ s, HasDerivAt f 0 r := fun r hr => by
      have h := hproduct r hr (hc r hr) V W (hV r hr) (hW r hr)
      simpa only [hVp r hr, hWp r hr, g.metricInner_zero_left,
        g.metricInner_zero_right, zero_add] using h
    exact hsOpen.is_const_of_deriv_eq_zero hsConn
      (fun r hr => (hf r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hf r hr).deriv) hu hv

/-- **Math.** The intrinsic product rule implies do Carmo's parallel-translation
definition of metric compatibility. -/
theorem AffineConnection.HasMetricProductRuleAlong.preservesMetricUnderParallelTransport
    {nabla : AffineConnection I M} {g : RiemannianMetric I M}
    (hproduct : nabla.HasMetricProductRuleAlong g) :
    nabla.PreservesMetricUnderParallelTransport g := by
  intro c a b hc
  exact (hproduct c).preservesMetricAlongOn isOpen_Ioo isPreconnected_Ioo hc

/-- **Math.** do Carmo Ch. 2, Definition 3.1 and Corollary 3.3: preservation
of the metric by parallel translation is equivalent to the ambient field
compatibility identity, with no transport-realization hypothesis in the public
statement.  Local realization is supplied internally by the single-chart
linear ODE construction. -/
theorem AffineConnection.preservesMetricUnderParallelTransport_iff_isMetricCompatible
    (nabla : AffineConnection I M) (g : RiemannianMetric I M) :
    nabla.PreservesMetricUnderParallelTransport g ↔
      nabla.IsMetricCompatible g := by
  constructor
  · intro hpres X Y Z p
    obtain ⟨c, eps, heps, hc0, hcurve, hrealize⟩ :=
      nabla.exists_integralCurve_parallelFieldRealization X p
    have hzero : (0 : ℝ) ∈ Ioo (-eps) eps := by constructor <;> linarith
    have hc : ∀ t ∈ Ioo (-eps) eps,
        MDifferentiableAt 𝓘(ℝ, ℝ) I c t := fun t ht =>
      (hcurve t (Ioo_subset_Icc_self ht)).mdifferentiableAt
    have hpresCurve := hpres c (-eps) eps hc
    have hproduct : nabla.HasMetricProductRuleAlongOn g c (Ioo (-eps) eps) :=
      (nabla.preservesMetricAlongOn_iff_hasMetricProductRuleAlongOn_of_realization
        g isOpen_Ioo isPreconnected_Ioo hc hrealize).mp hpresCurve
    have hc0diff : MDifferentiableAt 𝓘(ℝ, ℝ) I c 0 := hc 0 hzero
    have hvel : X (c 0) = DCVelocity (I := I) c 0 := by
      have hcurve0 := hcurve 0 (Ioo_subset_Icc_self hzero)
      have happ := congrArg (fun L => L (1 : ℝ)) hcurve0.mfderiv
      calc
        X (c 0) = ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c 0))) (1 : ℝ) := by
          rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
        _ = DCVelocity (I := I) c 0 := by
          exact happ.symm
    have hY : DifferentiableAt ℝ
        (chartFieldRep (I := I) c (c 0) (fun t => Y (c t))) 0 :=
      differentiableAt_chartFieldRep_comp_smoothVectorField_of_mdifferentiableAt
        (I := I) Y hc0diff
    have hZ : DifferentiableAt ℝ
        (chartFieldRep (I := I) c (c 0) (fun t => Z (c t))) 0 :=
      differentiableAt_chartFieldRep_comp_smoothVectorField_of_mdifferentiableAt
        (I := I) Z hc0diff
    have hprod := hproduct 0 hzero hc0diff
      (fun t => Y (c t)) (fun t => Z (c t)) hY hZ
    have hchain := hasDerivAt_comp_curve_DC (I := I)
      ((g.metricInner_field_contMDiff Y Z).mdifferentiableAt (by norm_num))
      hc0diff
    have huniq := hchain.unique hprod
    have hdir :
        mfderiv I 𝓘(ℝ, ℝ) (fun q => g.metricInner q (Y q) (Z q))
            (c 0) (DCVelocity (I := I) c 0)
          = X.dir (fun q => g.metricInner q (Y q) (Z q)) p := by
      rw [← hvel, hc0]
      rfl
    have hcovY := nabla.covDerivAlong_comp_smoothVectorField hc0diff X Y hvel
    have hcovZ := nabla.covDerivAlong_comp_smoothVectorField hc0diff X Z hvel
    rw [hdir, hcovY, hcovZ, hc0] at huniq
    exact huniq
  · intro hcompat
    exact AffineConnection.HasMetricProductRuleAlong.preservesMetricUnderParallelTransport
      ((nabla.isMetricCompatible_iff_hasMetricProductRuleAlong g).mp hcompat)

/-- **Math.** do Carmo Proposition 3.2: the intrinsic product rule is
equivalent to constancy of the metric pairing of parallel fields, interval by
interval. -/
theorem AffineConnection.preservesMetricUnderParallelTransport_iff_hasMetricProductRuleAlong
    (nabla : AffineConnection I M) (g : RiemannianMetric I M) :
    nabla.PreservesMetricUnderParallelTransport g ↔
      nabla.HasMetricProductRuleAlong g :=
  (nabla.preservesMetricUnderParallelTransport_iff_isMetricCompatible g).trans
    (nabla.isMetricCompatible_iff_hasMetricProductRuleAlong g)

/-- **Math.** A metric product rule makes the pairing of parallel fields constant. -/
theorem AffineConnection.HasMetricProductRuleAlongCurve.preservesMetricAlongCurve
    {nabla : AffineConnection I M} {g : RiemannianMetric I M} {c : ℝ → M}
    (hproduct : nabla.HasMetricProductRuleAlongCurve g c)
    (hc : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    nabla.PreservesMetricAlongCurve g c := by
  intro V W hV hW hVp hWp s t
  let f : ℝ → ℝ := fun r => g.metricInner (c r) (V r) (W r)
  have hf : ∀ r, HasDerivAt f 0 r := fun r => by
    have h := hproduct r (hc r) V W (hV r) (hW r)
    simpa only [hVp r, hWp r, g.metricInner_zero_left,
      g.metricInner_zero_right, zero_add] using h
  exact is_const_of_deriv_eq_zero (fun r => (hf r).differentiableAt)
    (fun r => (hf r).deriv) s t

/-- **Math.** do Carmo Ch. 2, Proposition 3.2 on a fixed curve.  Metric
preservation for parallel fields is equivalent to the product rule whenever
the connection's parallel ODE realizes every prescribed fibre value. -/
theorem AffineConnection.preservesMetricAlongCurve_iff_hasMetricProductRuleAlongCurve_of_realization
    (nabla : AffineConnection I M) (g : RiemannianMetric I M) {c : ℝ → M}
    (hc : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hrealize : nabla.HasParallelFieldRealizationAlong c) :
    nabla.PreservesMetricAlongCurve g c ↔
      nabla.HasMetricProductRuleAlongCurve g c := by
  constructor
  · intro hpres t hct V W hV hW
    obtain ⟨P, hP, hPp, hPt⟩ := hrealize t (V t)
    obtain ⟨Q, hQ, hQp, hQt⟩ := hrealize t (W t)
    let U : ∀ s, TangentSpace I (c s) := fun s => V s - P s
    let R : ∀ s, TangentSpace I (c s) := fun s => W s - Q s
    have hU : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) U) t := by
      rw [show U = fun s => V s - P s from rfl, chartFieldRep_sub]
      exact hV.sub (hP t)
    have hR : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) R) t := by
      rw [show R = fun s => W s - Q s from rfl, chartFieldRep_sub]
      exact hW.sub (hQ t)
    have hUt : U t = 0 := by
      change V t - P t = 0
      rw [hPt, sub_self]
    have hRt : R t = 0 := by
      change W t - Q t = 0
      rw [hQt, sub_self]
    have hDU : Riemannian.covDerivAlong (I := I) g c U t =
        nabla.covDerivAlong c V t := by
      have hnU := nabla.covDerivAlong_sub c V P hV (hP t)
      calc
        Riemannian.covDerivAlong (I := I) g c U t =
            g.leviCivitaConnection.covDerivAlong c U t :=
          (g.leviCivita_covDerivAlong_eq c U t).symm
        _ = nabla.covDerivAlong c U t :=
          (nabla.covDerivAlong_eq_of_field_eq_zero
            g.leviCivitaConnection c U hUt).symm
        _ = nabla.covDerivAlong c V t - nabla.covDerivAlong c P t := hnU
        _ = nabla.covDerivAlong c V t := by rw [hPp t, sub_zero]
    have hDR : Riemannian.covDerivAlong (I := I) g c R t =
        nabla.covDerivAlong c W t := by
      have hnR := nabla.covDerivAlong_sub c W Q hW (hQ t)
      calc
        Riemannian.covDerivAlong (I := I) g c R t =
            g.leviCivitaConnection.covDerivAlong c R t :=
          (g.leviCivita_covDerivAlong_eq c R t).symm
        _ = nabla.covDerivAlong c R t :=
          (nabla.covDerivAlong_eq_of_field_eq_zero
            g.leviCivitaConnection c R hRt).symm
        _ = nabla.covDerivAlong c W t - nabla.covDerivAlong c Q t := hnR
        _ = nabla.covDerivAlong c W t := by rw [hQp t, sub_zero]
    have hPQ : HasDerivAt
        (fun s => g.metricInner (c s) (P s) (Q s)) 0 t := by
      have heq : (fun s => g.metricInner (c s) (P s) (Q s)) =ᶠ[𝓝 t]
          fun _ => g.metricInner (c t) (P t) (Q t) :=
        Filter.Eventually.of_forall (fun s => hpres P Q hP hQ hPp hQp s t)
      exact (hasDerivAt_const t (g.metricInner (c t) (P t) (Q t))).congr_of_eventuallyEq heq
    have hUQ0 := hasDerivAt_metricInner_along_of_mdifferentiableAt
      (I := I) g hct hU (hQ t)
    have hUQ : HasDerivAt
        (fun s => g.metricInner (c s) (U s) (Q s))
        (g.metricInner (c t) (nabla.covDerivAlong c V t) (W t)) t := by
      simpa only [hDU, hUt, hQt, g.metricInner_zero_left, add_zero] using hUQ0
    have hVR0 := hasDerivAt_metricInner_along_of_mdifferentiableAt
      (I := I) g hct hV hR
    have hVR : HasDerivAt
        (fun s => g.metricInner (c s) (V s) (R s))
        (g.metricInner (c t) (V t) (nabla.covDerivAlong c W t)) t := by
      simpa only [hDR, hRt, g.metricInner_zero_right, zero_add] using hVR0
    have hsum := (hPQ.add hUQ).add hVR
    have heq : (fun s => g.metricInner (c s) (V s) (W s)) =
        fun s => (g.metricInner (c s) (P s) (Q s)
          + g.metricInner (c s) (U s) (Q s))
          + g.metricInner (c s) (V s) (R s) := by
      funext s
      simp only [U, R, g.metricInner_sub_left, g.metricInner_sub_right]
      ring
    exact (hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => congrFun heq s))).congr_deriv (by
        simp)
  · intro hproduct
    exact hproduct.preservesMetricAlongCurve hc

/-- **Math.** The Levi-Civita affine connection satisfies the arbitrary-field intrinsic
product rule along every differentiable curve. -/
theorem RiemannianMetric.leviCivitaConnection_hasMetricProductRuleAlong
    (g : RiemannianMetric I M) :
    g.leviCivitaConnection.HasMetricProductRuleAlong g := by
  intro c t hc V W hV hW
  have h := hasDerivAt_metricInner_along_of_mdifferentiableAt
    (I := I) g hc hV hW
  simpa only [g.leviCivita_covDerivAlong_eq] using h

/-- **Math.** For the Levi-Civita connection, both formulations in do Carmo Proposition
3.2 hold unconditionally (subject only to differentiability of the curve). -/
theorem RiemannianMetric.leviCivita_preservesMetricAlongCurve_iff_productRule
    (g : RiemannianMetric I M) {c : ℝ → M}
    (hc : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    g.leviCivitaConnection.PreservesMetricAlongCurve g c ↔
      g.leviCivitaConnection.HasMetricProductRuleAlongCurve g c := by
  constructor
  · intro _
    exact g.leviCivitaConnection_hasMetricProductRuleAlong c
  · intro hproduct
    exact hproduct.preservesMetricAlongCurve hc

/-- **Math.** do Carmo Ch. 2, Definition 3.1 and Proposition 3.2: the
Riemannian pairing of two Levi-Civita-parallel fields is constant. -/
theorem metricInner_const_of_isParallelAlong
    (g : RiemannianMetric I M) {c : ℝ → M}
    {V W : ∀ t, TangentSpace I (c t)}
    (hc : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hV : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t)
    (hVp : ∀ t, Riemannian.covDerivAlong (I := I) g c V t = 0)
    (hWp : ∀ t, Riemannian.covDerivAlong (I := I) g c W t = 0)
    (s t : ℝ) :
    g.metricInner (c s) (V s) (W s) = g.metricInner (c t) (V t) (W t) := by
  let f : ℝ → ℝ := fun r => g.metricInner (c r) (V r) (W r)
  have hf : ∀ r, HasDerivAt f 0 r := fun r => by
    have h := hasDerivAt_metricInner_along_of_mdifferentiableAt
      (I := I) g (hc r) (hV r) (hW r)
    simpa only [hVp r, hWp r, g.metricInner_zero_left,
      g.metricInner_zero_right, zero_add] using h
  exact is_const_of_deriv_eq_zero (fun r => (hf r).differentiableAt)
    (fun r => (hf r).deriv) s t

/-- **Math.** Two interval-native parallel fields have the same pairing at the
endpoints of a nonempty closed interval. -/
theorem metricInner_eq_endpoints_of_isParallelAlongWithinOn
    (g : RiemannianMetric I M) {c : ℝ → M}
    {V W : ∀ t, TangentSpace I (c t)} {a b : ℝ}
    (hV : IsParallelAlongWithinOn (I := I) g c V a b)
    (hW : IsParallelAlongWithinOn (I := I) g c W a b)
    (hab : a ≤ b) :
    g.metricInner (c a) (V a) (W a) =
      g.metricInner (c b) (V b) (W b) :=
  hV.metricInner_eq hW ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩

end Riemannian
