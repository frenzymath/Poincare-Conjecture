import DoCarmoLib.Riemannian.Connection.CovariantDerivativeAlong
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.CurveReadback
import DoCarmoLib.Riemannian.Variation.ArbitraryParallelTransport
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Intrinsic parallel fields and transport along a curve

This file gives complementary intrinsic notions. `IsParallelAlong` is the
pointwise, two-sided-derivative formulation using `covDerivAlong`, while
`IsParallelAlongOn` is the dependent-field wrapper around the established
`Jacobi.IsParallelFieldAlongOn` compatibility API. `IsParallelAlongWithinOn`
is the interval-native formulation: its local certificates use within
derivatives for both the base curve and the field, so its endpoint values have
honest one-sided semantics. For a globally `C¹` base curve it agrees on the full
closed interval with `Jacobi.IsParallelFieldAlongOn`.

For a globally `C¹` curve, prescribed initial data determine a unique field in
this closed-interval sense. The induced endpoint map is a linear equivalence of
the actual tangent spaces and preserves the Riemannian pairing. Piecewise-`C¹`
curves, represented by honest segment extensions, are treated in
`PiecewiseParallelAlong.lean`.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A tangent field along a curve satisfies the parallel equation on
`s` when its covariant derivative vanishes there.

This equation alone is intentionally unguarded: because `covDerivAlong` is
total, an irregular field can satisfy it when its coordinate derivatives
default to zero.  Use it together with `IsRegularFieldAlongOn`; the guarded
closed-interval and broken-curve notions are `IsParallelAlongWithinOn` and
`IsIntrinsicPiecewiseParallelAlongOn`. -/
def IsParallelAlong (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, covDerivAlong (I := I) g c V t = 0

/-- **Math.** A dependent tangent-field wrapper around the established
closed-interval `Variation.IsParallelCovariantFieldAlongOn` predicate.

This compatibility notion uses within derivatives for the field coordinate
reading but retains the legacy two-sided `deriv` for the base velocity.  Use
`IsParallelAlongWithinOn` below when the base curve is only `C¹` on the closed
interval and honest one-sided endpoint semantics are required. -/
def IsParallelAlongOn (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (a b : ℝ) : Prop :=
  Variation.IsParallelCovariantFieldAlongOn (I := I) g c
    (fun t => (V t : E)) a b

/-! ## Interval-native parallelism

The older chart certificate uses `deriv` for the base velocity.  That is correct
for a globally `C¹` curve, but at an endpoint of a merely interval-`C¹` curve it
reads the junk value of a two-sided derivative.  The certificate below instead
carries an actual within derivative of the base chart reading and uses that same
velocity in the field equation.  This makes restriction stable and gives honest
one-sided semantics at both endpoints. -/

/-- **Math.** In one chart, `w` is parallel along `c` on `[a,b]` when, at every
time, the chart reading of the base curve and that of the field have compatible
within derivatives

`u' = ξ`, `w' = -Γ(u)(ξ,w)`.

The velocity `ξ` is existential rather than written as `derivWithin u`; the
`HasDerivWithinAt` witness is the semantic content, and uniqueness of within
derivatives on a nondegenerate interval identifies it with `derivWithin`. -/
def IsParallelWithinSolOn (g : RiemannianMetric I M) (alpha : M)
    (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∃ velocity : E,
    HasDerivWithinAt (fun s => extChartAt I alpha (c s)) velocity (Icc a b) t ∧
      HasDerivWithinAt (chartFieldRep (I := I) c alpha V)
        (-Geodesic.chartChristoffelContraction (I := I) g alpha velocity
          (chartFieldRep (I := I) c alpha V t) (extChartAt I alpha (c t)))
        (Icc a b) t

namespace IsParallelWithinSolOn

variable {g : RiemannianMetric I M} {alpha : M} {c : ℝ → M}
  {V W : ∀ t, TangentSpace I (c t)} {a b a' b' : ℝ}

/-- **Math.** Restrict an interval-native chart certificate to a subinterval.
The same derivative witnesses remain valid after restricting the filter. -/
theorem mono (h : IsParallelWithinSolOn (I := I) g alpha c V a b)
    (ha : a ≤ a') (hb : b' ≤ b) :
    IsParallelWithinSolOn (I := I) g alpha c V a' b' := by
  intro t ht
  obtain ⟨velocity, hu, hV⟩ := h t (Icc_subset_Icc ha hb ht)
  exact ⟨velocity, hu.mono (Icc_subset_Icc ha hb),
    hV.mono (Icc_subset_Icc ha hb)⟩

/-- **Math.** The interval-native certificate depends only on the values of the
field on the interval. -/
theorem congr (h : IsParallelWithinSolOn (I := I) g alpha c V a b)
    (hVW : Set.EqOn V W (Icc a b)) :
    IsParallelWithinSolOn (I := I) g alpha c W a b := by
  intro t ht
  obtain ⟨velocity, hu, hV⟩ := h t ht
  have hrep : ∀ s ∈ Icc a b,
      chartFieldRep (I := I) c alpha W s =
        chartFieldRep (I := I) c alpha V s := by
    intro s hs
    rw [chartFieldRep_apply, chartFieldRep_apply, hVW hs]
  refine ⟨velocity, hu, ?_⟩
  rw [hrep t ht]
  exact hV.congr (fun s hs => hrep s hs) (hrep t ht)

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** An interval-native chart certificate is unchanged when the base
curve and the ambient values of its dependent tangent field agree on the
interval. -/
theorem congr_curve {d : ℝ → M} {W' : ∀ t, TangentSpace I (d t)}
    (h : IsParallelWithinSolOn (I := I) g alpha c V a b)
    (hcd : EqOn c d (Icc a b))
    (hVW : ∀ t ∈ Icc a b, (V t : E) = (W' t : E)) :
    IsParallelWithinSolOn (I := I) g alpha d W' a b := by
  intro t ht
  obtain ⟨velocity, hu, hV⟩ := h t ht
  have hu' : HasDerivWithinAt (fun s => extChartAt I alpha (d s)) velocity
      (Icc a b) t :=
    hu.congr (fun s hs => (congrArg (extChartAt I alpha) (hcd hs)).symm)
      (congrArg (extChartAt I alpha) (hcd ht)).symm
  have hrep : ∀ s ∈ Icc a b,
      chartFieldRep (I := I) d alpha W' s =
        chartFieldRep (I := I) c alpha V s := by
    intro s hs
    simp only [chartFieldRep_apply]
    rw [← hcd hs, hVW s hs]
  refine ⟨velocity, hu', ?_⟩
  have hfield := hV.congr (fun s hs => hrep s hs) (hrep t ht)
  convert hfield using 1
  rw [hrep t ht, ← hcd ht]

section Transfer

variable [I.Boundaryless]

/-- **Math.** Interval-native parallelism is invariant under a change of
chart.  Both the base velocity and the field derivative are transported by the
within-derivative chain rule; the Hessian term from differentiating the tangent
coordinate change cancels against the Christoffel transformation law. -/
theorem transfer {beta : M}
    (hsrcAlpha : ∀ t ∈ Icc a b, c t ∈ (chartAt H alpha).source)
    (hsrcBeta : ∀ t ∈ Icc a b, c t ∈ (chartAt H beta).source)
    (h : IsParallelWithinSolOn (I := I) g alpha c V a b) :
    IsParallelWithinSolOn (I := I) g beta c V a b := by
  intro t ht
  obtain ⟨velocity, hu, hV⟩ := h t ht
  have hxAlpha := hsrcAlpha t ht
  have hxBeta := hsrcBeta t ht
  have hyT : extChartAt I alpha (c t) ∈
      chartTransitionSource (I := I) (M := M) alpha beta :=
    extChartAt_mem_chartTransitionSource (I := I) hxAlpha hxBeta
  have hsymm : (extChartAt I alpha).symm (extChartAt I alpha (c t)) = c t :=
    (extChartAt I alpha).left_inv (by
      rw [extChartAt_source]
      exact hxAlpha)
  have hTd : HasFDerivAt (chartTransition (I := I) alpha beta)
      (tangentCoordChange I alpha beta (c t)) (extChartAt I alpha (c t)) := by
    have h0 := hasFDerivAt_chartTransition (I := I) hyT
    rwa [hsymm] at h0
  have hrep : ∀ s ∈ Icc a b,
      chartFieldRep (I := I) c beta V s =
        fderiv ℝ (chartTransition (I := I) alpha beta)
          (extChartAt I alpha (c s)) (chartFieldRep (I := I) c alpha V s) := by
    intro s hs
    have hyS : extChartAt I alpha (c s) ∈
        chartTransitionSource (I := I) (M := M) alpha beta :=
      extChartAt_mem_chartTransitionSource (I := I)
        (hsrcAlpha s hs) (hsrcBeta s hs)
    have hsymmS : (extChartAt I alpha).symm (extChartAt I alpha (c s)) = c s :=
      (extChartAt I alpha).left_inv (by
        rw [extChartAt_source]
        exact hsrcAlpha s hs)
    have hfdS : fderiv ℝ (chartTransition (I := I) alpha beta)
        (extChartAt I alpha (c s)) = tangentCoordChange I alpha beta (c s) := by
      rw [fderiv_chartTransition (I := I) hyS, hsymmS]
    rw [hfdS, chartFieldRep_apply, chartFieldRep_apply]
    exact (tangentCoordChange_comp (I := I)
      ⟨⟨mem_extChartAt_source (I := I) (c s), by
          rw [extChartAt_source]
          exact hsrcAlpha s hs⟩, by
        rw [extChartAt_source]
        exact hsrcBeta s hs⟩).symm
  have hchart : ∀ s ∈ Icc a b,
      extChartAt I beta (c s) =
        chartTransition (I := I) alpha beta (extChartAt I alpha (c s)) := by
    intro s hs
    exact (chartTransition_extChartAt (I := I) (hsrcAlpha s hs)).symm
  have hC' : HasDerivWithinAt
      (fun s => fderiv ℝ (chartTransition (I := I) alpha beta)
        (extChartAt I alpha (c s)))
      (fderiv ℝ (fderiv ℝ (chartTransition (I := I) alpha beta))
        (extChartAt I alpha (c t)) velocity) (Icc a b) t :=
    (hasFDerivAt_fderiv_chartTransition (I := I) hyT).comp_hasDerivWithinAt t hu
  have huBeta : HasDerivWithinAt (fun s => extChartAt I beta (c s))
      (tangentCoordChange I alpha beta (c t) velocity) (Icc a b) t := by
    have hcomp := hTd.comp_hasDerivWithinAt t hu
    exact hcomp.congr (fun s hs => hchart s hs) (hchart t ht)
  have hfd : fderiv ℝ (chartTransition (I := I) alpha beta)
      (extChartAt I alpha (c t)) = tangentCoordChange I alpha beta (c t) :=
    hTd.fderiv
  have hwT := hrep t ht
  have hval := (hC'.clm_apply hV).congr
    (fun s hs => hrep s hs) (hrep t ht)
  refine ⟨tangentCoordChange I alpha beta (c t) velocity, huBeta, ?_⟩
  have heq : -Geodesic.chartChristoffelContraction (I := I) g beta
        (tangentCoordChange I alpha beta (c t) velocity)
        (chartFieldRep (I := I) c beta V t) (extChartAt I beta (c t)) =
      fderiv ℝ (fderiv ℝ (chartTransition (I := I) alpha beta))
          (extChartAt I alpha (c t)) velocity
          (chartFieldRep (I := I) c alpha V t) +
        fderiv ℝ (chartTransition (I := I) alpha beta)
          (extChartAt I alpha (c t))
          (-Geodesic.chartChristoffelContraction (I := I) g alpha velocity
            (chartFieldRep (I := I) c alpha V t) (extChartAt I alpha (c t))) := by
    rw [hfd, map_neg,
      chartChristoffelContraction_change (I := I) g beta alpha hxBeta hxAlpha
        velocity (chartFieldRep (I := I) c alpha V t), hwT, hfd]
    abel
  rw [heq]
  exact hval

end Transfer

section Algebra

variable [I.Boundaryless]

/-- **Math.** The sum of two interval-native parallel fields is parallel. -/
theorem add (hV : IsParallelWithinSolOn (I := I) g alpha c V a b)
    (hW : IsParallelWithinSolOn (I := I) g alpha c W a b)
    (hab : a < b) :
    IsParallelWithinSolOn (I := I) g alpha c (fun t => V t + W t) a b := by
  intro t ht
  obtain ⟨v, huv, hVd⟩ := hV t ht
  obtain ⟨w, huw, hWd⟩ := hW t ht
  have hud := (uniqueDiffOn_Icc hab).uniqueDiffWithinAt ht
  have hvw : v = w := by
    rw [← huv.derivWithin hud, ← huw.derivWithin hud]
  subst w
  refine ⟨v, huv, ?_⟩
  have hd := hVd.add hWd
  convert hd using 1
  · exact chartFieldRep_add (I := I) c alpha V W
  · rw [chartFieldRep_add, Pi.add_apply,
      ← chartChristoffelContractionRight_apply, map_add,
      chartChristoffelContractionRight_apply,
      chartChristoffelContractionRight_apply, neg_add]

/-- **Math.** The difference of two interval-native parallel fields is parallel. -/
theorem sub (hV : IsParallelWithinSolOn (I := I) g alpha c V a b)
    (hW : IsParallelWithinSolOn (I := I) g alpha c W a b)
    (hab : a < b) :
    IsParallelWithinSolOn (I := I) g alpha c (fun t => V t - W t) a b := by
  intro t ht
  obtain ⟨v, huv, hVd⟩ := hV t ht
  obtain ⟨w, huw, hWd⟩ := hW t ht
  have hud := (uniqueDiffOn_Icc hab).uniqueDiffWithinAt ht
  have hvw : v = w := by
    rw [← huv.derivWithin hud, ← huw.derivWithin hud]
  subst w
  refine ⟨v, huv, ?_⟩
  have hd := hVd.sub hWd
  have hrepSub : chartFieldRep (I := I) c alpha (fun t => V t - W t) =
      chartFieldRep (I := I) c alpha V - chartFieldRep (I := I) c alpha W := by
    funext s
    exact map_sub (tangentCoordChange I (c s) alpha (c s)) (V s) (W s)
  convert hd using 1
  rw [hrepSub, Pi.sub_apply,
    ← chartChristoffelContractionRight_apply, map_sub,
    chartChristoffelContractionRight_apply,
    chartChristoffelContractionRight_apply]
  abel

/-- **Math.** A constant scalar multiple of an interval-native parallel field
is parallel. -/
theorem smul (r : ℝ) (hV : IsParallelWithinSolOn (I := I) g alpha c V a b) :
    IsParallelWithinSolOn (I := I) g alpha c (fun t => r • V t) a b := by
  intro t ht
  obtain ⟨v, huv, hVd⟩ := hV t ht
  refine ⟨v, huv, ?_⟩
  have hd := hVd.const_smul r
  convert hd using 1
  · exact chartFieldRep_smul (I := I) c alpha (fun _ => r) V
  · rw [chartFieldRep_smul, Pi.smul_apply',
      ← chartChristoffelContractionRight_apply, map_smul,
      chartChristoffelContractionRight_apply, ← smul_neg]

end Algebra

section Metric

variable [I.Boundaryless]

/-- **Math.** The chart-metric pairing of two interval-native parallel fields
is constant on the full closed interval. -/
theorem chartMetricInner_eq
    (hV : IsParallelWithinSolOn (I := I) g alpha c V a b)
    (hW : IsParallelWithinSolOn (I := I) g alpha c W a b)
    (_hab : a ≤ b)
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H alpha).source)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    chartMetricInner (I := I) g alpha (extChartAt I alpha (c s))
        (chartFieldRep (I := I) c alpha V s)
        (chartFieldRep (I := I) c alpha W s) =
      chartMetricInner (I := I) g alpha (extChartAt I alpha (c t))
        (chartFieldRep (I := I) c alpha V t)
        (chartFieldRep (I := I) c alpha W t) := by
  let u : ℝ → E := fun r => extChartAt I alpha (c r)
  let v : ℝ → E := chartFieldRep (I := I) c alpha V
  let w : ℝ → E := chartFieldRep (I := I) c alpha W
  let phi : ℝ → ℝ := fun r => chartMetricInner (I := I) g alpha (u r) (v r) (w r)
  have hu : ContinuousOn u (Icc a b) := by
    intro r hr
    obtain ⟨velocity, hur, _⟩ := hV r hr
    exact hur.continuousWithinAt
  have hv : ContinuousOn v (Icc a b) := by
    intro r hr
    obtain ⟨_, _, hvr⟩ := hV r hr
    exact hvr.continuousWithinAt
  have hw : ContinuousOn w (Icc a b) := by
    intro r hr
    obtain ⟨_, _, hwr⟩ := hW r hr
    exact hwr.continuousWithinAt
  have hutarget : ∀ r ∈ Icc a b, u r ∈ (extChartAt I alpha).target := by
    intro r hr
    exact (extChartAt I alpha).map_source (by
      rw [extChartAt_source]
      exact hsrc r hr)
  have hphi : ContinuousOn phi (Icc a b) :=
    Jacobi.continuousOn_chartMetricInner_pairing
      (I := I) g alpha hu hutarget hv hw
  have hderiv : ∀ r ∈ interior (Icc a b),
      HasDerivWithinAt phi 0 (interior (Icc a b)) r := by
    intro r hr
    have hrIoo : r ∈ Ioo a b := by rwa [interior_Icc] at hr
    have hrIcc : r ∈ Icc a b := Ioo_subset_Icc_self hrIoo
    have hnhds : Icc a b ∈ 𝓝 r := Icc_mem_nhds hrIoo.1 hrIoo.2
    obtain ⟨velocity, hur, hvr⟩ := hV r hrIcc
    obtain ⟨velocity', hur', hwr⟩ := hW r hrIcc
    have hvelocity : velocity' = velocity := by
      exact (hur'.hasDerivAt hnhds).unique (hur.hasDerivAt hnhds)
    subst velocity'
    have hurAt := hur.hasDerivAt hnhds
    have hvrAt := hvr.hasDerivAt hnhds
    have hwrAt := hwr.hasDerivAt hnhds
    have hbase : (extChartAt I alpha).symm (u r) ∈
        (trivializationAt E (TangentSpace I) alpha).baseSet := by
      rw [show u r = extChartAt I alpha (c r) from rfl,
        (extChartAt I alpha).left_inv (by
          rw [extChartAt_source]
          exact hsrc r hrIcc), trivializationAt_baseSet_eq_chartAt_source]
      exact hsrc r hrIcc
    have hG : ∀ i j, DifferentiableAt ℝ
        (chartGramOnE (I := I) g alpha i j) (u r) := by
      intro i j
      exact Jacobi.differentiableAt_chartGramOnE (I := I) g alpha
        (hutarget r hrIcc) i j
    have hmain := hasDerivAt_chartMetricInner_along (I := I) g alpha u v w
      hurAt.differentiableAt hvrAt.differentiableAt hwrAt.differentiableAt hG hbase
    have hcovV : covariantDerivCoord (I := I) g alpha u v r = 0 := by
      rw [covariantDerivCoord_def, hurAt.deriv, hvrAt.deriv]
      abel
    have hcovW : covariantDerivCoord (I := I) g alpha u w r = 0 := by
      rw [covariantDerivCoord_def, hurAt.deriv, hwrAt.deriv]
      abel
    have hzero : chartMetricInner (I := I) g alpha (u r)
          (covariantDerivCoord (I := I) g alpha u v r) (w r) +
        chartMetricInner (I := I) g alpha (u r) (v r)
          (covariantDerivCoord (I := I) g alpha u w r) = 0 := by
      rw [hcovV, hcovW, Jacobi.chartMetricInner_zero_left,
        Jacobi.chartMetricInner_zero_right, add_zero]
    rw [hzero] at hmain
    exact hmain.hasDerivWithinAt.mono interior_subset
  have hmono : MonotoneOn phi (Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hphi hderiv
      (fun _ _ => le_rfl)
  have hanti : AntitoneOn phi (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hphi hderiv
      (fun _ _ => le_rfl)
  change phi s = phi t
  rcases le_total s t with hst | hts
  · exact le_antisymm (hmono hs ht hst) (hanti hs ht hst)
  · exact le_antisymm (hanti ht hs hts) (hmono ht hs hts)

end Metric

end IsParallelWithinSolOn

/-- **Math.** A tangent field is intrinsically parallel on the closed interval
`[a,b]` with honest endpoint semantics if every time has a chart-local closed
window on which the base and field satisfy `IsParallelWithinSolOn`.  The window
is a neighbourhood relative to `[a,b]`, so its derivative at `a` or `b` is the
appropriate one-sided derivative. -/
def IsParallelAlongWithinOn (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (a b : ℝ) : Prop :=
  ∀ t₀ ∈ Icc a b, ∃ (alpha : M) (a' b' : ℝ), a' < b' ∧
    t₀ ∈ Icc a' b' ∧ Icc a' b' ⊆ Icc a b ∧
    Icc a' b' ∈ 𝓝[Icc a b] t₀ ∧
    (∀ t ∈ Icc a' b', c t ∈ (chartAt H alpha).source) ∧
    IsParallelWithinSolOn (I := I) g alpha c V a' b'

namespace IsParallelAlongWithinOn

variable [I.Boundaryless]
variable {g : RiemannianMetric I M} {c : ℝ → M}
  {V W : ∀ t, TangentSpace I (c t)} {a b : ℝ}

/-- **Math.** Localize an intrinsic within-parallel field into any chart that
contains a closed subinterval.  Chart covariance and locality of within
derivatives glue the pointwise certificates. -/
theorem isParallelWithinSolOn_of_mem_source
    (h : IsParallelAlongWithinOn (I := I) g c V a b)
    {beta : M} {l r : ℝ} (hsub : Icc l r ⊆ Icc a b)
    (hsrcBeta : ∀ t ∈ Icc l r, c t ∈ (chartAt H beta).source) :
    IsParallelWithinSolOn (I := I) g beta c V l r := by
  have key : ∀ t ∈ Icc l r, ∃ l' r' : ℝ,
      t ∈ Icc l' r' ∧ Icc l' r' ⊆ Icc l r ∧
      Icc l' r' ∈ 𝓝[Icc l r] t ∧
      IsParallelWithinSolOn (I := I) g beta c V l' r' := by
    intro t ht
    obtain ⟨alpha, a', b', _hab', ht', hsub', hnbhd', hsrcAlpha, hcert⟩ :=
      h t (hsub ht)
    let l' := max a' l
    let r' := min b' r
    have htNew : t ∈ Icc l' r' :=
      ⟨max_le ht'.1 ht.1, le_min ht'.2 ht.2⟩
    have hnewSubOld : Icc l' r' ⊆ Icc a' b' :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hnewSub : Icc l' r' ⊆ Icc l r :=
      Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
    have hnbhdNew : Icc l' r' ∈ 𝓝[Icc l r] t := by
      obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hnbhd'
      refine mem_nhdsWithin.2 ⟨U, hUopen, htU, fun s hs => ?_⟩
      have hsOld : s ∈ Icc a' b' := hUsub ⟨hs.1, hsub hs.2⟩
      exact ⟨max_le hsOld.1 hs.2.1, le_min hsOld.2 hs.2.2⟩
    have hsrcAlpha' : ∀ s ∈ Icc l' r',
        c s ∈ (chartAt H alpha).source :=
      fun s hs => hsrcAlpha s (hnewSubOld hs)
    have hsrcBeta' : ∀ s ∈ Icc l' r',
        c s ∈ (chartAt H beta).source :=
      fun s hs => hsrcBeta s (hnewSub hs)
    refine ⟨l', r', htNew, hnewSub, hnbhdNew, ?_⟩
    exact (hcert.mono (le_max_left _ _) (min_le_left _ _)).transfer
      hsrcAlpha' hsrcBeta'
  intro t ht
  obtain ⟨l', r', ht', _hsub', hnbhd', hcert⟩ := key t ht
  obtain ⟨velocity, hu, hV⟩ := hcert t ht'
  exact ⟨velocity, hu.mono_of_mem_nhdsWithin hnbhd',
    hV.mono_of_mem_nhdsWithin hnbhd'⟩

/-- **Math.** The intrinsic within-parallel predicate depends only on the field
over the stated interval. -/
theorem congr (h : IsParallelAlongWithinOn (I := I) g c V a b)
    (hVW : Set.EqOn V W (Icc a b)) :
    IsParallelAlongWithinOn (I := I) g c W a b := by
  intro t ht
  obtain ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc, hcert⟩ := h t ht
  exact ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc,
    hcert.congr (hVW.mono hsub)⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Intrinsic interval-native parallelism is invariant under replacing
the base curve and dependent field by ambient-equal values on the interval. -/
theorem congr_curve {d : ℝ → M} {W' : ∀ t, TangentSpace I (d t)}
    (h : IsParallelAlongWithinOn (I := I) g c V a b)
    (hcd : EqOn c d (Icc a b))
    (hVW : ∀ t ∈ Icc a b, (V t : E) = (W' t : E)) :
    IsParallelAlongWithinOn (I := I) g d W' a b := by
  intro t ht
  obtain ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc, hcert⟩ := h t ht
  refine ⟨alpha, a', b', hab', ht', hsub, hnbhd, ?_, ?_⟩
  · intro s hs
    rw [← hcd (hsub hs)]
    exact hsrc s hs
  · exact hcert.congr_curve (hcd.mono hsub)
      (fun s hs => hVW s (hsub hs))

/-- **Math.** Intrinsic interval-native parallel fields are closed under
addition. -/
theorem add (hV : IsParallelAlongWithinOn (I := I) g c V a b)
    (hW : IsParallelAlongWithinOn (I := I) g c W a b) :
    IsParallelAlongWithinOn (I := I) g c (fun t => V t + W t) a b := by
  intro t ht
  obtain ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc, hcertV⟩ := hV t ht
  have hcertW := hW.isParallelWithinSolOn_of_mem_source hsub hsrc
  exact ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc,
    hcertV.add hcertW hab'⟩

/-- **Math.** Intrinsic interval-native parallel fields are closed under
subtraction. -/
theorem sub (hV : IsParallelAlongWithinOn (I := I) g c V a b)
    (hW : IsParallelAlongWithinOn (I := I) g c W a b) :
    IsParallelAlongWithinOn (I := I) g c (fun t => V t - W t) a b := by
  intro t ht
  obtain ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc, hcertV⟩ := hV t ht
  have hcertW := hW.isParallelWithinSolOn_of_mem_source hsub hsrc
  exact ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc,
    hcertV.sub hcertW hab'⟩

/-- **Math.** Intrinsic interval-native parallel fields are closed under
constant scalar multiplication. -/
theorem smul (r : ℝ) (hV : IsParallelAlongWithinOn (I := I) g c V a b) :
    IsParallelAlongWithinOn (I := I) g c (fun t => r • V t) a b := by
  intro t ht
  obtain ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc, hcertV⟩ := hV t ht
  exact ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc, hcertV.smul r⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The intrinsic metric pairing of two interval-native parallel
fields is constant on the full closed interval.  Locally this is the chart
metric product rule; connectedness of `[a,b]` makes the local constants agree. -/
theorem metricInner_eq
    (hV : IsParallelAlongWithinOn (I := I) g c V a b)
    (hW : IsParallelAlongWithinOn (I := I) g c W a b)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    g.metricInner (c s) (V s) (W s) = g.metricInner (c t) (V t) (W t) := by
  let phi : Icc a b → ℝ := fun r => g.metricInner (c r) (V r) (W r)
  have hloc : IsLocallyConstant phi :=
    (IsLocallyConstant.iff_eventually_eq phi).2 fun x => by
      obtain ⟨alpha, a', b', hab', hx', hsub, hnbhd, hsrc, hcertV⟩ :=
        hV x x.property
      have hcertW := hW.isParallelWithinSolOn_of_mem_source hsub hsrc
      filter_upwards [preimage_coe_mem_nhds_subtype.2 hnbhd] with y hy
      have hy' : (y : ℝ) ∈ Icc a' b' := hy
      have hchart := hcertV.chartMetricInner_eq hcertW hab'.le hsrc hy' hx'
      have hpairY := Jacobi.metricInner_eq_chartMetricInner_rep
        (I := I) g (hsrc y hy') (fun r => (V r : E)) (fun r => (W r : E))
      have hpairX := Jacobi.metricInner_eq_chartMetricInner_rep
        (I := I) g (hsrc x hx') (fun r => (V r : E)) (fun r => (W r : E))
      change g.metricInner (c y) (V y) (W y) =
        g.metricInner (c x) (V x) (W x)
      rw [hpairY, hpairX]
      exact hchart
  letI : PreconnectedSpace (Icc a b) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  exact hloc.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Parallel fields carried by possibly different ambient intervals
have constant pairing on every common closed subinterval.  This is the local
comparison needed to prove that piecewise transport is independent of the
chosen subdivision. -/
theorem metricInner_eq_of_overlap
    {c : ℝ → M} {V W : ∀ t, TangentSpace I (c t)}
    {a₁ b₁ a₂ b₂ l r : ℝ}
    (hV : IsParallelAlongWithinOn (I := I) g c V a₁ b₁)
    (hW : IsParallelAlongWithinOn (I := I) g c W a₂ b₂)
    (hsubV : Icc l r ⊆ Icc a₁ b₁) (hsubW : Icc l r ⊆ Icc a₂ b₂)
    {s t : ℝ} (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) :
    g.metricInner (c s) (V s) (W s) = g.metricInner (c t) (V t) (W t) := by
  let phi : Icc l r → ℝ := fun x => g.metricInner (c x) (V x) (W x)
  have hloc : IsLocallyConstant phi :=
    (IsLocallyConstant.iff_eventually_eq phi).2 fun x => by
      obtain ⟨alpha, a', b', _hab', hx', hsub', hnbhd', hsrc', hcertV⟩ :=
        hV x (hsubV x.property)
      let p := max a' l
      let q := min b' r
      have hxPQ : (x : ℝ) ∈ Icc p q :=
        ⟨max_le hx'.1 x.property.1, le_min hx'.2 x.property.2⟩
      have hpq : p ≤ q := hxPQ.1.trans hxPQ.2
      have hsubLocal : Icc p q ⊆ Icc a' b' :=
        Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
      have hsubOverlap : Icc p q ⊆ Icc l r :=
        Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
      have hnbhdPQ : Icc p q ∈ 𝓝[Icc l r] (x : ℝ) := by
        obtain ⟨U, hUopen, hxU, hUsub⟩ := mem_nhdsWithin.1 hnbhd'
        refine mem_nhdsWithin.2 ⟨U, hUopen, hxU, fun y hy => ?_⟩
        have hyLocal : y ∈ Icc a' b' := hUsub ⟨hy.1, hsubV hy.2⟩
        exact ⟨max_le hyLocal.1 hy.2.1, le_min hyLocal.2 hy.2.2⟩
      have hsrcPQ : ∀ y ∈ Icc p q, c y ∈ (chartAt H alpha).source :=
        fun y hy => hsrc' y (hsubLocal hy)
      have hcertV' := hcertV.mono (le_max_left a' l) (min_le_left b' r)
      have hcertW' := hW.isParallelWithinSolOn_of_mem_source
        (hsubOverlap.trans hsubW) hsrcPQ
      filter_upwards [preimage_coe_mem_nhds_subtype.2 hnbhdPQ] with y hy
      have hyPQ : (y : ℝ) ∈ Icc p q := hy
      have hchart := hcertV'.chartMetricInner_eq hcertW' hpq hsrcPQ hyPQ hxPQ
      have hpairY := Jacobi.metricInner_eq_chartMetricInner_rep
        (I := I) g (hsrcPQ y hyPQ) (fun z => (V z : E)) (fun z => (W z : E))
      have hpairX := Jacobi.metricInner_eq_chartMetricInner_rep
        (I := I) g (hsrcPQ x hxPQ) (fun z => (V z : E)) (fun z => (W z : E))
      change g.metricInner (c y) (V y) (W y) =
        g.metricInner (c x) (V x) (W x)
      rw [hpairY, hpairX]
      exact hchart
  letI : PreconnectedSpace (Icc l r) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  exact hloc.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩

/-- **Math.** Uniqueness also compares parallel fields whose certificates live
on different outer intervals: if they agree once on a common closed interval,
they agree throughout that interval. -/
theorem eqOn_of_eq_at_of_overlap
    {c : ℝ → M} {V W : ∀ t, TangentSpace I (c t)}
    {a₁ b₁ a₂ b₂ l r t₀ : ℝ}
    (hV : IsParallelAlongWithinOn (I := I) g c V a₁ b₁)
    (hW : IsParallelAlongWithinOn (I := I) g c W a₂ b₂)
    (hsubV : Icc l r ⊆ Icc a₁ b₁) (hsubW : Icc l r ⊆ Icc a₂ b₂)
    (ht₀ : t₀ ∈ Icc l r) (h₀ : V t₀ = W t₀) :
    Set.EqOn V W (Icc l r) := by
  intro t ht
  have hVV := hV.metricInner_eq_of_overlap hV hsubV hsubV ht ht₀
  have hVW := hV.metricInner_eq_of_overlap hW hsubV hsubW ht ht₀
  have hWV := hW.metricInner_eq_of_overlap hV hsubW hsubV ht ht₀
  have hWW := hW.metricInner_eq_of_overlap hW hsubW hsubW ht ht₀
  have hzero : g.metricInner (c t)
      (V t - W t : TangentSpace I (c t)) (V t - W t) = 0 := by
    rw [g.metricInner_sub_left, g.metricInner_sub_right,
      g.metricInner_sub_right, hVV, hVW, hWV, hWW, h₀]
    ring
  by_contra hne
  have hdiff : (V t - W t : TangentSpace I (c t)) ≠ 0 := sub_ne_zero.2 hne
  exact absurd hzero (g.metricInner_self_pos (c t) _ hdiff).ne'

/-- **Math.** Two interval-native parallel fields which agree at one point
agree everywhere on the closed interval. -/
theorem eqOn_of_eq_at
    (hV : IsParallelAlongWithinOn (I := I) g c V a b)
    (hW : IsParallelAlongWithinOn (I := I) g c W a b)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (h₀ : V t₀ = W t₀) :
    Set.EqOn V W (Icc a b) := by
  have hD := hV.sub hW
  intro t ht
  have hconst := hD.metricInner_eq hD ht ht₀
  have hzero₀ : V t₀ - W t₀ = 0 := sub_eq_zero.2 h₀
  rw [hzero₀] at hconst
  have hz : g.metricInner (c t₀) (0 : TangentSpace I (c t₀)) 0 = 0 :=
    g.metricInner_zero_left (c t₀) 0
  have hzero : g.metricInner (c t)
      (V t - W t : TangentSpace I (c t)) (V t - W t) = 0 :=
    hconst.trans hz
  by_contra hne
  have hdiff : (V t - W t : TangentSpace I (c t)) ≠ 0 :=
    sub_ne_zero.2 hne
  exact absurd hzero (g.metricInner_self_pos (c t) _ hdiff).ne'

end IsParallelAlongWithinOn

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** On a single chart interval, an interval-`C¹` curve admits an
intrinsic within-parallel field with any prescribed initial chart value.  The
linear ODE coefficient uses the continuous within velocity of the chart curve. -/
theorem exists_intrinsic_chart_parallelWithin
    {g : RiemannianMetric I M} {c : ℝ → M} {a b : ℝ} {alpha : M}
    (hab : a < b) (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H alpha).source) (v₀ : E) :
    ∃ V : ∀ t, TangentSpace I (c t),
      IsParallelWithinSolOn (I := I) g alpha c V a b ∧
      chartFieldRep (I := I) c alpha V a = v₀ ∧
      ∀ t ∈ Icc a b,
        V t = tangentCoordChange I alpha (c t) (c t)
          (chartFieldRep (I := I) c alpha V t) := by
  let u : ℝ → E := fun t => extChartAt I alpha (c t)
  let velocity : ℝ → E := derivWithin u (Icc a b)
  have huC1 : ContDiffOn ℝ 1 u (Icc a b) :=
    Geodesic.contDiffOn_extChartAt_comp hc hsrc
  have hvelocity : ContinuousOn velocity (Icc a b) :=
    huC1.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  have hu : ContinuousOn u (Icc a b) := huC1.continuousOn
  have hmem : ∀ t ∈ Icc a b,
      u t ∈ interior (extChartAt I alpha).target := by
    intro t ht
    rw [(isOpen_extChartAt_target (I := I) alpha).interior_eq]
    exact (extChartAt I alpha).map_source (by
      rw [extChartAt_source]
      exact hsrc t ht)
  have hcoeff : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g alpha
        (velocity t) (u t)) (Icc a b) :=
    by
      have hGamma : ContinuousOn (Jacobi.chartChristoffelBilin (I := I) g alpha)
          (interior (extChartAt I alpha).target) :=
        (Jacobi.contDiffOn_chartChristoffelBilin (I := I) g alpha).continuousOn
      have hcomp : ContinuousOn
          (fun t => Jacobi.chartChristoffelBilin (I := I) g alpha (u t)) (Icc a b) :=
        hGamma.comp hu hmem
      refine (hcomp.clm_apply hvelocity).congr fun t _ => ?_
      rw [Jacobi.chartChristoffelContractionRight_eq_bilin]
  obtain ⟨Kreal, hKreal⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hcoeff
  let K : NNReal := ⟨max Kreal 0, le_max_right _ _⟩
  let A : ℝ → E →L[ℝ] E := fun t =>
    -chartChristoffelContractionRight (I := I) g alpha (velocity t) (u t)
  have hAcont : ContinuousOn A (Icc a b) := hcoeff.neg
  have hAK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K := by
    intro t ht
    rw [show A t = -chartChristoffelContractionRight (I := I) g alpha
      (velocity t) (u t) from rfl]
    simp only [nnnorm_neg]
    rw [← NNReal.coe_le_coe]
    exact (hKreal t ht).trans (le_max_left _ _)
  obtain ⟨w, hw₀, hw⟩ :=
    LinearODE.exists_hasDerivWithinAt_Icc hab.le A v₀ hAcont hAK
  let V : ∀ t, TangentSpace I (c t) := fun t =>
    tangentCoordChange I alpha (c t) (c t) (w t)
  have hrep : ∀ t ∈ Icc a b,
      chartFieldRep (I := I) c alpha V t = w t := by
    intro t ht
    exact Jacobi.tangentCoordChange_realize_self (I := I) (hsrc t ht) (w t)
  refine ⟨V, ?_, ?_, ?_⟩
  · intro t ht
    have hubase : HasDerivWithinAt u (velocity t) (Icc a b) t := by
      exact (huC1.differentiableOn one_ne_zero t ht).hasDerivWithinAt
    refine ⟨velocity t, hubase, ?_⟩
    have hfield := hw t ht
    rw [show A t (w t) =
        -Geodesic.chartChristoffelContraction (I := I) g alpha
          (velocity t) (w t) (u t) by
      simp only [A, neg_apply,
        chartChristoffelContractionRight_apply]] at hfield
    rw [hrep t ht]
    exact hfield.congr (fun s hs => hrep s hs) (hrep t ht)
  · rw [hrep a (left_mem_Icc.2 hab.le), hw₀]
  · intro t ht
    show tangentCoordChange I alpha (c t) (c t) (w t) =
      tangentCoordChange I alpha (c t) (c t)
        (chartFieldRep (I := I) c alpha V t)
    rw [hrep t ht]

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Every interval-`C¹` curve admits a within-parallel field with a
prescribed initial tangent, even when the curve crosses arbitrarily many charts. -/
theorem exists_isParallelAlongWithinOn
    {g : RiemannianMetric I M} {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    (v₀ : TangentSpace I (c a)) :
    ∃ V : ∀ t, TangentSpace I (c t),
      IsParallelAlongWithinOn (I := I) g c V a b ∧ V a = v₀ := by
  classical
  have hccont : ContinuousOn c (Icc a b) := hc.continuousOn
  have hchart : ∀ t ∈ Icc a b, ∃ eps > (0 : ℝ),
      ∀ s ∈ Icc a b ∩ Icc (t - eps) (t + eps),
        c s ∈ (chartAt H (c t)).source := by
    intro t ht
    have hpre : c ⁻¹' (chartAt H (c t)).source ∈ 𝓝[Icc a b] t :=
      (hccont t ht).preimage_mem_nhdsWithin
        ((chartAt H (c t)).open_source.mem_nhds (mem_chart_source H (c t)))
    obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hpre
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.1 hUopen t htU
    refine ⟨eps / 2, by linarith, fun s hs => hUsub ⟨?_, hs.1⟩⟩
    exact hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      have hd : |s - t| ≤ eps / 2 :=
        abs_le.2 ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩
      linarith)
  let S : Set ℝ := {r | r ∈ Ioc a b ∧
    ∃ V : ∀ t, TangentSpace I (c t),
      IsParallelAlongWithinOn (I := I) g c V a r ∧ V a = v₀}
  obtain ⟨eps₀, heps₀, hball₀⟩ := hchart a ⟨le_rfl, hab.le⟩
  have hstep₀ : min b (a + eps₀) ∈ S := by
    let r₀ := min b (a + eps₀)
    have har₀ : a < r₀ := lt_min hab (by linarith)
    have hr₀b : r₀ ≤ b := min_le_left _ _
    have hsub₀ : Icc a r₀ ⊆ Icc a b := Icc_subset_Icc le_rfl hr₀b
    have hsrc₀ : ∀ t ∈ Icc a r₀, c t ∈ (chartAt H (c a)).source := by
      intro t ht
      exact hball₀ t ⟨hsub₀ ht, ⟨by linarith [ht.1],
        le_trans ht.2 (le_trans (min_le_right _ _) (by linarith))⟩⟩
    obtain ⟨V, hcert, hVa, _hread⟩ :=
      exists_intrinsic_chart_parallelWithin (I := I) har₀ (hc.mono hsub₀) hsrc₀
        (v₀ : E)
    have hVa' : V a = v₀ := by
      have hself : chartFieldRep (I := I) c (c a) V a = V a := by
        rw [chartFieldRep_apply]
        exact tangentCoordChange_self (I := I)
          (mem_extChartAt_source (I := I) (c a))
      change V a = v₀
      rw [← hself, hVa]
    refine ⟨⟨har₀, hr₀b⟩, V, ?_, hVa'⟩
    intro t ht
    exact ⟨c a, a, r₀, har₀, ht, subset_rfl,
      self_mem_nhdsWithin, hsrc₀, hcert⟩
  have hSne : S.Nonempty := ⟨_, hstep₀⟩
  have hSbdd : BddAbove S := ⟨b, fun _ hs => hs.1.2⟩
  let q := sSup S
  have haq : a < q :=
    lt_of_lt_of_le (lt_min hab (by linarith)) (le_csSup hSbdd hstep₀)
  have hqb : q ≤ b := csSup_le hSne fun _ hs => hs.1.2
  obtain ⟨eps, heps, hball⟩ := hchart q ⟨haq.le, hqb⟩
  have hdelta : (0 : ℝ) < min eps (q - a) := lt_min heps (by linarith)
  obtain ⟨q', hq'S, hq'lt⟩ := exists_lt_of_lt_csSup hSne
    (show q - min eps (q - a) < sSup S by
      change q - min eps (q - a) < q
      linarith)
  have hq'le : q' ≤ q := le_csSup hSbdd hq'S
  obtain ⟨hq'Ioc, V₁, hPar₁, hV₁a⟩ := hq'S
  let l := max a (q - eps)
  let r := min b (q + eps)
  have hlq' : l < q' := max_lt hq'Ioc.1 (by
    have hmin := min_le_left eps (q - a)
    linarith)
  have hqr : q ≤ r := le_min hqb (by linarith)
  have hlq : l < q := lt_of_lt_of_le hlq' hq'le
  have hlr : l < r := lt_of_lt_of_le hlq hqr
  have hla : a ≤ l := le_max_left _ _
  have hrb : r ≤ b := min_le_left _ _
  have hsubLR : Icc l r ⊆ Icc a b := Icc_subset_Icc hla hrb
  have hsrcLR : ∀ t ∈ Icc l r, c t ∈ (chartAt H (c q)).source := by
    intro t ht
    apply hball t
    refine ⟨hsubLR ht, ?_⟩
    constructor
    · exact le_trans (le_max_right a (q - eps)) ht.1
    · exact le_trans ht.2 (min_le_right _ _)
  have hsubAQ' : Icc a q' ⊆ Icc a b :=
    Icc_subset_Icc le_rfl hq'Ioc.2
  have hsubLQ' : Icc l q' ⊆ Icc l r :=
    Icc_subset_Icc le_rfl (le_trans hq'le hqr)
  have hcert₁ := hPar₁.isParallelWithinSolOn_of_mem_source
    (Icc_subset_Icc hla le_rfl)
    (fun t ht => hsrcLR t (hsubLQ' ht))
  obtain ⟨V₂, hcert₂, hV₂l, hread₂⟩ :=
    exists_intrinsic_chart_parallelWithin (I := I) hlr
      (hc.mono hsubLR) hsrcLR (chartFieldRep (I := I) c (c q) V₁ l)
  have hV₂l' : V₂ l = V₁ l := by
    rw [hread₂ l (left_mem_Icc.2 hlr.le), hV₂l, chartFieldRep_apply]
    change tangentCoordChange I (c q) (c l) (c l)
        (tangentCoordChange I (c l) (c q) (c l) (V₁ l : E)) = (V₁ l : E)
    rw [tangentCoordChange_comp (I := I) (w := c l) (x := c q)
      (y := c l) (z := c l)
      ⟨⟨mem_extChartAt_source (I := I) (c l), by
          rw [extChartAt_source]
          exact hsrcLR l (left_mem_Icc.2 hlr.le)⟩,
        mem_extChartAt_source (I := I) (c l)⟩]
    exact tangentCoordChange_self (mem_extChartAt_source (I := I) (c l))
  have hPar₁over : IsParallelAlongWithinOn (I := I) g c V₁ l q' := by
    intro t ht
    exact ⟨c q, l, q', hlq', ht, subset_rfl, self_mem_nhdsWithin,
      fun s hs => hsrcLR s (hsubLQ' hs), hcert₁⟩
  have hPar₂over : IsParallelAlongWithinOn (I := I) g c V₂ l q' := by
    intro t ht
    exact ⟨c q, l, q', hlq', ht, subset_rfl, self_mem_nhdsWithin,
      fun s hs => hsrcLR s (hsubLQ' hs),
      hcert₂.mono le_rfl (le_trans hq'le hqr)⟩
  have hEq : Set.EqOn V₁ V₂ (Icc l q') :=
    hPar₁over.eqOn_of_eq_at hPar₂over
      (left_mem_Icc.2 hlq'.le) hV₂l'.symm
  let Vg : ∀ t, TangentSpace I (c t) := fun t =>
    if t ≤ q' then V₁ t else V₂ t
  have hVg₁ : Set.EqOn Vg V₁ (Icc a q') :=
    fun _ ht => if_pos ht.2
  have hVg₂ : Set.EqOn Vg V₂ (Icc l r) := by
    intro t ht
    by_cases htq' : t ≤ q'
    · rw [show Vg t = if t ≤ q' then V₁ t else V₂ t by rfl, if_pos htq']
      exact hEq ⟨ht.1, htq'⟩
    · rw [show Vg t = if t ≤ q' then V₁ t else V₂ t by rfl, if_neg htq']
  have hAlong : IsParallelAlongWithinOn (I := I) g c Vg a r := by
    intro t ht
    by_cases htq' : t < q'
    · obtain ⟨alpha, a', b', hab', ht', hsub', hnbhd', hsrc', hcert'⟩ :=
        hPar₁ t ⟨ht.1, htq'.le⟩
      refine ⟨alpha, a', b', hab', ht',
        hsub'.trans (Icc_subset_Icc le_rfl (le_trans hq'le hqr)), ?_, hsrc', ?_⟩
      · obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hnbhd'
        refine mem_nhdsWithin.2 ⟨U ∩ Iio q', hUopen.inter isOpen_Iio,
          ⟨htU, htq'⟩, fun s hs => ?_⟩
        exact hUsub ⟨hs.1.1, ⟨hs.2.1, hs.1.2.le⟩⟩
      · exact hcert'.congr (fun s hs => (hVg₁ (hsub' hs)).symm)
    · rw [not_lt] at htq'
      refine ⟨c q, l, r, hlr, ⟨le_trans hlq'.le htq', ht.2⟩,
        Icc_subset_Icc hla le_rfl, ?_, hsrcLR, ?_⟩
      · refine mem_nhdsWithin.2 ⟨Ioi l, isOpen_Ioi,
          lt_of_lt_of_le hlq' htq', fun s hs => ⟨hs.1.le, hs.2.2⟩⟩
      · exact hcert₂.congr (fun s hs => (hVg₂ hs).symm)
  have hVga : Vg a = v₀ := by
    rw [hVg₁ ⟨le_rfl, hq'Ioc.1.le⟩, hV₁a]
  have hrS : r ∈ S :=
    ⟨⟨lt_of_lt_of_le haq hqr, hrb⟩, Vg, hAlong, hVga⟩
  rcases lt_or_eq_of_le hqb with hlt | heq
  · exfalso
    have hrq : r ≤ q := le_csSup hSbdd hrS
    have hqr' : q < r := lt_min hlt (by linarith)
    exact (not_lt_of_ge hrq) hqr'
  · have hrb' : r = b := by
      dsimp [r]
      rw [← heq]
      exact min_eq_left (by linarith)
    obtain ⟨_, V, hV, hVa⟩ := hrS
    exact ⟨V, hrb' ▸ hV, hVa⟩

/-- **Math.** An interval-`C¹` curve has a unique within-parallel field with a
prescribed initial tangent, with uniqueness on the whole closed interval. -/
theorem exists_unique_isParallelAlongWithinOn
    {g : RiemannianMetric I M} {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    (v₀ : TangentSpace I (c a)) :
    ∃ V : ∀ t, TangentSpace I (c t),
      IsParallelAlongWithinOn (I := I) g c V a b ∧ V a = v₀ ∧
      ∀ W : ∀ t, TangentSpace I (c t),
        IsParallelAlongWithinOn (I := I) g c W a b → W a = v₀ →
          Set.EqOn W V (Icc a b) := by
  obtain ⟨V, hV, hVa⟩ :=
    exists_isParallelAlongWithinOn (I := I) hab hc v₀
  refine ⟨V, hV, hVa, ?_⟩
  intro W hW hWa
  exact hW.eqOn_of_eq_at hV (left_mem_Icc.2 hab.le) (hWa.trans hVa.symm)

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** For a globally `C¹` base curve, the interval-native intrinsic
predicate agrees on the entire closed interval with the established
`Jacobi.IsParallelFieldAlongOn` predicate.  At the endpoints the global
derivative and the within derivative coincide; no endpoint is discarded. -/
theorem isParallelAlongWithinOn_iff_isParallelFieldAlongOn
    {g : RiemannianMetric I M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b : ℝ}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) :
    IsParallelAlongWithinOn (I := I) g c V a b ↔
      Jacobi.IsParallelFieldAlongOn (I := I) g c (fun t => (V t : E)) a b := by
  constructor
  · intro h
    apply Variation.IsParallelCovariantFieldAlongOn.isParallelFieldAlongOn
    intro t ht
    obtain ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc, hcert⟩ := h t ht
    refine ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc, ?_⟩
    intro s hs
    obtain ⟨velocity, hu, hV⟩ := hcert s hs
    have huGlobal : DifferentiableAt ℝ
        (fun r => extChartAt I alpha (c r)) s :=
      ((contMDiffAt_extChartAt' (I := I) (n := 1) (hsrc s hs)).comp
        s hc.contMDiffAt).contDiffAt.differentiableAt (by norm_num)
    have hud := (uniqueDiffOn_Icc hab').uniqueDiffWithinAt hs
    have hvelocity : velocity = deriv (fun r => extChartAt I alpha (c r)) s := by
      rw [← hu.derivWithin hud]
      exact huGlobal.hasDerivAt.hasDerivWithinAt.derivWithin hud
    have hrep : chartFieldRep (I := I) c alpha V =
        Jacobi.chartVectorRep (I := I) c alpha (fun t => (V t : E)) := by
      rfl
    rw [← hrep]
    simpa only [Jacobi.chartVectorRep, map_zero, zero_sub, ← hvelocity] using hV
  · intro h
    have hCov : Variation.IsParallelCovariantFieldAlongOn (I := I) g c
        (fun t => (V t : E)) a b :=
      Variation.IsParallelFieldAlongOn.isParallelCovariantFieldAlongOn h
    intro t ht
    obtain ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc, hcert⟩ := hCov t ht
    refine ⟨alpha, a', b', hab', ht', hsub, hnbhd, hsrc, ?_⟩
    intro s hs
    have huGlobal : DifferentiableAt ℝ
        (fun r => extChartAt I alpha (c r)) s :=
      ((contMDiffAt_extChartAt' (I := I) (n := 1) (hsrc s hs)).comp
        s hc.contMDiffAt).contDiffAt.differentiableAt (by norm_num)
    refine ⟨deriv (fun r => extChartAt I alpha (c r)) s,
      huGlobal.hasDerivAt.hasDerivWithinAt, ?_⟩
    have hrep : chartFieldRep (I := I) c alpha V =
        Jacobi.chartVectorRep (I := I) c alpha (fun t => (V t : E)) := by
      rfl
    rw [hrep]
    simpa only [Jacobi.chartVectorRep, map_zero, zero_sub] using hcert s hs

/-- **Math.** The intrinsic closed-interval predicate is exactly the existing
parallel-field predicate, on its full domain `Icc a b` (including both
endpoints). -/
theorem isParallelAlongOn_iff_isParallelFieldAlongOn
    {g : RiemannianMetric I M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b : ℝ} :
    IsParallelAlongOn (I := I) g c V a b ↔
      Jacobi.IsParallelFieldAlongOn (I := I) g c (fun t => (V t : E)) a b := by
  constructor
  · exact Variation.IsParallelCovariantFieldAlongOn.isParallelFieldAlongOn
  · exact Variation.IsParallelFieldAlongOn.isParallelCovariantFieldAlongOn

/-- **Math.** The existing chart-local compact-interval certificate for a
parallel field implies intrinsic parallelism at every interior time. The
restriction to `Ioo a b` converts the certificate's within derivative into the
two-sided derivative used by `covDerivAlong`. -/
theorem Variation.IsParallelCovariantFieldAlongOn.isParallelAlong_Ioo
    {g : RiemannianMetric I M} {c : ℝ → M} {V : ℝ → E} {a b : ℝ}
    (hV : Variation.IsParallelCovariantFieldAlongOn (I := I) g c V a b)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) :
    IsParallelAlong (I := I) g c
      (fun t => (V t : TangentSpace I (c t))) (Ioo a b) := by
  intro t ht
  obtain ⟨α, a', b', _hab', ht', _hsub, hnbhd, hsrc, hcert⟩ :=
    hV t (Ioo_subset_Icc_self ht)
  have htInterior : t ∈ interior (Icc a b) := by
    rwa [interior_Icc]
  have hnbhd_full : Icc a' b' ∈ 𝓝 t := by
    rw [nhdsWithin_eq_nhds.2
      (mem_interior_iff_mem_nhds.1 htInterior)] at hnbhd
    exact hnbhd
  have htIoo' : t ∈ Ioo a' b' := by
    rw [← interior_Icc]
    exact mem_interior_iff_mem_nhds.2 hnbhd_full
  have hu : DifferentiableAt ℝ (fun s => extChartAt I α (c s)) t :=
    (Variation.isChartDifferentiableOn_of_contMDiff
      (I := I) (a := a) (b := b) hc)
      t (Ioo_subset_Icc_self ht) α (hsrc t ht')
  have hrep : chartFieldRep (I := I) c α
      (fun s => (V s : TangentSpace I (c s))) =
      Jacobi.chartVectorRep (I := I) c α V := by
    set_option backward.isDefEq.respectTransparency false in
      rfl
  have hfield : DifferentiableAt ℝ
      (chartFieldRep (I := I) c α
        (fun s => (V s : TangentSpace I (c s)))) t := by
    rw [hrep]
    exact hcert.differentiableAt htIoo'
  have hcoord : covariantDerivCoord (I := I) g α
      (fun s => extChartAt I α (c s))
      (chartFieldRep (I := I) c α
        (fun s => (V s : TangentSpace I (c s)))) t = 0 := by
    rw [hrep]
    simpa only [Jacobi.chartVectorRep, map_zero] using
      hcert.covariantDerivCoord_eq htIoo'
  exact (covDerivAlong_eq_zero_iff_chart (I := I) g α
    hc.continuous.continuousAt (hsrc t ht') hu hfield).2 hcoord

/-- **Math.** On the interior, the endpoint-safe predicate reduces to the
ordinary intrinsic equation `D V / dt = 0`. -/
theorem IsParallelAlongOn.isParallelAlong_Ioo
    {g : RiemannianMetric I M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b : ℝ}
    (hV : IsParallelAlongOn (I := I) g c V a b)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) :
    IsParallelAlong (I := I) g c V (Ioo a b) :=
  Variation.IsParallelCovariantFieldAlongOn.isParallelAlong_Ioo hV hc

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Along a curve that is `C¹` on all of `ℝ`, every prescribed initial
tangent vector extends to a closed-interval parallel field, uniquely on
`[a,b]`.  For the book's interval-`C¹` statement use
`exists_unique_isParallelAlongWithinOn`; for broken curves use
`exists_unique_isIntrinsicPiecewiseParallelAlongOn`. -/
theorem exists_unique_isParallelAlongOn
    {g : RiemannianMetric I M} {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) (v₀ : TangentSpace I (c a)) :
    ∃ V : ∀ t, TangentSpace I (c t),
      IsParallelAlongOn (I := I) g c V a b ∧ V a = v₀ ∧
      ∀ W : ∀ t, TangentSpace I (c t),
        IsParallelAlongOn (I := I) g c W a b → W a = v₀ →
          Set.EqOn W V (Icc a b) := by
  obtain ⟨w, hw, hwa, huniq⟩ :=
    Variation.exists_parallelCovariantFieldAlongOn_unique
      (I := I) (g := g) hab hc (v₀ : E)
  let V : ∀ t, TangentSpace I (c t) := fun t => (w t : TangentSpace I (c t))
  refine ⟨V, hw, ?_, ?_⟩
  · change (w a : E) = (v₀ : E)
    exact hwa
  · intro W hW hWa t ht
    change (W t : E) = (V t : E)
    exact huniq (fun s => (W s : E)) hW (congrArg (fun x => (x : E)) hWa) ht

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The canonical field seeded at the left endpoint by `w₀` is
intrinsically parallel on the open interval. -/
theorem Variation.parallelCovariantFieldSeed_isParallelAlong_Ioo
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) (w₀ : E) :
    IsParallelAlong (I := I) g c
      (fun t => (Variation.parallelCovariantFieldSeed (I := I) (E := E) g hab hc w₀ t :
        TangentSpace I (c t))) (Ioo a b) :=
  (Variation.parallelCovariantFieldSeed_isParallel
    (I := I) (E := E) g hab hc w₀).isParallelAlong_Ioo hc

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Parallel transport along a curve that is `C¹` on all of `ℝ`,
viewed as a linear equivalence between the actual endpoint tangent spaces.  For
the book's interval-`C¹` and piecewise-`C¹` statements use the `WithinOn` API
and `intrinsicPiecewiseParallelTransportTangentEquiv`, respectively. -/
noncomputable def parallelTransportTangentEquiv
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) :
    TangentSpace I (c a) ≃ₗ[ℝ] TangentSpace I (c b) :=
  let P : E ≃ₗ[ℝ] E :=
    Variation.parallelCovariantTransportEquiv
      (I := I) (E := E) g hab hc (right_mem_Icc.2 hab.le)
  { toFun := fun v => (P (v : E) : TangentSpace I (c b))
    invFun := fun v => (P.symm (v : E) : TangentSpace I (c a))
    left_inv := by
      intro v
      change P.symm (P (v : E)) = (v : E)
      exact P.symm_apply_apply (v : E)
    right_inv := by
      intro v
      change P (P.symm (v : E)) = (v : E)
      exact P.apply_symm_apply (v : E)
    map_add' := by
      intro v w
      change P ((v : E) + (w : E)) = P (v : E) + P (w : E)
      exact P.map_add (v : E) (w : E)
    map_smul' := by
      intro r v
      change P (r • (v : E)) = r • P (v : E)
      exact P.map_smul r (v : E) }

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem parallelTransportTangentEquiv_apply
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    (v : TangentSpace I (c a)) :
    parallelTransportTangentEquiv (I := I) g hab hc v =
      (Variation.parallelCovariantTransportAlong (I := I) g hab hc
        (right_mem_Icc.2 hab.le) (v : E) : TangentSpace I (c b)) := by
  change
    Variation.parallelCovariantTransportEquiv
        (I := I) (E := E) g hab hc (right_mem_Icc.2 hab.le) (v : E) =
      Variation.parallelCovariantTransportAlong
        (I := I) (E := E) g hab hc (right_mem_Icc.2 hab.le) (v : E)
  exact Variation.parallelCovariantTransportEquiv_apply
    (I := I) (E := E) g hab hc (right_mem_Icc.2 hab.le) (v : E)

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Intrinsic endpoint parallel transport preserves the Riemannian
inner product. -/
theorem metricInner_parallelTransportTangentEquiv
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    (v w : TangentSpace I (c a)) :
    g.metricInner (c b)
        (parallelTransportTangentEquiv (I := I) g hab hc v)
        (parallelTransportTangentEquiv (I := I) g hab hc w) =
      g.metricInner (c a) v w := by
  simpa only [parallelTransportTangentEquiv_apply] using
    Variation.metricInner_parallelCovariantTransportAlong
      (I := I) (E := E) g hab hc (right_mem_Icc.2 hab.le) (v : E) (w : E)

end Boundaryless

end Riemannian

end
