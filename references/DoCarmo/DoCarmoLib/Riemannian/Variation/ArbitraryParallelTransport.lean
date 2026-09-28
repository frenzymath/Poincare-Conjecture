import DoCarmoLib.Riemannian.Variation.ParallelCovariantField
import DoCarmoLib.Riemannian.Jacobi.ParallelTransport

/-!
# Parallel transport along an arbitrary C1 curve

Do Carmo, *Riemannian Geometry*, Ch. 2, Proposition 2.6, for the Levi-Civita
connection of a Riemannian metric.  Unlike the older manifold-level parallel
transport in `Jacobi/ParallelFieldAlong.lean`, the curve in this file is not
assumed to be a geodesic.

A field is parallel when its covariant derivative is zero, expressed using the
chart-local predicate `IsCovariantDerivFieldAlongOn`.  A global `C1` hypothesis
on the curve makes the coordinate velocity continuous in every chart window;
the resulting linear ODE is solved in one chart and continued across chart
overlaps by the chart covariance of the covariant derivative.

The uniqueness statement is interval-relative: fields are maps on all of `R`,
but the parallel-field predicate constrains them only on the stated interval.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A field along a curve is parallel when its covariant derivative is the zero
field.  This definition is chart-local through `IsCovariantDerivFieldAlongOn`,
so it applies to curves which leave every single chart. -/
def IsParallelCovariantFieldAlongOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (V : ℝ → E) (a b : ℝ) : Prop :=
  IsCovariantDerivFieldAlongOn (I := I) g γ V (fun _ => 0) a b

section Regularity

variable [I.Boundaryless]

/-- **Math.** A globally `C¹` manifold curve is differentiable in every chart containing
its value. -/
theorem isChartDifferentiableOn_of_contMDiff {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    IsChartDifferentiableOn (I := I) γ a b := by
  intro t _ht α hsrc
  have hcompM : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (fun s => extChartAt I α (γ s)) t :=
    (contMDiffAt_extChartAt' (I := I) (n := 1) hsrc).comp t hγ.contMDiffAt
  exact hcompM.contDiffAt.differentiableAt (by norm_num)

/-- **Math.** On a chart window, the ordinary derivative of the chart reading of a
globally `C¹` manifold curve is continuous, including at the endpoints. -/
theorem continuousOn_deriv_extChartAt_comp_of_contMDiff
    {γ : ℝ → M} {a b : ℝ} {α : M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H α).source) :
    ContinuousOn (deriv (fun t => extChartAt I α (γ t))) (Icc a b) := by
  intro t ht
  have hcompM : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (fun s => extChartAt I α (γ s)) t :=
    (contMDiffAt_extChartAt' (I := I) (n := 1) (hsrc t ht)).comp t hγ.contMDiffAt
  have hcomp : ContDiffAt ℝ 1 (fun s => extChartAt I α (γ s)) t :=
    hcompM.contDiffAt
  have happ : ContinuousAt
      (fun s => fderiv ℝ (fun r => extChartAt I α (γ r)) s 1) t :=
    (hcomp.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  simpa only [fderiv_apply_one_eq_deriv] using happ.continuousWithinAt

end Regularity

section LocalExistence

variable [I.Boundaryless]

/-- **Math.** A parallel field with prescribed left-endpoint chart coordinates on a
single chart window, read back as an own-foot field along the manifold curve. -/
theorem exists_intrinsic_chart_parallelCovariant
    {g : RiemannianMetric I M} {γ : ℝ → M} {l r : ℝ} {β : M}
    (hlr : l ≤ r)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ)
    (hsrc : ∀ t ∈ Icc l r, γ t ∈ (chartAt H β).source)
    (P0 : E) :
    ∃ w : ℝ → E,
      IsCovariantDerivSolOn (I := I) g β (fun t => extChartAt I β (γ t))
        (chartVectorRep (I := I) γ β w)
        (chartVectorRep (I := I) γ β (fun _ => (0 : E))) l r
      ∧ chartVectorRep (I := I) γ β w l = P0
      ∧ (∀ t ∈ Icc l r, w t =
          tangentCoordChange I β (γ t) (γ t)
            (chartVectorRep (I := I) γ β w t)) := by
  let u : ℝ → E := fun t => extChartAt I β (γ t)
  have hu_cont : ContinuousOn u (Icc l r) := by
    intro t ht
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc t ht)).comp
        hγ.continuous.continuousAt).continuousWithinAt
  have hu'_cont : ContinuousOn (deriv u) (Icc l r) := by
    exact continuousOn_deriv_extChartAt_comp_of_contMDiff (I := I) hγ hsrc
  have hmem : ∀ t ∈ Icc l r, u t ∈ interior (extChartAt I β).target := by
    intro t ht
    rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
    exact (extChartAt I β).map_source
      (by rw [extChartAt_source]; exact hsrc t ht)
  have hcont := continuousOn_chartChristoffelContractionRight_comp
    (I := I) g β hu_cont hu'_cont hmem
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨wc, hwcl, hsys⟩ := exists_isParallelCoord_Icc (I := I) g β u hlr P0
    (K := ⟨max C 0, le_max_right C 0⟩) hcont (fun t ht => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hC t ht).trans (le_max_left C 0))
  let w : ℝ → E := fun t => tangentCoordChange I β (γ t) (γ t) (wc t)
  have hrep : ∀ t ∈ Icc l r, chartVectorRep (I := I) γ β w t = wc t := by
    intro t ht
    exact tangentCoordChange_realize_self (I := I) (hsrc t ht) (wc t)
  refine ⟨w, ?_, ?_, ?_⟩
  · intro t ht
    have hz : chartVectorRep (I := I) γ β (fun _ => (0 : E)) t = 0 := by
      simp [chartVectorRep_apply]
    rw [hrep t ht, hz, zero_sub]
    exact (hsys t ht).congr (fun y hy => hrep y hy) (hrep t ht)
  · rw [hrep l (left_mem_Icc.2 hlr), hwcl]
  · intro t ht
    show tangentCoordChange I β (γ t) (γ t) (wc t) =
      tangentCoordChange I β (γ t) (γ t)
        (chartVectorRep (I := I) γ β w t)
    rw [hrep t ht]

end LocalExistence

/-! ## Existence on a compact interval -/

section GlobalExistence

variable [I.Boundaryless]

/-- **Math.** A covariant-derivative certificate with zero derivative field is
the usual chart parallel-transport ODE certificate. -/
theorem IsCovariantDerivSolOn.isParallelSolOn_of_eq_zero
    {g : RiemannianMetric I M} {α : M} {u w D : ℝ → E} {a b : ℝ}
    (h : IsCovariantDerivSolOn (I := I) g α u w D a b)
    (hD : ∀ t ∈ Icc a b, D t = 0) :
    IsParallelSolOn (I := I) g α u w a b := by
  intro t ht
  have hderiv := h t ht
  rw [hD t ht, zero_sub] at hderiv
  exact hderiv

/-- **Math.** Existence of a parallel field with prescribed value at the left
endpoint along an arbitrary globally `C¹` curve on a compact interval.  The
curve may cross arbitrarily many charts. -/
theorem exists_parallelCovariantFieldAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (w₀ : E) :
    ∃ w : ℝ → E, IsParallelCovariantFieldAlongOn (I := I) g γ w a b ∧ w a = w₀ := by
  classical
  have hγc : ∀ t ∈ Icc a b, ContinuousAt γ t :=
    fun _t _ht => hγ.continuous.continuousAt
  have hdiff : IsChartDifferentiableOn (I := I) γ a b :=
    isChartDifferentiableOn_of_contMDiff (I := I) hγ
  -- Every time has a closed interval around it lying in the chart at its image.
  have hchart : ∀ c₀ ∈ Icc a b, ∃ ε > (0 : ℝ),
      ∀ s ∈ Icc (c₀ - ε) (c₀ + ε), γ s ∈ (chartAt H (γ c₀)).source := by
    intro c₀ hc₀
    have hpre := (hγc c₀ hc₀).preimage_mem_nhds
      ((chartAt H (γ c₀)).open_source.mem_nhds (mem_chart_source H (γ c₀)))
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 hpre
    refine ⟨ε / 2, by linarith, fun s hs => hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have hdist : |s - c₀| ≤ ε / 2 :=
      abs_le.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
    linarith
  -- Right endpoints up to which a left-seeded field has been constructed.
  let S : Set ℝ := {c | c ∈ Ioc a b ∧ ∃ w : ℝ → E,
    IsParallelCovariantFieldAlongOn (I := I) g γ w a c ∧ w a = w₀}
  obtain ⟨ε₀, hε₀, hball₀⟩ := hchart a ⟨le_rfl, hab.le⟩
  have hstep₀ : min b (a + ε₀) ∈ S := by
    let r₀ := min b (a + ε₀)
    have har₀ : a < r₀ := lt_min hab (by linarith)
    have hr₀b : r₀ ≤ b := min_le_left _ _
    have hsrc₀ : ∀ t ∈ Icc a r₀, γ t ∈ (chartAt H (γ a)).source :=
      fun t ht => hball₀ t ⟨by linarith [ht.1], le_trans ht.2
        (le_trans (min_le_right _ _) (by linarith))⟩
    obtain ⟨w₁, hcert₁, hw₁l, _hwread⟩ :=
      exists_intrinsic_chart_parallelCovariant (I := I) har₀.le hγ hsrc₀ w₀
    have hw₁a : w₁ a = w₀ := by
      have hread : chartVectorRep (I := I) γ (γ a) w₁ a = w₁ a := by
        rw [chartVectorRep_apply]
        exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) (γ a))
      rw [← hread, hw₁l]
    refine ⟨⟨har₀, hr₀b⟩, w₁, ?_, hw₁a⟩
    intro t₀ ht₀
    exact ⟨γ a, a, r₀, har₀, ht₀, subset_rfl, self_mem_nhdsWithin,
      hsrc₀, hcert₁⟩
  have hSne : S.Nonempty := ⟨_, hstep₀⟩
  have hSbdd : BddAbove S := ⟨b, fun _s hs => hs.1.2⟩
  let c := sSup S
  have hac : a < c :=
    lt_of_lt_of_le (lt_min hab (by linarith)) (le_csSup hSbdd hstep₀)
  have hcb : c ≤ b := csSup_le hSne fun _s hs => hs.1.2
  obtain ⟨ε, hε, hball⟩ := hchart c ⟨hac.le, hcb⟩
  have hδ : (0 : ℝ) < min ε (c - a) := lt_min hε (by linarith)
  obtain ⟨c', hc'S, hc'lt⟩ := exists_lt_of_lt_csSup hSne
    (show c - min ε (c - a) < sSup S by change c - min ε (c - a) < c; linarith)
  have hc'le : c' ≤ c := le_csSup hSbdd hc'S
  obtain ⟨hc'Ioc, w₁, hPar₁, hw₁a⟩ := hc'S
  let l := max a (c - ε)
  let r := min b (c + ε)
  have hlc' : l < c' := max_lt hc'Ioc.1 (by
    have hmin := min_le_left ε (c - a)
    linarith)
  have hcr : c ≤ r := le_min hcb (by linarith)
  have hlc : l < c := lt_of_lt_of_le hlc' hc'le
  have hlr : l < r := lt_of_lt_of_le hlc hcr
  have hla : a ≤ l := le_max_left _ _
  have hrb : r ≤ b := min_le_left _ _
  have hsub_lr : Icc l r ⊆ Icc a b := Icc_subset_Icc hla hrb
  have hsrc_lr : ∀ t ∈ Icc l r, γ t ∈ (chartAt H (γ c)).source :=
    fun t ht => hball t ⟨le_trans (by
      have hmax := le_max_right a (c - ε)
      dsimp [l] at ht
      linarith) ht.1, le_trans ht.2 (min_le_right _ _)⟩
  have hsub_ac' : Icc a c' ⊆ Icc a b := Icc_subset_Icc le_rfl hc'Ioc.2
  have hsub_lc' : Icc l c' ⊆ Icc l r :=
    Icc_subset_Icc le_rfl (le_trans hc'le hcr)
  have hloc := hPar₁.isCovariantDerivSolOn_of_mem_source
    (fun t ht => hdiff t (hsub_ac' ht))
    (fun t ht => hγc t (hsub_ac' ht))
    (Icc_subset_Icc hla le_rfl)
    (fun t ht => hsrc_lr t (hsub_lc' ht))
  obtain ⟨w₂, hcert₂, hw₂l, _hwread₂⟩ :=
    exists_intrinsic_chart_parallelCovariant (I := I) hlr.le hγ hsrc_lr
      (chartVectorRep (I := I) γ (γ c) w₁ l)
  have hu_cont : ContinuousOn (fun t => extChartAt I (γ c) (γ t)) (Icc l c') := by
    intro t ht
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc_lr t (hsub_lc' ht))).comp
        hγ.continuous.continuousAt).continuousWithinAt
  have hu'_cont : ContinuousOn
      (deriv (fun t => extChartAt I (γ c) (γ t))) (Icc l c') :=
    continuousOn_deriv_extChartAt_comp_of_contMDiff (I := I) hγ
      (fun t ht => hsrc_lr t (hsub_lc' ht))
  have hmem : ∀ t ∈ Icc l c', extChartAt I (γ c) (γ t) ∈
      interior (extChartAt I (γ c)).target := by
    intro t ht
    rw [(isOpen_extChartAt_target (I := I) (γ c)).interior_eq]
    exact (extChartAt I (γ c)).map_source
      (by rw [extChartAt_source]; exact hsrc_lr t (hsub_lc' ht))
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_chartChristoffelContractionRight_comp (I := I) g (γ c)
      hu_cont hu'_cont hmem)
  have hKnn : ∀ t ∈ Icc l c',
      ‖chartChristoffelContractionRight (I := I) g (γ c)
        (deriv (fun s => extChartAt I (γ c) (γ s)) t)
        (extChartAt I (γ c) (γ t))‖₊ ≤
        (⟨max K 0, le_max_right K 0⟩ : ℝ≥0) := by
    intro t ht
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hK t ht).trans (le_max_left K 0)
  have hlocPar : IsParallelSolOn (I := I) g (γ c)
      (fun t => extChartAt I (γ c) (γ t))
      (chartVectorRep (I := I) γ (γ c) w₁) l c' :=
    hloc.isParallelSolOn_of_eq_zero (fun t _ht => by simp [chartVectorRep_apply])
  have hcert₂Par : IsParallelSolOn (I := I) g (γ c)
      (fun t => extChartAt I (γ c) (γ t))
      (chartVectorRep (I := I) γ (γ c) w₂) l c' :=
    (hcert₂.mono le_rfl (le_trans hc'le hcr)).isParallelSolOn_of_eq_zero
      (fun t _ht => by simp [chartVectorRep_apply])
  have hEq := isParallelSol_eqOn_Icc (I := I) g (γ c)
    (fun t => extChartAt I (γ c) (γ t)) hKnn hlocPar hcert₂Par hw₂l.symm
  have hwEq : ∀ t ∈ Icc l c', w₁ t = w₂ t := by
    intro t ht
    have hread := congrArg (tangentCoordChange I (γ c) (γ t) (γ t)) (hEq ht)
    rwa [chartVectorRep_apply, chartVectorRep_apply,
      tangentCoordChange_readback (I := I) (hsrc_lr t (hsub_lc' ht)) (w₁ t),
      tangentCoordChange_readback (I := I) (hsrc_lr t (hsub_lc' ht)) (w₂ t)] at hread
  let wg : ℝ → E := fun t => if t ≤ c' then w₁ t else w₂ t
  have hwg_eq_w₁ : ∀ t ∈ Icc a c', wg t = w₁ t :=
    fun t ht => if_pos ht.2
  have hwg_eq_w₂ : ∀ t ∈ Icc l r, wg t = w₂ t := by
    intro t ht
    by_cases htc : t ≤ c'
    · rw [show wg t = if t ≤ c' then w₁ t else w₂ t by rfl, if_pos htc]
      exact hwEq t ⟨ht.1, htc⟩
    · rw [show wg t = if t ≤ c' then w₁ t else w₂ t by rfl, if_neg htc]
  have hAlong : IsParallelCovariantFieldAlongOn (I := I) g γ wg a r := by
    intro t₀ ht₀
    by_cases ht₀c : t₀ < c'
    · obtain ⟨α, a₁, b₁, hab₁, ht₁, hsub₁, hnbhd₁, hsrc₁, hPar₁'⟩ :=
        hPar₁ t₀ ⟨ht₀.1, ht₀c.le⟩
      refine ⟨α, a₁, b₁, hab₁, ht₁,
        hsub₁.trans (Icc_subset_Icc le_rfl (le_trans hc'le hcr)), ?_, hsrc₁, ?_⟩
      · obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hnbhd₁
        refine mem_nhdsWithin.2 ⟨U ∩ Iio c', hUopen.inter isOpen_Iio, ⟨htU, ht₀c⟩,
          fun s hs => ?_⟩
        exact hUsub ⟨hs.1.1, ⟨hs.2.1, hs.1.2.le⟩⟩
      · refine hPar₁'.congr ?_ (fun _t _ht => rfl)
        intro t ht
        rw [chartVectorRep_apply, chartVectorRep_apply, hwg_eq_w₁ t (hsub₁ ht)]
    · rw [not_lt] at ht₀c
      refine ⟨γ c, l, r, hlr, ⟨le_trans hlc'.le ht₀c, ht₀.2⟩,
        Icc_subset_Icc hla le_rfl, ?_, hsrc_lr, ?_⟩
      · refine mem_nhdsWithin.2 ⟨Ioi l, isOpen_Ioi, lt_of_lt_of_le hlc' ht₀c,
          fun s hs => ⟨hs.1.le, hs.2.2⟩⟩
      · refine hcert₂.congr ?_ (fun _t _ht => rfl)
        intro t ht
        rw [chartVectorRep_apply, chartVectorRep_apply, hwg_eq_w₂ t ht]
  have hwga : wg a = w₀ := by
    rw [hwg_eq_w₁ a ⟨le_rfl, hc'Ioc.1.le⟩, hw₁a]
  have hrS : r ∈ S := ⟨⟨lt_of_lt_of_le hac hcr, hrb⟩, wg, hAlong, hwga⟩
  rcases lt_or_eq_of_le hcb with hlt | heqb
  · exfalso
    have hrc : r ≤ c := le_csSup hSbdd hrS
    have hcr' : c < r := lt_min hlt (by linarith)
    exact (not_lt_of_ge hrc) hcr'
  · have hrb' : r = b := by
      dsimp [r]
      rw [← heqb]
      exact min_eq_left (by linarith)
    obtain ⟨_, w, hPar, hwa⟩ := hrS
    exact ⟨w, hrb' ▸ hPar, hwa⟩

end GlobalExistence

/-! ## Linearity and uniqueness -/

section Uniqueness

variable [I.Boundaryless]

/-- **Math.** The difference of two chart covariant-derivative pairs has
covariant derivative equal to the difference of their derivative fields. -/
theorem IsCovariantDerivSolOn.sub
    {g : RiemannianMetric I M} {α : M} {u V DV W DW : ℝ → E} {a b : ℝ}
    (hV : IsCovariantDerivSolOn (I := I) g α u V DV a b)
    (hW : IsCovariantDerivSolOn (I := I) g α u W DW a b) :
    IsCovariantDerivSolOn (I := I) g α u
      (fun t => V t - W t) (fun t => DV t - DW t) a b := by
  intro t ht
  have h := (hV t ht).sub (hW t ht)
  change HasDerivWithinAt (V - W) _ (Icc a b) t
  convert h using 1
  rw [← chartChristoffelContractionRight_apply, map_sub,
    chartChristoffelContractionRight_apply, chartChristoffelContractionRight_apply]
  simp only [sub_eq_add_neg]
  abel

/-- **Math.** The difference of two parallel fields is parallel along an
arbitrary chart-differentiable continuous curve. -/
theorem IsParallelCovariantFieldAlongOn.sub
    {g : RiemannianMetric I M} {γ : ℝ → M} {V W : ℝ → E} {a b : ℝ}
    (hV : IsParallelCovariantFieldAlongOn (I := I) g γ V a b)
    (hW : IsParallelCovariantFieldAlongOn (I := I) g γ W a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    IsParallelCovariantFieldAlongOn (I := I) g γ (fun t => V t - W t) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hcertV⟩ := hV t₀ ht₀
  have hcertW := hW.isCovariantDerivSolOn_of_mem_source hdiff hγc hsub hsrc (β := α)
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc,
    (hcertV.sub hcertW).congr ?_ ?_⟩
  · intro t _ht
    simp only [chartVectorRep_apply, map_sub]
  · intro t _ht
    simp [chartVectorRep_apply]

/-- **Math.** The squared norm of a parallel field is constant along an
arbitrary chart-differentiable continuous curve. -/
theorem IsParallelCovariantFieldAlongOn.metricInner_self_eq
    {g : RiemannianMetric I M} {γ : ℝ → M} {V : ℝ → E} {a b : ℝ}
    (hV : IsParallelCovariantFieldAlongOn (I := I) g γ V a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    g.metricInner (γ s) (V s : TangentSpace I (γ s)) (V s) =
      g.metricInner (γ t) (V t : TangentSpace I (γ t)) (V t) := by
  let φ : ℝ → ℝ :=
    fun r => g.metricInner (γ r) (V r : TangentSpace I (γ r)) (V r)
  have hφc : ContinuousOn φ (Icc a b) :=
    hV.continuousOn_metricInner hV hdiff hγc
  have hderiv : ∀ r ∈ interior (Icc a b),
      HasDerivWithinAt φ 0 (interior (Icc a b)) r := by
    intro r hr
    have hr' : r ∈ Ioo a b := by rwa [interior_Icc] at hr
    have h := hV.hasDerivAt_metricInner_self hdiff hγc hr'
    simpa only [g.metricInner_zero_left, mul_zero] using h.hasDerivWithinAt
  have hmono : MonotoneOn φ (Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hφc hderiv
      (fun _r _hr => le_rfl)
  have hanti : AntitoneOn φ (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hφc hderiv
      (fun _r _hr => le_rfl)
  change φ s = φ t
  rcases le_total s t with hst | hts
  · exact le_antisymm (hmono hs ht hst) (hanti hs ht hst)
  · exact le_antisymm (hanti ht hs hts) (hmono ht hs hts)

/-! ### Pairing preservation and the transport map -/

/-- **Math.** The intrinsic pairing of two parallel fields is constant along an
arbitrary chart-differentiable continuous curve.  This is the bilinear form of
`metricInner_self_eq`; it is the metric-preservation statement needed to regard
parallel transport as an isometry between the endpoint tangent spaces. -/
theorem IsParallelCovariantFieldAlongOn.metricInner_eq
    {g : RiemannianMetric I M} {γ : ℝ → M} {V W : ℝ → E} {a b : ℝ}
    (hV : IsParallelCovariantFieldAlongOn (I := I) g γ V a b)
    (hW : IsParallelCovariantFieldAlongOn (I := I) g γ W a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    g.metricInner (γ s) (V s : TangentSpace I (γ s)) (W s) =
      g.metricInner (γ t) (V t : TangentSpace I (γ t)) (W t) := by
  change IsCovariantDerivFieldAlongOn (I := I) g γ V (fun _ => 0) a b at hV
  change IsCovariantDerivFieldAlongOn (I := I) g γ W (fun _ => 0) a b at hW
  let φ : ℝ → ℝ :=
    fun r => g.metricInner (γ r) (V r : TangentSpace I (γ r)) (W r)
  have hφc : ContinuousOn φ (Icc a b) :=
    hV.continuousOn_metricInner hW hdiff hγc
  have hderiv : ∀ r ∈ interior (Icc a b),
      HasDerivWithinAt φ 0 (interior (Icc a b)) r := by
    intro r hr
    have hr' : r ∈ Ioo a b := by rwa [interior_Icc] at hr
    have h := hV.hasDerivAt_metricInner hW hdiff hγc hr'
    simpa only [g.metricInner_zero_left, g.metricInner_zero_right, zero_add] using
      h.hasDerivWithinAt
  have hmono : MonotoneOn φ (Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hφc hderiv
      (fun _r _hr => le_rfl)
  have hanti : AntitoneOn φ (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hφc hderiv
      (fun _r _hr => le_rfl)
  change φ s = φ t
  rcases le_total s t with hst | hts
  · exact le_antisymm (hmono hs ht hst) (hanti hs ht hst)
  · exact le_antisymm (hanti ht hs hts) (hmono ht hs hts)

/-- **Math.** Uniqueness of parallel transport on the interval.  Two parallel
fields agreeing at any one time agree everywhere on the interval. -/
theorem IsParallelCovariantFieldAlongOn.eqOn_of_eq_at
    {g : RiemannianMetric I M} {γ : ℝ → M} {V W : ℝ → E} {a b t₀ : ℝ}
    (hV : IsParallelCovariantFieldAlongOn (I := I) g γ V a b)
    (hW : IsParallelCovariantFieldAlongOn (I := I) g γ W a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (ht₀ : t₀ ∈ Icc a b) (h₀ : V t₀ = W t₀) :
    Set.EqOn V W (Icc a b) := by
  have hD : IsParallelCovariantFieldAlongOn (I := I) g γ
      (fun t => V t - W t) a b := hV.sub hW hdiff hγc
  intro t ht
  have hconst := hD.metricInner_self_eq hdiff hγc ht ht₀
  have hD₀ : V t₀ - W t₀ = 0 := sub_eq_zero.2 h₀
  rw [hD₀] at hconst
  have hz : g.metricInner (γ t₀) (0 : TangentSpace I (γ t₀)) 0 = 0 :=
    g.metricInner_zero_left (γ t₀) 0
  have hzero : g.metricInner (γ t)
      ((V t - W t : E) : TangentSpace I (γ t)) (V t - W t) = 0 :=
    hconst.trans hz
  by_contra hne
  have hdiffne : (V t - W t : TangentSpace I (γ t)) ≠ 0 :=
    sub_ne_zero.2 hne
  exact absurd hzero (g.metricInner_self_pos (γ t) _ hdiffne).ne'

/-- **Math.** Left-endpoint existence and interval uniqueness, packaged in the
form used by do Carmo's parallel-transport proposition. -/
theorem exists_parallelCovariantFieldAlongOn_unique
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (w₀ : E) :
    ∃ w : ℝ → E,
      IsParallelCovariantFieldAlongOn (I := I) g γ w a b ∧ w a = w₀ ∧
      ∀ w' : ℝ → E, IsParallelCovariantFieldAlongOn (I := I) g γ w' a b →
        w' a = w₀ → Set.EqOn w' w (Icc a b) := by
  obtain ⟨w, hw, hwa⟩ := exists_parallelCovariantFieldAlongOn (I := I) hab hγ w₀
  refine ⟨w, hw, hwa, fun w' hw' hw'a => ?_⟩
  exact hw'.eqOn_of_eq_at hw
    (isChartDifferentiableOn_of_contMDiff (I := I) hγ)
    (fun _t _ht => hγ.continuous.continuousAt)
    ⟨le_rfl, hab.le⟩ (hw'a.trans hwa.symm)

end Uniqueness

/-! ## Transport from an arbitrary time -/

section ArbitrarySeed

variable [I.Boundaryless]

/-- **Math.** A constant scalar multiple of a chart covariant-derivative pair
has the correspondingly scaled covariant derivative. -/
theorem IsCovariantDerivSolOn.const_smul
    {g : RiemannianMetric I M} {α : M} {u V DV : ℝ → E} {a b : ℝ}
    (c : ℝ) (hV : IsCovariantDerivSolOn (I := I) g α u V DV a b) :
    IsCovariantDerivSolOn (I := I) g α u
      (fun t => c • V t) (fun t => c • DV t) a b := by
  intro t ht
  have h := (hV t ht).const_smul c
  change HasDerivWithinAt (c • V) _ (Icc a b) t
  convert h using 1
  rw [← chartChristoffelContractionRight_apply, map_smul,
    chartChristoffelContractionRight_apply, smul_sub]

/-- **Math.** A constant scalar multiple of a parallel field is parallel. -/
theorem IsParallelCovariantFieldAlongOn.smul
    {g : RiemannianMetric I M} {γ : ℝ → M} {V : ℝ → E} {a b : ℝ}
    (c : ℝ) (hV : IsParallelCovariantFieldAlongOn (I := I) g γ V a b) :
    IsParallelCovariantFieldAlongOn (I := I) g γ (fun t => c • V t) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hcertV⟩ := hV t₀ ht₀
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc,
    (hcertV.const_smul c).congr ?_ ?_⟩
  · intro t _ht
    simp only [chartVectorRep_apply, map_smul]
  · intro t _ht
    simp [chartVectorRep_apply]

/-- **Math.** The sum of two parallel fields is parallel along an arbitrary
chart-differentiable continuous curve. -/
theorem IsParallelCovariantFieldAlongOn.add
    {g : RiemannianMetric I M} {γ : ℝ → M} {V W : ℝ → E} {a b : ℝ}
    (hV : IsParallelCovariantFieldAlongOn (I := I) g γ V a b)
    (hW : IsParallelCovariantFieldAlongOn (I := I) g γ W a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    IsParallelCovariantFieldAlongOn (I := I) g γ (fun t => V t + W t) a b := by
  have hsub := hV.sub (hW.smul (-1)) hdiff hγc
  simpa [sub_eq_add_neg] using hsub

/-- **Math.** The canonical parallel field obtained by solving from the left
endpoint with the prescribed seed. -/
noncomputable def parallelCovariantFieldSeed
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (w₀ : E) : ℝ → E :=
  Classical.choose (exists_parallelCovariantFieldAlongOn (I := I) (g := g) hab hγ w₀)

/-- **Math.** The canonical left-seeded field is parallel. -/
theorem parallelCovariantFieldSeed_isParallel
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (w₀ : E) :
    IsParallelCovariantFieldAlongOn (I := I) g γ
      (parallelCovariantFieldSeed (I := I) g hab hγ w₀) a b :=
  (Classical.choose_spec
    (exists_parallelCovariantFieldAlongOn (I := I) (g := g) hab hγ w₀)).1

/-- **Math.** The canonical left-seeded field has the prescribed value at the
left endpoint. -/
theorem parallelCovariantFieldSeed_left
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (w₀ : E) :
    parallelCovariantFieldSeed (I := I) g hab hγ w₀ a = w₀ :=
  (Classical.choose_spec
    (exists_parallelCovariantFieldAlongOn (I := I) (g := g) hab hγ w₀)).2

/-- **Math.** Evaluation at a time in the interval of the canonical left-seeded
parallel field, as a linear endomorphism of the model tangent space. -/
noncomputable def parallelCovariantTransportAlong
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {t : ℝ} (ht : t ∈ Icc a b) :
    E →ₗ[ℝ] E where
  toFun w₀ := parallelCovariantFieldSeed (I := I) g hab hγ w₀ t
  map_add' x y := by
    have hdiff : IsChartDifferentiableOn (I := I) γ a b :=
      isChartDifferentiableOn_of_contMDiff (I := I) hγ
    have hγc : ∀ s ∈ Icc a b, ContinuousAt γ s :=
      fun _s _hs => hγ.continuous.continuousAt
    have hsum := (parallelCovariantFieldSeed_isParallel (I := I) g hab hγ x).add
      (parallelCovariantFieldSeed_isParallel (I := I) g hab hγ y) hdiff hγc
    have hseed := parallelCovariantFieldSeed_isParallel (I := I) g hab hγ (x + y)
    have hleft : parallelCovariantFieldSeed (I := I) g hab hγ (x + y) a =
        parallelCovariantFieldSeed (I := I) g hab hγ x a +
          parallelCovariantFieldSeed (I := I) g hab hγ y a := by
      rw [parallelCovariantFieldSeed_left, parallelCovariantFieldSeed_left,
        parallelCovariantFieldSeed_left]
    exact hseed.eqOn_of_eq_at hsum hdiff hγc ⟨le_rfl, hab.le⟩ hleft ht
  map_smul' c x := by
    have hdiff : IsChartDifferentiableOn (I := I) γ a b :=
      isChartDifferentiableOn_of_contMDiff (I := I) hγ
    have hγc : ∀ s ∈ Icc a b, ContinuousAt γ s :=
      fun _s _hs => hγ.continuous.continuousAt
    have hsmul :=
      (parallelCovariantFieldSeed_isParallel (I := I) g hab hγ x).smul c
    have hseed := parallelCovariantFieldSeed_isParallel (I := I) g hab hγ (c • x)
    have hleft : parallelCovariantFieldSeed (I := I) g hab hγ (c • x) a =
        c • parallelCovariantFieldSeed (I := I) g hab hγ x a := by
      rw [parallelCovariantFieldSeed_left, parallelCovariantFieldSeed_left]
    exact hseed.eqOn_of_eq_at hsmul hdiff hγc ⟨le_rfl, hab.le⟩ hleft ht

@[simp] theorem parallelCovariantTransportAlong_apply
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {t : ℝ} (ht : t ∈ Icc a b) (w₀ : E) :
    parallelCovariantTransportAlong (I := I) g hab hγ ht w₀ =
      parallelCovariantFieldSeed (I := I) g hab hγ w₀ t :=
  rfl

/-- **Math.** The two manifold-level notions of a parallel field agree.  The
chart-free covariant-derivative predicate is exactly the zero-derivative
specialization of the geodesic parallel-field predicate used by the Ch. 3
transport API. -/
theorem IsParallelFieldAlongOn.isParallelCovariantFieldAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {V : ℝ → E} {a b : ℝ}
    (hV : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ V a b) :
    IsParallelCovariantFieldAlongOn (I := I) g γ V a b := by
  exact hV.isCovariantDerivFieldAlongOn

/-- **Math.** Conversely, a zero covariant-derivative certificate is a parallel
field certificate in the original geodesic API.  This direction is useful when
feeding the arbitrary-curve construction into do Carmo's existing uniqueness
theorems (cf. `lem:dc-ch9-3-1-velocity-frame`). -/
theorem IsParallelCovariantFieldAlongOn.isParallelFieldAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {V : ℝ → E} {a b : ℝ}
    (hV : IsParallelCovariantFieldAlongOn (I := I) g γ V a b) :
    Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ V a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hcert⟩ := hV t₀ ht₀
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, ?_⟩
  intro t ht
  have hz : chartVectorRep (I := I) γ α (fun _ => (0 : E)) t = 0 := by
    simp [chartVectorRep_apply]
  have hc := hcert t ht
  rw [hz, zero_sub] at hc
  exact hc

/-- **Math.** On a geodesic, the arbitrary-curve transport map is the same map
as do Carmo's established `parallelTransportAlong`.  The proof converts the
left-seeded covariant field to the geodesic predicate and invokes uniqueness;
this keeps later Ch. 9 orientation arguments on one canonical transport map. -/
theorem parallelCovariantTransportAlong_eq_parallelTransportAlong
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn (I := I) g γ (Icc a b))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {t : ℝ} (ht : t ∈ Icc a b) :
    parallelCovariantTransportAlong (I := I) g hab hγ ht =
      Riemannian.Jacobi.parallelTransportAlong (E := E) (I := I) (g := g) (γ := γ) hab hgeo
        (fun _t _ht => hγ.continuous.continuousAt) ht := by
  let hγc : ∀ t ∈ Icc a b, ContinuousAt γ t :=
    fun _t _ht => hγ.continuous.continuousAt
  ext w
  have hnew := parallelCovariantFieldSeed_isParallel (I := I) g hab hγ w
  have hold : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ
      (parallelCovariantFieldSeed (I := I) g hab hγ w) a b :=
    hnew.isParallelFieldAlongOn
  have hleft : parallelCovariantFieldSeed (I := I) g hab hγ w a = w :=
    parallelCovariantFieldSeed_left (I := I) g hab hγ w
  have heq := Riemannian.Jacobi.parallelFieldSeed_eq (E := E) (I := I) (g := g) (γ := γ)
    (hab := hab) (hgeo := hgeo) (hγc := hγc) hold hleft t ht
  exact heq.symm

/-- **Math.** Parallel transport to the initial time is the identity. -/
@[simp] theorem parallelCovariantTransportAlong_left
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (w₀ : E) :
    parallelCovariantTransportAlong (I := I) g hab hγ
      (left_mem_Icc.2 hab.le) w₀ = w₀ :=
  parallelCovariantFieldSeed_left (I := I) g hab hγ w₀

/-- **Math.** At the initial time the transport determinant is `1`. -/
@[simp] theorem parallelCovariantTransportAlong_det_left
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    LinearMap.det (parallelCovariantTransportAlong (I := I) g hab hγ
      (left_mem_Icc.2 hab.le)) = 1 := by
  have hmap : parallelCovariantTransportAlong (I := I) g hab hγ
      (left_mem_Icc.2 hab.le) = LinearMap.id := by
    ext v
    exact parallelCovariantTransportAlong_left (I := I) g hab hγ v
  rw [hmap, LinearMap.det_id]

/-- **Math.** Parallel transport along an arbitrary globally `C¹` curve preserves
the Riemannian pairing between the endpoint tangent spaces. -/
theorem metricInner_parallelCovariantTransportAlong
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {t : ℝ} (ht : t ∈ Icc a b) (v w : E) :
    g.metricInner (γ t)
        (parallelCovariantTransportAlong (I := I) g hab hγ ht v :
          TangentSpace I (γ t))
        (parallelCovariantTransportAlong (I := I) g hab hγ ht w) =
      g.metricInner (γ a) (v : TangentSpace I (γ a)) w := by
  have h := (parallelCovariantFieldSeed_isParallel (I := I) g hab hγ v).metricInner_eq
    (parallelCovariantFieldSeed_isParallel (I := I) g hab hγ w)
    (isChartDifferentiableOn_of_contMDiff (I := I) hγ)
    (fun _s _hs => hγ.continuous.continuousAt)
    (left_mem_Icc.2 hab.le) ht
  simpa only [parallelCovariantTransportAlong_apply, parallelCovariantFieldSeed_left]
    using h.symm

/-- **Math.** Evaluation of parallel transport at any interval time is
injective: equality there propagates back to the left endpoint. -/
theorem parallelCovariantTransportAlong_injective
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Injective (parallelCovariantTransportAlong (I := I) g hab hγ ht) := by
  intro x y hxy
  have heq := (parallelCovariantFieldSeed_isParallel (I := I) g hab hγ x).eqOn_of_eq_at
    (parallelCovariantFieldSeed_isParallel (I := I) g hab hγ y)
    (isChartDifferentiableOn_of_contMDiff (I := I) hγ)
    (fun _s _hs => hγ.continuous.continuousAt) ht hxy
  have hleft := heq ⟨le_rfl, hab.le⟩
  rwa [parallelCovariantFieldSeed_left, parallelCovariantFieldSeed_left] at hleft

/-- **Math.** The determinant of parallel transport never vanishes.  Together
with `parallelCovariantTransportAlong_left`, this gives the algebraic part of
orientation preservation; fixing its sign additionally requires continuity in
a coherent oriented trivialization along the curve. -/
theorem parallelCovariantTransportAlong_det_ne_zero
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {t : ℝ} (ht : t ∈ Icc a b) :
    LinearMap.det (parallelCovariantTransportAlong (I := I) g hab hγ ht) ≠ 0 := by
  intro hdet
  have hker : (parallelCovariantTransportAlong (I := I) g hab hγ ht).ker ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
  exact hker (LinearMap.ker_eq_bot.mpr
    (parallelCovariantTransportAlong_injective (I := I) g hab hγ ht))

/-- **Math.** A continuous determinant representative of parallel transport has
positive sign throughout the interval.  The hypothesis `hd` is deliberately
explicit: establishing it requires a coherent oriented tangent trivialization,
which is separate from the chart-free parallel-field construction above. -/
theorem parallelCovariantTransportAlong_det_pos_of_continuousOn
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (d : ℝ → ℝ)
    (hd : ∀ s (hs : s ∈ Icc a b),
      d s = LinearMap.det (parallelCovariantTransportAlong (I := I) g hab hγ hs))
    (hcont : ContinuousOn d (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) :
    0 < LinearMap.det (parallelCovariantTransportAlong (I := I) g hab hγ ht) := by
  rw [← hd t ht]
  have hleft : d a = 1 := by
    rw [hd a (left_mem_Icc.2 hab.le), parallelCovariantTransportAlong_det_left]
  have hne : ∀ s (hs : s ∈ Icc a b), d s ≠ 0 := by
    intro s hs hz
    apply parallelCovariantTransportAlong_det_ne_zero (I := I) g hab hγ hs
    rw [← hd s hs]
    exact hz
  by_contra hnot
  have hle : d t ≤ 0 := le_of_not_gt hnot
  have hlt : d t < 0 := lt_of_le_of_ne hle (hne t ht)
  have hzmem : (0 : ℝ) ∈ Set.Icc (d t) (d a) := by
    constructor
    · exact hlt.le
    · rw [hleft]
      norm_num
  have hcont_at : ContinuousOn d (Icc a t) :=
    hcont.mono (Icc_subset_Icc le_rfl ht.2)
  obtain ⟨u, hu, hdu⟩ := (intermediate_value_Icc' ht.1 hcont_at) hzmem
  exact hne u (Icc_subset_Icc le_rfl ht.2 hu) hdu

/-- **Math.** Parallel transport from the left endpoint to any time in the
interval is a linear equivalence. -/
noncomputable def parallelCovariantTransportEquiv
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {t : ℝ} (ht : t ∈ Icc a b) :
    E ≃ₗ[ℝ] E :=
  LinearEquiv.ofInjectiveEndo (parallelCovariantTransportAlong (I := I) g hab hγ ht)
    (parallelCovariantTransportAlong_injective (I := I) g hab hγ ht)

@[simp] theorem parallelCovariantTransportEquiv_apply
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {t : ℝ} (ht : t ∈ Icc a b) (w₀ : E) :
    parallelCovariantTransportEquiv (I := I) g hab hγ ht w₀ =
      parallelCovariantTransportAlong (I := I) g hab hγ ht w₀ :=
  rfl

/-- **Math.** Existence and interval uniqueness of a parallel field with a
prescribed value at an arbitrary time of the interval.  Uniqueness is stated as
`EqOn` because fields are unconstrained outside the interval. -/
theorem exists_parallelCovariantFieldAlongOn_at
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b t₀ : ℝ} (hab : a < b)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (ht₀ : t₀ ∈ Icc a b) (w₀ : E) :
    ∃ w : ℝ → E,
      IsParallelCovariantFieldAlongOn (I := I) g γ w a b ∧ w t₀ = w₀ ∧
      ∀ w' : ℝ → E, IsParallelCovariantFieldAlongOn (I := I) g γ w' a b →
        w' t₀ = w₀ → Set.EqOn w' w (Icc a b) := by
  let P := parallelCovariantTransportEquiv (I := I) g hab hγ ht₀
  let x₀ : E := P.symm w₀
  let w := parallelCovariantFieldSeed (I := I) g hab hγ x₀
  have hw : IsParallelCovariantFieldAlongOn (I := I) g γ w a b :=
    parallelCovariantFieldSeed_isParallel (I := I) g hab hγ x₀
  have hwt₀ : w t₀ = w₀ := by
    change P x₀ = w₀
    exact P.apply_symm_apply w₀
  refine ⟨w, hw, hwt₀, fun w' hw' hw't₀ => ?_⟩
  exact hw'.eqOn_of_eq_at hw
    (isChartDifferentiableOn_of_contMDiff (I := I) hγ)
    (fun _s _hs => hγ.continuous.continuousAt) ht₀ (hw't₀.trans hwt₀.symm)

end ArbitrarySeed

end Riemannian.Variation
