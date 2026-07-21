import MorganTianLib.Ch01.ParallelTransfer
import MorganTianLib.Ch01.JacobiExistence

/-!
# Poincaré Ch. 1, §1.3 — parallel transport along a geodesic, across charts

`ParallelFrame` solves the parallel-transport ODE inside a *single* chart.  But
a geodesic of any appreciable length leaves every chart, and the comparison
theorems (`thm:sectional-curvature-comparison`, `thm:bishop-gromov`) integrate
along radial geodesics all the way out to the conjugate radius.  This file
removes the single-chart restriction.

* `IsParallelAlongOn g γ V a b` — the **manifold-level** statement that the
  intrinsic field `V` (with `V τ` the tangent vector at `γ τ`, carried in the
  chart at its own foot) is parallel along `γ` on `[a, b]`: near every time it
  admits *some* chart-local parallel certificate.  This is the exact analogue
  of `IsJacobiFieldAlongOn`, and it is chart-local by design precisely because
  no single chart covers the curve.
* `IsParallelAlongOn.isParallelSolOn_of_mem_source` — **localization**: on any
  subinterval whose `γ`-image lies in one chart, the patchwork certificate
  collapses to a single honest chart-`β` certificate.  This is what
  `IsParallelSolOn.transfer` buys us.
* `exists_intrinsic_chart_parallel` — the single-chart solve, read back to the
  feet of `γ`.
* `exists_isParallelAlongOn` — **existence of parallel transport with
  prescribed initial vector, along a geodesic crossing arbitrarily many
  charts**, by a supremum walk: extend the solution as far as possible, and at
  the supremum re-solve in a fresh chart, gluing by ODE uniqueness.
* `IsParallelAlongOn.metricInner_eq` — parallel transport is an **isometry**:
  the metric inner product of two parallel fields is constant along `γ`.  The
  chart-local constancy of `ParallelFrame` is upgraded to the whole interval by
  a second supremum walk.

Blueprint: `lem:parallel-frame`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1;
do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.6.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Generalities on the chart parallel system -/

/-- **Math.** A Grönwall bound for the parallel-transport coefficient on a
compact interval, from continuity. -/
theorem exists_nnnorm_chartChristoffelContractionRight_le
    (g : RiemannianMetric I M) (α : M) {u : ℝ → E} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn (deriv u) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b,
      ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_chartChristoffelContractionRight_comp (I := I) g α hu hu' hmem)
  refine ⟨⟨max C 0, le_max_right _ _⟩, fun t ht => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hC t ht).trans (le_max_left _ _)

/-- **Math.** The chart parallel system only depends on the values of the field
on the interval. -/
theorem IsParallelSolOn.congr {g : RiemannianMetric I M} {α : M}
    {u V V' : ℝ → E} {a b : ℝ}
    (h : IsParallelSolOn (I := I) g α u V a b)
    (hV : ∀ t ∈ Icc a b, V' t = V t) :
    IsParallelSolOn (I := I) g α u V' a b := by
  intro t ht
  rw [hV t ht]
  exact (h t ht).congr (fun y hy => hV y hy) (hV t ht)

/-- **Math.** The chart parallel system restricts to a subinterval. -/
theorem IsParallelSolOn.mono {g : RiemannianMetric I M} {α : M}
    {u V : ℝ → E} {a b a' b' : ℝ}
    (h : IsParallelSolOn (I := I) g α u V a b) (ha : a ≤ a') (hb : b' ≤ b) :
    IsParallelSolOn (I := I) g α u V a' b' :=
  fun t ht => (h t (Icc_subset_Icc ha hb ht)).mono (Icc_subset_Icc ha hb)

/-! ### Parallel fields along a geodesic -/

/-- **Math.** The field `V` (with `V τ` the chart-at-its-own-foot reading of a
tangent vector at `γ τ`) is **parallel along `γ` on `[a, b]`**: near every time
of `[a, b]` there is a chart whose source contains a piece of `γ` around that
time, in which the chart reading of `V` solves the parallel-transport ODE.

Like `IsJacobiFieldAlongOn`, this is deliberately a *patchwork* condition: a
geodesic need not stay in any one chart.  Chart-change covariance
(`IsParallelSolOn.transfer`) is what makes it coherent, and it is upgraded to a
single-chart certificate on any subinterval that does stay in one chart by
`IsParallelAlongOn.isParallelSolOn_of_mem_source`.

Blueprint: `lem:parallel-frame`. -/
def IsParallelAlongOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (V : ℝ → E) (a b : ℝ) : Prop :=
  ∀ t₀ ∈ Icc a b, ∃ (α : M) (a' b' : ℝ), a' < b' ∧ t₀ ∈ Icc a' b' ∧
    Icc a' b' ⊆ Icc a b ∧ Icc a' b' ∈ 𝓝[Icc a b] t₀ ∧
    (∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H α).source) ∧
    IsParallelSolOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (chartVectorRep (I := I) γ α V) a' b'

section Localize

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Localization.** A parallel field along a geodesic restricts, on
any subinterval whose `γ`-image lies in the source of one chart `β`, to a
chart-`β` certificate on the whole subinterval: each chart-local witness
transfers to `β` (`IsParallelSolOn.transfer`) on the intersected interval, and
the certificates glue by locality of `HasDerivWithinAt`. -/
theorem IsParallelAlongOn.isParallelSolOn_of_mem_source
    {g : RiemannianMetric I M} {γ : ℝ → M} {V : ℝ → E} {a b : ℝ}
    (hPar : IsParallelAlongOn (I := I) g γ V a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {β : M} {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (hsrcβ : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H β).source) :
    IsParallelSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
      (chartVectorRep (I := I) γ β V) c d := by
  have key : ∀ t ∈ Icc c d, ∃ a' b' : ℝ, t ∈ Icc a' b' ∧
      Icc a' b' ⊆ Icc c d ∧ Icc a' b' ∈ 𝓝[Icc c d] t ∧
      IsParallelSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
        (chartVectorRep (I := I) γ β V) a' b' := by
    intro t ht
    obtain ⟨α', a₁, b₁, hab₁, ht₁, hsub₁, hnbhd₁, hsrc₁, hP₁⟩ :=
      hPar t (hsub ht)
    refine ⟨max a₁ c, min b₁ d, ⟨max_le ht₁.1 ht.1,
      le_min ht₁.2 ht.2⟩, ?_, ?_, ?_⟩
    · exact Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
    · obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hnbhd₁
      refine mem_nhdsWithin.2 ⟨U, hUopen, htU, fun σ hσ => ?_⟩
      have hσ₁ : σ ∈ Icc a₁ b₁ := hUsub ⟨hσ.1, hsub hσ.2⟩
      exact ⟨max_le hσ₁.1 hσ.2.1, le_min hσ₁.2 hσ.2.2⟩
    · have hgeo' : IsGeodesicOn (I := I) g γ (Icc (max a₁ c) (min b₁ d)) :=
        fun τ hτ => hgeo τ (hsub ⟨le_trans (le_max_right _ _) hτ.1,
          le_trans hτ.2 (min_le_right _ _)⟩)
      have hγc' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d), ContinuousAt γ τ :=
        fun τ hτ => hγc τ (hsub ⟨le_trans (le_max_right _ _) hτ.1,
          le_trans hτ.2 (min_le_right _ _)⟩)
      have hsrcα' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d),
          γ τ ∈ (chartAt H α').source :=
        fun τ hτ => hsrc₁ τ ⟨le_trans (le_max_left _ _) hτ.1,
          le_trans hτ.2 (min_le_left _ _)⟩
      have hsrcβ' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d),
          γ τ ∈ (chartAt H β).source :=
        fun τ hτ => hsrcβ τ ⟨le_trans (le_max_right _ _) hτ.1,
          le_trans hτ.2 (min_le_right _ _)⟩
      exact (hP₁.mono (le_max_left _ _) (min_le_left _ _)).transfer
        hgeo' hγc' hsrcα' hsrcβ'
  intro t ht
  obtain ⟨a', b', ht', _hsub', hnbhd', hcert⟩ := key t ht
  exact (hcert t ht').mono_of_mem_nhdsWithin hnbhd'

/-! ### Single-chart solve and readback -/

/-- **Math.** A single-chart parallel field with prescribed chart reading at
the left endpoint, returned as an intrinsic field along `γ`: solve the chart
parallel ODE (`Riemannian.exists_isParallelCoord_Icc`) and read the solution
back to the feet of `γ`. -/
theorem exists_intrinsic_chart_parallel
    {g : RiemannianMetric I M} {γ : ℝ → M} {l r : ℝ} {β : M}
    (hlr : l ≤ r)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc l r))
    (hγc : ∀ t ∈ Icc l r, ContinuousAt γ t)
    (hsrc : ∀ τ ∈ Icc l r, γ τ ∈ (chartAt H β).source)
    (P0 : E) :
    ∃ V : ℝ → E,
      IsParallelSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
        (chartVectorRep (I := I) γ β V) l r
      ∧ chartVectorRep (I := I) γ β V l = P0
      ∧ (∀ τ ∈ Icc l r, V τ
          = tangentCoordChange I β (γ τ) (γ τ)
              (chartVectorRep (I := I) γ β V τ)) := by
  have hu_cont : ContinuousOn (fun τ => extChartAt I β (γ τ)) (Icc l r) := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc τ hτ)).comp
        (hγc τ hτ)).continuousWithinAt
  have hu'_cont : ContinuousOn (deriv (fun τ => extChartAt I β (γ τ)))
      (Icc l r) := fun τ hτ =>
    (hgeo.continuousAt_deriv_extChartAt hτ (hγc τ hτ)
      (hsrc τ hτ)).continuousWithinAt
  have hmem : ∀ τ ∈ Icc l r, (fun τ' => extChartAt I β (γ τ')) τ
      ∈ interior (extChartAt I β).target := by
    intro τ hτ
    rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
    exact (extChartAt I β).map_source
      (by rw [extChartAt_source]; exact hsrc τ hτ)
  have hcont := continuousOn_chartChristoffelContractionRight_comp (I := I) g β
    hu_cont hu'_cont hmem
  obtain ⟨K, hK⟩ := exists_nnnorm_chartChristoffelContractionRight_le (I := I)
    g β hu_cont hu'_cont hmem
  obtain ⟨Vc, hVcl, hsys⟩ :=
    exists_isParallelCoord_Icc (I := I) g β (fun τ => extChartAt I β (γ τ))
      hlr P0 hcont hK
  refine ⟨fun τ => tangentCoordChange I β (γ τ) (γ τ) (Vc τ), ?_, ?_, ?_⟩
  · -- the readback has chart reading `Vc` on `[l, r]`
    refine IsParallelSolOn.congr (V := Vc) hsys ?_
    intro τ hτ
    show tangentCoordChange I (γ τ) β (γ τ)
      (tangentCoordChange I β (γ τ) (γ τ) (Vc τ)) = Vc τ
    exact tangentCoordChange_realize_self (I := I) (hsrc τ hτ) (Vc τ)
  · show tangentCoordChange I (γ l) β (γ l)
      (tangentCoordChange I β (γ l) (γ l) (Vc l)) = P0
    rw [tangentCoordChange_realize_self (I := I)
      (hsrc l (left_mem_Icc.2 hlr)) (Vc l)]
    exact hVcl
  · intro τ hτ
    show tangentCoordChange I β (γ τ) (γ τ) (Vc τ)
      = tangentCoordChange I β (γ τ) (γ τ)
          (tangentCoordChange I (γ τ) β (γ τ)
            (tangentCoordChange I β (γ τ) (γ τ) (Vc τ)))
    rw [tangentCoordChange_realize_self (I := I) (hsrc τ hτ) (Vc τ)]

end Localize

/-! ### Existence of parallel transport across charts -/

section Existence

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Existence of parallel transport along a geodesic** with
prescribed initial vector (Morgan–Tian §1.3; `lem:parallel-frame`).  The
geodesic may cross arbitrarily many charts: the solution is continued by a
supremum walk, gluing single-chart solutions by ODE uniqueness through the
chart-change covariance of the parallel system (`IsParallelSolOn.transfer`).

Blueprint: `lem:parallel-frame`. -/
theorem exists_isParallelAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (V₀ : TangentSpace I (γ a)) :
    ∃ V : ℝ → E, IsParallelAlongOn (I := I) g γ V a b ∧ V a = V₀ := by
  classical
  -- a uniform chart interval around each time
  have hchart : ∀ c0 ∈ Icc a b, ∃ ε > (0 : ℝ),
      ∀ σ ∈ Icc (c0 - ε) (c0 + ε), γ σ ∈ (chartAt H (γ c0)).source := by
    intro c0 hc0
    have h1 := (hγc c0 hc0).preimage_mem_nhds
      ((chartAt H (γ c0)).open_source.mem_nhds (mem_chart_source H (γ c0)))
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 h1
    refine ⟨ε / 2, by linarith, fun σ hσ => hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have h2 : |σ - c0| ≤ ε / 2 :=
      abs_le.2 ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    linarith
  -- the set of right endpoints up to which a solution exists
  set S : Set ℝ := {c | c ∈ Ioc a b ∧ ∃ V : ℝ → E,
    IsParallelAlongOn (I := I) g γ V a c ∧ V a = V₀} with hS
  -- initial step: a single-chart solution near `a`
  obtain ⟨ε₀, hε₀, hball₀⟩ := hchart a ⟨le_refl a, hab.le⟩
  have hstep0 : min b (a + ε₀) ∈ S := by
    set r₀ := min b (a + ε₀) with hr₀
    have har₀ : a < r₀ := lt_min hab (by linarith)
    have hr₀b : r₀ ≤ b := min_le_left _ _
    have hsub₀ : Icc a r₀ ⊆ Icc a b := Icc_subset_Icc le_rfl hr₀b
    have hsrc₀ : ∀ τ ∈ Icc a r₀, γ τ ∈ (chartAt H (γ a)).source :=
      fun τ hτ => hball₀ τ ⟨by linarith [hτ.1], le_trans hτ.2
        (le_trans (min_le_right _ _) (by linarith))⟩
    obtain ⟨V1, hcert1, hV1l, _hVred⟩ :=
      exists_intrinsic_chart_parallel (I := I) har₀.le
        (fun τ hτ => hgeo τ (hsub₀ hτ)) (fun τ hτ => hγc τ (hsub₀ hτ))
        hsrc₀ (V₀ : E)
    have hV1a : V1 a = V₀ := by
      have h1 : chartVectorRep (I := I) γ (γ a) V1 a = V1 a := by
        rw [chartVectorRep_apply]
        exact tangentCoordChange_self (I := I)
          (mem_extChartAt_source (I := I) (γ a))
      rw [← h1, hV1l]
    refine ⟨⟨har₀, hr₀b⟩, V1, ?_, hV1a⟩
    intro t₀ ht₀
    exact ⟨γ a, a, r₀, har₀, ht₀, subset_rfl, self_mem_nhdsWithin,
      hsrc₀, hcert1⟩
  have hne : S.Nonempty := ⟨_, hstep0⟩
  have hbdd : BddAbove S := ⟨b, fun s hs => hs.1.2⟩
  set c := sSup S with hc
  have hac : a < c :=
    lt_of_lt_of_le (lt_min hab (by linarith)) (le_csSup hbdd hstep0)
  have hcb : c ≤ b := csSup_le hne fun s hs => hs.1.2
  -- chart at the supremum
  obtain ⟨ε, hε, hball⟩ := hchart c ⟨hac.le, hcb⟩
  -- a solved endpoint close below the supremum
  have hδ : (0 : ℝ) < min ε (c - a) := lt_min hε (by linarith)
  obtain ⟨c', hc'S, hc'lt⟩ :=
    exists_lt_of_lt_csSup hne (show c - min ε (c - a) < sSup S by
      rw [← hc]; linarith)
  have hc'le : c' ≤ c := le_csSup hbdd hc'S
  obtain ⟨hc'Ioc, V1, hPar1, hV1a⟩ := hc'S
  -- the gluing window
  set l := max a (c - ε) with hl
  set r := min b (c + ε) with hr
  have hlc' : l < c' := max_lt hc'Ioc.1
    (by have := min_le_left ε (c - a); linarith)
  have hcr : c ≤ r := le_min hcb (by linarith)
  have hlc : l < c := lt_of_lt_of_le hlc' hc'le
  have hlr : l < r := lt_of_lt_of_le hlc hcr
  have hla : a ≤ l := le_max_left _ _
  have hrb : r ≤ b := min_le_left _ _
  have hsub_lr : Icc l r ⊆ Icc a b := Icc_subset_Icc hla hrb
  have hsrc_lr : ∀ τ ∈ Icc l r, γ τ ∈ (chartAt H (γ c)).source :=
    fun τ hτ => hball τ ⟨le_trans (by have := le_max_right a (c - ε); linarith)
      hτ.1, le_trans hτ.2 (min_le_right _ _)⟩
  have hgeo_lr : IsGeodesicOn (I := I) g γ (Icc l r) :=
    fun τ hτ => hgeo τ (hsub_lr hτ)
  have hγc_lr : ∀ τ ∈ Icc l r, ContinuousAt γ τ :=
    fun τ hτ => hγc τ (hsub_lr hτ)
  -- localize the old solution into the chart at `γ c` on `[l, c']`
  have hsub_ac' : Icc a c' ⊆ Icc a b := Icc_subset_Icc le_rfl hc'Ioc.2
  have hsub_lc' : Icc l c' ⊆ Icc l r :=
    Icc_subset_Icc le_rfl (le_trans hc'le hcr)
  have hloc := hPar1.isParallelSolOn_of_mem_source
    (fun τ hτ => hgeo τ (hsub_ac' hτ)) (fun τ hτ => hγc τ (hsub_ac' hτ))
    (Icc_subset_Icc hla le_rfl)
    (fun τ hτ => hsrc_lr τ (hsub_lc' hτ))
  -- solve in the chart at `γ c` on `[l, r]` with matched data at `l`
  obtain ⟨V2, hcert2, hV2l, _hVred2⟩ :=
    exists_intrinsic_chart_parallel (I := I) hlr.le hgeo_lr hγc_lr hsrc_lr
      (chartVectorRep (I := I) γ (γ c) V1 l)
  -- coefficient bound for uniqueness on `[l, c']`
  have hu_cont : ContinuousOn (fun τ => extChartAt I (γ c) (γ τ))
      (Icc l c') := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc_lr τ (hsub_lc' hτ))).comp
        (hγc_lr τ (hsub_lc' hτ))).continuousWithinAt
  have hu'_cont : ContinuousOn
      (deriv (fun τ => extChartAt I (γ c) (γ τ))) (Icc l c') := fun τ hτ =>
    (hgeo_lr.continuousAt_deriv_extChartAt (hsub_lc' hτ)
      (hγc_lr τ (hsub_lc' hτ)) (hsrc_lr τ (hsub_lc' hτ))).continuousWithinAt
  have hmem : ∀ τ ∈ Icc l c', (fun τ' => extChartAt I (γ c) (γ τ')) τ
      ∈ interior (extChartAt I (γ c)).target := by
    intro τ hτ
    rw [(isOpen_extChartAt_target (I := I) (γ c)).interior_eq]
    exact (extChartAt I (γ c)).map_source
      (by rw [extChartAt_source]; exact hsrc_lr τ (hsub_lc' hτ))
  obtain ⟨K, hK⟩ := exists_nnnorm_chartChristoffelContractionRight_le (I := I)
    g (γ c) hu_cont hu'_cont hmem
  -- ODE uniqueness: the two solutions agree on `[l, c']`
  have hEq := IsParallelSolOn.eqOn_of_left hK hloc
    (hcert2.mono le_rfl (le_trans hc'le hcr)) hV2l.symm
  have hVeq : ∀ τ ∈ Icc l c', V1 τ = V2 τ := by
    intro τ hτ
    have h1 := hEq hτ
    have h2 := congrArg (tangentCoordChange I (γ c) (γ τ) (γ τ)) h1
    rwa [chartVectorRep_apply, chartVectorRep_apply,
      tangentCoordChange_readback (I := I) (hsrc_lr τ (hsub_lc' hτ)) (V1 τ),
      tangentCoordChange_readback (I := I) (hsrc_lr τ (hsub_lc' hτ)) (V2 τ)]
      at h2
  -- the glued field
  set Vg : ℝ → E := fun τ => if τ ≤ c' then V1 τ else V2 τ with hVg
  have hVg_eq_V1 : ∀ τ ∈ Icc a c', Vg τ = V1 τ :=
    fun τ hτ => if_pos hτ.2
  have hVg_eq_V2 : ∀ τ ∈ Icc l r, Vg τ = V2 τ := by
    intro τ hτ
    by_cases hτc : τ ≤ c'
    · show (if τ ≤ c' then V1 τ else V2 τ) = V2 τ
      rw [if_pos hτc]
      exact hVeq τ ⟨hτ.1, hτc⟩
    · show (if τ ≤ c' then V1 τ else V2 τ) = V2 τ
      rw [if_neg hτc]
  -- the glued field is parallel on `[a, r]`
  have hAlong : IsParallelAlongOn (I := I) g γ Vg a r := by
    intro t₀ ht₀
    by_cases ht₀c : t₀ < c'
    · -- reuse the old chart-local witness below `c'`
      obtain ⟨α', a₁, b₁, hab₁, ht₁, hsub₁, hnbhd₁, hsrc₁, hP₁⟩ :=
        hPar1 t₀ ⟨ht₀.1, ht₀c.le⟩
      refine ⟨α', a₁, b₁, hab₁, ht₁,
        hsub₁.trans (Icc_subset_Icc le_rfl (le_trans hc'le hcr)), ?_,
        hsrc₁, ?_⟩
      · obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hnbhd₁
        refine mem_nhdsWithin.2 ⟨U ∩ Iio c', hUopen.inter isOpen_Iio,
          ⟨htU, ht₀c⟩, fun σ hσ => ?_⟩
        exact hUsub ⟨hσ.1.1, ⟨hσ.2.1, hσ.1.2.le⟩⟩
      · refine hP₁.congr ?_
        intro τ hτ
        rw [chartVectorRep_apply, chartVectorRep_apply,
          hVg_eq_V1 τ (hsub₁ hτ)]
    · -- above `c'`, use the chart at `γ c` on `[l, r]`
      rw [not_lt] at ht₀c
      refine ⟨γ c, l, r, hlr, ⟨le_trans hlc'.le ht₀c, ht₀.2⟩,
        Icc_subset_Icc hla le_rfl, ?_, hsrc_lr, ?_⟩
      · refine mem_nhdsWithin.2 ⟨Ioi l, isOpen_Ioi,
          lt_of_lt_of_le hlc' ht₀c, fun σ hσ => ?_⟩
        exact ⟨hσ.1.le, hσ.2.2⟩
      · refine hcert2.congr ?_
        intro τ hτ
        rw [chartVectorRep_apply, chartVectorRep_apply, hVg_eq_V2 τ hτ]
  have hVga : Vg a = V₀ := by
    have h1 : Vg a = V1 a := hVg_eq_V1 a ⟨le_refl a, hc'Ioc.1.le⟩
    rw [h1, hV1a]
  have hrS : r ∈ S := ⟨⟨lt_of_lt_of_le hac hcr, hrb⟩, Vg, hAlong, hVga⟩
  -- conclude: the supremum must be `b`, and then `r = b`
  rcases lt_or_eq_of_le hcb with hlt | heqb
  · exfalso
    have h1 : r ≤ c := le_csSup hbdd hrS
    have h2 : c < r := lt_min hlt (by linarith)
    linarith
  · have hrb' : r = b := by
      rw [hr, ← heqb]
      exact min_eq_left (by linarith)
    obtain ⟨_, V, hPar, hVa⟩ := hrS
    exact ⟨V, hrb' ▸ hPar, hVa⟩

end Existence

end MorganTianLib

end
