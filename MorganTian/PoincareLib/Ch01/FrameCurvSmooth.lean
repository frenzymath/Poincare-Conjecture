import PoincareLib.Ch01.FrameRadialBridge
import PoincareLib.Ch01.GeodesicRegularity

/-!
# Poincaré Ch. 1, §1.4 — smoothness in `t` of the frame Jacobi operator

`FrameCurvContinuity` / `FrameRadialBridge` prove that the frame curvature
coefficient `ℛᵢⱼ(t)` and the frame Jacobi operator `frameCurvOp g γ e t` are
**continuous** in `t` along a geodesic.  That is enough to run the ODE theory
(`IsRadialJacobi`), but it caps every solution of the Jacobi equation
`y″ + ℛ y = 0` at `C²`, whereas the second-variation machinery
(`deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`) demands `C³` data.
This file removes the cap: **`frameCurvOp` is `C^n` in `t` for every `n`.**

The route is the ODE bootstrap of `GeodesicRegularity`.  Two ingredients:

* `contDiffOn_firstOrderLinearODE` — the **parallel-transport bootstrap**, the
  manifold-free companion of `contDiffOn_secondOrderODE`.  If `V′ = −Γ(u)(u′, V)`
  on an **open** `J`, with `Γ` of class `C^∞` on an open `U ⊇ u(J)` and `u`, `u′`
  of class `C^∞` on `J`, then `V` is `C^n` on `J` for every `n`.  The induction is
  the same single line: `V` is differentiable with `V′ = −Γ(u)(u′, V)` a `C^n`
  expression in `C^n` data, so `contDiffOn_succ_iff_deriv_of_isOpen` (openness is
  load-bearing) upgrades `V` from `C^n` to `C^{n+1}`.  The equation is *linear* and
  *first order*, so this is strictly easier than the geodesic bootstrap.

* `contDiffOn_chartVectorRep_of_isParallelAlongOn` — its geometric corollary: a
  **parallel frame along a geodesic is `C^n` in `t`**, read in a fixed chart, on
  an open set of times whose `γ`-image stays in that chart.  The coefficient is
  the real Levi-Civita `Γ = chartChristoffelBilin g β` (`C^∞` on the chart-target
  interior), and the curve `u = φ_β ∘ γ` is `C^∞` by
  `contDiffOn_chartReading_of_isGeodesicOn`.

With those in hand, the fixed-chart formula `frameCurv_eq_chart`,

`ℛᵢⱼ(τ) = −⟨ℛ_chart(u τ)(u̇ τ)(Eⱼ,β(τ)), Eᵢ,β(τ)⟩_{G(u τ)}`,

exhibits `ℛᵢⱼ` as a `C^n` expression in `C^n` data: the chart curvature
endomorphism is a polynomial in `Γ` and `∂Γ` evaluated along `u` and `u̇`
(`contDiffOn_chartCurvatureEndo_comp'`), the frame readings are `C^n` by the
bootstrap, and the chart Gram pairing is `C^∞` in the foot
(`contDiffOn_chartMetricInner_comp`).  Smoothness is local, so — exactly as for
continuity — the single-chart statement glues along a geodesic crossing
arbitrarily many charts (`contDiffOn_of_locally_contDiffOn`).

The times form the **open** interval `Ioo a b`: openness is what the bootstrap
consumes, and it is no loss, since the geometric situation always extends the
geodesic a little past the interval of interest (`Icc c d ⊆ Ioo a b`, see
`contDiffOn_frameCurvOp_Icc`).

Main results:

* `contDiffOn_firstOrderLinearODE` — the parallel-transport bootstrap;
* `contDiffOn_chartVectorRep_of_isParallelAlongOn` — a parallel frame is `C^n`;
* `contDiffOn_frameCurv` — the frame curvature coefficient is `C^n` in `t`;
* `contDiffOn_frameCurvOp` (and `contDiffOn_frameCurvOp_infty`,
  `contDiffOn_frameCurvOp_Icc`) — **the frame Jacobi operator is `C^n` in `t`**,
  a drop-in upgrade of `continuousOn_frameCurvOp`.

Blueprint: `lem:jacobi-frame-reduction`, `prop:minimal-geodesic-no-conjugate`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

/-! ### The manifold-free bootstrap for a linear first-order ODE -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Math.** **ODE bootstrap for the parallel-transport equation.**  Let `J ⊆ ℝ`
be open, `U ⊆ E` a set carrying a `C^∞` coefficient map
`Γ : E → E →L[ℝ] E →L[ℝ] E`, and let `u : ℝ → E` be a curve of class `C^∞` with
`C^∞` derivative whose foot stays in `U`.  If `V : ℝ → E` satisfies the linear
first-order system

`V′(t) = −Γ(u t)(u′ t, V t)` for all `t ∈ J`,

then `V` is `C^n` on `J`, for every `n`.

*Proof.*  Induction on `n`.  For `n = 0`, `V` is differentiable, hence continuous.
For the step, assume `V` is `C^n` on `J`.  Then `V′ = −Γ(u)(u′, V)` is a `C^n`
expression in `C^n` data (`Γ ∘ u` is `C^n` because `Γ` is `C^∞` on `U` and `u` maps
`J` to `U`; `u′` and `V` are `C^n`), so `V′` is `C^n` on `J`, and — `J` being
**open** — `contDiffOn_succ_iff_deriv_of_isOpen` upgrades `V` to `C^{n+1}`.  ∎

This is the first-order linear companion of `contDiffOn_secondOrderODE`; as there,
no completeness, no finite-dimensionality and no uniqueness theory is used. -/
theorem contDiffOn_firstOrderLinearODE
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u V : ℝ → E} {J : Set ℝ} {U : Set E}
    (hJ : IsOpen J) (hΓ : ContDiffOn ℝ ∞ Γ U)
    (hmem : ∀ t ∈ J, u t ∈ U)
    (hu : ContDiffOn ℝ ∞ u J) (hu' : ContDiffOn ℝ ∞ (deriv u) J)
    (hV : ∀ t ∈ J, HasDerivAt V (-(Γ (u t) (deriv u t) (V t))) t)
    (n : ℕ) :
    ContDiffOn ℝ n V J := by
  have hdV : DifferentiableOn ℝ V J := fun t ht =>
    (hV t ht).differentiableAt.differentiableWithinAt
  have hdd : ∀ t ∈ J, deriv V t = -(Γ (u t) (deriv u t) (V t)) :=
    fun t ht => (hV t ht).deriv
  have hmaps : Set.MapsTo u J U := fun t ht => hmem t ht
  induction n with
  | zero => exact contDiffOn_zero.mpr hdV.continuousOn
  | succ n ih =>
    have hΓn : ContDiffOn ℝ n Γ U := contDiffOn_infty.mp hΓ n
    have hun : ContDiffOn ℝ n u J := contDiffOn_infty.mp hu n
    have hu'n : ContDiffOn ℝ n (deriv u) J := contDiffOn_infty.mp hu' n
    have hrhs : ContDiffOn ℝ n (fun t => -(Γ (u t) (deriv u t) (V t))) J :=
      (((hΓn.comp hun hmaps).clm_apply hu'n).clm_apply ih).neg
    have hdV_n : ContDiffOn ℝ n (deriv V) J := hrhs.congr hdd
    exact (contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨hdV, by simp, hdV_n⟩

/-- **Math.** The solution of the parallel-transport ODE is `C^∞` on an open set of
times. -/
theorem contDiffOn_infty_firstOrderLinearODE
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {u V : ℝ → E} {J : Set ℝ} {U : Set E}
    (hJ : IsOpen J) (hΓ : ContDiffOn ℝ ∞ Γ U)
    (hmem : ∀ t ∈ J, u t ∈ U)
    (hu : ContDiffOn ℝ ∞ u J) (hu' : ContDiffOn ℝ ∞ (deriv u) J)
    (hV : ∀ t ∈ J, HasDerivAt V (-(Γ (u t) (deriv u t) (V t))) t) :
    ContDiffOn ℝ ∞ V J :=
  contDiffOn_infty.mpr fun n =>
    contDiffOn_firstOrderLinearODE hJ hΓ hmem hu hu' hV n

end Abstract

/-! ### Smoothness of the chart data along a `C^∞` curve -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

set_option maxSynthPendingDepth 6 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Math.** **The chart Jacobi operator `ℛ_chart(u)(·, u̇)u̇` is `C^n` along a
`C^∞` curve** staying over the interior of the chart target.  By
`chartCurvatureEndo_eq` it is a polynomial expression in `Γ = chartChristoffelBilin`,
its first derivative `∂Γ` (both `C^∞` on the chart-target interior — `Γ` by
`contDiffOn_chartChristoffelBilin`, `∂Γ` by `contDiffOn_infty_iff_fderiv_of_isOpen`), the foot
`u` and the velocity `u̇`; each block is a `clm_comp`/`clm_apply` of `C^n` data.

This is the `ContDiffOn` upgrade of `continuousOn_chartCurvatureEndo_comp`. -/
theorem contDiffOn_chartCurvatureEndo_comp' (g : RiemannianMetric I M) (α : M)
    {u : ℝ → E} {J : Set ℝ}
    (hu : ContDiffOn ℝ ∞ u J) (hu' : ContDiffOn ℝ ∞ (deriv u) J)
    (hmem : ∀ t ∈ J, u t ∈ interior (extChartAt I α).target) (n : ℕ) :
    ContDiffOn ℝ n (fun t => chartCurvatureEndo (I := I) g α (u t) (deriv u t)) J := by
  have hmaps : Set.MapsTo u J (interior (extChartAt I α).target) := fun t ht => hmem t ht
  have hΓb_cd := contDiffOn_chartChristoffelBilin (I := I) g α
  have hun : ContDiffOn ℝ n u J := contDiffOn_infty.mp hu n
  have hu'n : ContDiffOn ℝ n (deriv u) J := contDiffOn_infty.mp hu' n
  have hG : ContDiffOn ℝ n (fun t => chartChristoffelBilin (I := I) g α (u t)) J :=
    (contDiffOn_infty.mp hΓb_cd n).comp hun hmaps
  have hDGamInf : ContDiffOn ℝ ∞ (fderiv ℝ (chartChristoffelBilin (I := I) g α))
      (interior (extChartAt I α).target) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_interior).mp hΓb_cd).2
  have hDΓ : ContDiffOn ℝ n (fderiv ℝ (chartChristoffelBilin (I := I) g α))
      (interior (extChartAt I α).target) := contDiffOn_infty.mp hDGamInf n
  have hDG : ContDiffOn ℝ n
      (fun t => fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t)) J :=
    hDΓ.comp hun hmaps
  have happE : ContDiffOn ℝ n
      (fun t => (ContinuousLinearMap.apply ℝ E : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] E)
        (deriv u t)) J := by
    simpa [Function.comp_def] using
      (ContinuousLinearMap.apply ℝ E :
        E →L[ℝ] (E →L[ℝ] E) →L[ℝ] E).contDiff.comp_contDiffOn hu'n
  have happEE : ContDiffOn ℝ n
      (fun t => (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) :
        E →L[ℝ] (E →L[ℝ] E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)) (deriv u t)) J := by
    simpa [Function.comp_def] using
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) :
        E →L[ℝ] (E →L[ℝ] E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E)).contDiff.comp_contDiffOn hu'n
  -- the four blocks of `chartCurvatureEndo_eq`
  have h1 := happE.clm_comp (happEE.clm_comp hDG)
  have h2 := happE.clm_comp (hDG.clm_apply hu'n)
  have h3 : ContDiffOn ℝ n (fun t => (ContinuousLinearMap.apply ℝ E
      (chartChristoffelBilin (I := I) g α (u t) (deriv u t) (deriv u t))).comp
        (chartChristoffelBilin (I := I) g α (u t))) J :=
    ((ContinuousLinearMap.apply ℝ E).contDiff.comp_contDiffOn
      ((hG.clm_apply hu'n).clm_apply hu'n)).clm_comp hG
  have h4 := (hG.clm_apply hu'n).clm_comp (happE.clm_comp hG)
  refine (((h1.sub h2).add h3).sub h4).congr fun t _ => ?_
  rw [chartCurvatureEndo_eq]

/-- **Math.** **The chart Gram pairing is `C^n` along `C^n` data.**  The Gram
coefficients `G_{ij}` are `C^∞` on the chart target
(`chartGramOnE_contDiffOn`), and `⟨X, Y⟩_{u} = ∑_{ij} G_{ij}(u) X^i Y^j` is
polynomial in them and in the (continuous-linear) coordinates of `X`, `Y`.

This is the `ContDiffOn` upgrade of `continuousOn_chartMetricInner_comp`. -/
theorem contDiffOn_chartMetricInner_comp (g : RiemannianMetric I M) (α : M)
    {u X Y : ℝ → E} {J : Set ℝ} {n : ℕ}
    (hu : ContDiffOn ℝ n u J) (hX : ContDiffOn ℝ n X J) (hY : ContDiffOn ℝ n Y J)
    (hmem : ∀ t ∈ J, u t ∈ (extChartAt I α).target) :
    ContDiffOn ℝ n (fun t => chartMetricInner (I := I) g α (u t) (X t) (Y t)) J := by
  classical
  have hmaps : Set.MapsTo u J (extChartAt I α).target := fun t ht => hmem t ht
  simp only [chartMetricInner_def]
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
  refine ContDiffOn.mul (ContDiffOn.mul ?_ ?_) ?_
  · exact (contDiffOn_infty.mp (chartGramOnE_contDiffOn (I := I) g α i j) n).comp hu hmaps
  · have := (Geodesic.chartCoordFunctional (E := E) i).contDiff.comp_contDiffOn hX
    simpa [Function.comp_def, Geodesic.chartCoordFunctional_apply] using this
  · have := (Geodesic.chartCoordFunctional (E := E) j).contDiff.comp_contDiffOn hY
    simpa [Function.comp_def, Geodesic.chartCoordFunctional_apply] using this

/-! ### A parallel frame along a geodesic is smooth in `t` -/

/-- **Math.** **The parallel-transport bootstrap, on the manifold.**  Let `γ` be a
geodesic on `[a, b]` and `V` a field parallel along it.  On any *open* set of times
`Ioo c d` with `Icc c d ⊆ [a, b]` and `γ(Icc c d)` inside the source of the chart at
`β`, the chart-`β` reading of `V` is `C^n`, for every `n`.

*Proof.*  Localization (`IsParallelAlongOn.isParallelSolOn_of_mem_source`) turns the
patchwork parallelism into the single-chart ODE

`V′(τ) = −Γ_β(u τ)(u̇ τ, V τ)`,  `u = φ_β ∘ γ`, `Γ_β = chartChristoffelBilin g β`,

valid on `Icc c d`, hence with two-sided derivatives at interior times.  The curve
`u` is `C^∞` on `Ioo c d` together with its velocity (geodesic regularity,
`contDiffOn_chartReading_of_isGeodesicOn`), the coefficient `Γ_β` is `C^∞` on the
chart-target interior, and `u` maps `Ioo c d` there.  `contDiffOn_firstOrderLinearODE`
concludes.  ∎

This is deliverable (1): the parallel frame, which the intrinsic theory only ever
produced as a `C¹` object, is in fact `C^∞` in `t`. -/
theorem contDiffOn_chartVectorRep_of_isParallelAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {V : ℝ → E} {a b : ℝ}
    (hPar : IsParallelAlongOn (I := I) g γ V a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {β : M} {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (hsrc : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H β).source) (n : ℕ) :
    ContDiffOn ℝ n (chartVectorRep (I := I) γ β V) (Ioo c d) := by
  have hIoo : Ioo c d ⊆ Icc c d := Ioo_subset_Icc_self
  have hsol : IsParallelSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
      (chartVectorRep (I := I) γ β V) c d :=
    hPar.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc
  -- the chart reading of the geodesic is `C^∞` on the open interval, with its velocity
  have hgeo' : IsGeodesicOn (I := I) g γ (Ioo c d) := fun t ht => hgeo t (hsub (hIoo ht))
  have hγc' : ∀ t ∈ Ioo c d, ContinuousAt γ t := fun t ht => hγc t (hsub (hIoo ht))
  have hsrc' : ∀ t ∈ Ioo c d, γ t ∈ (chartAt H β).source := fun t ht => hsrc t (hIoo ht)
  have hu : ContDiffOn ℝ ∞ (Geodesic.chartReading (I := I) β γ) (Ioo c d) :=
    contDiffOn_chartReading_infty_of_isGeodesicOn g isOpen_Ioo hgeo' hγc' hsrc'
  have hu' : ContDiffOn ℝ ∞ (deriv (Geodesic.chartReading (I := I) β γ)) (Ioo c d) :=
    contDiffOn_infty.mpr fun m =>
      contDiffOn_deriv_chartReading_of_isGeodesicOn g isOpen_Ioo hgeo' hγc' hsrc' m
  have hmem : ∀ t ∈ Ioo c d, Geodesic.chartReading (I := I) β γ t
      ∈ interior (extChartAt I β).target := by
    intro t ht
    rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
    exact (extChartAt I β).map_source (by rw [extChartAt_source]; exact hsrc' t ht)
  -- the parallel ODE, with two-sided derivatives at interior times
  have hV : ∀ t ∈ Ioo c d, HasDerivAt (chartVectorRep (I := I) γ β V)
      (-(chartChristoffelBilin (I := I) g β
          (Geodesic.chartReading (I := I) β γ t)
          (deriv (Geodesic.chartReading (I := I) β γ) t)
          (chartVectorRep (I := I) γ β V t))) t := by
    intro t ht
    have h := (hsol t (hIoo ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rwa [show chartChristoffelBilin (I := I) g β
        (Geodesic.chartReading (I := I) β γ t)
        (deriv (Geodesic.chartReading (I := I) β γ) t)
        (chartVectorRep (I := I) γ β V t)
        = Geodesic.chartChristoffelContraction (I := I) g β
            (deriv (fun τ => extChartAt I β (γ τ)) t)
            (chartVectorRep (I := I) γ β V t)
            ((fun τ => extChartAt I β (γ τ)) t) from
      chartChristoffelBilin_apply (I := I) g β _ _ _]
  exact contDiffOn_firstOrderLinearODE (Γ := chartChristoffelBilin (I := I) g β)
    isOpen_Ioo (contDiffOn_chartChristoffelBilin (I := I) g β) hmem hu hu' hV n

/-! ### The frame curvature coefficient is smooth in `t` -/

/-- **Math.** **Smoothness of the curvature coefficient on a single-chart
subinterval.**  If `γ(Icc c d)` lies in the source of the chart at `β`, then
`τ ↦ ℛᵢⱼ(τ)` is `C^n` on the open interval `Ioo c d`.

All three factors of the fixed-chart formula `frameCurv_eq_chart` are `C^n` there:
the chart reading `u = φ_β ∘ γ` and its velocity (geodesic regularity), the chart
readings `Eₖ,β` of the parallel frame (the parallel-transport bootstrap above), and
the chart curvature endomorphism and Gram pairing (chart-data smoothness). -/
theorem contDiffOn_frameCurv_of_mem_source
    {g : RiemannianMetric I M} {γ : ℝ → M} {e : Fin (Module.finrank ℝ E) → ℝ → E}
    {a b : ℝ} (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {β : M} {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (hsrc : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H β).source)
    (i j : Fin (Module.finrank ℝ E)) (n : ℕ) :
    ContDiffOn ℝ n (frameCurv (I := I) g γ e i j) (Ioo c d) := by
  have hIoo : Ioo c d ⊆ Icc c d := Ioo_subset_Icc_self
  have hgeo' : IsGeodesicOn (I := I) g γ (Ioo c d) := fun t ht => hgeo t (hsub (hIoo ht))
  have hγc' : ∀ t ∈ Ioo c d, ContinuousAt γ t := fun t ht => hγc t (hsub (hIoo ht))
  have hsrc' : ∀ t ∈ Ioo c d, γ t ∈ (chartAt H β).source := fun t ht => hsrc t (hIoo ht)
  have hu : ContDiffOn ℝ ∞ (Geodesic.chartReading (I := I) β γ) (Ioo c d) :=
    contDiffOn_chartReading_infty_of_isGeodesicOn g isOpen_Ioo hgeo' hγc' hsrc'
  have hu' : ContDiffOn ℝ ∞ (deriv (Geodesic.chartReading (I := I) β γ)) (Ioo c d) :=
    contDiffOn_infty.mpr fun m =>
      contDiffOn_deriv_chartReading_of_isGeodesicOn g isOpen_Ioo hgeo' hγc' hsrc' m
  have hmem : ∀ t ∈ Ioo c d, Geodesic.chartReading (I := I) β γ t
      ∈ interior (extChartAt I β).target := by
    intro t ht
    rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
    exact (extChartAt I β).map_source (by rw [extChartAt_source]; exact hsrc' t ht)
  have hmem' : ∀ t ∈ Ioo c d, Geodesic.chartReading (I := I) β γ t
      ∈ (extChartAt I β).target := fun t ht => interior_subset (hmem t ht)
  -- the chart readings of the parallel frame are `C^n`
  have hrep : ∀ k, ContDiffOn ℝ n (chartVectorRep (I := I) γ β (e k)) (Ioo c d) := fun k =>
    contDiffOn_chartVectorRep_of_isParallelAlongOn (hPar k) hgeo hγc hsub hsrc n
  -- the chart Jacobi endomorphism along the curve
  have hendo : ContDiffOn ℝ n (fun τ => chartCurvatureEndo (I := I) g β
      (Geodesic.chartReading (I := I) β γ τ)
      (deriv (Geodesic.chartReading (I := I) β γ) τ)) (Ioo c d) :=
    contDiffOn_chartCurvatureEndo_comp' g β hu hu' hmem n
  have hEj : ContDiffOn ℝ n (fun τ => chartCurvatureEndo (I := I) g β
      (Geodesic.chartReading (I := I) β γ τ)
      (deriv (Geodesic.chartReading (I := I) β γ) τ)
      (chartVectorRep (I := I) γ β (e j) τ)) (Ioo c d) := hendo.clm_apply (hrep j)
  have hmain : ContDiffOn ℝ n (fun τ => - chartMetricInner (I := I) g β
      (Geodesic.chartReading (I := I) β γ τ)
      (chartCurvatureEndo (I := I) g β
        (Geodesic.chartReading (I := I) β γ τ)
        (deriv (Geodesic.chartReading (I := I) β γ) τ)
        (chartVectorRep (I := I) γ β (e j) τ))
      (chartVectorRep (I := I) γ β (e i) τ)) (Ioo c d) :=
    (contDiffOn_chartMetricInner_comp g β (contDiffOn_infty.mp hu n) hEj (hrep i) hmem').neg
  refine hmain.congr fun τ hτ => ?_
  exact frameCurv_eq_chart (I := I) e (hgeo' τ hτ) (hγc' τ hτ) (hsrc' τ hτ) i j

/-- **Math.** **The curvature coefficient is `C^n` along the whole geodesic.**
Smoothness, like continuity, is a local property, and every interior time
`t ∈ Ioo a b` has an open neighbourhood `Ioo c d ⊆ Ioo a b` whose `γ`-image lies in
the single chart at `γ t`.  `contDiffOn_frameCurv_of_mem_source` gives `C^n` there,
and `contDiffOn_of_locally_contDiffOn` glues.

The chart-crossing jumps of the raw readings cancel exactly as in
`continuousOn_frameCurv`: the intrinsic scalar `ℛᵢⱼ` never mentions them. -/
theorem contDiffOn_frameCurv
    {g : RiemannianMetric I M} {γ : ℝ → M} {e : Fin (Module.finrank ℝ E) → ℝ → E}
    {a b : ℝ} (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (i j : Fin (Module.finrank ℝ E)) (n : ℕ) :
    ContDiffOn ℝ n (frameCurv (I := I) g γ e i j) (Ioo a b) := by
  refine contDiffOn_of_locally_contDiffOn fun t ht => ?_
  have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  -- a relative interval around `t` whose `γ`-image lies in the chart at `γ t`
  have hnhds : γ ⁻¹' (chartAt H (γ t)).source ∈ 𝓝 t :=
    (hγc t htIcc).preimage_mem_nhds
      ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set c := max a (t - ε / 2) with hc
  set d := min b (t + ε / 2) with hd
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsrc : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H (γ t)).source := by
    intro τ hτ
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : t - ε / 2 ≤ τ := le_trans (le_max_right _ _) hτ.1
    have h2 : τ ≤ t + ε / 2 := le_trans hτ.2 (min_le_right _ _)
    have : |τ - t| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  refine ⟨Ioo c d, isOpen_Ioo, ⟨max_lt ht.1 (by linarith), lt_min ht.2 (by linarith)⟩, ?_⟩
  exact (contDiffOn_frameCurv_of_mem_source hPar hgeo hγc hsub hsrc i j n).mono
    inter_subset_right

/-! ### The frame Jacobi operator is smooth in `t` -/

/-- **Math.** **Smoothness of the frame Jacobi operator** — the drop-in upgrade of
`continuousOn_frameCurvOp` from `C⁰` to `C^n`, and the regularity that lets the two
halves of `prop:minimal-geodesic-no-conjugate` meet: a solution of the frame Jacobi
equation `y″ + ℛ y = 0` with `ℛ = frameCurvOp` of class `C^n` is of class `C^{n+2}`,
in particular `C³`, which is what the piece second-variation formula demands.

The operator is a finite sum of *fixed* rank-one operators with the curvature
coefficients as scalars, so it inherits their smoothness (`contDiffOn_frameCurv`). -/
theorem contDiffOn_frameCurvOp {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {a b : ℝ}
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) (n : ℕ) :
    ContDiffOn ℝ n (frameCurvOp (I := I) g γ e) (Ioo a b) := by
  classical
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
  exact ((contDiffOn_frameCurv hPar hgeo hγc i j n).neg).smul contDiffOn_const

/-- **Math.** The frame Jacobi operator is `C^∞` in `t` on the open interval. -/
theorem contDiffOn_frameCurvOp_infty {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {a b : ℝ}
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    ContDiffOn ℝ ∞ (frameCurvOp (I := I) g γ e) (Ioo a b) :=
  contDiffOn_infty.mpr fun n => contDiffOn_frameCurvOp hPar hgeo hγc n

/-- **Math.** **The form the consumers want.**  A radial geodesic is always defined a
little past the interval of interest (`a < 0` and `B < b`, exactly as in
`isJacobiSolOn_frameVec`), so the closed interval `[c, d]` of interest sits inside the
open interval `(a, b)` and the frame Jacobi operator is `C^n` on it. -/
theorem contDiffOn_frameCurvOp_Icc {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {a b c d : ℝ}
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hac : a < c) (hdb : d < b) (n : ℕ) :
    ContDiffOn ℝ n (frameCurvOp (I := I) g γ e) (Icc c d) :=
  (contDiffOn_frameCurvOp hPar hgeo hγc n).mono fun _ ht =>
    ⟨lt_of_lt_of_le hac ht.1, lt_of_le_of_lt ht.2 hdb⟩

end Manifold

end PoincareLib

end

#print axioms PoincareLib.contDiffOn_firstOrderLinearODE
#print axioms PoincareLib.contDiffOn_chartVectorRep_of_isParallelAlongOn
#print axioms PoincareLib.contDiffOn_frameCurv
#print axioms PoincareLib.contDiffOn_frameCurvOp
#print axioms PoincareLib.contDiffOn_frameCurvOp_Icc
