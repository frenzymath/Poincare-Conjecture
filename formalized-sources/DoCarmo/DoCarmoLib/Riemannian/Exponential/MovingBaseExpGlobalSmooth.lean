import DoCarmoLib.Riemannian.Exponential.CInftyBall
import DoCarmoLib.Riemannian.Exponential.CInftyGlobal
import DoCarmoLib.Riemannian.Geodesic.FlowReadback
import DoCarmoLib.Riemannian.Exponential.GlobalExp
import DoCarmoLib.Riemannian.Jacobi.JacobiManifold
import DoCarmoLib.Riemannian.Jacobi.JacobiFrameSmooth

/-!
# Smooth moving-base complete exponential endpoints

`CInftyBall.lean` gives a joint `C^∞` coordinate flow near a fixed chart
basepoint.  This file supplies the missing readback step to the complete
exponential and packages the resulting composition theorem for dependent
basepoint/tangent families.  It is the local analytic input needed before a
Bonnet--Myers exponential variation can be assembled over a whole geodesic.

The final theorem deliberately keeps the chart-state map and tangent section
as hypotheses.  Building those data globally over an arbitrary tangent bundle
section, and choosing one flow chart over an entire compact geodesic, remain
separate finite-cover work.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ### Smoothness of complete geodesics -/

/-- **Math.** A complete global geodesic is `C^∞`.  At time `0`, read its
velocity `v` in the chart at `p = γ(0)`.  Intrinsic uniqueness identifies the
whole curve with the radial global-exponential curve
`t ↦ expMapGlobal p (t • v)`, which is smooth by
`contMDiff_expMapGlobal`.

This upgrades the `C¹` regularity supplied by `IsGeodesicOn.contMDiffOn` and is
the base-curve regularity needed to bootstrap parallel fields to `C^∞` in
`IsParallelFieldAlongOn.contDiffOn_infty_chartVectorRep`. -/
theorem contMDiff_infty_of_isGeodesic [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hγc : Continuous γ) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
  classical
  let p : M := γ 0
  obtain ⟨v, _a, hv, _hev, _ha, _hchr⟩ := hgeo 0
  have hv' : HasDerivAt (fun s => extChartAt I p (γ s)) v 0 := by
    simpa only [p, Riemannian.Geodesic.chartLocalCurve_def] using hv
  have heq : γ = Riemannian.Geodesic.globalGeodesic (I := I) g hg p v :=
    Riemannian.Geodesic.globalGeodesic_eq (I := I) g hg hgeo hγc rfl hv'
  have hγexp : γ = fun t => expMapGlobal (I := I) g hg p (t • v) := by
    funext t
    have ht := congrFun heq t
    calc
      γ t = Riemannian.Geodesic.globalGeodesic (I := I) g hg p
          (v : TangentSpace I p) t := ht
      _ = expMapGlobal (I := I) g hg p (t • (v : TangentSpace I p)) :=
        (expMapGlobal_smul (I := I) g hg p (v : TangentSpace I p) t).symm
  rw [hγexp]
  have hlin : ContDiff ℝ ∞ (fun t : ℝ => t • (v : E)) := by fun_prop
  simpa only [Function.comp_apply] using
    (contMDiff_expMapGlobal (I := I) g hg p).comp hlin.contMDiff

/-! ### Zero-slice readback -/

/-- **Math.** The radial derivative of the complete exponential map at the
zero vector is the prescribed tangent vector:

`d/ds|₀ extChartAt p (expMapGlobal p (s • v)) = v`.

Together with `expMapGlobal_zero`, this identifies the zero slice and the
variational field of the concrete Bonnet--Myers exponential surface. -/
theorem hasDerivAt_extChartAt_expMapGlobal_smul
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : TangentSpace I p) :
    HasDerivAt (fun s : ℝ => extChartAt I p
      (expMapGlobal (I := I) g hg p (s • v))) (v : E) 0 := by
  have hfun : (fun s : ℝ => extChartAt I p
      (expMapGlobal (I := I) g hg p (s • v))) =
      fun s => extChartAt I p
        (Riemannian.Geodesic.globalGeodesic (I := I) g hg p v s) := by
    funext s
    rw [expMapGlobal_smul]
  rw [hfun]
  simpa only [Riemannian.Geodesic.chartReading_def] using
    Riemannian.Geodesic.hasDerivAt_chartReading_globalGeodesic g hg p v

/-! ### The flow composition and readback -/

/-- **Math.** A smooth family of admissible coordinate states can be composed
with the uniform geodesic flow endpoint without losing `C^∞` regularity. -/
theorem exists_contDiffOn_pairFlow_surface (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E), 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (Riemannian.Geodesic.geodesicSprayCoord (I := I) g p
            (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε,
          Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      ∀ {s : Set (E × E)} {u : E × E → E × E},
        ContDiffOn ℝ ∞ u s →
        (∀ x ∈ s, ((u x).1, T⁻¹ • (u x).2) ∈
          ball ((extChartAt I p p, (0 : E)) : E × E) r) →
        ContDiffOn ℝ ∞
          (fun x : E × E =>
            ((u x).1, (Z (((u x).1, T⁻¹ • (u x).2) : E × E) T).1)) s := by
  classical
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hpair⟩ :=
    exists_pairMap_contDiffOn_infty (I := I) g p
  refine ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, ?_⟩
  intro s u hu hmem
  exact hpair.comp hu (fun x hx => hmem x hx)

open Riemannian.Geodesic

/-- **Math.** The endpoint of an admissible uniform coordinate flow agrees
with the complete global exponential based at the same point.  The proof uses
geodesic uniqueness/readback on an open time window around the initial time. -/
theorem expMapGlobal_eq_pairFlow_endpoint
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] {p : M} {r ε T : ℝ} {Z : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (Riemannian.Geodesic.geodesicSprayCoord (I := I) g p
          (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε,
        Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {q : M} {v : TangentSpace I q} {w : E}
    (hq : q ∈ (chartAt H p).source)
    (hw : tangentCoordChange I q p q v = w)
    (hmem : ((extChartAt I p q, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r) :
    expMapGlobal (I := I) g hg q v =
      (extChartAt I p).symm
        ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) T).1) := by
  have hq_ext : q ∈ (extChartAt I p).source := by
    rw [extChartAt_source]
    exact hq
  have hglobal_geo : IsGeodesicOn (I := I) g
      (globalGeodesic (I := I) g hg q v) (Ioo (-2 : ℝ) 2) := by
    intro t ht
    exact (isGeodesic_globalGeodesic g hg q v) t
  have hglobal_cont : ContinuousOn
      (globalGeodesic (I := I) g hg q v) (Ioo (-2 : ℝ) 2) :=
    (continuous_globalGeodesic g hg q v).continuousOn
  have hglobal_zero : globalGeodesic (I := I) g hg q v 0 =
      (extChartAt I p).symm (extChartAt I p q) := by
    rw [globalGeodesic_zero]
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]; exact hq)).symm
  have hglobal_vel : HasDerivAt
      (fun τ => extChartAt I p (globalGeodesic (I := I) g hg q v τ)) w 0 := by
    have hgeo0 : HasGeodesicEquationAt (I := I) g
        (globalGeodesic (I := I) g hg q v) 0 :=
      (isGeodesic_globalGeodesic g hg q v) 0
    have hcont0 : ContinuousAt (globalGeodesic (I := I) g hg q v) 0 :=
      (continuous_globalGeodesic g hg q v).continuousAt
    have hsrc0 : globalGeodesic (I := I) g hg q v 0 ∈ (chartAt H p).source := by
      simpa only [globalGeodesic_zero] using hq
    have hderiv := hgeo0.eventually_hasDerivAt_extChartAt hcont0 hsrc0
    have hderiv0 := hderiv.self_of_nhds
    have hmove : deriv (chartLocalCurve (I := I)
        (globalGeodesic (I := I) g hg q v) 0) 0 = v := by
      have hbase := (hasDerivAt_chartReading_globalGeodesic g hg q v).deriv
      have hfun : chartLocalCurve (I := I)
          (globalGeodesic (I := I) g hg q v) 0 =
          chartReading (I := I) q (globalGeodesic (I := I) g hg q v) := by
        funext t
        simp only [chartLocalCurve_def, chartReading_def, globalGeodesic_zero]
      rw [hfun]
      exact hbase
    rw [hmove] at hderiv0
    simp only [globalGeodesic_zero] at hderiv0
    rw [hw] at hderiv0
    exact hderiv0
  have hread := IsGeodesicOn.eq_uniform_flow_readback (I := I)
      (g := g) (p := p) (σ := globalGeodesic (I := I) g hg q v)
      (y := extChartAt I p q) (w := w) hglobal_geo hT hTε hflow hmem
      (by norm_num) hglobal_cont hglobal_zero hglobal_vel
  have hratio : 1 < ε / T := (one_lt_div hT).mpr hTε
  have hmin : 1 < min 2 (ε / T) := lt_min (by norm_num) hratio
  have h1mem : (1 : ℝ) ∈ Ioo (-(min 2 (ε / T))) (min 2 (ε / T)) := by
    constructor <;> linarith
  rw [expMapGlobal_def]
  simpa using hread h1mem

/-! ### The dependent-family composition package -/

/-- **Math.** Once a dependent family of basepoints and tangent vectors is
represented by a smooth chart-state map, its complete exponential endpoint is
`C^∞` in all parameters.  This is the local moving-base exponential input for
the Bonnet--Myers variation; the theorem intentionally leaves construction of
the chart-state and tangent-section data to its caller. -/
theorem exists_contDiffOn_extChartAt_expMapGlobal_of_pairInput
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E),
      0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (Riemannian.Geodesic.geodesicSprayCoord (I := I) g p
            (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε,
          Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      ∀ {A : Set (ℝ × ℝ)} {u : ℝ × ℝ → E × E}
        {q : ℝ × ℝ → M} {v : (x : ℝ × ℝ) → TangentSpace I (q x)},
        ContDiffOn ℝ ∞ u A →
        (∀ x ∈ A, q x ∈ (chartAt H p).source) →
        (∀ x ∈ A, (u x).1 = extChartAt I p (q x)) →
        (∀ x ∈ A,
          tangentCoordChange I (q x) p (q x) (v x) = (u x).2) →
        (∀ x ∈ A,
          ((u x).1, T⁻¹ • (u x).2) ∈
            ball ((extChartAt I p p, (0 : E)) : E × E) r) →
        ContDiffOn ℝ ∞
          (fun x => extChartAt I p
            (expMapGlobal (I := I) g hg (q x) (v x))) A := by
  classical
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hpair⟩ :=
    exists_pairMap_contDiffOn_infty (I := I) g p
  refine ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, ?_⟩
  intro A u q v hu hq hbase hvel hmem
  have hpaircomp : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ =>
        ((u x).1, (Z (((u x).1, T⁻¹ • (u x).2) : E × E) T).1)) A := by
    exact hpair.comp hu (fun x hx => hmem x hx)
  have hflowcoord : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => (Z (((u x).1, T⁻¹ • (u x).2) : E × E) T).1) A := by
    exact contDiff_snd.comp_contDiffOn hpaircomp
  refine hflowcoord.congr (fun x hx => ?_)
  have hmemx : ((extChartAt I p (q x), T⁻¹ • (u x).2) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r := by
    exact ball_subset_closedBall (by simpa [hbase x hx] using hmem x hx)
  have hexp := expMapGlobal_eq_pairFlow_endpoint (I := I) g hg hT hTε hflow
      (q := q x) (v := v x) (w := (u x).2) (hq x hx) (hvel x hx) hmemx
  have htarget :
      (Z ((extChartAt I p (q x), T⁻¹ • (u x).2) : E × E) T).1 ∈
        (extChartAt I p).target := by
    obtain ⟨hz0, hzd, hzmem⟩ := hflow _ hmemx
    exact (hzmem T ⟨by linarith [hT, hTε], hTε.le⟩).1
  rw [hbase x hx, hexp]
  exact (extChartAt I p).right_inv htarget

/-- **Math.** A smooth scalar multiple of a smooth chart-coordinate field has
a jointly `C^∞` complete-exponential variation on any one-chart product slab.
The explicit ball hypothesis is the local flow-domain condition; a finite chart
cover is still needed to turn this into a global variation over a long geodesic. -/
theorem exists_contDiffOn_extChartAt_expMapGlobal_smul_field
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E),
      0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (Riemannian.Geodesic.geodesicSprayCoord (I := I) g p
            (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε,
          Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      ∀ {S J : Set ℝ} {A : Set (ℝ × ℝ)} {γ : ℝ → M} {V : ℝ → E},
        A = S ×ˢ J →
        ContDiffOn ℝ ∞ (fun t => extChartAt I p (γ t)) J →
        ContDiffOn ℝ ∞ (Riemannian.Jacobi.chartVectorRep (I := I) γ p V) J →
        (∀ t ∈ J, γ t ∈ (chartAt H p).source) →
        (∀ x ∈ A,
          ((extChartAt I p (γ x.2),
            T⁻¹ • (x.1 • Riemannian.Jacobi.chartVectorRep (I := I) γ p V x.2)) : E × E) ∈
            ball ((extChartAt I p p, (0 : E)) : E × E) r) →
        ContDiffOn ℝ ∞
          (fun x : ℝ × ℝ => extChartAt I p
            (expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2))) A := by
  classical
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hcore⟩ :=
    exists_contDiffOn_extChartAt_expMapGlobal_of_pairInput (I := I) g hg p
  refine ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, ?_⟩
  intro S J A γ V hA hγ hV hq hmem
  subst A
  let u : ℝ × ℝ → E × E := fun x =>
    (extChartAt I p (γ x.2), x.1 • Riemannian.Jacobi.chartVectorRep (I := I) γ p V x.2)
  have hu1 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => extChartAt I p (γ x.2))
      (S ×ˢ J) := by
    exact hγ.comp contDiffOn_snd (fun x hx => hx.2)
  have hVprod : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => Riemannian.Jacobi.chartVectorRep (I := I) γ p V x.2)
        (S ×ˢ J) := by
    exact hV.comp contDiffOn_snd (fun x hx => hx.2)
  have hu2 : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => x.1 • Riemannian.Jacobi.chartVectorRep (I := I) γ p V x.2)
      (S ×ˢ J) := contDiffOn_fst.smul hVprod
  have hu : ContDiffOn ℝ ∞ u (S ×ˢ J) := by
    exact hu1.prodMk hu2
  apply hcore hu
  · intro x hx
    exact hq x.2 hx.2
  · intro x hx
    rfl
  · intro x hx
    simp only [u, Riemannian.Jacobi.chartVectorRep_apply]
    exact (tangentCoordChange I (γ x.2) p (γ x.2)).map_smul _ _
  · intro x hx
    simpa [u] using hmem x hx

/-! ### The exponential variation along a parallel field -/

/-- **Math.** Let `γ` be a complete geodesic and `V` a parallel field along it.
At every interior time `t₀`, the concrete exponential variation

`f(s,t) = expMapGlobal (γ t) (s • V t)`

has a `C^∞` coordinate reading near `(0,t₀)`, in the chart centred at `γ t₀`.
The proof supplies the two hypotheses left explicit by
`exists_contDiffOn_extChartAt_expMapGlobal_of_pairInput`: the geodesic chart
reading is smooth by `contMDiff_infty_of_isGeodesic`, and the parallel-field
reading is smooth by the linear-ODE bootstrap
`IsParallelFieldAlongOn.contDiffOn_infty_chartVectorRep`.  The local flow-ball
condition is obtained by continuity at `(0,t₀)`, where the scaled input is the
centre `(extChartAt (γ t₀) (γ t₀), 0)`.

This is the local surface regularity needed for the Bonnet--Myers
second-variation surface; compactness of `[0,1]` can subsequently turn these
pointwise neighbourhoods into one uniform parameter strip. -/
theorem exists_open_contMDiffOn_expMapGlobal_smul_parallel [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {V : ℝ → E} {a b t₀ : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (hV : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ V a b)
    (ht₀ : t₀ ∈ Ioo a b) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, t₀) ∈ U ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2)) U ∧
      ∀ x ∈ U, expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2) ∈
        (chartAt H (γ t₀)).source := by
  classical
  set p : M := γ t₀ with hp
  have hnhds : γ ⁻¹' (chartAt H p).source ∈ 𝓝 t₀ :=
    hγc.continuousAt.preimage_mem_nhds
      ((chartAt H p).open_source.mem_nhds (by simp [p]))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set c := max a (t₀ - ε / 2) with hc
  set d := min b (t₀ + ε / 2) with hd
  have hsub : Icc c d ⊆ Icc a b :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have htcd : t₀ ∈ Ioo c d := by
    constructor
    · exact max_lt ht₀.1 (by linarith)
    · exact lt_min ht₀.2 (by linarith)
  have hsrc : ∀ t ∈ Icc c d, γ t ∈ (chartAt H p).source := by
    intro t ht
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : t₀ - ε / 2 ≤ t := le_trans (le_max_right _ _) ht.1
    have h2 : t ≤ t₀ + ε / 2 := le_trans ht.2 (min_le_right _ _)
    have habs : |t - t₀| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hγsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ :=
    contMDiff_infty_of_isGeodesic (I := I) g hg hgeo hγc
  have hγchart : ContDiffOn ℝ ∞ (fun t => extChartAt I p (γ t)) (Ioo c d) := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_extChartAt (I := I) (x := p)).comp hγsmooth.contMDiffOn
      (fun t ht => hsrc t (Ioo_subset_Icc_self ht))
  have htarget : ∀ t ∈ Ioo c d,
      extChartAt I p (γ t) ∈ interior (extChartAt I p).target := by
    intro t ht
    rw [(isOpen_extChartAt_target (I := I) p).interior_eq]
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc t (Ioo_subset_Icc_self ht))
  have hVchart : ContDiffOn ℝ ∞
      (Riemannian.Jacobi.chartVectorRep (I := I) γ p V) (Ioo c d) :=
    hV.contDiffOn_infty_chartVectorRep
      (show Riemannian.Jacobi.IsGeodesicOn (I := I) g γ (Icc a b) from fun t _ => hgeo t)
      (fun _ _ => hγc.continuousAt) hsub hsrc hγchart htarget
  obtain ⟨r, εf, T, Z, hr, hεf, hT, hTεf, hflow, hcore⟩ :=
    exists_contDiffOn_extChartAt_expMapGlobal_of_pairInput (I := I) g hg p
  let u : ℝ × ℝ → E × E := fun x =>
    (extChartAt I p (γ x.2),
      x.1 • Riemannian.Jacobi.chartVectorRep (I := I) γ p V x.2)
  let scaled : ℝ × ℝ → E × E := fun x => ((u x).1, T⁻¹ • (u x).2)
  let B : Set (ℝ × ℝ) := (univ ×ˢ Ioo c d) ∩
    scaled ⁻¹' ball ((extChartAt I p p, (0 : E)) : E × E) r
  have hu1 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => extChartAt I p (γ x.2))
      (univ ×ˢ Ioo c d) :=
    hγchart.comp contDiffOn_snd (fun x hx => hx.2)
  have hVprod : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => Riemannian.Jacobi.chartVectorRep (I := I) γ p V x.2)
      (univ ×ˢ Ioo c d) :=
    hVchart.comp contDiffOn_snd (fun x hx => hx.2)
  have hu2 : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => x.1 • Riemannian.Jacobi.chartVectorRep (I := I) γ p V x.2)
      (univ ×ˢ Ioo c d) := contDiffOn_fst.smul hVprod
  have hu : ContDiffOn ℝ ∞ u (univ ×ˢ Ioo c d) := hu1.prodMk hu2
  have hscaled : ContDiffOn ℝ ∞ scaled (univ ×ˢ Ioo c d) :=
    (contDiff_fst.comp_contDiffOn hu).prodMk
      (contDiffOn_const.smul (contDiff_snd.comp_contDiffOn hu))
  have hprod : univ ×ˢ Ioo c d ∈ 𝓝 ((0, t₀) : ℝ × ℝ) :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, htcd⟩
  have hscaled0 : scaled (0, t₀) = ((extChartAt I p p, (0 : E)) : E × E) := by
    simp [scaled, u, p]
  have hpre : scaled ⁻¹' ball ((extChartAt I p p, (0 : E)) : E × E) r ∈
      𝓝 ((0, t₀) : ℝ × ℝ) := by
    have hscont : ContinuousAt scaled (0, t₀) := (hscaled.contDiffAt hprod).continuousAt
    apply hscont.preimage_mem_nhds
    rw [hscaled0]
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)
  have hBnhds : B ∈ 𝓝 ((0, t₀) : ℝ × ℝ) := inter_mem hprod hpre
  have huB : ContDiffOn ℝ ∞ u B := hu.mono inter_subset_left
  have hout : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => extChartAt I p
        (expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2))) B := by
    apply hcore huB
    · intro x hx
      exact hsrc x.2 (Ioo_subset_Icc_self hx.1.2)
    · intro x hx
      rfl
    · intro x hx
      simp only [u, Riemannian.Jacobi.chartVectorRep_apply]
      exact (tangentCoordChange I (γ x.2) p (γ x.2)).map_smul _ _
    · intro x hx
      exact hx.2
  have hBopen : IsOpen B :=
    hscaled.continuousOn.isOpen_inter_preimage
      (isOpen_univ.prod isOpen_Ioo) Metric.isOpen_ball
  have hBmem : (0, t₀) ∈ B := mem_of_mem_nhds hBnhds
  have houtsrc : ∀ x ∈ B,
      expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2) ∈ (chartAt H p).source := by
    intro x hx
    have hxsrc : γ x.2 ∈ (chartAt H p).source :=
      hsrc x.2 (Ioo_subset_Icc_self hx.1.2)
    have hw : tangentCoordChange I (γ x.2) p (γ x.2) (x.1 • V x.2) = (u x).2 := by
      simp only [u, Riemannian.Jacobi.chartVectorRep_apply]
      exact (tangentCoordChange I (γ x.2) p (γ x.2)).map_smul _ _
    have hmem : ((extChartAt I p (γ x.2), T⁻¹ • (u x).2) : E × E) ∈
        closedBall ((extChartAt I p p, (0 : E)) : E × E) r := by
      simpa only [scaled, u] using ball_subset_closedBall hx.2
    have hexp := expMapGlobal_eq_pairFlow_endpoint (I := I) g hg hT hTεf hflow
      (q := γ x.2) (v := x.1 • V x.2) (w := (u x).2) hxsrc hw hmem
    have htargetZ :
        (Z ((extChartAt I p (γ x.2), T⁻¹ • (u x).2) : E × E) T).1 ∈
          (extChartAt I p).target :=
      ((hflow _ hmem).2.2 T ⟨by linarith [hT, hTεf], hTεf.le⟩).1
    rw [hexp]
    have hmaps := (extChartAt I p).map_target htargetZ
    rwa [extChartAt_source] at hmaps
  let f : ℝ × ℝ → M := fun x => expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2)
  have hfB : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f B := by
    intro x hx
    have hreadAt : ContDiffAt ℝ ∞ (fun y => extChartAt I p (f y)) x :=
      hout.contDiffAt (hBopen.mem_nhds hx)
    have hreadM : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
        (fun y => extChartAt I p (f y)) x := hreadAt.contMDiffAt
    have htargetx : extChartAt I p (f x) ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact houtsrc x hx)
    have hinv : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (extChartAt I p (f x)) :=
      (contMDiffOn_extChartAt_symm (I := I) p).contMDiffAt
        ((isOpen_extChartAt_target (I := I) p).mem_nhds htargetx)
    have hcomp := hinv.comp x hreadM
    apply (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hBopen.mem_nhds hx] with y hy
    show f y = (extChartAt I p).symm (extChartAt I p (f y))
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact houtsrc y hy)).symm
  exact ⟨B, hBopen, hBmem, hfB, by simpa only [p] using houtsrc⟩

/-- **Math.** Coordinate-at-point form of
`exists_open_contMDiffOn_expMapGlobal_smul_parallel`.  It is retained as the
lightweight interface for callers that need one fixed output chart. -/
theorem contDiffAt_extChartAt_expMapGlobal_smul_parallel [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {V : ℝ → E} {a b t₀ : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (hV : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ V a b)
    (ht₀ : t₀ ∈ Ioo a b) :
    ContDiffAt ℝ ∞
        (fun x : ℝ × ℝ => extChartAt I (γ t₀)
          (expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2))) (0, t₀) ∧
      (∀ᶠ x : ℝ × ℝ in 𝓝 (0, t₀),
        expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2) ∈
          (chartAt H (γ t₀)).source) := by
  obtain ⟨U, hUopen, h0U, hfU, hsrcU⟩ :=
    exists_open_contMDiffOn_expMapGlobal_smul_parallel (I := I) g hg hgeo hγc hV ht₀
  have hreadM : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (fun x : ℝ × ℝ => extChartAt I (γ t₀)
        (expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2))) U :=
    (contMDiffOn_extChartAt (I := I) (x := γ t₀)).comp hfU hsrcU
  have hread : ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => extChartAt I (γ t₀)
        (expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2))) U := by
    rwa [contMDiffOn_iff_contDiffOn] at hreadM
  refine ⟨hread.contDiffAt (hUopen.mem_nhds h0U), ?_⟩
  filter_upwards [hUopen.mem_nhds h0U] with x hx
  exact hsrcU x hx

/-- **Math.** Manifold-valued form of
`contDiffAt_extChartAt_expMapGlobal_smul_parallel`: the exponential variation
along a parallel field is genuinely `C^∞` at every point `(0,t₀)` of its zero
slice.  The eventual chart-source clause returned by the coordinate theorem is
what makes the inverse-chart composition sound. -/
theorem contMDiffAt_expMapGlobal_smul_parallel [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {V : ℝ → E} {a b t₀ : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (hV : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ V a b)
    (ht₀ : t₀ ∈ Ioo a b) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2)) (0, t₀) := by
  let f : ℝ × ℝ → M := fun x =>
    expMapGlobal (I := I) g hg (γ x.2) (x.1 • V x.2)
  obtain ⟨hread, hsrc⟩ :=
    contDiffAt_extChartAt_expMapGlobal_smul_parallel (I := I) g hg hgeo hγc hV ht₀
  have hreadM : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (fun x => extChartAt I (γ t₀) (f x)) (0, t₀) := by
    exact hread.contMDiffAt
  have hf0 : f (0, t₀) = γ t₀ := by
    dsimp only [f]
    rw [zero_smul]
    change expMapGlobal (I := I) g hg (γ t₀) (0 : TangentSpace I (γ t₀)) = γ t₀
    exact expMapGlobal_zero (I := I) g hg (γ t₀)
  have hcenterSrc : f (0, t₀) ∈ (chartAt H (γ t₀)).source := by
    rw [hf0]
    exact mem_chart_source H (γ t₀)
  have hcenterTarget : extChartAt I (γ t₀) (f (0, t₀)) ∈
      (extChartAt I (γ t₀)).target :=
    (extChartAt I (γ t₀)).map_source (by rwa [extChartAt_source])
  have hinv : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I (γ t₀)).symm
      (extChartAt I (γ t₀) (f (0, t₀))) :=
    (contMDiffOn_extChartAt_symm (I := I) (γ t₀)).contMDiffAt
      ((isOpen_extChartAt_target (I := I) (γ t₀)).mem_nhds hcenterTarget)
  have hcomp := hinv.comp (0, t₀) hreadM
  change ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ f (0, t₀)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with x hx
  show f x = (extChartAt I (γ t₀)).symm (extChartAt I (γ t₀) (f x))
  exact ((extChartAt I (γ t₀)).left_inv (by rwa [extChartAt_source])).symm

/-- **Math.** Open-neighborhood form for a smooth scalar multiple of a
parallel field.  It pulls the open neighborhood for `e` back along the smooth
reparametrization `(s,t) ↦ (s φ(t),t)`. -/
theorem exists_open_contMDiffOn_expMapGlobal_smul_smul_parallel [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {e : ℝ → E} {φ : ℝ → ℝ} {a b t₀ : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (he : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ e a b)
    (hφ : ContDiff ℝ ∞ φ) (ht₀ : t₀ ∈ Ioo a b) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, t₀) ∈ U ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2)
          (x.1 • (φ x.2 • e x.2))) U := by
  obtain ⟨U, hUopen, h0U, hbase, _hsrc⟩ :=
    exists_open_contMDiffOn_expMapGlobal_smul_parallel (I := I) g hg hgeo hγc he ht₀
  let reparam : ℝ × ℝ → ℝ × ℝ := fun x => (x.1 * φ x.2, x.2)
  let W : Set (ℝ × ℝ) := reparam ⁻¹' U
  have hreparam : ContDiff ℝ ∞ reparam := by
    dsimp only [reparam]
    fun_prop
  have hWopen : IsOpen W := hUopen.preimage hreparam.continuous
  have h0W : (0, t₀) ∈ W := by
    simpa [W, reparam] using h0U
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      ((fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2) (x.1 • e x.2)) ∘ reparam) W :=
    hbase.comp hreparam.contMDiff.contMDiffOn (fun x hx => hx)
  refine ⟨W, hWopen, h0W, ?_⟩
  have hfun :
      ((fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2) (x.1 • e x.2)) ∘ reparam) =
        fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2)
          (x.1 • (φ x.2 • e x.2)) := by
    funext x
    simp only [Function.comp_apply, reparam, mul_smul]
  rwa [hfun] at hcomp

/-- **Math.** The Bonnet--Myers sine variation is `C^∞` on an open
neighborhood of every zero-slice point `(0,t₀)`. -/
theorem exists_open_contMDiffOn_expMapGlobal_sine_parallel [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {e : ℝ → E} {a b t₀ : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (he : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ e a b)
    (ht₀ : t₀ ∈ Ioo a b) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, t₀) ∈ U ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2)
          (x.1 • (Real.sin (Real.pi * x.2) • e x.2))) U := by
  exact exists_open_contMDiffOn_expMapGlobal_smul_smul_parallel
    (I := I) g hg hgeo hγc he (φ := fun t => Real.sin (Real.pi * t))
      (t₀ := t₀) (by fun_prop) ht₀

/-- **Math.** A smooth scalar multiple `φ(t)e(t)` of a parallel field gives a
smooth exponential variation.  This is the parallel-field theorem precomposed
with `(s,t) ↦ (s φ(t),t)`; the identity
`(s φ(t)) • e(t) = s • (φ(t) • e(t))` reads back the desired field. -/
theorem contMDiffAt_expMapGlobal_smul_smul_parallel [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {e : ℝ → E} {φ : ℝ → ℝ} {a b t₀ : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (he : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ e a b)
    (hφ : ContDiff ℝ ∞ φ) (ht₀ : t₀ ∈ Ioo a b) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2)
        (x.1 • (φ x.2 • e x.2))) (0, t₀) := by
  let reparam : ℝ × ℝ → ℝ × ℝ := fun x => (x.1 * φ x.2, x.2)
  have hreparam : ContDiff ℝ ∞ reparam := by
    dsimp only [reparam]
    fun_prop
  have hbase := contMDiffAt_expMapGlobal_smul_parallel (I := I) g hg hgeo hγc he ht₀
  have hbase' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2) (x.1 • e x.2))
      (reparam (0, t₀)) := by
    simpa [reparam] using hbase
  have hcomp := hbase'.comp (0, t₀) hreparam.contMDiff.contMDiffAt
  have hfun :
      ((fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2) (x.1 • e x.2)) ∘ reparam) =
        fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2)
          (x.1 • (φ x.2 • e x.2)) := by
    funext x
    simp only [Function.comp_apply, reparam, mul_smul]
  rw [← hfun]
  exact hcomp

/-- **Math.** The concrete Bonnet--Myers sine variation
`f(s,t) = exp_{γ(t)}(s sin(πt)e(t))` is `C^∞` at every point of its zero slice
over the interior of the parallel-field interval. -/
theorem contMDiffAt_expMapGlobal_sine_parallel [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {e : ℝ → E} {a b t₀ : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (he : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ e a b)
    (ht₀ : t₀ ∈ Ioo a b) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2)
        (x.1 • (Real.sin (Real.pi * x.2) • e x.2))) (0, t₀) := by
  exact contMDiffAt_expMapGlobal_smul_smul_parallel (I := I) g hg hgeo hγc he
    (φ := fun t => Real.sin (Real.pi * t)) (t₀ := t₀) (by fun_prop) ht₀

/-- **Math.** The Bonnet--Myers sine variation is `C^∞` on one uniform
product strip around its full zero slice over `[0,1]`.  The local open
neighborhoods supplied by
`exists_open_contMDiffOn_expMapGlobal_sine_parallel` glue smoothly because
they are open; the generalized tube lemma then extracts a product
neighborhood, and a symmetric interval is chosen inside its parameter factor. -/
theorem exists_contMDiffOn_infty_expMapGlobal_sine_parallel_strip [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {e : ℝ → E} {a b : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (he : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ e a b)
    (hsegment : Icc (0 : ℝ) 1 ⊆ Ioo a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ J : Set ℝ, IsOpen J ∧ Icc (0 : ℝ) 1 ⊆ J ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2)
          (x.1 • (Real.sin (Real.pi * x.2) • e x.2)))
        (Ioo (-δ) δ ×ˢ J) := by
  let f : ℝ × ℝ → M := fun x => expMapGlobal (I := I) g hg (γ x.2)
    (x.1 • (Real.sin (Real.pi * x.2) • e x.2))
  have hlocal : ∀ t : Icc (0 : ℝ) 1,
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, (t : ℝ)) ∈ U ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U := by
    intro t
    exact exists_open_contMDiffOn_expMapGlobal_sine_parallel
      (I := I) g hg hgeo hγc he (hsegment t.property)
  choose U hUopen h0U hfU using hlocal
  let Ω : Set (ℝ × ℝ) := ⋃ t : Icc (0 : ℝ) 1, U t
  have hΩopen : IsOpen Ω := isOpen_iUnion fun t => hUopen t
  have hfΩ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f Ω :=
    ContMDiffOn.iUnion_of_isOpen hfU hUopen
  have hzero : ({0} : Set ℝ) ×ˢ Icc (0 : ℝ) 1 ⊆ Ω := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    rw [mem_singleton_iff] at hs
    change s = 0 at hs
    change t ∈ Icc (0 : ℝ) 1 at ht
    subst s
    exact mem_iUnion_of_mem (⟨t, ht⟩ : Icc (0 : ℝ) 1) (h0U ⟨t, ht⟩)
  obtain ⟨u, J, hu, hJ, h0u, hIJ, huJ⟩ :=
    generalized_tube_lemma (isCompact_singleton : IsCompact ({0} : Set ℝ))
      isCompact_Icc hΩopen hzero
  have hu0 : u ∈ 𝓝 (0 : ℝ) := hu.mem_nhds (h0u (mem_singleton 0))
  obtain ⟨l, r, hlr, hlr_u⟩ := mem_nhds_iff_exists_Ioo_subset.1 hu0
  let δ : ℝ := min (-l) r
  have hδ : 0 < δ := by
    rw [lt_min_iff]
    exact ⟨by linarith [hlr.1], hlr.2⟩
  refine ⟨δ, hδ, J, hJ, hIJ, hfΩ.mono ?_⟩
  intro x hx
  apply huJ
  refine ⟨hlr_u ?_, hx.2⟩
  constructor <;> dsimp only [δ] at * <;> linarith [hx.1.1, hx.1.2,
    min_le_left (-l) r, min_le_right (-l) r]

/-- **Math.** The pointwise smoothness of the Bonnet--Myers sine variation
upgrades, at the finite order needed for second variation, to one product
neighbourhood of its whole zero slice over `[0,1]`.  More precisely, there is
a symmetric parameter interval and an open time set containing `[0,1]` on
which the variation is `C³`.

The proof first takes the open set of points where the surface is `C³`.
Pointwise `C^∞` regularity puts `{0} × [0,1]` inside this set; the generalized
tube lemma then supplies product neighbourhoods, and a symmetric real interval
is extracted from the neighbourhood of `0`. -/
theorem exists_contMDiffOn_three_expMapGlobal_sine_parallel_strip [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {e : ℝ → E} {a b : ℝ}
    (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (he : Riemannian.Jacobi.IsParallelFieldAlongOn (I := I) g γ e a b)
    (hsegment : Icc (0 : ℝ) 1 ⊆ Ioo a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ J : Set ℝ, IsOpen J ∧ Icc (0 : ℝ) 1 ⊆ J ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3
        (fun x : ℝ × ℝ => expMapGlobal (I := I) g hg (γ x.2)
          (x.1 • (Real.sin (Real.pi * x.2) • e x.2)))
        (Ioo (-δ) δ ×ˢ J) := by
  let f : ℝ × ℝ → M := fun x => expMapGlobal (I := I) g hg (γ x.2)
    (x.1 • (Real.sin (Real.pi * x.2) • e x.2))
  let U : Set (ℝ × ℝ) := {x | ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 3 f x}
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).1 hx
  have hzero : ({0} : Set ℝ) ×ˢ Icc (0 : ℝ) 1 ⊆ U := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    rw [mem_singleton_iff] at hs
    change s = 0 at hs
    change t ∈ Icc (0 : ℝ) 1 at ht
    subst s
    exact contMDiffAt_infty.mp
      (contMDiffAt_expMapGlobal_sine_parallel (I := I) g hg hgeo hγc he (hsegment ht)) 3
  obtain ⟨u, J, hu, hJ, h0u, hIJ, huJ⟩ :=
    generalized_tube_lemma (isCompact_singleton : IsCompact ({0} : Set ℝ))
      isCompact_Icc hUopen hzero
  have hu0 : u ∈ 𝓝 (0 : ℝ) := hu.mem_nhds (h0u (mem_singleton 0))
  obtain ⟨l, r, hlr, hlr_u⟩ := mem_nhds_iff_exists_Ioo_subset.1 hu0
  let δ : ℝ := min (-l) r
  have hδ : 0 < δ := by
    rw [lt_min_iff]
    exact ⟨by linarith [hlr.1], hlr.2⟩
  refine ⟨δ, hδ, J, hJ, hIJ, ?_⟩
  intro x hx
  apply (huJ ⟨hlr_u ?_, hx.2⟩).contMDiffWithinAt
  constructor <;> dsimp only [δ] at * <;> linarith [hx.1.1, hx.1.2,
    min_le_left (-l) r, min_le_right (-l) r]

end Exponential
end Riemannian

end
