import MorganTianLib.Ch02.GeodesicContinuousDependence
import MorganTianLib.Ch02.GeodesicContinuousDependenceTM
import MorganTianLib.Ch02.GeodesicLimits
import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodHuniq

/-!
# Morgan–Tian Ch. 2 — limits of minimizing geodesics (tangent-bundle version)

Blueprint `lem:limit-of-minimizing-geodesics`.  Let `(M, g)` be a complete
Riemannian manifold (ambient distance = the Riemannian distance of `g`), let
`I ⊆ ℝ` be an interval containing `0`, and let `In k ⊆ ℝ` be windows exhausting
`I` (every compact subset of `I` lies in `In k` for all large `k`).  Suppose the
`γs k : ℝ → M` are **unit-speed minimizing geodesics**: each is a geodesic of `g`
(`IsGeodesic`, continuous) with unit conserved speed (`speedSq g (γs k) 0 = 1`)
and minimizing on its window (`IsMinGeodesicOn (γs k) (In k)`), and the initial
points `γs k 0` converge to `p`.  Then, after passing to a subsequence, the
`γs k` converge to a unit-speed minimizing geodesic `γ : ℝ → M` with `γ 0 = p`,
*uniformly on every compact time interval*, and their initial data converge in
the tangent bundle: `(γs k 0, γs k '(0)) → (γ 0, γ'(0))`.

The engine is `lem:geodesic-continuous-dependence`
(`GeodesicContinuousDependence.lean`).  The one genuinely new ingredient is
**Step 1**: extract a convergent subsequence of initial *velocities*.  The chart
velocities `ξ k = (φ_p ∘ γs k)'(0)` are bounded — the conserved unit speed
controls them through the local coordinate-norm/Gram estimate
`exists_sq_norm_deriv_le_speedSq` (`‖ξ k‖² ≤ c · speedSq g (γs k) 0 = c`) once
`γs k 0` is near `p` — so Bolzano–Weierstrass on a closed ball of the
finite-dimensional model `E` (`IsCompact.tendsto_subseq`) yields a subsequence
`ξ (φ ·) → x`.  The geodesic `γ` with initial chart velocity `x` at `p`
(`exists_globalGeodesic_initial`) is then the limit: the convergence invariant
`Riemannian.Geodesic.ConvAt γ (γs ∘ φ) 0` holds at time `0` by construction,
and the continuous-dependence machinery propagates it (`convAt_of_convAt_zero`,
`tendsto_apply_of_convAt_zero`, `tendstoUniformlyOn_of_convAt_zero`).  Minimality
of `γ` on `I` passes to the limit from `IsMinGeodesicOn (γs (φ ·)) (In (φ ·))`
by continuity of the distance and pointwise convergence.

Only the ambient formulation with *global* geodesics `γs k : ℝ → M` is used here;
the blueprint's preliminary extension of window-geodesics to global ones (its
appeal to `lem:geodesic-continuous-dependence`(1)) is folded into the hypotheses.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.1–2.2.
-/

open Set Filter Metric Riemannian Riemannian.Geodesic Riemannian.Exponential
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]

/-! ## Extending a closed geodesic window

The book starts the limiting-geodesics argument with curves defined only on
closed windows.  The continuous-dependence engine below uses global curves, so
we make that extension explicit rather than hiding it in the theorem
hypotheses.
-/

/-- **Math.** A geodesic on a nondegenerate closed interval has a global geodesic
extension.  The extension is obtained by normalising the interval to `Icc 0 1`,
using the endpoint extension theorem, and then applying complete-manifold
existence and uniqueness for the initial data at time `0`. -/
theorem exists_globalGeodesic_eqOn_of_isGeodesicOn_Icc
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) :
    ∃ Γ : ℝ → M, IsGeodesic (I := I) g Γ ∧ Continuous Γ ∧
      Set.EqOn Γ γ (Icc a b) := by
  classical
  have hk : 0 < b - a := sub_pos.mpr hab
  let α : ℝ → M := fun s => γ ((b - a) * s + a)
  have hαmap : MapsTo (fun s : ℝ => (b - a) * s + a) (Icc 0 1) (Icc a b) := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2, hk]
  have hαgeo : IsGeodesicOn (I := I) g α (Icc 0 1) := by
    have h := isGeodesicOn_comp_affine (I := I) (g := g) hgeo
      (κ := b - a) (c := a)
    exact h.mono hαmap
  have hαcont : ContinuousOn α (Icc 0 1) := by
    exact hcont.comp ((continuous_const.mul continuous_id).add continuous_const).continuousOn
      hαmap
  obtain ⟨lo, hi, β, hlo, hhi, hβgeo, hβcont, hβα⟩ :=
    Riemannian.Exponential.exists_geodesic_window_of_isGeodesicOn_Icc
      (I := I) g hαgeo hαcont
  have h0β : (0 : ℝ) ∈ Ioo lo hi := ⟨hlo, by linarith⟩
  have hβ0 : β 0 = γ a := by
    rw [hβα ⟨le_rfl, by norm_num⟩]
    simp [α]
  let v : E := deriv (fun τ => extChartAt I (β 0) (β τ)) 0
  have hβderiv : HasDerivAt (fun τ => extChartAt I (β 0) (β τ)) v 0 := by
    exact (hβgeo 0 h0β).hasDerivAt_extChartAt_deriv
      ((hβcont 0 h0β).continuousAt (isOpen_Ioo.mem_nhds h0β))
      (mem_chart_source H (β 0))
  obtain ⟨Γ₀, hΓ₀0, hΓ₀deriv, hΓ₀cont, hΓ₀geo⟩ :=
    exists_globalGeodesic_initial (I := I) g hg (β 0) v
  have hβΓ₀ : Set.EqOn β Γ₀ (Ioo lo hi) := by
    apply eqOn_of_initial_data (I := I) g isOpen_Ioo isPreconnected_Ioo h0β
      hβgeo (hΓ₀geo.isGeodesicOn _) hβcont hΓ₀cont.continuousOn
    · exact hΓ₀0.symm
    · exact hβderiv.deriv.trans hΓ₀deriv.deriv.symm
  let Γ : ℝ → M := fun t => Γ₀ ((b - a)⁻¹ * t + (-(b - a)⁻¹ * a))
  have hΓgeo : IsGeodesic (I := I) g Γ := by
    have h := isGeodesicOn_comp_affine (I := I) (g := g)
      (hΓ₀geo.isGeodesicOn (Set.univ : Set ℝ))
      (κ := (b - a)⁻¹) (c := -(b - a)⁻¹ * a)
    intro t
    simpa [Γ] using h t (Set.mem_univ t)
  have hΓcont : Continuous Γ := by
    dsimp [Γ]
    exact hΓ₀cont.comp (by fun_prop)
  refine ⟨Γ, hΓgeo, hΓcont, ?_⟩
  intro t ht
  let s : ℝ := (b - a)⁻¹ * t + (-(b - a)⁻¹ * a)
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    dsimp [s]
    constructor <;> field_simp [hk.ne'] <;> nlinarith [ht.1, ht.2]
  have hsopen : s ∈ Ioo lo hi := by
    constructor
    · linarith [hlo, hs.1]
    · linarith [hhi, hs.2]
  have hst : (b - a) * s + a = t := by
    dsimp [s]
    field_simp [hk.ne']
    ring
  change Γ₀ s = γ t
  rw [← hβΓ₀ hsopen, hβα hs]
  dsimp [α]
  rw [hst]

/-- **Math.** **Limits of minimizing geodesics, tangent-bundle version**
(blueprint `lem:limit-of-minimizing-geodesics`).  On a complete Riemannian
manifold, a sequence of unit-speed minimizing geodesics `γs k` on windows `In k`
exhausting an interval `I ∋ 0`, with initial points converging to `p`,
subconverges to a unit-speed minimizing geodesic `γ` on `I` with `γ 0 = p`:
uniformly on every compact interval `[-T, T]`, and in the tangent bundle at time
`0` (the invariant `ConvAt γ (γs ∘ φ) 0`, i.e. `(γs k 0, γs k '(0)) → (p,
γ'(0))`). -/
theorem exists_isMinGeodesicOn_convAt_of_tendsto (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M]
    {I₀ : Set ℝ} (hI₀ : I₀.OrdConnected)
    {In : ℕ → Set ℝ} {γs : ℕ → ℝ → M}
    (hgeo : ∀ k, IsGeodesic (I := I) g (γs k)) (hc : ∀ k, Continuous (γs k))
    (hspeed : ∀ k, speedSq (I := I) g (γs k) 0 = 1)
    (hmin : ∀ k, IsMinGeodesicOn (γs k) (In k))
    (hexh : ∀ J : Set ℝ, IsCompact J → J ⊆ I₀ → ∀ᶠ k in atTop, J ⊆ In k)
    {p : M} (hp : Tendsto (fun k => γs k 0) atTop (𝓝 p)) :
    ∃ (φ : ℕ → ℕ) (γ : ℝ → M),
      StrictMono φ ∧ IsGeodesic (I := I) g γ ∧ Continuous γ ∧ γ 0 = p ∧
      IsMinGeodesicOn γ I₀ ∧
      ConvAt (I := I) γ (fun j => γs (φ j)) 0 ∧
      (∀ T : ℝ, TendstoUniformlyOn (fun j => γs (φ j)) γ atTop (Icc (-T) T)) ∧
      Tendsto
        (fun j =>
          (⟨γs (φ j) 0, curveVelocity (I := I) (γs (φ j)) 0⟩ : TangentBundle I M))
        atTop
        (𝓝 (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M)) := by
  classical
  -- Local coordinate-velocity bound near `p` (constant `c`, neighbourhood `V`).
  obtain ⟨c, V, hcpos, hVnhds, -, hbound⟩ :=
    exists_sq_norm_deriv_le_speedSq (I := I) g p
  -- Eventually `γs k 0` lies in the chart source of `p` and reads into `V`.
  have hsrcEv : ∀ᶠ k in atTop, γs k 0 ∈ (chartAt H p).source :=
    hp.eventually ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
  have hVEv : ∀ᶠ k in atTop, extChartAt I p (γs k 0) ∈ V :=
    ((continuousAt_extChartAt p).tendsto.comp hp).eventually hVnhds
  -- Step 1a: the chart velocities `ξ k = (φ_p ∘ γs k)'(0)` are eventually `≤ √c`.
  have hboundEv : ∀ᶠ k in atTop,
      ‖deriv (fun τ => extChartAt I p (γs k τ)) 0‖ ≤ Real.sqrt c := by
    filter_upwards [hsrcEv, hVEv] with k hsrc hVmem
    have hHD : HasDerivAt (fun τ => extChartAt I p (γs k τ))
        (deriv (fun τ => extChartAt I p (γs k τ)) 0) 0 :=
      ((hgeo k).hasGeodesicEquationAt 0).hasDerivAt_extChartAt_deriv
        (hc k).continuousAt hsrc
    have hb := hbound (hc k).continuousAt hsrc hVmem hHD
    rw [hspeed k, mul_one] at hb
    have hsq := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_sq (norm_nonneg _)] at hsq
  rw [eventually_atTop] at hboundEv
  obtain ⟨N, hN⟩ := hboundEv
  -- Step 1b: Bolzano–Weierstrass on the closed `√c`-ball of the model `E`.
  have hKcpt : IsCompact (Metric.closedBall (0 : E) (Real.sqrt c)) :=
    isCompact_closedBall _ _
  have hmemK : ∀ j : ℕ,
      deriv (fun τ => extChartAt I p (γs (j + N) τ)) 0 ∈
        Metric.closedBall (0 : E) (Real.sqrt c) := fun j =>
    mem_closedBall_zero_iff.mpr (hN (j + N) (Nat.le_add_left N j))
  obtain ⟨x, -, ψ, hψ, hconv⟩ := hKcpt.tendsto_subseq hmemK
  -- The reindexing subsequence `φ = ψ · + N`.
  have hφmono : StrictMono (fun j => ψ j + N) := fun _ _ hab =>
    Nat.add_lt_add_right (hψ hab) N
  have hφat : Tendsto (fun j => ψ j + N) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_right (ψ j) N) hψ.tendsto_atTop
  have hφpos : Tendsto (fun j => γs (ψ j + N) 0) atTop (𝓝 p) := hp.comp hφat
  -- Step 2: the candidate limit geodesic `γ` with initial chart velocity `x`.
  obtain ⟨γ, hγ0, hγHD, hγcont, hγgeo⟩ :=
    exists_globalGeodesic_initial (I := I) g hg p x
  set γs' : ℕ → ℝ → M := fun j => γs (ψ j + N) with hγs'
  have hgeoφ : ∀ n, IsGeodesic (I := I) g (γs' n) := fun n => hgeo (ψ n + N)
  have hcφ : ∀ n, Continuous (γs' n) := fun n => hc (ψ n + N)
  -- Step 3: the convergence invariant holds at time `0`.
  have hConv : ConvAt (I := I) γ γs' 0 := by
    refine ⟨?_, ?_⟩
    · show Tendsto (fun n => γs (ψ n + N) 0) atTop (𝓝 (γ 0))
      rw [hγ0]; exact hφpos
    · show Tendsto (fun n => deriv (fun τ => extChartAt I (γ 0) (γs (ψ n + N) τ)) 0)
        atTop (𝓝 (deriv (fun τ => extChartAt I (γ 0) (γ τ)) 0))
      simp only [hγ0]
      rw [hγHD.deriv]
      exact hconv
  -- Step 5: minimality of `γ` on `I₀` passes to the limit.
  have hγmin : IsMinGeodesicOn γ I₀ := by
    intro s hs t ht
    have hsP : Tendsto (fun n => γs' n s) atTop (𝓝 (γ s)) :=
      tendsto_apply_of_convAt_zero (I := I) g hγgeo hγcont hgeoφ hcφ hConv s
    have htP : Tendsto (fun n => γs' n t) atTop (𝓝 (γ t)) :=
      tendsto_apply_of_convAt_zero (I := I) g hγgeo hγcont hgeoφ hcφ hConv t
    have hdist : Tendsto (fun n => dist (γs' n s) (γs' n t)) atTop
        (𝓝 (dist (γ s) (γ t))) := hsP.dist htP
    -- The endpoints eventually lie in a common window, where the distance is `|s - t|`.
    have hsmem : min s t ∈ I₀ := by
      rcases le_total s t with h | h
      · rwa [min_eq_left h]
      · rwa [min_eq_right h]
    have htmem : max s t ∈ I₀ := by
      rcases le_total s t with h | h
      · rwa [max_eq_right h]
      · rwa [max_eq_left h]
    have hJsub : Icc (min s t) (max s t) ⊆ I₀ := hI₀.out hsmem htmem
    have hev : ∀ᶠ n in atTop, Icc (min s t) (max s t) ⊆ In (ψ n + N) :=
      hφat.eventually (hexh _ isCompact_Icc hJsub)
    have hconst : ∀ᶠ n in atTop, dist (γs' n s) (γs' n t) = |s - t| := by
      filter_upwards [hev] with n hn
      exact hmin (ψ n + N) (hn ⟨min_le_left s t, le_max_left s t⟩)
        (hn ⟨min_le_right s t, le_max_right s t⟩)
    have hconstT : Tendsto (fun n => dist (γs' n s) (γs' n t)) atTop (𝓝 |s - t|) :=
      Tendsto.congr' (hconst.mono fun n h => h.symm) tendsto_const_nhds
    exact tendsto_nhds_unique hdist hconstT
  -- Step 4: assemble, with uniform convergence from `tendstoUniformlyOn_of_convAt_zero`.
  refine ⟨fun j => ψ j + N, γ, hφmono, hγgeo, hγcont, hγ0, hγmin, hConv,
    (fun T => ?_), ?_⟩
  · exact tendstoUniformlyOn_of_convAt_zero (I := I) g hg hγcont hγgeo hcφ hgeoφ hConv T
  · simpa only [γs'] using
      (tendsto_tangentBundle_velocity_of_convAt (I := I) g hγgeo hγcont hgeoφ hcφ hConv)

private theorem continuousAt_of_speedSq_eq_one (g : RiemannianMetric I M)
    {γ : ℝ → M} {t : ℝ} (hspeed : speedSq (I := I) g γ t = 1) :
    ContinuousAt γ t := by
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := by
    by_contra h
    have hz := mfderiv_zero_of_not_mdifferentiableAt h
    rw [speedSq_def, hz] at hspeed
    simp at hspeed
  exact hmd.continuousAt

private theorem deriv_chartReading_eq_of_eqOn_Icc
    (g : RiemannianMetric I M) {Γ γ : ℝ → M} {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b)
    (hΓgeo : IsGeodesic (I := I) g Γ)
    (hγgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hΓcont : ContinuousAt Γ t) (hγcont : ContinuousAt γ t)
    (heq : Set.EqOn Γ γ (Icc a b)) :
    deriv (chartReading (I := I) (γ t) Γ) t =
      deriv (chartReading (I := I) (γ t) γ) t := by
  have hteq : Γ t = γ t := heq ht
  have hΓd : HasDerivAt (chartReading (I := I) (γ t) Γ)
      (deriv (chartReading (I := I) (γ t) Γ) t) t := by
    exact (hΓgeo t).hasDerivAt_extChartAt_deriv hΓcont
      (by rw [hteq]; exact mem_chart_source H (γ t))
  have hγd : HasDerivAt (chartReading (I := I) (γ t) γ)
      (deriv (chartReading (I := I) (γ t) γ) t) t := by
    exact (hγgeo t ht).hasDerivAt_extChartAt_deriv hγcont
      (mem_chart_source H (γ t))
  have hEqChart : ∀ s ∈ Icc a b,
      chartReading (I := I) (γ t) γ s =
        chartReading (I := I) (γ t) Γ s := by
    intro s hs
    dsimp [chartReading]
    rw [heq hs]
  have hΓdw : HasDerivWithinAt (chartReading (I := I) (γ t) Γ)
      (deriv (chartReading (I := I) (γ t) Γ) t) (Icc a b) t :=
    hΓd.hasDerivWithinAt
  have hΓdw' := hΓdw.congr hEqChart (hEqChart t ht)
  exact (uniqueDiffOn_Icc hab t ht).eq_deriv (Icc a b) hΓdw' hγd.hasDerivWithinAt

private theorem curveVelocityCoord_eq_of_eqOn_Icc
    (g : RiemannianMetric I M) {Γ γ : ℝ → M} {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b)
    (hΓgeo : IsGeodesic (I := I) g Γ)
    (hγgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hΓcont : ContinuousAt Γ t) (hγcont : ContinuousAt γ t)
    (heq : Set.EqOn Γ γ (Icc a b)) :
    curveVelocityCoord (I := I) Γ t = curveVelocityCoord (I := I) γ t := by
  change deriv (chartReading (I := I) (Γ t) Γ) t =
    deriv (chartReading (I := I) (γ t) γ) t
  have h := deriv_chartReading_eq_of_eqOn_Icc (I := I) g hab ht hΓgeo hγgeo
    hΓcont hγcont heq
  rw [heq ht]
  exact h

private theorem tangentBundle_curveVelocity_eq_of_eqOn_Icc
    (g : RiemannianMetric I M) {Γ γ : ℝ → M} {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b)
    (hΓgeo : IsGeodesic (I := I) g Γ)
    (hγgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hΓcont : ContinuousAt Γ t) (hγcont : ContinuousAt γ t)
    (heq : Set.EqOn Γ γ (Icc a b)) :
    (⟨Γ t, curveVelocity (I := I) Γ t⟩ : TangentBundle I M) =
      ⟨γ t, curveVelocity (I := I) γ t⟩ := by
  have hval : Γ t = γ t := heq ht
  have hcoord := curveVelocityCoord_eq_of_eqOn_Icc (I := I) g hab ht hΓgeo hγgeo
    hΓcont hγcont heq
  rw [hval]
  exact congrArg
    (fun w : E =>
      (⟨γ t, (w : TangentSpace I (γ t))⟩ : TangentBundle I M)) hcoord

private theorem speedSq_eq_of_eqOn_Icc
    (g : RiemannianMetric I M) {Γ γ : ℝ → M} {a b : ℝ}
    (hab : a < b) (hΓgeo : IsGeodesic (I := I) g Γ)
    (hγgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hΓcont : Continuous Γ) (hγcont : ContinuousAt γ 0)
    (heq : Set.EqOn Γ γ (Icc a b)) (h0 : (0 : ℝ) ∈ Icc a b)
    (hspeed : speedSq (I := I) g γ 0 = 1) :
    speedSq (I := I) g Γ 0 = 1 := by
  have hΓs := (hΓgeo 0).speedSq_eq_chartMetricInner_of_mem_source
    hΓcont.continuousAt (β := γ 0) (by rw [heq h0]; exact mem_chart_source H (γ 0))
  have hγs := (hγgeo 0 h0).speedSq_eq_chartMetricInner_of_mem_source
    hγcont (β := γ 0) (mem_chart_source H (γ 0))
  have hderiv := deriv_chartReading_eq_of_eqOn_Icc (I := I) g hab h0 hΓgeo hγgeo
    hΓcont.continuousAt hγcont heq
  have hval : chartReading (I := I) (γ 0) Γ 0 =
      chartReading (I := I) (γ 0) γ 0 := by
    dsimp [chartReading]
    rw [heq h0]
  calc
    speedSq (I := I) g Γ 0 = chartMetricInner (I := I) g (γ 0)
        (chartReading (I := I) (γ 0) Γ 0)
        (deriv (chartReading (I := I) (γ 0) Γ) 0)
        (deriv (chartReading (I := I) (γ 0) Γ) 0) := hΓs
    _ = chartMetricInner (I := I) g (γ 0)
        (chartReading (I := I) (γ 0) γ 0)
        (deriv (chartReading (I := I) (γ 0) γ) 0)
        (deriv (chartReading (I := I) (γ 0) γ) 0) := by rw [hval, hderiv]
    _ = speedSq (I := I) g γ 0 := hγs.symm
    _ = 1 := hspeed

/-- **Math.** Window-domain integration for the limiting-minimizing-geodesics
theorem.  After discarding finitely many degenerate windows, the existing
global compactness theorem is applied to explicit global extensions and its
uniform and initial-state conclusions are transferred back to the original
window curves.  The window curves are still represented as total maps here;
`IsGeodesicOn` and the `speedSq` hypothesis therefore retain the current
Riemannian encoding of the endpoint derivative. -/
theorem exists_isMinGeodesicOn_of_Icc_tendsto
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {I₀ : Set ℝ} (hI₀ : I₀.OrdConnected) (h0I₀ : (0 : ℝ) ∈ I₀)
    (hneI₀ : ∃ q : ℝ, q ∈ I₀ ∧ q ≠ 0)
    {a b : ℕ → ℝ} {γs : ℕ → ℝ → M}
    (h0 : ∀ k, (0 : ℝ) ∈ Icc (a k) (b k))
    (hgeo : ∀ k, IsGeodesicOn (I := I) g (γs k) (Icc (a k) (b k)))
    (hspeed : ∀ k, speedSq (I := I) g (γs k) 0 = 1)
    (hmin : ∀ k, IsMinGeodesicOn (γs k) (Icc (a k) (b k)))
    (hexh : ∀ J : Set ℝ, IsCompact J → J ⊆ I₀ →
      ∀ᶠ k in atTop, J ⊆ Icc (a k) (b k))
    {p : M} (hp : Tendsto (fun k => γs k 0) atTop (𝓝 p)) :
    ∃ (φ : ℕ → ℕ) (γ : ℝ → M),
      StrictMono φ ∧ IsGeodesic (I := I) g γ ∧ Continuous γ ∧ γ 0 = p ∧
      IsMinGeodesicOn γ I₀ ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ I₀ →
        TendstoUniformlyOn (fun j => γs (φ j)) γ atTop K) ∧
      Tendsto
        (fun j =>
          (⟨γs (φ j) 0, curveVelocity (I := I) (γs (φ j)) 0⟩ : TangentBundle I M))
        atTop
        (𝓝 (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M)) := by
  obtain ⟨q, hqI, hqne⟩ := hneI₀
  let u : ℝ := min 0 q
  let v : ℝ := max 0 q
  have huv : u < v := by
    dsimp [u, v]
    exact min_lt_max.mpr hqne.symm
  have hJsub : Icc u v ⊆ I₀ := by
    intro t ht
    by_cases hq : 0 ≤ q
    · have hu : u = 0 := min_eq_left hq
      have hv : v = q := max_eq_right hq
      rw [hu, hv] at ht
      exact hI₀.out h0I₀ hqI ht
    · have hq' : q ≤ 0 := le_of_not_ge hq
      have hu : u = q := min_eq_right hq'
      have hv : v = 0 := max_eq_left hq'
      rw [hu, hv] at ht
      exact hI₀.out hqI h0I₀ ht
  have hJev := hexh (Icc u v) isCompact_Icc hJsub
  rw [eventually_atTop] at hJev
  obtain ⟨N, hN⟩ := hJev
  have htail : ∀ j : ℕ, a (j + N) < b (j + N) := by
    intro j
    have hsub := hN (j + N) (Nat.le_add_left N j)
    have hu := hsub ⟨le_rfl, huv.le⟩
    have hv := hsub ⟨huv.le, le_rfl⟩
    exact lt_of_le_of_lt hu.1 (lt_of_lt_of_le huv hv.2)
  have hshift : Tendsto (fun j : ℕ => j + N) atTop atTop :=
    tendsto_add_atTop_nat N
  have hpTail : Tendsto (fun j => γs (j + N) 0) atTop (𝓝 p) := hp.comp hshift
  have hext : ∀ j : ℕ, ∃ Γj : ℝ → M,
      IsGeodesic (I := I) g Γj ∧ Continuous Γj ∧
        Set.EqOn Γj (γs (j + N)) (Icc (a (j + N)) (b (j + N))) := by
    intro j
    exact exists_globalGeodesic_eqOn_of_isGeodesicOn_Icc (I := I) g hg
      (htail j) (hgeo (j + N)) (hmin (j + N)).continuousOn
  choose Γ hΓgeo hΓcont hΓeq using hext
  have hγc0 : ∀ k : ℕ, ContinuousAt (γs k) 0 := fun k =>
    continuousAt_of_speedSq_eq_one (I := I) g (hspeed k)
  have hΓspeed : ∀ j : ℕ, speedSq (I := I) g (Γ j) 0 = 1 := by
    intro j
    exact speedSq_eq_of_eqOn_Icc (I := I) g (htail j) (hΓgeo j)
      (hgeo (j + N)) (hΓcont j) (hγc0 (j + N)) (hΓeq j)
      (h0 (j + N)) (hspeed (j + N))
  have hΓmin : ∀ j : ℕ,
      IsMinGeodesicOn (Γ j) (Icc (a (j + N)) (b (j + N))) := by
    intro j s hs t ht
    rw [hΓeq j hs, hΓeq j ht]
    exact hmin (j + N) hs ht
  have hexhTail : ∀ J : Set ℝ, IsCompact J → J ⊆ I₀ →
      ∀ᶠ j in atTop, J ⊆ Icc (a (j + N)) (b (j + N)) := by
    intro J hJc hJs
    have hEv := hexh J hJc hJs
    rw [eventually_atTop] at hEv ⊢
    obtain ⟨K, hK⟩ := hEv
    refine ⟨K, ?_⟩
    intro j hj
    exact hK (j + N) (le_trans hj (Nat.le_add_right j N))
  have hpΓ : Tendsto (fun j => Γ j 0) atTop (𝓝 p) := by
    apply hpTail.congr'
    exact Filter.Eventually.of_forall fun j => (hΓeq j (h0 (j + N))).symm
  obtain ⟨φ, γ, hφ, hγgeo, hγcont, hγ0, hγmin, hConv, hUniform, hTM⟩ :=
    exists_isMinGeodesicOn_convAt_of_tendsto (I := I) g hg hI₀
      (In := fun j => Icc (a (j + N)) (b (j + N))) (γs := Γ)
      (fun j => hΓgeo j) (fun j => hΓcont j) hΓspeed hΓmin hexhTail hpΓ
  let ψ : ℕ → ℕ := fun j => φ j + N
  let Γout : ℕ → ℝ → M := fun j => Γ (φ j)
  have hψmono : StrictMono ψ := fun i j hij =>
    Nat.add_lt_add_right (hφ hij) N
  have hψtop : Tendsto ψ atTop atTop := by
    dsimp [ψ]
    exact hshift.comp hφ.tendsto_atTop
  have hΓoutEq : ∀ j : ℕ,
      Set.EqOn (Γout j) (γs (ψ j)) (Icc (a (ψ j)) (b (ψ j))) := by
    intro j s hs
    dsimp [Γout, ψ]
    exact hΓeq (φ j) hs
  have hUniformOrig : ∀ K : Set ℝ, IsCompact K → K ⊆ I₀ →
      TendstoUniformlyOn (fun j => γs (ψ j)) γ atTop K := by
    intro K hKc hKs
    obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : ℝ)
    have hKR : K ⊆ Icc (-R) R := by
      intro x hx
      have hx' := hR hx
      have habs : |x| ≤ R := by
        simpa [Real.dist_eq] using hx'
      exact abs_le.mp habs
    have hU := (hUniform R).mono hKR
    have hEv : ∀ᶠ j in atTop,
        Set.EqOn (Γ (φ j)) (γs (ψ j)) K := by
      filter_upwards [hψtop.eventually (hexh K hKc hKs)] with j hj
      exact (hΓoutEq j).mono hj
    exact hU.congr hEv
  have hStateEq : ∀ j : ℕ,
      (⟨Γout j 0, curveVelocity (I := I) (Γout j) 0⟩ : TangentBundle I M) =
        ⟨γs (ψ j) 0, curveVelocity (I := I) (γs (ψ j)) 0⟩ := by
    intro j
    dsimp [Γout, ψ]
    exact tangentBundle_curveVelocity_eq_of_eqOn_Icc (I := I) g
      (htail (φ j)) (h0 (φ j + N)) (hΓgeo (φ j)) (hgeo (φ j + N))
      (hΓcont (φ j)).continuousAt (hγc0 (φ j + N)) (hΓeq (φ j))
  have hTMOrig : Tendsto
      (fun j =>
        (⟨γs (ψ j) 0, curveVelocity (I := I) (γs (ψ j)) 0⟩ : TangentBundle I M))
      atTop (𝓝 (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M)) := by
    apply hTM.congr'
    exact Filter.Eventually.of_forall hStateEq
  refine ⟨ψ, γ, hψmono, hγgeo, hγcont, hγ0, hγmin, ?_, hTMOrig⟩
  · intro K hKc hKs
    exact hUniformOrig K hKc hKs

end MorganTianLib

end
