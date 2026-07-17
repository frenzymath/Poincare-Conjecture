import PoincareLib.Ch02.EndsEndpointContinuity
import OpenGALib.Riemannian.Geodesic.FlowReadback
import OpenGALib.Riemannian.Geodesic.DataTransfer
import OpenGALib.Riemannian.Geodesic.Completeness

/-!
# Morgan–Tian Ch. 2 — discharging the flow-box convergence step

`EndsEndpointContinuity.lean` reduces the endpoint continuity
`GeodesicEndpointContinuity g p` (the analytic input of `lem:ends-exist`) to the
**flow-box step** `ConvStepProperty g` — the universally quantified form of do
Carmo's `Riemannian.Geodesic.exists_conv_step`, which is still `sorry` in
`OpenGALib`.  This file discharges `ConvStepProperty g` unconditionally, thereby
closing `lem:ends-exist` to a full `\leanok`.

The argument is do Carmo's flow-box chaining (Ch. 7, Theorem 2.8, f ⟹ b),
assembled from the sorry-free `OpenGALib` toolkit:

* **`ConvChartAt`** — the convergence invariant read in a *fixed* chart at a
  flow-box centre `x` (positions and chart-`x` velocities converge).
* **`convAt_iff_convChartAt`** — the moving-chart invariant `ConvAt` (chart at
  the limit foot `γ t`) is equivalent to the fixed-chart one, by the
  chart-to-chart velocity transfer `tendsto_deriv_extChartAt_transfer`.
* **`convAt_comp_affine`** — `ConvAt` is invariant under affine
  reparametrisation of the whole family (velocities scale by the nonzero
  factor `κ`, so convergence is preserved).  This lets us *slow the geodesics
  down* so their chart velocities fit into a fixed flow-box velocity ball.
* **`convChartAt_propagate`** — the heart: at a flow-box centre `x`, if `γ`'s
  data at a base time `t` is admissible (fits the flow ball) and the fixed-chart
  invariant holds at `t`, then the flow-box readback
  (`exists_uniform_flow_readback`, position *and* velocity) together with the
  flow's Lipschitz dependence on initial data (`exists_uniform_geodesic_flow`)
  propagate it to every time `t + s` inside the flow window.
* **`convStepProperty`** — the assembly: at each base time `tstar`, centre a
  flow box at `x = γ tstar`, slow the family down enough that the data stays
  admissible on a small interval, and read off the radius `ρ`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7, Theorem 2.8, f) ⟹ b).
-/

open Set Filter Metric Riemannian Riemannian.Geodesic Riemannian.Exponential
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- **Math.** **The fixed-chart convergence invariant.** Positions of the
sequence `γs n` converge to those of the limit geodesic `γ`, and the velocities
read in the *fixed* chart at the flow-box centre `x` converge, at time `t`. -/
def ConvChartAt (g : RiemannianMetric I M) (x : M) (γ : ℝ → M) (γs : ℕ → ℝ → M)
    (t : ℝ) : Prop :=
  Tendsto (fun n => γs n t) atTop (𝓝 (γ t)) ∧
    Tendsto (fun n => deriv (fun τ => extChartAt I x (γs n τ)) t) atTop
      (𝓝 (deriv (fun τ => extChartAt I x (γ τ)) t))

/-- **Math.** **Moving-chart ↔ fixed-chart invariant.** For a base point `x`
whose chart contains the limit foot `γ t`, the moving-chart invariant `ConvAt`
(velocities read in the chart at `γ t`) is equivalent to the fixed-chart
invariant `ConvChartAt` (velocities read in the chart at `x`).  Both share the
position clause; the velocity clauses are exchanged by the chart-to-chart
transfer `tendsto_deriv_extChartAt_transfer`. -/
theorem convAt_iff_convChartAt (g : RiemannianMetric I M) {x : M}
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγgeo : IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (hγsgeo : ∀ n, IsGeodesic (I := I) g (γs n)) (hγsc : ∀ n, Continuous (γs n))
    {t : ℝ} (hxsrc : γ t ∈ (chartAt H x).source) :
    ConvAt (I := I) g γ γs t ↔ ConvChartAt (I := I) g x γ γs t := by
  constructor
  · rintro ⟨hpos, hvel⟩
    refine ⟨hpos, ?_⟩
    exact tendsto_deriv_extChartAt_transfer (α := γ t) (β := x)
      (fun n => (hγsgeo n).hasGeodesicEquationAt t)
      (fun n => (hγsc n).continuousAt)
      (hγgeo.hasGeodesicEquationAt t) hγc.continuousAt
      (mem_chart_source H (γ t)) hxsrc hpos hvel
  · rintro ⟨hpos, hvel⟩
    refine ⟨hpos, ?_⟩
    exact tendsto_deriv_extChartAt_transfer (α := x) (β := γ t)
      (fun n => (hγsgeo n).hasGeodesicEquationAt t)
      (fun n => (hγsc n).continuousAt)
      (hγgeo.hasGeodesicEquationAt t) hγc.continuousAt
      hxsrc (mem_chart_source H (γ t)) hpos hvel

/-- **Math.** Affine reparametrisation `τ ↦ κ τ + c` scales the derivative of a
composite by the factor `κ` (unconditionally, even where `F` is not
differentiable). -/
theorem deriv_comp_affine (F : ℝ → E) (κ c s : ℝ) :
    deriv (fun τ => F (κ * τ + c)) s = κ • deriv F (κ * s + c) := by
  have h := deriv_comp_mul_left κ (fun σ => F (σ + c)) s
  simpa [deriv_comp_add_const] using h

/-- **Math.** **Affine reparametrisation invariance of the invariant.** For a
nonzero factor `κ`, the invariant `ConvAt` for the affinely reparametrised
family `s ↦ γ (κ s + c)` at time `s` is equivalent to the invariant for the
original family at time `κ s + c`.  Positions are literally the same points;
the chart velocities differ by the fixed nonzero factor `κ`, so convergence is
preserved. -/
theorem convAt_comp_affine (g : RiemannianMetric I M)
    {γ : ℝ → M} {γs : ℕ → ℝ → M} {κ c : ℝ} (hκ : κ ≠ 0) {s : ℝ} :
    ConvAt (I := I) g (fun τ => γ (κ * τ + c)) (fun n τ => γs n (κ * τ + c)) s ↔
      ConvAt (I := I) g γ γs (κ * s + c) := by
  have key : ∀ F : ℝ → E, deriv (fun τ => F (κ * τ + c)) s = κ • deriv F (κ * s + c) := by
    intro F
    have h := deriv_comp_mul_left κ (fun σ => F (σ + c)) s
    simpa [deriv_comp_add_const] using h
  simp only [ConvAt]
  refine and_congr Iff.rfl ?_
  rw [show (fun n => deriv (fun τ => extChartAt I (γ (κ * s + c)) (γs n (κ * τ + c))) s)
        = fun n => κ • deriv (fun σ => extChartAt I (γ (κ * s + c)) (γs n σ)) (κ * s + c) from
      funext fun n => key (fun σ => extChartAt I (γ (κ * s + c)) (γs n σ)),
    key (fun σ => extChartAt I (γ (κ * s + c)) (γ σ))]
  exact tendsto_const_smul_iff₀ hκ

/-- **Math.** **Flow-box propagation of the fixed-chart invariant.** Let `Z` be
a uniform geodesic flow box at `x` (as produced by
`exists_uniform_geodesic_flow`), with radius `r`, time `ε`, rescale `T` and
data-Lipschitz constant `L`.  Suppose the limit geodesic `γ`'s chart-`x` data at
a base time `t` lies in the half-ball, and the fixed-chart invariant holds at
`t`.  Then for every `s` in the flow window `|s| < ε/T` the invariant holds at
`t + s`: the readback (`exists_uniform_flow_readback`) computes both position and
chart velocity of every admissible geodesic from the flow, and the flow depends
Lipschitz-continuously on its initial data, so data convergence at `t`
propagates to position and velocity convergence at `t + s`. -/
theorem convChartAt_propagate (g : RiemannianMetric I M) (x : M)
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγgeo : IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (hγsgeo : ∀ n, IsGeodesic (I := I) g (γs n)) (hγsc : ∀ n, Continuous (γs n))
    {r ε T : ℝ} {Z : E × E → ℝ → E × E} {L : ℝ≥0}
    (hr : 0 < r) (hε : 0 < ε) (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I x x, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g x (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I x).target ×ˢ (univ : Set E)))
    (hLip : ∀ t ∈ Icc (-ε) ε, LipschitzOnWith L (Z · t)
      (closedBall ((extChartAt I x x, (0 : E)) : E × E) r))
    (hreadback : ∀ y w : E,
      ((y, T⁻¹ • w) : E × E) ∈ closedBall ((extChartAt I x x, (0 : E)) : E × E) r →
      ∀ (σ : ℝ → M) (a : ℝ), 0 < a →
        IsGeodesicOn (I := I) g σ (Ioo (-a) a) →
        ContinuousOn σ (Ioo (-a) a) →
        σ 0 = (extChartAt I x).symm y →
        HasDerivAt (fun τ : ℝ => extChartAt I x (σ τ)) w 0 →
        ∀ s ∈ Ioo (-(min a (ε / T))) (min a (ε / T)),
          σ s = (extChartAt I x).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1) ∧
          deriv (fun τ : ℝ => extChartAt I x (σ τ)) s =
            T • (Z ((y, T⁻¹ • w) : E × E) (s * T)).2)
    {t s : ℝ} (hsrc_t : γ t ∈ (chartAt H x).source)
    (hadm : ((extChartAt I x (γ t), T⁻¹ • deriv (fun τ => extChartAt I x (γ τ)) t) : E × E)
      ∈ closedBall ((extChartAt I x x, (0 : E)) : E × E) (r / 2))
    (hswin : |s| < ε / T)
    (hconv : ConvChartAt (I := I) g x γ γs t) :
    ConvChartAt (I := I) g x γ γs (t + s) := by
  set z₀ : E × E := ((extChartAt I x x, (0 : E)) : E × E) with hz₀
  set zγ : E × E := ((extChartAt I x (γ t),
    T⁻¹ • deriv (fun τ => extChartAt I x (γ τ)) t) : E × E) with hzγ
  set zn : ℕ → E × E := fun n => ((extChartAt I x (γs n t),
    T⁻¹ • deriv (fun τ => extChartAt I x (γs n τ)) t) : E × E) with hzn
  -- the flow time `s * T` lies inside the flow-box time window `[-ε, ε]`
  have hsT_mem : s * T ∈ Icc (-ε) ε := by
    have h1 : |s| * T < ε := (lt_div_iff₀ hT).mp hswin
    have h2 : |s * T| < ε := by rw [abs_mul, abs_of_pos hT]; exact h1
    rw [mem_Icc]
    exact ⟨(abs_lt.mp h2).1.le, (abs_lt.mp h2).2.le⟩
  -- **readback for one global geodesic curve** through the flow box centred at `x`
  have rb : ∀ (c : ℝ → M), IsGeodesic (I := I) g c → Continuous c →
      ((extChartAt I x (c t),
          T⁻¹ • deriv (fun τ => extChartAt I x (c τ)) t) : E × E) ∈ closedBall z₀ r →
      c t ∈ (chartAt H x).source →
      c (t + s) = (extChartAt I x).symm ((Z ((extChartAt I x (c t),
            T⁻¹ • deriv (fun τ => extChartAt I x (c τ)) t) : E × E) (s * T)).1) ∧
        deriv (fun τ => extChartAt I x (c τ)) (t + s) =
          T • (Z ((extChartAt I x (c t),
            T⁻¹ • deriv (fun τ => extChartAt I x (c τ)) t) : E × E) (s * T)).2 := by
    intro c hcg hcc hcadm hcsrc
    have hcsrc' : c t ∈ (extChartAt I x).source := by rw [extChartAt_source]; exact hcsrc
    have hFderiv : HasDerivAt (fun τ => extChartAt I x (c τ))
        (deriv (fun τ => extChartAt I x (c τ)) t) t :=
      (hcg.hasGeodesicEquationAt t).hasDerivAt_extChartAt_deriv hcc.continuousAt hcsrc
    have ha : (0 : ℝ) < ε / T + 1 := by
      have := div_pos hε hT; linarith
    have hσgeo : IsGeodesicOn (I := I) g (fun s' => c (s' + t))
        (Ioo (-(ε / T + 1)) (ε / T + 1)) := (isGeodesic_comp_add hcg t).isGeodesicOn _
    have hσcont : ContinuousOn (fun s' => c (s' + t)) (Ioo (-(ε / T + 1)) (ε / T + 1)) :=
      (hcc.comp (continuous_add_right t)).continuousOn
    have hσ0 : (fun s' => c (s' + t)) 0 = (extChartAt I x).symm (extChartAt I x (c t)) := by
      simp only [zero_add]
      exact ((extChartAt I x).left_inv hcsrc').symm
    have hsmem : s ∈ Ioo (-(min (ε / T + 1) (ε / T))) (min (ε / T + 1) (ε / T)) := by
      rw [min_eq_right (by linarith)]
      exact ⟨(abs_lt.mp hswin).1, (abs_lt.mp hswin).2⟩
    have hres := hreadback (extChartAt I x (c t)) (deriv (fun τ => extChartAt I x (c τ)) t)
      hcadm (fun s' => c (s' + t)) (ε / T + 1) ha hσgeo hσcont hσ0
      (HasDerivAt.comp_add_const 0 t (by rw [zero_add]; exact hFderiv)) s hsmem
    -- translate the flow-window conclusions from base `s + t` to `t + s`
    have hveleq : deriv (fun τ : ℝ => extChartAt I x ((fun s' => c (s' + t)) τ)) s
        = deriv (fun τ => extChartAt I x (c τ)) (s + t) :=
      deriv_comp_add_const (fun τ => extChartAt I x (c τ)) t s
    refine ⟨?_, ?_⟩
    · rw [add_comm t s]; exact hres.1
    · rw [add_comm t s, ← hveleq]; exact hres.2
  -- **data convergence at `t`** (positions and chart-`x` velocities)
  have hyconv : Tendsto (fun n => extChartAt I x (γs n t)) atTop
      (𝓝 (extChartAt I x (γ t))) :=
    ((continuousAt_extChartAt' (by rw [extChartAt_source]; exact hsrc_t)).tendsto).comp hconv.1
  have hzconv : Tendsto zn atTop (𝓝 zγ) :=
    hyconv.prodMk_nhds (hconv.2.const_smul T⁻¹)
  -- **admissibility** of `γ`'s data, and eventually of `γs n`'s data
  have hzγr : zγ ∈ closedBall z₀ r :=
    Metric.closedBall_subset_closedBall (by linarith) hadm
  have hev_adm : ∀ᶠ n in atTop, zn n ∈ closedBall z₀ r := by
    have hdist : ∀ᶠ n in atTop, dist (zn n) zγ < r / 2 :=
      (Metric.tendsto_nhds.mp hzconv) (r / 2) (by linarith)
    filter_upwards [hdist] with n hn
    rw [mem_closedBall]
    calc dist (zn n) z₀ ≤ dist (zn n) zγ + dist zγ z₀ := dist_triangle _ _ _
      _ ≤ r / 2 + r / 2 := add_le_add hn.le (mem_closedBall.mp hadm)
      _ = r := by ring
  have hev_src : ∀ᶠ n in atTop, γs n t ∈ (chartAt H x).source :=
    hconv.1.eventually_mem ((chartAt H x).open_source.mem_nhds hsrc_t)
  -- **flow depends Lipschitz-continuously on its data** at the flow time `s * T`
  have hZconv : Tendsto (fun n => Z (zn n) (s * T)) atTop (𝓝 (Z zγ (s * T))) := by
    have hcw : ContinuousWithinAt (fun z => Z z (s * T)) (closedBall z₀ r) zγ :=
      ((hLip (s * T) hsT_mem).continuousOn).continuousWithinAt hzγr
    exact Filter.Tendsto.comp
      (show Tendsto (fun z => Z z (s * T)) (𝓝[closedBall z₀ r] zγ) (𝓝 (Z zγ (s * T))) from hcw)
      (tendsto_nhdsWithin_iff.mpr ⟨hzconv, hev_adm⟩)
  have htgt : (Z zγ (s * T)).1 ∈ (extChartAt I x).target :=
    ((hflow zγ hzγr).2.2 (s * T) hsT_mem).1
  have hfst : Tendsto (fun n => (Z (zn n) (s * T)).1) atTop (𝓝 ((Z zγ (s * T)).1)) :=
    (continuous_fst.tendsto _).comp hZconv
  have hpos_flow : Tendsto (fun n => (extChartAt I x).symm ((Z (zn n) (s * T)).1)) atTop
      (𝓝 ((extChartAt I x).symm ((Z zγ (s * T)).1))) := by
    have hca : ContinuousAt (extChartAt I x).symm ((Z zγ (s * T)).1) :=
      continuousAt_extChartAt_symm'' htgt
    exact Filter.Tendsto.comp
      (show Tendsto (extChartAt I x).symm (𝓝 ((Z zγ (s * T)).1))
          (𝓝 ((extChartAt I x).symm ((Z zγ (s * T)).1))) from hca) hfst
  have hsnd : Tendsto (fun n => (Z (zn n) (s * T)).2) atTop (𝓝 ((Z zγ (s * T)).2)) :=
    (continuous_snd.tendsto _).comp hZconv
  have hvel_flow : Tendsto (fun n => T • (Z (zn n) (s * T)).2) atTop
      (𝓝 (T • (Z zγ (s * T)).2)) :=
    hsnd.const_smul T
  -- **assemble** the invariant at `t + s`
  have rbγ := rb γ hγgeo hγc hzγr hsrc_t
  refine ⟨?_, ?_⟩
  · rw [rbγ.1]
    refine Filter.Tendsto.congr' ?_ hpos_flow
    filter_upwards [hev_adm, hev_src] with n hn hns
    exact ((rb (γs n) (hγsgeo n) (hγsc n) hn hns).1).symm
  · rw [rbγ.2]
    refine Filter.Tendsto.congr' ?_ hvel_flow
    filter_upwards [hev_adm, hev_src] with n hn hns
    exact ((rb (γs n) (hγsgeo n) (hγsc n) hn hns).2).symm

/-- **Math.** **The flow-box convergence step, discharged.** The universally
quantified form of do Carmo's `exists_conv_step`: around every base time there
is a radius on which the convergence invariant `ConvAt` propagates.  This closes
`lem:ends-exist` — every conditional theorem of `EndsExist.lean` becomes
unconditional (see `geodesicEndpointContinuity` below). -/
theorem convStepProperty (g : RiemannianMetric I M) :
    ConvStepProperty (I := I) g := by
  intro γ γs hγgeo hγc hγsgeo hγsc tstar
  set x : M := γ tstar with hxdef
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip, hzero, hmax⟩ :=
    exists_uniform_geodesic_flow (I := I) g x
  set T : ℝ := ε / 2 with hTdef
  have hT : 0 < T := half_pos hε
  have hTε : T < ε := half_lt_self hε
  have hεT : (0 : ℝ) < ε / T := div_pos hε hT
  set z₀ : E × E := ((extChartAt I x x, (0 : E)) : E × E) with hz₀
  -- readback reconstructed for this flow box (see `exists_uniform_flow_readback`)
  have hreadback : ∀ y w : E,
      ((y, T⁻¹ • w) : E × E) ∈ closedBall z₀ r →
      ∀ (σ : ℝ → M) (a : ℝ), 0 < a →
        IsGeodesicOn (I := I) g σ (Ioo (-a) a) →
        ContinuousOn σ (Ioo (-a) a) →
        σ 0 = (extChartAt I x).symm y →
        HasDerivAt (fun τ : ℝ => extChartAt I x (σ τ)) w 0 →
        ∀ s ∈ Ioo (-(min a (ε / T))) (min a (ε / T)),
          σ s = (extChartAt I x).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1) ∧
          deriv (fun τ : ℝ => extChartAt I x (σ τ)) s =
            T • (Z ((y, T⁻¹ • w) : E × E) (s * T)).2 := by
    intro y w hmem σ a ha hσgeo hσc hσ0 hσv s hs
    have hEqOn := hσgeo.eq_uniform_flow_readback hT hTε hflow hmem ha hσc hσ0 hσv
    refine ⟨hEqOn hs, ?_⟩
    obtain ⟨-, -, -, -, -, hvelJ⟩ :=
      isGeodesicOn_uniform_flow_segment_Ioo (I := I) g x hT hTε hflow hmem
    have hsub_J : Ioo (-(min a (ε / T))) (min a (ε / T)) ⊆ Ioo (-(ε / T)) (ε / T) :=
      Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
    have hev : (fun τ : ℝ => extChartAt I x (σ τ)) =ᶠ[𝓝 s]
        (fun τ : ℝ => extChartAt I x
          ((extChartAt I x).symm ((Z ((y, T⁻¹ • w) : E × E) (τ * T)).1))) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with τ hτ
      exact congrArg (extChartAt I x) (hEqOn hτ)
    rw [hev.deriv_eq]
    exact (hvelJ s (hsub_J hs)).deriv
  -- rescaling factor: slow the geodesics down so their chart velocity fits the ball
  set v : E := deriv (fun τ => extChartAt I x (γ τ)) tstar with hvdef
  set κ : ℝ := min 1 (r * T / (4 * (‖v‖ + 1))) with hκdef
  have hκpos : 0 < κ := lt_min one_pos (by positivity)
  have hκne : κ ≠ 0 := hκpos.ne'
  have hκle2 : κ ≤ r * T / (4 * (‖v‖ + 1)) := min_le_right _ _
  set c₀ : ℝ := tstar - κ * tstar with hc₀
  set γR : ℝ → M := fun σ => γ (κ * σ + c₀) with hγRdef
  set γRs : ℕ → ℝ → M := fun n σ => γs n (κ * σ + c₀) with hγRsdef
  have hγRgeo : IsGeodesic (I := I) g γR := by
    intro τ; rw [hγRdef]
    exact hasGeodesicEquationAt_comp_affine (hγgeo.hasGeodesicEquationAt (κ * τ + c₀))
  have hγRc : Continuous γR := hγc.comp (by fun_prop)
  have hγRsgeo : ∀ n, IsGeodesic (I := I) g (γRs n) := by
    intro n τ; rw [hγRsdef]
    exact hasGeodesicEquationAt_comp_affine ((hγsgeo n).hasGeodesicEquationAt (κ * τ + c₀))
  have hγRsc : ∀ n, Continuous (γRs n) := fun n => (hγsc n).comp (by fun_prop)
  have hAtstar : κ * tstar + c₀ = tstar := by rw [hc₀]; ring
  have hγRtstar : γR tstar = x := by
    show γ (κ * tstar + c₀) = x; rw [hAtstar]
  have hγRtstar_src : γR tstar ∈ (chartAt H x).source := by rw [hγRtstar]; exact mem_chart_source H x
  have hw₀ : deriv (fun τ => extChartAt I x (γR τ)) tstar = κ • v := by
    have h := deriv_comp_affine (fun σ => extChartAt I x (γ σ)) κ c₀ tstar
    rw [hAtstar] at h; rw [hvdef]; exact h
  -- `γR`'s data at `tstar` (`= dγ`), admissible with room (in the `r/4`-ball)
  set dγ : E × E := ((extChartAt I x (γR tstar),
    T⁻¹ • deriv (fun τ => extChartAt I x (γR τ)) tstar) : E × E) with hdγdef
  have hbound : T⁻¹ * (κ * ‖v‖) ≤ r / 4 := by
    have hb1 : κ * (4 * (‖v‖ + 1)) ≤ r * T := (le_div_iff₀ (by positivity)).mp hκle2
    have hb2 : κ * ‖v‖ ≤ r / 4 * T := by nlinarith [hb1, hκpos.le, norm_nonneg v]
    have h3 := mul_le_mul_of_nonneg_left hb2 (by positivity : (0 : ℝ) ≤ T⁻¹)
    rwa [show T⁻¹ * (r / 4 * T) = r / 4 from by field_simp] at h3
  have hdγ_r4 : dγ ∈ closedBall z₀ (r / 4) := by
    rw [hdγdef, hz₀, hγRtstar, hw₀, mem_closedBall, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    rw [max_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [norm_smul, norm_smul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hT, abs_of_pos hκpos]
    exact hbound
  have hdγ_r : dγ ∈ closedBall z₀ r :=
    Metric.closedBall_subset_closedBall (by linarith) hdγ_r4
  -- readback of `γR` about `tstar`
  have hσc_geo : IsGeodesicOn (I := I) g (fun s' => γR (s' + tstar)) (Ioo (-(ε / T + 1)) (ε / T + 1)) :=
    (isGeodesic_comp_add hγRgeo tstar).isGeodesicOn _
  have hσc_cont : ContinuousOn (fun s' => γR (s' + tstar)) (Ioo (-(ε / T + 1)) (ε / T + 1)) :=
    (hγRc.comp (continuous_add_right tstar)).continuousOn
  have hσc_0 : (fun s' => γR (s' + tstar)) 0 = (extChartAt I x).symm (extChartAt I x (γR tstar)) := by
    simp only [zero_add]
    exact ((extChartAt I x).left_inv (by rw [extChartAt_source]; exact hγRtstar_src)).symm
  have hσc_deriv : HasDerivAt (fun τ : ℝ => extChartAt I x ((fun s' => γR (s' + tstar)) τ))
      (deriv (fun τ => extChartAt I x (γR τ)) tstar) 0 := by
    have hde : HasDerivAt (fun τ => extChartAt I x (γR τ))
        (deriv (fun τ => extChartAt I x (γR τ)) tstar) tstar :=
      (hγRgeo.hasGeodesicEquationAt tstar).hasDerivAt_extChartAt_deriv hγRc.continuousAt hγRtstar_src
    exact HasDerivAt.comp_add_const 0 tstar (by rw [zero_add]; exact hde)
  have ha1 : (0 : ℝ) < ε / T + 1 := by linarith
  have hrb_all := hreadback (extChartAt I x (γR tstar))
    (deriv (fun τ => extChartAt I x (γR τ)) tstar) hdγ_r
    (fun s' => γR (s' + tstar)) (ε / T + 1) ha1 hσc_geo hσc_cont hσc_0 hσc_deriv
  have hmin : min (ε / T + 1) (ε / T) = ε / T := min_eq_right (by linarith)
  -- the base data at time `s' + tstar` equals the flow point `Z dγ (s'*T)`
  have hD_eq : ∀ s' : ℝ, |s'| < ε / T →
      ((extChartAt I x (γR (s' + tstar)),
        T⁻¹ • deriv (fun τ => extChartAt I x (γR τ)) (s' + tstar)) : E × E) = Z dγ (s' * T) := by
    intro s' hs'
    have hmem' : s' ∈ Ioo (-(min (ε / T + 1) (ε / T))) (min (ε / T + 1) (ε / T)) := by
      rw [hmin]; exact ⟨(abs_lt.mp hs').1, (abs_lt.mp hs').2⟩
    obtain ⟨hpos_id, hvel_id⟩ := hrb_all s' hmem'
    rw [← hdγdef] at hpos_id hvel_id
    have hpos_id' : γR (s' + tstar) = (extChartAt I x).symm ((Z dγ (s' * T)).1) := hpos_id
    have hsT_mem : s' * T ∈ Icc (-ε) ε := by
      have h1 : |s'| * T < ε := (lt_div_iff₀ hT).mp hs'
      have h2 : |s' * T| < ε := by rw [abs_mul, abs_of_pos hT]; exact h1
      rw [mem_Icc]; exact ⟨(abs_lt.mp h2).1.le, (abs_lt.mp h2).2.le⟩
    have htgt : (Z dγ (s' * T)).1 ∈ (extChartAt I x).target :=
      ((hflow dγ hdγ_r).2.2 (s' * T) hsT_mem).1
    have hveleq : deriv (fun τ : ℝ => extChartAt I x ((fun s'' => γR (s'' + tstar)) τ)) s'
        = deriv (fun τ => extChartAt I x (γR τ)) (s' + tstar) :=
      deriv_comp_add_const (fun τ => extChartAt I x (γR τ)) tstar s'
    rw [hveleq] at hvel_id
    have ha : extChartAt I x (γR (s' + tstar)) = (Z dγ (s' * T)).1 := by
      rw [hpos_id', (extChartAt I x).right_inv htgt]
    have hb : T⁻¹ • deriv (fun τ => extChartAt I x (γR τ)) (s' + tstar) = (Z dγ (s' * T)).2 := by
      rw [hvel_id, inv_smul_smul₀ hT.ne']
    rw [ha, hb]
  -- `Z dγ` is continuous in time, so the base data stays admissible near `tstar`
  have hZcontOn : ContinuousOn (Z dγ) (Icc (-ε) ε) := fun t' ht' =>
    ((hflow dγ hdγ_r).2.1 t' ht').continuousWithinAt
  have hZ0 : Z dγ 0 = dγ := (hflow dγ hdγ_r).1
  have htend : Tendsto (fun s' => Z dγ (s' * T)) (𝓝 0) (𝓝 (Z dγ 0)) := by
    have h1 : Tendsto (Z dγ) (𝓝 0) (𝓝 (Z dγ 0)) :=
      hZcontOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
    have h2 : Tendsto (fun s' : ℝ => s' * T) (𝓝 0) (𝓝 0) := by
      have := (continuous_mul_right T).tendsto (0 : ℝ); simpa using this
    exact h1.comp h2
  have hnbhd : closedBall z₀ (r / 2) ∈ 𝓝 (Z dγ 0) := by
    rw [hZ0]
    refine mem_of_superset (Metric.ball_mem_nhds dγ (by linarith : (0 : ℝ) < r / 4)) ?_
    intro w hw
    rw [mem_ball] at hw; rw [mem_closedBall]
    calc dist w z₀ ≤ dist w dγ + dist dγ z₀ := dist_triangle _ _ _
      _ ≤ r / 4 + r / 4 := add_le_add hw.le (mem_closedBall.mp hdγ_r4)
      _ ≤ r / 2 := by linarith
  have hev_ball : ∀ᶠ s' in 𝓝 (0 : ℝ), Z dγ (s' * T) ∈ closedBall z₀ (r / 2) :=
    htend.eventually_mem hnbhd
  have hev_win : ∀ᶠ s' in 𝓝 (0 : ℝ), |s'| < ε / T := by
    have : Ioo (-(ε / T)) (ε / T) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hεT
    filter_upwards [this] with s' hs'; exact abs_lt.mpr hs'
  have hnhds : ∀ᶠ s' in 𝓝 (0 : ℝ),
      ((extChartAt I x (γR (s' + tstar)),
        T⁻¹ • deriv (fun τ => extChartAt I x (γR τ)) (s' + tstar)) : E × E)
        ∈ closedBall z₀ (r / 2)
      ∧ γR (s' + tstar) ∈ (chartAt H x).source := by
    filter_upwards [hev_ball, hev_win] with s' hb hw
    refine ⟨?_, ?_⟩
    · rw [hD_eq s' hw]; exact hb
    · -- `γR(s'+tstar)` lies in a chart source (its chart position is honest)
      have hmem' : s' ∈ Ioo (-(min (ε / T + 1) (ε / T))) (min (ε / T + 1) (ε / T)) := by
        rw [hmin]; exact ⟨(abs_lt.mp hw).1, (abs_lt.mp hw).2⟩
      have hpos_id := (hrb_all s' hmem').1
      rw [← hdγdef] at hpos_id
      have hpos_id' : γR (s' + tstar) = (extChartAt I x).symm ((Z dγ (s' * T)).1) := hpos_id
      have hsT_mem : s' * T ∈ Icc (-ε) ε := by
        have h1 : |s'| * T < ε := (lt_div_iff₀ hT).mp hw
        have h2 : |s' * T| < ε := by rw [abs_mul, abs_of_pos hT]; exact h1
        rw [mem_Icc]; exact ⟨(abs_lt.mp h2).1.le, (abs_lt.mp h2).2.le⟩
      have htgt : (Z dγ (s' * T)).1 ∈ (extChartAt I x).target :=
        ((hflow dγ hdγ_r).2.2 (s' * T) hsT_mem).1
      rw [hpos_id', ← extChartAt_source (I := I) x]
      exact (extChartAt I x).map_target htgt
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.eventually_nhds_iff.mp hnhds
  set δ : ℝ := min δ₀ (ε / (2 * T)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (by positivity)
  have hδlt : δ < ε / T := by
    have hd : δ ≤ ε / (2 * T) := min_le_right _ _
    have hlt : ε / (2 * T) < ε / T := by
      rw [show ε / (2 * T) = (ε / T) / 2 from by rw [mul_comm, ← div_div]]
      exact half_lt_self hεT
    linarith
  -- the step radius
  refine ⟨κ * (δ / 2), by positivity, ?_⟩
  intro t u ht hu hconvt
  set σt : ℝ := tstar + (t - tstar) / κ with hσtdef
  set σu : ℝ := tstar + (u - tstar) / κ with hσudef
  have hAσt : κ * σt + c₀ = t := by rw [hσtdef, hc₀]; field_simp; ring
  have hAσu : κ * σu + c₀ = u := by rw [hσudef, hc₀]; field_simp; ring
  have hσt_near : |σt - tstar| < δ := by
    rw [hσtdef]; simp only [add_sub_cancel_left, abs_div, abs_of_pos hκpos]
    rw [div_lt_iff₀ hκpos]
    have : |t - tstar| ≤ κ * (δ / 2) := ht
    calc |t - tstar| ≤ κ * (δ / 2) := ht
      _ < δ * κ := by nlinarith [hδpos, hκpos]
  have hσu_near : |σu - tstar| < δ := by
    rw [hσudef]; simp only [add_sub_cancel_left, abs_div, abs_of_pos hκpos]
    rw [div_lt_iff₀ hκpos]
    calc |u - tstar| ≤ κ * (δ / 2) := hu
      _ < δ * κ := by nlinarith [hδpos, hκpos]
  -- admissibility + source at the base `σt`, and the window bound
  have hPt := hδ₀ (show dist (σt - tstar) 0 < δ₀ by
    rw [Real.dist_eq, sub_zero]; exact lt_of_lt_of_le hσt_near (min_le_left _ _))
  have hsrc_σt : γR σt ∈ (chartAt H x).source := by
    have := hPt.2
    rwa [show (σt - tstar) + tstar = σt from by ring] at this
  have hadm_σt : ((extChartAt I x (γR σt),
      T⁻¹ • deriv (fun τ => extChartAt I x (γR τ)) σt) : E × E) ∈ closedBall z₀ (r / 2) := by
    have := hPt.1
    rwa [show (σt - tstar) + tstar = σt from by ring] at this
  have hwin_σ : |σu - σt| < ε / T := by
    have h1 : |σu - σt| ≤ |σu - tstar| + |σt - tstar| := by
      have := abs_sub_le σu tstar σt
      rwa [abs_sub_comm tstar σt] at this
    have h2δ : δ + δ ≤ ε / T := by
      have hd : δ ≤ ε / (2 * T) := min_le_right _ _
      have heq : ε / (2 * T) = ε / T / 2 := by rw [mul_comm, ← div_div]
      rw [heq] at hd; linarith
    linarith
  -- transport `ConvAt(γ,γs,t)` to `ConvChartAt(x,γR,γRs,σt)`, propagate to `σu`, transport back
  have hcc_t : ConvChartAt (I := I) g x γR γRs σt := by
    rw [← convAt_iff_convChartAt g hγRgeo hγRc hγRsgeo hγRsc hsrc_σt]
    have := (convAt_comp_affine g (γ := γ) (γs := γs) (κ := κ) (c := c₀) hκne (s := σt)).mpr
    rw [hγRdef, hγRsdef]
    exact this (by rw [hAσt]; exact hconvt)
  have hcc_u : ConvChartAt (I := I) g x γR γRs σu := by
    have hprop := convChartAt_propagate g x hγRgeo hγRc hγRsgeo hγRsc hr hε hT hTε
      hflow hLip hreadback (t := σt) (s := σu - σt) hsrc_σt hadm_σt hwin_σ hcc_t
    rwa [show σt + (σu - σt) = σu from by ring] at hprop
  have hca_u : ConvAt (I := I) g γR γRs σu :=
    (convAt_iff_convChartAt g hγRgeo hγRc hγRsgeo hγRsc
      (show γR σu ∈ (chartAt H x).source by
        have := (hδ₀ (show dist (σu - tstar) 0 < δ₀ by
          rw [Real.dist_eq, sub_zero]; exact lt_of_lt_of_le hσu_near (min_le_left _ _))).2
        rwa [show (σu - tstar) + tstar = σu from by ring] at this)).mpr hcc_u
  have := (convAt_comp_affine g (γ := γ) (γs := γs) (κ := κ) (c := c₀) hκne (s := σu)).mp
  rw [hγRdef, hγRsdef] at hca_u
  have hfin := this hca_u
  rwa [hAσu] at hfin

/-- **Math.** **Endpoint continuity, unconditional.** Combining
`geodesicEndpointContinuity_of_convStep` with the discharged step
`convStepProperty`. -/
theorem geodesicEndpointContinuity (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) (p : M) :
    GeodesicEndpointContinuity (I := I) g p :=
  geodesicEndpointContinuity_of_convStep g hg p (convStepProperty g)

/-- **Math.** A complete Riemannian manifold (metrized by the Riemannian distance
of `g`) is a **proper** metric space — unconditionally, the endpoint-continuity
hypothesis now being discharged by `geodesicEndpointContinuity`. -/
theorem properSpace_of_complete' (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) : ProperSpace M :=
  properSpace_of_complete g hg p (geodesicEndpointContinuity g hg p)

/-- **Math.** Blueprint `lem:ends-exist` (ray half), **unconditional**: a
complete, connected, non-compact Riemannian manifold has a unit-speed minimizing
geodesic ray emanating from any point `p`. -/
theorem exists_isGeodesicRay_of_complete_noncompact' (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] [ConnectedSpace M] [NoncompactSpace M]
    (p : M) : ∃ γ : ℝ → M, IsGeodesicRay γ ∧ γ 0 = p :=
  exists_isGeodesicRay_of_complete_noncompact g hg p (geodesicEndpointContinuity g hg p)

/-- **Math.** Blueprint `lem:ends-exist` (line half), **unconditional**: a
complete, connected Riemannian manifold with two distinct ends contains a
unit-speed minimizing geodesic line. -/
theorem exists_isMinGeodesicOn_univ_of_complete_ends_ne' (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] [ConnectedSpace M]
    (p : M) {e₁ e₂ : SpaceOfEnds M} (hne : e₁ ≠ e₂) :
    ∃ γ : ℝ → M, IsMinGeodesicOn γ Set.univ :=
  exists_isMinGeodesicOn_univ_of_complete_ends_ne g hg p (geodesicEndpointContinuity g hg p) hne

end PoincareLib

end
