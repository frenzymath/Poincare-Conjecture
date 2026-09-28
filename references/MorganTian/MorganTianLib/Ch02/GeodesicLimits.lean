import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Int.Interval
import MorganTianLib.Ch02.Busemann

/-!
# Poincaré Ch. 2, §2.1 — Limits of minimizing geodesics (metric version)

The metric-space core of Morgan–Tian's "limits of minimizing geodesics" arguments
(blueprint `lem:metric-limit-of-minimizing`, the metric backbone of
`lem:limit-of-minimizing-geodesics` and `lem:ends-exist`): in a proper metric space, a
sequence of unit-speed minimizing geodesics `σ k` defined on windows `In k` exhausting a
window `I`, whose values at `0` stay in a fixed compact set, subconverges — uniformly on
compact subsets of `I` — to a unit-speed minimizing geodesic defined on all of `I`.

## Main declarations

* `IsMinGeodesicOn γ I`: `γ` is a **unit-speed minimizing geodesic on `I`**, in the metric
  sense `dist (γ s) (γ t) = |s - t|` for `s, t ∈ I` (values outside `I` are junk).
  For `I = Set.Ici 0` this is exactly `IsGeodesicRay` (`isGeodesicRay_iff_isMinGeodesicOn`);
  for `I = Set.univ` it is a minimizing geodesic line.
* `HasMinSegments M`: any two points of `M` are joined by a unit-speed minimizing segment.
  In a complete Riemannian manifold this holds by `lem:minimizing-segment-exists`
  (Hopf–Rinow); we take it as a hypothesis at the metric level.
* `exists_isMinGeodesicOn_hyperfilter_limit`: the compactness core — pointwise limits along
  the hyperfilter (a fixed non-principal ultrafilter on `ℕ`) exist by properness and are
  again minimizing on `I`.
* `exists_isMinGeodesicOn_tendstoLocallyUniformlyOn`: the subsequence form matching the
  blueprint statement — some subsequence `σ ∘ φ` converges uniformly on compact subsets of
  `I` to a minimizing geodesic `γ` on `I` (blueprint `lem:metric-limit-of-minimizing`).
* `exists_isGeodesicRay_of_noncompact`: a noncompact proper space with minimizing segments
  has a minimizing geodesic ray from every point — the ray half of blueprint
  `lem:ends-exist`.

## Design notes

* The limit geodesic is *constructed* by taking limits along `Filter.hyperfilter ℕ`: for
  each time `t ∈ I` the points `σ k t` eventually lie in a fixed closed ball (properness),
  so the ultrafilter limit exists; minimality passes to the limit because `dist` is
  continuous and each identity `dist (σ k s) (σ k t) = |s - t|` holds eventually. The
  uniform-on-compacts subsequence is then extracted against the limit on the finite grids
  `(1/(n+1))ℤ ∩ [-n, n] ∩ I`, using that all the maps involved are `1`-Lipschitz on their
  windows; this is where `OrdConnected` of the windows (they are intervals containing `0`)
  is used, to round times toward `0` without leaving any window.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.1.
-/

open Filter Topology Metric Set

namespace MorganTianLib

variable {M : Type*} [MetricSpace M]

/-! ## Minimizing geodesics on a window -/

/-- `γ` is a **unit-speed minimizing geodesic on `I`**: `dist (γ s) (γ t) = |s - t|` for all
`s, t ∈ I`. Values of `γ` outside `I` are irrelevant junk. Taking `I = Set.Icc a b` gives
minimizing segments, `I = Set.Ici 0` minimizing rays (= `IsGeodesicRay`), and `I = Set.univ`
minimizing lines. -/
def IsMinGeodesicOn (γ : ℝ → M) (I : Set ℝ) : Prop :=
  ∀ ⦃s⦄, s ∈ I → ∀ ⦃t⦄, t ∈ I → dist (γ s) (γ t) = |s - t|

/-- A minimizing geodesic on `I` is minimizing on any subwindow. -/
theorem IsMinGeodesicOn.mono {γ : ℝ → M} {I J : Set ℝ} (h : IsMinGeodesicOn γ I)
    (hJI : J ⊆ I) : IsMinGeodesicOn γ J :=
  fun _ hs _ ht => h (hJI hs) (hJI ht)

/-- `IsGeodesicRay` is exactly `IsMinGeodesicOn` on the window `[0, ∞)`. -/
theorem isGeodesicRay_iff_isMinGeodesicOn {γ : ℝ → M} :
    IsGeodesicRay γ ↔ IsMinGeodesicOn γ (Set.Ici 0) :=
  Iff.rfl

/-- A unit-speed minimizing geodesic is `1`-Lipschitz on its window. -/
theorem IsMinGeodesicOn.lipschitzOnWith {γ : ℝ → M} {I : Set ℝ} (h : IsMinGeodesicOn γ I) :
    LipschitzOnWith 1 γ I :=
  LipschitzOnWith.of_dist_le_mul fun s hs t ht => by
    rw [h hs ht, NNReal.coe_one, one_mul, Real.dist_eq]

/-- A unit-speed minimizing geodesic is continuous on its window. -/
theorem IsMinGeodesicOn.continuousOn {γ : ℝ → M} {I : Set ℝ} (h : IsMinGeodesicOn γ I) :
    ContinuousOn γ I :=
  h.lipschitzOnWith.continuousOn

/-- Reparameterizing a minimizing geodesic by an arclength translation. -/
theorem IsMinGeodesicOn.comp_add_right {γ : ℝ → M} {I : Set ℝ} (h : IsMinGeodesicOn γ I)
    (c : ℝ) : IsMinGeodesicOn (fun t => γ (t + c)) ((· + c) ⁻¹' I) := by
  intro s hs t ht
  have := h hs ht
  rwa [add_sub_add_right_eq_sub] at this

/-- **Existence of minimizing segments**: any two points `x, y` are joined by a unit-speed
minimizing geodesic segment `σ : [0, d(x,y)] → M` from `x` to `y`. This is the metric-space
abstraction of blueprint `lem:minimizing-segment-exists`, which provides it for complete
Riemannian manifolds via Hopf–Rinow. -/
def HasMinSegments (M : Type*) [MetricSpace M] : Prop :=
  ∀ x y : M, ∃ σ : ℝ → M,
    σ 0 = x ∧ σ (dist x y) = y ∧ IsMinGeodesicOn σ (Set.Icc 0 (dist x y))

/-! ## The compactness core: limits along the hyperfilter -/

/-- **Limits of minimizing geodesics, ultrafilter form.** Let `M` be proper, let
`σ k` be unit-speed minimizing geodesics on windows `In k` containing `0`, whose window
eventually contains any given point of `I`, and whose anchor points `σ k 0` all lie in a
compact set `K`. Then the pointwise limits of the `σ k` along the hyperfilter exist and
define a unit-speed minimizing geodesic on `I` anchored in `K`. -/
theorem exists_isMinGeodesicOn_hyperfilter_limit [ProperSpace M]
    {I : Set ℝ} (h0I : (0 : ℝ) ∈ I)
    {In : ℕ → Set ℝ} {σ : ℕ → ℝ → M}
    (hσ : ∀ k, IsMinGeodesicOn (σ k) (In k)) (h0In : ∀ k, (0 : ℝ) ∈ In k)
    (hexh : ∀ t ∈ I, ∀ᶠ k in atTop, t ∈ In k)
    {K : Set M} (hK : IsCompact K) (hanchor : ∀ k, σ k 0 ∈ K) :
    ∃ γ : ℝ → M, IsMinGeodesicOn γ I ∧ γ 0 ∈ K ∧
      ∀ t ∈ I, Tendsto (fun k => σ k t) (hyperfilter ℕ : Filter ℕ) (𝓝 (γ t)) := by
  classical
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (σ 0 0)
  -- for each `t ∈ I`, the points `σ k t` eventually lie in a fixed closed ball
  have hball : ∀ t ∈ I, ∀ᶠ k in (hyperfilter ℕ : Filter ℕ),
      σ k t ∈ closedBall (σ 0 0) (R + |t|) := by
    intro t ht
    filter_upwards [(hexh t ht).filter_mono Nat.hyperfilter_le_atTop] with k hk
    have h1 : dist (σ k t) (σ k 0) = |t| := by
      have := hσ k hk (h0In k)
      rwa [sub_zero] at this
    have h2 : dist (σ k 0) (σ 0 0) ≤ R := hR (hanchor k)
    have h3 := dist_triangle (σ k t) (σ k 0) (σ 0 0)
    rw [mem_closedBall]
    linarith
  -- ultrafilter limits exist by properness
  have hlim : ∀ t : ℝ, ∃ a : M,
      t ∈ I → Tendsto (fun k => σ k t) (hyperfilter ℕ : Filter ℕ) (𝓝 a) := by
    intro t
    by_cases ht : t ∈ I
    · have hmem : closedBall (σ 0 0) (R + |t|) ∈
          (hyperfilter ℕ).map fun k => σ k t := by
        exact hball t ht
      obtain ⟨a, -, ha⟩ := (isCompact_closedBall (σ 0 0) (R + |t|)).ultrafilter_le_nhds' _ hmem
      rw [Ultrafilter.coe_map] at ha
      exact ⟨a, fun _ => ha⟩
    · exact ⟨σ 0 0, fun h => absurd h ht⟩
  choose γ hγ using hlim
  refine ⟨γ, ?_, ?_, fun t ht => hγ t ht⟩
  · -- minimality passes to the ultrafilter limit
    intro s hs t ht
    have h1 : Tendsto (fun k => dist (σ k s) (σ k t)) (hyperfilter ℕ : Filter ℕ)
        (𝓝 (dist (γ s) (γ t))) := (hγ s hs).dist (hγ t ht)
    have h2 : (fun k => dist (σ k s) (σ k t)) =ᶠ[(hyperfilter ℕ : Filter ℕ)]
        fun _ => |s - t| := by
      filter_upwards [(hexh s hs).filter_mono Nat.hyperfilter_le_atTop,
        (hexh t ht).filter_mono Nat.hyperfilter_le_atTop] with k hks hkt
      exact hσ k hks hkt
    exact tendsto_nhds_unique (h1.congr' h2) tendsto_const_nhds
  · exact hK.isClosed.mem_of_tendsto (hγ 0 h0I) (Eventually.of_forall hanchor)

/-! ## The subsequence form: uniform convergence on compact subsets -/

/-- A property holding on a hyperfilter set holds frequently at infinity (hyperfilter sets
are infinite, since the hyperfilter extends the cofinite filter). -/
private theorem frequently_atTop_of_hyperfilter {p : ℕ → Prop}
    (h : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), p k) : ∃ᶠ k in atTop, p k := by
  rw [← Nat.cofinite_eq_atTop]
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨k, h1, h2⟩ := (h.and (hcon.filter_mono hyperfilter_le_cofinite)).exists
  exact h2 h1

/-- **Limits of minimizing geodesics, metric version** (blueprint
`lem:metric-limit-of-minimizing`). Let `M` be a proper metric space, let `I` be a closed
interval (in the `OrdConnected` sense) containing `0`, and for each `k` let `σ k` be a
unit-speed minimizing geodesic on an interval window `In k ∋ 0`, such that every point of
`I` eventually belongs to `In k`, and such that all anchor points `σ k 0` lie in a fixed
compact set `K`. Then there are a unit-speed minimizing geodesic `γ : I → M` anchored in
`K` and a subsequence of the `σ k` converging to `γ` uniformly on compact subsets of `I`. -/
theorem exists_isMinGeodesicOn_tendstoLocallyUniformlyOn [ProperSpace M]
    {I : Set ℝ} (hIc : IsClosed I) (hIo : I.OrdConnected) (h0I : (0 : ℝ) ∈ I)
    {In : ℕ → Set ℝ} {σ : ℕ → ℝ → M}
    (hσ : ∀ k, IsMinGeodesicOn (σ k) (In k))
    (hIno : ∀ k, (In k).OrdConnected) (h0In : ∀ k, (0 : ℝ) ∈ In k)
    (hexh : ∀ t ∈ I, ∀ᶠ k in atTop, t ∈ In k)
    {K : Set M} (hK : IsCompact K) (hanchor : ∀ k, σ k 0 ∈ K) :
    ∃ γ : ℝ → M, IsMinGeodesicOn γ I ∧ γ 0 ∈ K ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun n => σ (φ n)) γ atTop I := by
  classical
  obtain ⟨γ, hγgeo, hγ0, hγlim⟩ :=
    exists_isMinGeodesicOn_hyperfilter_limit h0I hσ h0In hexh hK hanchor
  -- each compact window of `I` is eventually contained in `In k`
  have hwin : ∀ n : ℕ, ∀ᶠ k in atTop, I ∩ Icc (-(n : ℝ)) n ⊆ In k := by
    intro n
    rcases (I ∩ Icc (-(n : ℝ)) n).eq_empty_or_nonempty with he | hne
    · filter_upwards with k
      rw [he]
      exact empty_subset _
    · have hcpt : IsCompact (I ∩ Icc (-(n : ℝ)) n) := isCompact_Icc.inter_left hIc
      have hinf := hcpt.sInf_mem hne
      have hsup := hcpt.sSup_mem hne
      filter_upwards [hexh _ hinf.1, hexh _ hsup.1] with k hik hsk
      intro t ht
      exact (hIno k).out hik hsk ⟨csInf_le hcpt.bddBelow ht, le_csSup hcpt.bddAbove ht⟩
  -- convergence on the finite grid of scale `1/(n+1)` inside `[-n, n] ∩ I`,
  -- eventually along the hyperfilter
  have hgrid : ∀ n : ℕ, ∀ᶠ k in (hyperfilter ℕ : Filter ℕ),
      ∀ j ∈ Finset.Icc (-((n : ℤ) * ((n : ℤ) + 1))) ((n : ℤ) * ((n : ℤ) + 1)),
        ∀ _ : ((j : ℝ) / ((n : ℝ) + 1)) ∈ I,
          dist (σ k ((j : ℝ) / ((n : ℝ) + 1))) (γ ((j : ℝ) / ((n : ℝ) + 1)))
            < 1 / ((n : ℝ) + 1) := by
    intro n
    rw [eventually_all_finset]
    intro j _
    by_cases hj : ((j : ℝ) / ((n : ℝ) + 1)) ∈ I
    · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      filter_upwards [(hγlim _ hj).eventually_mem (ball_mem_nhds _ hpos)] with k hk
      exact fun _ => mem_ball.mp hk
    · filter_upwards with k h
      exact absurd h hj
  -- the stage-`n` properties hold on a hyperfilter set, hence frequently in `atTop`
  have hPfreq : ∀ n : ℕ, ∃ᶠ k in atTop,
      (I ∩ Icc (-(n : ℝ)) n ⊆ In k) ∧
      ∀ j ∈ Finset.Icc (-((n : ℤ) * ((n : ℤ) + 1))) ((n : ℤ) * ((n : ℤ) + 1)),
        ∀ _ : ((j : ℝ) / ((n : ℝ) + 1)) ∈ I,
          dist (σ k ((j : ℝ) / ((n : ℝ) + 1))) (γ ((j : ℝ) / ((n : ℝ) + 1)))
            < 1 / ((n : ℝ) + 1) := fun n =>
    frequently_atTop_of_hyperfilter
      (((hwin n).filter_mono Nat.hyperfilter_le_atTop).and (hgrid n))
  obtain ⟨φ, hφmono, hφP⟩ := extraction_forall_of_frequently hPfreq
  refine ⟨γ, hγgeo, hγ0, φ, hφmono, ?_⟩
  -- uniform convergence near each point of `I`, by rounding times to the grid
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  refine ⟨I ∩ ball x 1, inter_mem_nhdsWithin I (ball_mem_nhds x one_pos), ?_⟩
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (|x| + 1)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (3 / ε)
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with n hn
  obtain ⟨Pwin, Pgrid⟩ := hφP n
  intro y hy
  have hyI : y ∈ I := hy.1
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hyb : |y| ≤ (n : ℝ) := by
    have h1 : |y - x| < 1 := by
      have := mem_ball.mp hy.2
      rwa [Real.dist_eq] at this
    have h2 : |y| ≤ |x| + 1 := by
      have := abs_sub_abs_le_abs_sub y x
      linarith
    have h3 : (N₁ : ℝ) ≤ (n : ℝ) :=
      Nat.cast_le.mpr ((le_max_left _ _).trans hn)
    linarith
  -- round `y` toward `0` to a grid point `q ∈ I`
  have key : ∃ q : ℝ, q ∈ I ∧ |q| ≤ |y| ∧ |y - q| ≤ 1 / ((n : ℝ) + 1) ∧
      dist (σ (φ n) q) (γ q) < 1 / ((n : ℝ) + 1) := by
    rcases le_or_gt 0 y with hy0 | hy0
    · -- `y ≥ 0`: round down
      set j : ℤ := ⌊y * ((n : ℝ) + 1)⌋ with hj
      set q : ℝ := (j : ℝ) / ((n : ℝ) + 1) with hqdef
      have hj0 : 0 ≤ j := Int.floor_nonneg.mpr (by positivity)
      have hq0 : 0 ≤ q := div_nonneg (by exact_mod_cast hj0) hnpos.le
      have hqy : q ≤ y := by
        rw [hqdef, div_le_iff₀ hnpos]
        exact Int.floor_le _
      have hyq : y - q < 1 / ((n : ℝ) + 1) := by
        have h1 : y * ((n : ℝ) + 1) < (j : ℝ) + 1 := Int.lt_floor_add_one _
        have h2 : y < ((j : ℝ) + 1) / ((n : ℝ) + 1) := by
          rw [lt_div_iff₀ hnpos]
          exact h1
        rw [add_div] at h2
        rw [hqdef]
        linarith
      have hqI : q ∈ I := hIo.out h0I hyI ⟨hq0, hqy⟩
      have hjmem : j ∈ Finset.Icc (-((n : ℤ) * ((n : ℤ) + 1))) ((n : ℤ) * ((n : ℤ) + 1)) := by
        rw [Finset.mem_Icc]
        constructor
        · exact le_trans (neg_nonpos.mpr (by positivity)) hj0
        · have h1 : (j : ℝ) ≤ y * ((n : ℝ) + 1) := Int.floor_le _
          have h2 : y * ((n : ℝ) + 1) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
            have : y ≤ (n : ℝ) := (le_abs_self y).trans hyb
            nlinarith
          exact_mod_cast h1.trans h2
      refine ⟨q, hqI, ?_, ?_, Pgrid j hjmem hqI⟩
      · rw [abs_of_nonneg hq0, abs_of_nonneg hy0]
        exact hqy
      · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - q)]
        exact hyq.le
    · -- `y < 0`: round up
      set j : ℤ := ⌈y * ((n : ℝ) + 1)⌉ with hj
      set q : ℝ := (j : ℝ) / ((n : ℝ) + 1) with hqdef
      have hj0 : j ≤ 0 := Int.ceil_le.mpr (by push_cast; nlinarith)
      have hq0 : q ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hj0) hnpos.le
      have hyq : y ≤ q := by
        rw [hqdef, le_div_iff₀ hnpos]
        exact Int.le_ceil _
      have hqy : q - y < 1 / ((n : ℝ) + 1) := by
        have h1 : (j : ℝ) < y * ((n : ℝ) + 1) + 1 := Int.ceil_lt_add_one _
        have h2 : q < (y * ((n : ℝ) + 1) + 1) / ((n : ℝ) + 1) := by
          rw [hqdef, div_lt_div_iff_of_pos_right hnpos]
          exact h1
        have h3 : (y * ((n : ℝ) + 1) + 1) / ((n : ℝ) + 1) = y + 1 / ((n : ℝ) + 1) := by
          field_simp
        rw [h3] at h2
        linarith
      have hqI : q ∈ I := hIo.out hyI h0I ⟨hyq, hq0⟩
      have hjmem : j ∈ Finset.Icc (-((n : ℤ) * ((n : ℤ) + 1))) ((n : ℤ) * ((n : ℤ) + 1)) := by
        rw [Finset.mem_Icc]
        constructor
        · have h1 : y * ((n : ℝ) + 1) ≤ (j : ℝ) := Int.le_ceil _
          have h2 : -((n : ℝ) * ((n : ℝ) + 1)) ≤ y * ((n : ℝ) + 1) := by
            have : -(n : ℝ) ≤ y := (neg_le_of_abs_le hyb)
            nlinarith
          exact_mod_cast h2.trans h1
        · exact hj0.trans (by positivity)
      refine ⟨q, hqI, ?_, ?_, Pgrid j hjmem hqI⟩
      · rw [abs_of_nonpos hq0, abs_of_nonpos hy0.le]
        linarith
      · rw [abs_of_nonpos (by linarith : y - q ≤ 0)]
        linarith
  obtain ⟨q, hqI, hqa, hyqd, hqσ⟩ := key
  -- both `y` and `q` lie in the window of `σ (φ n)`
  have hywin : y ∈ In (φ n) := Pwin ⟨hyI, abs_le.mp hyb⟩
  have hqwin : q ∈ In (φ n) := Pwin ⟨hqI, abs_le.mp (hqa.trans hyb)⟩
  -- the three-term estimate
  have e1 : dist (γ y) (γ q) = |y - q| := hγgeo hyI hqI
  have e2 : dist (σ (φ n) q) (σ (φ n) y) = |q - y| := hσ (φ n) hqwin hywin
  have tri : dist (γ y) (σ (φ n) y) ≤
      dist (γ y) (γ q) + dist (γ q) (σ (φ n) q) + dist (σ (φ n) q) (σ (φ n) y) :=
    dist_triangle4 _ _ _ _
  have hqγ : dist (γ q) (σ (φ n) q) < 1 / ((n : ℝ) + 1) := by
    rw [dist_comm]
    exact hqσ
  have habs : |q - y| = |y - q| := abs_sub_comm q y
  -- conclude: the total error is `< 3/(n+1) < ε`
  have hεn : 3 / ((n : ℝ) + 1) < ε := by
    have h1 : (3 : ℝ) / ε ≤ (N₂ : ℝ) := hN₂
    have h2 : (N₂ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr ((le_max_right _ _).trans hn)
    rw [div_lt_iff₀ hnpos]
    have h3 : (3 : ℝ) / ε < (n : ℝ) + 1 := by linarith
    calc (3 : ℝ) = 3 / ε * ε := by field_simp
      _ < ((n : ℝ) + 1) * ε := by
          exact mul_lt_mul_of_pos_right h3 hε
      _ = ε * ((n : ℝ) + 1) := mul_comm _ _
  calc dist (γ y) (σ (φ n) y)
      ≤ dist (γ y) (γ q) + dist (γ q) (σ (φ n) q) + dist (σ (φ n) q) (σ (φ n) y) := tri
    _ = |y - q| + dist (γ q) (σ (φ n) q) + |y - q| := by rw [e1, e2, habs]
    _ < 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
        have := hyqd
        linarith [hqγ]
    _ = 3 / ((n : ℝ) + 1) := by ring
    _ < ε := hεn

/-! ## Existence of rays -/

/-- **Noncompact proper spaces have rays** (the ray half of blueprint `lem:ends-exist`,
metric version): if `M` is a noncompact proper metric space in which any two points are
joined by a minimizing segment, then every point of `M` is the origin of a unit-speed
minimizing geodesic ray. -/
theorem exists_isGeodesicRay_of_noncompact [ProperSpace M] [NoncompactSpace M]
    (hseg : HasMinSegments M) (p : M) :
    ∃ γ : ℝ → M, IsGeodesicRay γ ∧ γ 0 = p := by
  classical
  -- `M` is unbounded
  have hunb : ∀ R : ℝ, ∃ q : M, R ≤ dist p q := by
    intro R
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set M) ⊆ closedBall p R := fun q _ => by
      rw [mem_closedBall, dist_comm]
      exact (h q).le
    exact NoncompactSpace.noncompact_univ (X := M)
      ((isCompact_closedBall p R).of_isClosed_subset isClosed_univ hsub)
  choose q hq using hunb
  choose σ hσ0 hσd hσgeo using fun k : ℕ => hseg p (q k)
  -- exhaustion: any `t ≥ 0` lies in `[0, d(p, q k)]` for all large `k`
  have hexh : ∀ t ∈ Set.Ici (0 : ℝ), ∀ᶠ k in atTop,
      t ∈ Set.Icc 0 (dist p (q (k : ℕ))) := by
    intro t ht
    filter_upwards [eventually_ge_atTop ⌈t⌉₊] with k hk
    refine Set.mem_Icc.mpr ⟨ht, ?_⟩
    calc t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
      _ ≤ (k : ℝ) := Nat.cast_le.mpr hk
      _ ≤ dist p (q (k : ℕ)) := hq _
  have hanch : ∀ k : ℕ, σ k 0 ∈ ({p} : Set M) := by
    intro k
    rw [hσ0 k]
    exact Set.mem_singleton p
  obtain ⟨γ, hγgeo, hγ0, -⟩ := exists_isMinGeodesicOn_hyperfilter_limit
    Set.self_mem_Ici hσgeo
    (fun k => Set.mem_Icc.mpr ⟨le_refl 0, dist_nonneg⟩) hexh
    isCompact_singleton hanch
  exact ⟨γ, isGeodesicRay_iff_isMinGeodesicOn.mpr hγgeo, hγ0⟩

end MorganTianLib
