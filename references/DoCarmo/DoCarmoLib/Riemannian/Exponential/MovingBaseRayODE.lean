import DoCarmoLib.Riemannian.Geodesic.FlowC2Dependence
import DoCarmoLib.Riemannian.Geodesic.FlowHomogeneity

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

/-!
# The geodesic ODE along rays at a moving base (do Carmo Ch. 3, §2–3)

`RayODE.lean` packages, at the *fixed* base `p`, the analytic input the Gauss lemma
needs: the chart reading `f = φ_p ∘ exp_p` is `C²` on a ball, `(df)₀ = id`, and each
ray velocity solves the chart-`p` geodesic equation. Its ray-reparametrization step
(`key`) descends the coordinate spray trajectory to a `maximalGeodesic` witness
**anchored at the chart centre `φ_p p`**, so it cannot be reused at a *moving* base
point `q ≠ p`.

For the base-uniform Gauss estimate (`Exponential/MovingBaseGauss.lean`, the lower-bound
crux `Hlb` of `prop:dc-ch3-4-2`) one needs the same package for the *flow reading*
`f_y : w ↦ (Z (y, T⁻¹ • w) T)₁` of the coordinate geodesic spray flow `Z` through a
**free base point** `y = φ_p q ∈ (extChartAt I p).target`, with no manifold descent
available. This file supplies the two base-free linchpins that replace the manifold
route:

* `geodesicFlow_eqOn_of_zero_velocity` — the **zero-velocity equilibrium**: the spray
  trajectory `Z (y, 0)` from any admissible base is *constant* at `(y, 0)` (the spray
  vanishes on the zero section, `geodesicSprayCoord_zero_velocity`). This gives
  `f_y 0 = y` and pins the reference point for the confinement estimate;
* `geodesicFlow_fst_fibre_time_movingBase` — the **ray reparametrization**
  `(Z (y, a • v) T)₁ = (Z (y, v) (a * T))₁` for small base offset and velocity, obtained
  by confining both the `a•v`-trajectory and the fibre-time-rescaled `v`-trajectory to a
  common Lipschitz region around `z₀` (via the flow's initial-condition Lipschitz clause
  and the equilibrium) and invoking the coordinate homogeneity
  `sprayCoord_fst_fibre_time` of `FlowHomogeneity.lean`. This is the exact replacement of
  `RayODE`'s `key` at a moving base.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian
namespace Exponential

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The zero-velocity trajectory of the coordinate geodesic spray is
constant.** Let `Z` be a local flow of the coordinate spray at `p` (the raw clauses of
`exists_uniform_geodesic_flow`: `Z z 0 = z`, the spray ODE on `Icc (-ε) ε`, trajectories
in the chart region). For any admissible base `(y, 0)` (with `y ∈ (extChartAt I p).target`)
the trajectory `Z (y, 0)` stays at `(y, 0)` throughout the open window `Ioo (-ε) ε`: the
spray vanishes on the zero section, so the constant curve solves the same ODE, and
local Grönwall uniqueness plus connectedness of the interval force agreement. -/
theorem geodesicFlow_eqOn_of_zero_velocity (g : RiemannianMetric I M) (p : M)
    {Z : E × E → ℝ → E × E} {r ε : ℝ} (hε : 0 < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {y : E} (hy : ((y, (0 : E)) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r) :
    ∀ t ∈ Ioo (-ε) ε, Z ((y, (0 : E)) : E × E) t = ((y, (0 : E)) : E × E) := by
  classical
  set x₀ : E × E := ((y, (0 : E)) : E × E) with hx₀def
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g p ζ.1 ζ.2 with hFdef
  obtain ⟨h0, hd, hmem⟩ := hflow x₀ hy
  -- `(y, 0)` lies in the open chart region, where the spray is `C¹`
  have hx₀Ω : x₀ ∈ (extChartAt I p).target ×ˢ (univ : Set E) := by
    have := hmem 0 ⟨by linarith [hε], hε.le⟩
    rwa [h0] at this
  have hFc1 : ContDiffAt ℝ 1 F x₀ := by
    have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
      (isOpen_extChartAt_target p).prod isOpen_univ
    exact ((contDiffOn_geodesicSprayCoord_prod (I := I) g p).contDiffAt
      (hopen.mem_nhds hx₀Ω)).of_le (by norm_num)
  obtain ⟨K, sLip, hsLip, hlip⟩ := hFc1.exists_lipschitzOnWith
  have hx₀sLip : x₀ ∈ sLip := mem_of_mem_nhds hsLip
  -- the spray vanishes at `x₀`, so the constant curve solves the ODE
  have hFx₀ : F x₀ = 0 := by
    rw [hFdef]; simp only [hx₀def]
    exact geodesicSprayCoord_zero_velocity (I := I) g p y
  -- the trajectory solves the ODE (as a full derivative) on the open window
  have hZd : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (Z x₀) (F (Z x₀ t)) t := fun t ht =>
    (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hcontZ : ContinuousOn (Z x₀) (Ioo (-ε) ε) := fun t ht =>
    ((hZd t ht).continuousAt).continuousWithinAt
  -- the agreement set and its window-local openness via Grönwall uniqueness
  set S : Set ℝ := {t : ℝ | Z x₀ t = x₀} with hSdef
  have h0S : (0 : ℝ) ∈ S := by rw [hSdef, mem_setOf_eq, h0]
  have hSlocal : ∀ t ∈ Ioo (-ε) ε, t ∈ S →
      ∀ᶠ s in 𝓝 t, s ∈ Ioo (-ε) ε ∧ Z x₀ s = x₀ := by
    intro t ht htS
    have hZt : Z x₀ t = x₀ := htS
    have hsLip' : sLip ∈ 𝓝 (Z x₀ t) := by rw [hZt]; exact hsLip
    have hmemsLip : ∀ᶠ s in 𝓝 t, Z x₀ s ∈ sLip :=
      ((hZd t ht).continuousAt).eventually_mem hsLip'
    obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      (hmemsLip.and (isOpen_Ioo.mem_nhds ht))
    set δ : ℝ := δ₀ / 2 with hδdef
    have hδpos : 0 < δ := by positivity
    have hsubIcc : Icc (t - δ) (t + δ) ⊆ Ioo (-ε) ε := by
      intro s hs
      have hsball : s ∈ Metric.ball t δ₀ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
        exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
      exact (hball s hsball).2
    have hsball' : ∀ s ∈ Ioo (t - δ) (t + δ), s ∈ Metric.ball t δ₀ := by
      intro s hs
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have htIoo : t ∈ Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
    have heqOn : EqOn (Z x₀) (fun _ => x₀) (Icc (t - δ) (t + δ)) := by
      refine ODE_solution_unique_of_mem_Icc (v := fun _ => F) (s := fun _ => sLip)
        (fun s _ => hlip) htIoo
        (fun s hs => ((hZd s (hsubIcc hs)).continuousAt).continuousWithinAt)
        (fun s hs => hZd s (hsubIcc (Ioo_subset_Icc_self hs)))
        (fun s hs => (hball s (hsball' s hs)).1)
        (continuousOn_const)
        (fun s _ => by simpa [hFx₀] using hasDerivAt_const s x₀)
        (fun s _ => hx₀sLip)
        hZt
    filter_upwards [isOpen_Ioo.mem_nhds htIoo] with s hs
    exact ⟨hsubIcc (Ioo_subset_Icc_self hs), heqOn (Ioo_subset_Icc_self hs)⟩
  -- `S ∩ Ioo` is open in `ℝ`
  have hSIooOpen : IsOpen (S ∩ Ioo (-ε) ε) := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    filter_upwards [hSlocal t ht.2 ht.1] with s hs
    exact ⟨hs.2, hs.1⟩
  -- transfer the clopen argument to the connected subspace `Ioo (-ε) ε`
  set J : Set ℝ := Ioo (-ε) ε with hJdef
  haveI : PreconnectedSpace J :=
    (Subtype.preconnectedSpace (isPreconnected_Ioo (a := -ε) (b := ε)))
  set Tset : Set J := {t : J | Z x₀ (t : ℝ) = x₀} with hTsetdef
  have hTopen : IsOpen Tset := by
    have : Tset = Subtype.val ⁻¹' (S ∩ Ioo (-ε) ε) := by
      ext t
      simp only [hTsetdef, mem_setOf_eq, mem_preimage, mem_inter_iff, hSdef]
      exact ⟨fun h => ⟨h, t.2⟩, fun h => h.1⟩
    rw [this]
    exact hSIooOpen.preimage continuous_subtype_val
  have hTclosed : IsClosed Tset := by
    have hcont : Continuous fun t : J => Z x₀ (t : ℝ) :=
      hcontZ.comp_continuous continuous_subtype_val (fun t => t.2)
    have : Tset = (fun t : J => Z x₀ (t : ℝ)) ⁻¹' {x₀} := rfl
    rw [this]
    exact isClosed_singleton.preimage hcont
  have hTne : Tset.Nonempty :=
    ⟨⟨0, ⟨neg_lt_zero.mpr hε, hε⟩⟩, h0S⟩
  have hTuniv : Tset = univ := (IsClopen.eq_univ ⟨hTclosed, hTopen⟩ hTne)
  intro t ht
  have : (⟨t, ht⟩ : J) ∈ Tset := by rw [hTuniv]; trivial
  exact this

/-- **Math.** **Base-free ray reparametrization of the coordinate geodesic spray flow.**
Let `Z` be a local flow of the coordinate spray at `p` with the raw clauses of
`exists_uniform_geodesic_flow` (base value, spray ODE, chart membership) and the
initial-condition Lipschitz clause `hLip` on the flow ball. Then there are thresholds
`η, ρv > 0` and a window bound `b > 1` such that for every base point `y` within `η` of the
chart centre and every velocity `v` with `‖v‖ < ρv`, the horizontal component of the spray
flow obeys the fibre–time homogeneity

`(Z (y, a • v) T).1 = (Z (y, v) (a * T)).1`   for all `|a| < b`.

This is do Carmo's `γ(t, q, a v) = γ(a t, q, v)` (Lemma 2.6) read in the fixed chart at `p`
through a **moving base** `q = φ_p⁻¹ y`, and is the exact replacement of `RayODE`'s manifold
descent `key`. The proof confines both the `a•v`-trajectory and the fibre-time-rescaled
`v`-trajectory to a spray-Lipschitz ball around `z₀` — using the flow Lipschitz clause and
the zero-velocity equilibrium `geodesicFlow_eqOn_of_zero_velocity` as the reference point —
and then invokes the coordinate homogeneity `sprayCoord_fst_fibre_time`. -/
theorem geodesicFlow_fst_fibre_time_movingBase (g : RiemannianMetric I M) (p : M)
    {Z : E × E → ℝ → E × E} {r ε T : ℝ} {L : ℝ≥0} (hr : 0 < r) (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    (hLip : ∀ t ∈ Icc (-ε) ε, LipschitzOnWith L (Z · t)
      (closedBall ((extChartAt I p p, (0 : E)) : E × E) r)) :
    ∃ η ρv b : ℝ, 0 < η ∧ 0 < ρv ∧ 1 < b ∧
      ∀ (y v : E), dist y (extChartAt I p p) < η → ‖v‖ < ρv →
        ∀ a : ℝ, |a| < b →
          (Z ((y, a • v) : E × E) T).1 = (Z ((y, v) : E × E) (a * T)).1 := by
  classical
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g p ζ.1 ζ.2 with hFdef
  have hεpos : 0 < ε := hT.trans hTε
  -- the spray is `C¹` at the zero section, hence Lipschitz on a ball around `z₀`
  obtain ⟨K, sLip, hsLip, hlip⟩ :=
    (contDiffAt_geodesicSprayCoord_zero (I := I) g p).exists_lipschitzOnWith
  obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.mem_nhds_iff.mp hsLip
  -- the window bound `b ∈ (1, ε/T)` and the time window radius `d ∈ (T, ε/b)`
  set b : ℝ := (1 + ε / T) / 2 with hbdef
  have hεT1 : 1 < ε / T := (one_lt_div hT).mpr hTε
  have hb1 : 1 < b := by rw [hbdef]; linarith
  have hbpos : 0 < b := lt_trans one_pos hb1
  have hbεT : b < ε / T := by rw [hbdef]; linarith
  have hTεb : T < ε / b := by
    rw [lt_div_iff₀ hbpos, mul_comm]
    exact (lt_div_iff₀ hT).mp hbεT
  set d : ℝ := (T + ε / b) / 2 with hddef
  have hdpos : 0 < d := by rw [hddef]; have := hTεb; positivity
  have hdT : T < d := by rw [hddef]; linarith
  have hdεb : d < ε / b := by rw [hddef]; linarith
  have hbd_lt : b * d < ε := by
    have hstep : b * d < b * (ε / b) :=
      mul_lt_mul_of_pos_left hdεb hbpos
    rwa [mul_div_cancel₀ _ hbpos.ne'] at hstep
  have hεbε : ε / b ≤ ε := by rw [div_le_iff₀ hbpos]; nlinarith [hεpos, hb1]
  have hdε : d < ε := lt_of_lt_of_le hdεb hεbε
  have hIoodε : Ioo (-d) d ⊆ Ioo (-ε) ε :=
    Ioo_subset_Ioo (neg_le_neg hdε.le) hdε.le
  -- the smallness thresholds
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  set η : ℝ := min r (ρ' / 2) with hηdef
  have hηpos : 0 < η := lt_min hr (by positivity)
  have hηr : η ≤ r := min_le_left _ _
  have hηρ2 : η ≤ ρ' / 2 := min_le_right _ _
  have hden : 0 < 2 * (b * (L : ℝ) + 1) := by positivity
  set ρv : ℝ := min (r / b) (ρ' / (2 * (b * (L : ℝ) + 1))) with hρvdef
  have hρvpos : 0 < ρv := lt_min (by positivity) (by positivity)
  have hρvrb : ρv ≤ r / b := min_le_left _ _
  have hbLρv : b * (L : ℝ) * ρv ≤ ρ' / 2 := by
    have hstep : b * (L : ℝ) * (ρ' / (2 * (b * (L : ℝ) + 1))) ≤ ρ' / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith [hρ'pos, hLnn, hbpos.le, mul_nonneg hbpos.le hLnn]
    exact le_trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)) hstep
  refine ⟨η, ρv, b, hηpos, hρvpos, hb1, ?_⟩
  intro y v hy hv a ha
  have hyd : dist y (extChartAt I p p) < η := hy
  -- initial-condition memberships in the flow ball
  have hdy0 : dist ((y, (0 : E)) : E × E) z₀ = dist y (extChartAt I p p) := by
    rw [hz₀def, Prod.dist_eq]; simp only [dist_self]; exact max_eq_left dist_nonneg
  have hy0mem : ((y, (0 : E)) : E × E) ∈ closedBall z₀ r := by
    rw [mem_closedBall, hdy0]; exact le_trans hyd.le hηr
  have havmem : ((y, a • v) : E × E) ∈ closedBall z₀ r := by
    rw [mem_closedBall, hz₀def, Prod.dist_eq]
    refine max_le (le_trans hyd.le hηr) ?_
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc |a| * ‖v‖ ≤ b * ρv :=
          mul_le_mul ha.le hv.le (norm_nonneg v) hbpos.le
      _ ≤ b * (r / b) := mul_le_mul_of_nonneg_left hρvrb hbpos.le
      _ = r := by rw [mul_div_cancel₀ _ hbpos.ne']
  have hvmem : ((y, v) : E × E) ∈ closedBall z₀ r := by
    rw [mem_closedBall, hz₀def, Prod.dist_eq]
    refine max_le (le_trans hyd.le hηr) ?_
    rw [dist_zero_right]
    calc ‖v‖ ≤ ρv := hv.le
      _ ≤ r / b := hρvrb
      _ ≤ r := by rw [div_le_iff₀ hbpos]; nlinarith [hr, hb1]
  -- the zero-velocity equilibrium at base `y`
  have hequil : ∀ t ∈ Ioo (-ε) ε, Z ((y, (0 : E)) : E × E) t = ((y, (0 : E)) : E × E) :=
    geodesicFlow_eqOn_of_zero_velocity (I := I) g p hεpos hflow hy0mem
  -- confinement of a trajectory `Z (y, w)` towards the equilibrium `(y, 0)`
  have hconf : ∀ (w : E) (t : ℝ), ((y, w) : E × E) ∈ closedBall z₀ r → t ∈ Ioo (-ε) ε →
      dist (Z ((y, w) : E × E) t) ((y, (0 : E)) : E × E) ≤ (L : ℝ) * ‖w‖ := by
    intro w t hwmem ht
    have h1 := (hLip t (Ioo_subset_Icc_self ht)).dist_le_mul _ hwmem _ hy0mem
    rw [hequil t ht] at h1
    refine le_trans h1 (le_of_eq ?_)
    rw [Prod.dist_eq]; simp only [dist_self, dist_zero_right]
    rw [max_eq_right (norm_nonneg w)]
  -- rescaled times stay in the ODE window
  have haτ : ∀ τ ∈ Ioo (-d) d, a * τ ∈ Ioo (-ε) ε := by
    intro τ hτ
    rw [mem_Ioo, ← abs_lt]
    calc |a * τ| = |a| * |τ| := abs_mul a τ
      _ < b * d := by
          apply mul_lt_mul' ha.le (abs_lt.mpr ⟨by linarith [hτ.1], hτ.2⟩) (abs_nonneg τ) hbpos
      _ < ε := hbd_lt
  -- distance from `z₀` to `(y, 0)` is strictly small
  have hdy0small : dist ((y, (0 : E)) : E × E) z₀ < ρ' / 2 := by
    rw [hdy0]; exact lt_of_lt_of_le hyd hηρ2
  -- the `a • v` velocity contributes at most `ρ'/2` after the flow-Lipschitz bound
  have hav : (L : ℝ) * ‖a • v‖ ≤ ρ' / 2 := by
    rw [norm_smul, Real.norm_eq_abs, ← mul_assoc, mul_comm (L : ℝ) |a|, mul_assoc]
    calc |a| * ((L : ℝ) * ‖v‖) ≤ b * ((L : ℝ) * ρv) :=
          mul_le_mul ha.le
            (mul_le_mul_of_nonneg_left hv.le hLnn) (by positivity) hbpos.le
      _ = b * (L : ℝ) * ρv := by ring
      _ ≤ ρ' / 2 := hbLρv
  -- the `a • v`-trajectory lands in `sLip`
  have hαmem : ∀ τ ∈ Ioo (-d) d, Z ((y, a • v) : E × E) τ ∈ sLip := by
    intro τ hτ
    apply hρ'sub; rw [mem_ball]
    have hc := hconf (a • v) τ havmem (hIoodε hτ)
    calc dist (Z ((y, a • v) : E × E) τ) z₀
        ≤ dist (Z ((y, a • v) : E × E) τ) ((y, (0:E)):E×E)
            + dist ((y, (0:E)):E×E) z₀ := dist_triangle _ _ _
      _ ≤ (L : ℝ) * ‖a • v‖ + dist ((y, (0:E)):E×E) z₀ := add_le_add hc le_rfl
      _ < ρ' / 2 + ρ' / 2 := add_lt_add_of_le_of_lt hav hdy0small
      _ = ρ' := by ring
  -- the fibre-time-rescaled `v`-trajectory `ζ` lands in `sLip`
  have hζmem : ∀ τ ∈ Ioo (-d) d,
      (((Z ((y, v) : E × E) (a * τ)).1, a • (Z ((y, v) : E × E) (a * τ)).2) : E × E)
        ∈ sLip := by
    intro τ hτ
    apply hρ'sub; rw [mem_ball]
    have hc := hconf v (a * τ) hvmem (haτ τ hτ)
    set Zc := Z ((y, v) : E × E) (a * τ) with hZcdef
    have hprod : dist Zc ((y, (0:E)):E×E) = max (dist Zc.1 y) (dist Zc.2 0) :=
      Prod.dist_eq (x := Zc) (y := ((y, (0:E)):E×E))
    have h1le : dist Zc.1 y ≤ (L : ℝ) * ‖v‖ :=
      le_trans (le_trans (le_max_left _ _) (le_of_eq hprod.symm)) hc
    have h2le : ‖Zc.2‖ ≤ (L : ℝ) * ‖v‖ := by
      rw [← dist_zero_right]
      exact le_trans (le_trans (le_max_right _ _) (le_of_eq hprod.symm)) hc
    -- `ζ(τ)` is close to the equilibrium `(y,0)`
    have hζdist : dist ((Zc.1, a • Zc.2) : E × E) ((y, (0:E)):E×E) ≤ b * (L : ℝ) * ‖v‖ := by
      rw [Prod.dist_eq]
      refine max_le (le_trans h1le ?_) ?_
      · rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) hb1.le
      · rw [dist_zero_right, norm_smul, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul ha.le h2le (norm_nonneg _) hbpos.le
    have hζsmall : b * (L : ℝ) * ‖v‖ ≤ ρ' / 2 :=
      le_trans (mul_le_mul_of_nonneg_left hv.le (by positivity)) hbLρv
    calc dist ((Zc.1, a • Zc.2) : E × E) z₀
        ≤ dist ((Zc.1, a • Zc.2) : E × E) ((y, (0:E)):E×E)
            + dist ((y, (0:E)):E×E) z₀ := dist_triangle _ _ _
      _ < ρ' / 2 + ρ' / 2 := add_lt_add_of_le_of_lt (le_trans hζdist hζsmall) hdy0small
      _ = ρ' := by ring
  -- the ODE clauses for both trajectories
  have hαode : ∀ τ ∈ Ioo (-d) d,
      HasDerivAt (Z ((y, a • v) : E × E))
        (geodesicSprayCoord (I := I) g p (Z ((y, a • v) : E × E) τ).1
          (Z ((y, a • v) : E × E) τ).2) τ ∧ Z ((y, a • v) : E × E) τ ∈ sLip := by
    intro τ hτ
    have hτε : τ ∈ Ioo (-ε) ε := hIoodε hτ
    exact ⟨((hflow _ havmem).2.1 τ (Ioo_subset_Icc_self hτε)).hasDerivAt
      (Icc_mem_nhds hτε.1 hτε.2), hαmem τ hτ⟩
  have hZcode : ∀ τ ∈ Ioo (-d) d,
      HasDerivAt (Z ((y, v) : E × E))
        (geodesicSprayCoord (I := I) g p (Z ((y, v) : E × E) (a * τ)).1
          (Z ((y, v) : E × E) (a * τ)).2) (a * τ) := by
    intro τ hτ
    have haτε : a * τ ∈ Ioo (-ε) ε := haτ τ hτ
    exact ((hflow _ hvmem).2.1 (a * τ) (Ioo_subset_Icc_self haτε)).hasDerivAt
      (Icc_mem_nhds haτε.1 haτε.2)
  -- the initial-value match `Z(y,a•v) 0 = ((Z(y,v) 0).1, a • (Z(y,v) 0).2)`
  have h0match : Z ((y, a • v) : E × E) 0
      = (((Z ((y, v) : E × E) 0).1, a • (Z ((y, v) : E × E) 0).2) : E × E) := by
    rw [(hflow _ havmem).1, (hflow _ hvmem).1]
  -- apply the coordinate homogeneity
  have hTIoo : T ∈ Ioo (-d) d := ⟨by linarith [hdpos, hT], hdT⟩
  exact sprayCoord_fst_fibre_time (I := I) g p a hlip
    (neg_lt_zero.mpr hdpos) hdpos hαode hZcode hζmem h0match hTIoo

set_option linter.unusedVariables false in
/-- **Math.** **The moving-base flow reading of `exp` is `C²` on a ball.** For a local
geodesic-spray flow family `σ` at `p` (the curve-valued form of the flow) whose
initial-condition dependence is `C²` — i.e. `σ` is strictly Fréchet differentiable with
derivative computed by the variational flow `τ` (`hC1τ`), and `τ` is itself strictly
differentiable (`hC2τ`), the two second-order flow-dependence clauses of
`exists_uniform_geodesic_flow_hasStrictFDerivAt_opFlow` — the chart reading
`w ↦ (σ (y, T⁻¹ • w) at time T).1` of the exponential map through any base point `y`
within `r` of the chart centre is `C²` on the ball `‖w‖ < r · T`. This is the
base-uniform second-order regularity input (`hC2`) of the Gauss lemma, the moving-base
analogue of `exists_contDiffOn_two_extChartAt_expMap_ball`. The derivative at `w` is the
fixed continuous-linear image `Φ (τ (y, T⁻¹ • w))` of the variational flow, and strict
differentiability of `τ` makes that derivative map `C¹`, i.e. the reading `C²`. -/
theorem contDiffOn_two_movingBase_flowReading (g : RiemannianMetric I M) (p : M)
    {r T : ℝ}
    {σ : E × E → C(Set.Icc (0 : ℝ) T, E × E)}
    {τ : E × E → C(Set.Icc (0 : ℝ) T, (E × E) →L[ℝ] (E × E))}
    (hT : 0 < T)
    (hC1τ : ∀ x₀ ∈ ball ((extChartAt I p p, (0 : E)) : E × E) r,
      ∃ D : E × E →L[ℝ] C(Set.Icc (0 : ℝ) T, E × E),
        (∀ v : E × E, D v = postcomp (ContinuousLinearMap.apply ℝ (E × E) v) (τ x₀)) ∧
        HasStrictFDerivAt σ D x₀)
    (hC2τ : ∀ x₀ ∈ ball ((extChartAt I p p, (0 : E)) : E × E) r,
      ∃ Dτ : E × E →L[ℝ] C(Set.Icc (0 : ℝ) T, (E × E) →L[ℝ] (E × E)),
        HasStrictFDerivAt τ Dτ x₀)
    {y : E} (hy : dist y (extChartAt I p p) < r) :
    ContDiffOn ℝ 2
      (fun w : E => (σ ((y, T⁻¹ • w) : E × E) ⟨T, ⟨hT.le, le_rfl⟩⟩).1) (ball (0 : E) (r * T)) := by
  classical
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set tT : Set.Icc (0 : ℝ) T := ⟨T, ⟨hT.le, le_rfl⟩⟩ with htTdef
  set ρ : ℝ := r * T with hρdef
  -- the affine reparametrization `w ↦ (y, w/T)` and its (base-independent) derivative
  set ι : E → E × E := fun w => (y, T⁻¹ • w) with hιdef
  set Dι : E →L[ℝ] E × E :=
    (0 : E →L[ℝ] E).prod (T⁻¹ • ContinuousLinearMap.id ℝ E) with hDιdef
  have hι : ∀ w₀ : E, HasStrictFDerivAt ι Dι w₀ := fun w₀ =>
    (hasStrictFDerivAt_const _ _).prodMk
      (T⁻¹ • ContinuousLinearMap.id ℝ E).hasStrictFDerivAt
  have hxmem : ∀ w₀ : E, ‖w₀‖ < ρ → ι w₀ ∈ ball z₀ r := by
    intro w₀ hw₀
    rw [hιdef, mem_ball, hz₀def, Prod.dist_eq]
    refine max_lt hy ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le, inv_mul_lt_iff₀ hT]
    rw [mul_comm]; rwa [hρdef] at hw₀
  -- the fixed evaluation functional: evaluate at time `T`, project, precompose with `Dι`
  set Φ : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ] (E →L[ℝ] E) :=
    ((((ContinuousLinearMap.compL ℝ E (E × E) E).flip Dι).comp
      (ContinuousLinearMap.compL ℝ (E × E) (E × E) E
        (ContinuousLinearMap.fst ℝ E E))).comp
      (ContinuousMap.evalCLM ℝ tT)) with hΦdef
  -- the reading is strictly differentiable at every point of the ball
  have hstricte : ∀ w₀ : E, ‖w₀‖ < ρ →
      HasStrictFDerivAt (fun w : E => (σ (ι w) tT).1) (Φ (τ (ι w₀))) w₀ := by
    intro w₀ hw₀
    obtain ⟨D, hDτ, hstrict⟩ := hC1τ (ι w₀) (hxmem w₀ hw₀)
    have heval : HasStrictFDerivAt (fun z => σ z tT)
        ((ContinuousMap.evalCLM ℝ tT).comp D) (ι w₀) :=
      (ContinuousMap.evalCLM ℝ tT).hasStrictFDerivAt.comp (ι w₀) hstrict
    have hfstσ : HasStrictFDerivAt (fun z => (σ z tT).1)
        ((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)) (ι w₀) :=
      (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.comp (ι w₀) heval
    have hcomp : HasStrictFDerivAt (fun w => (σ (ι w) tT).1)
        (((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι) w₀ :=
      hfstσ.comp w₀ (hι w₀)
    have hDid : ((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι = Φ (τ (ι w₀)) := by
      refine ContinuousLinearMap.ext fun v => ?_
      show ((D (Dι v)) tT).1 = _
      rw [hDτ (Dι v)]; rfl
    rw [hDid] at hcomp
    exact hcomp
  -- the derivative family `w ↦ Φ (τ (ι w))` is itself strictly differentiable
  have hstrictd : ∀ w₀ ∈ ball (0 : E) ρ,
      HasStrictFDerivAt (fun w : E => Φ (τ (ι w)))
        (fderiv ℝ (fun w : E => Φ (τ (ι w))) w₀) w₀ := by
    intro w₀ hw₀
    obtain ⟨Dτ, hDτs⟩ := hC2τ (ι w₀) (hxmem w₀ (mem_ball_zero_iff.mp hw₀))
    have h : HasStrictFDerivAt (fun w : E => Φ (τ (ι w)))
        ((Φ.comp Dτ).comp Dι) w₀ :=
      (Φ.hasStrictFDerivAt.comp (ι w₀) hDτs).comp w₀ (hι w₀)
    rw [h.hasFDerivAt.fderiv]; exact h
  -- assemble `C²` on the open ball via `C¹` of the derivative map
  have h2eq : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2eq, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
  refine ⟨fun w hw => ((hstricte w
    (mem_ball_zero_iff.mp hw)).differentiableAt).differentiableWithinAt,
    fun h => by simp at h, ?_⟩
  have hfeq : ∀ w ∈ ball (0 : E) ρ,
      fderiv ℝ (fun w : E => (σ (ι w) tT).1) w = Φ (τ (ι w)) := fun w hw =>
    (hstricte w (mem_ball_zero_iff.mp hw)).hasFDerivAt.fderiv
  exact (contDiffOn_one_of_forall_hasStrictFDerivAt isOpen_ball hstrictd).congr hfeq

end Exponential
end Riemannian
