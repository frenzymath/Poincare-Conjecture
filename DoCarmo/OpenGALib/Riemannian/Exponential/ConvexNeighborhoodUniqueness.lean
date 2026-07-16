import OpenGALib.Riemannian.Exponential.MovingBaseProp36LowerBound

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Convex neighborhoods: the base-uniform geodesic-uniqueness engine (do Carmo Ch. 3, §4)

This file supplies the *injectivity half* of the local-uniqueness hypothesis `Huniq` of do Carmo's
Proposition 4.2 (`exists_stronglyConvex_closedBall_of_uniq` in `ConvexNeighborhoodProp42.lean`).

The `Hlb` lower bound is already discharged (`exists_movingBase_prop36_lower_bound`).  What remains
for `Huniq` is: two minimizing geodesics near `p` joining the same pair of points coincide.  do
Carmo derives this from the injectivity of `exp_{q₁}` on a normal ball, uniformly in the base `q₁`.
The totally-normal `C¹` diffeomorphism `exists_totallyNormal_c1_diffeo` already packages that
base-uniform injectivity (the pair map `G(q, w) = (q, exp_q w)` is `InjOn`, with a *unique* velocity
parameter `w` in the `δ`-ball realizing each endpoint pair).

The two results here are:

* `movingBase_geodesic_eqOn_flow_reading` — the `EqOn` upgrade of
  `movingBase_geodesic_endpoint_eq_flow_reading`: a geodesic `γ` on an open window `(lo, hi) ∋ 0`
  with initial chart-`p` velocity `w` *coincides* with the flow-reading geodesic `gw_w` on the
  overlap window `(lo, hi) ∩ (-(ε/T), ε/T)` (not merely at the endpoint `1`).  This is the intrinsic
  uniqueness `hEq` already proved inside the endpoint version, exposed as a reusable lemma and
  freed of the `1 < hi` restriction.

* `exists_movingBase_geodesic_uniqueness` — the base-uniform uniqueness *engine*: there are radii
  `β, ρw > 0` such that any two geodesics `γ₁, γ₂` on open windows `⊋ [0,1]`, joining the same pair
  `q₁, q₂ ∈ closedBall p β`, with initial chart-`p` velocities `w₁, w₂` of norm `< ρw`, coincide on
  `[0,1]`.  Proof: each `γᵢ` equals its flow reading `gw_{wᵢ}` on a window `⊇ [0,1]` (via
  `movingBase_geodesic_eqOn_flow_reading`), so `gw_{wᵢ}(1) = q₂`; the diffeomorphism's *unique-`w`*
  clause forces `w₁ = w₂`, hence `gw_{w₁} = gw_{w₂}`, hence `γ₁ = γ₂` on `[0,1]`.

The residual for the *fully abstract* `Huniq` (a bare minimizing geodesic on `Icc 0 1`, with neither
an open window nor velocity data) is now only the *presentation*: equip such a geodesic with an open
time window `⊋ [0,1]`, its chart-`p` velocity `w` at `0`, and the bound `‖w‖ < ρw`, then apply the
engine.  The endpoint values `α 0 = q₁`, `α 1 = q₂` are *known* (not Cauchy limits), so a
completeness-free local prolongation of `α` past each endpoint by the geodesic flow at that known
point supplies the window — this is strictly easier than the base-uniform normal-radius wall `Hlb`
faced, and in particular does *not* need the radial reach `t₁ = 1`.  The velocity bound follows from
the conserved speed `= d(q₁, q₂) ≤ 2β` via the base-uniform chart-Gram comparison.  See `I-0213`.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal ENNReal

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M')]

/-- **Math.** **A moving-base geodesic coincides with its flow reading on the overlap window**
(do Carmo Ch. 3, Prop. 3.7 / definition of `exp`, base-uniform).  Let `Z` be the geodesic-spray flow
of `exists_totallyNormal_c1_diffeo`.  A continuous intrinsic geodesic `γ` on an open window
`(lo, hi) ∋ 0` whose foot `γ 0 = q₁` lies in the chart at `p` and whose chart-`p` coordinate velocity
at `0` is `w` *coincides* with the flow-reading geodesic `s ↦ φ_p⁻¹((Z(φ_p q₁, T⁻¹ • w)(sT))₁)` on the
overlap window `(lo, hi) ∩ (-(εF/T), εF/T)`.  This is the intrinsic-uniqueness identification
(`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) at the shared initial position and chart-`p` velocity,
exposed as `EqOn` (rather than the single-point `γ 1 = …` of
`movingBase_geodesic_endpoint_eq_flow_reading`) and requiring only `lo < 0 < hi`. -/
theorem movingBase_geodesic_eqOn_flow_reading
    (g : RiemannianMetric I M') (p : M') {lo hi T rF εF : ℝ} {Z : E × E → ℝ → E × E}
    {γ : ℝ → M'} {q₁ : M'} {w : E}
    (hTpos : 0 < T) (hTεF : T < εF)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) rF,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-εF) εF, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-εF) εF) t) ∧
      (∀ t ∈ Icc (-εF) εF, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    (hmem : ((extChartAt I p q₁, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) rF)
    (hlo : lo < 0) (hhi : 0 < hi)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo lo hi)) (hcont : ContinuousOn γ (Ioo lo hi))
    (hγ0 : γ 0 = q₁) (hqsrc : q₁ ∈ (chartAt H p).source)
    (hvel : HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0) :
    Set.EqOn γ (fun s : ℝ => (extChartAt I p).symm
        ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) (s * T)).1))
      (Ioo (max lo (-(εF / T))) (min hi (εF / T))) := by
  classical
  set y : E := extChartAt I p q₁ with hydef
  set gw : ℝ → M' := fun s : ℝ => (extChartAt I p).symm
    ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1) with hgwdef
  obtain ⟨hgw0, hgwcont, hgwgeo, hgwread, hgwd0, hgwdint⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hTpos hTεF hflow hmem
  have hεT : 0 < εF / T := div_pos (hTpos.trans hTεF) hTpos
  set S : Set ℝ := Ioo (max lo (-(εF / T))) (min hi (εF / T)) with hSdef
  have hloneg : max lo (-(εF / T)) < 0 := max_lt hlo (by linarith)
  have hhipos : (0 : ℝ) < min hi (εF / T) := lt_min hhi hεT
  have h0S : (0 : ℝ) ∈ S := ⟨hloneg, hhipos⟩
  have hS_lo : S ⊆ Ioo lo hi :=
    Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hS_J : S ⊆ Ioo (-(εF / T)) (εF / T) :=
    Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have hγS : IsGeodesicOn (I := I) g γ S := hgeo.mono hS_lo
  have hgwS : IsGeodesicOn (I := I) g gw S := hgwgeo.mono hS_J
  have hγcS : ContinuousOn γ S := hcont.mono hS_lo
  have hgwcS : ContinuousOn gw S := hgwcont.mono hS_J
  have hγ0src : γ 0 ∈ (chartAt H p).source := by rw [hγ0]; exact hqsrc
  have hstart : gw 0 = q₁ := by
    have : gw 0 = (extChartAt I p).symm y := hgw0
    rw [this, hydef, (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hqsrc)]
  have heq0 : γ 0 = gw 0 := by rw [hγ0, hstart]
  have hvγ : deriv (chartReading (I := I) p γ) 0 = w := hvel.deriv
  have hvgw : deriv (chartReading (I := I) p gw) 0 = w := hgwd0.deriv
  exact IsGeodesicOn.eqOn_of_deriv_chartReading_eq isOpen_Ioo isPreconnected_Ioo
    hγS hgwS hγcS hgwcS h0S heq0 hγ0src (hvγ.trans hvgw.symm)

/-- **Math.** **The base-uniform geodesic-uniqueness engine** (the injectivity half of `Huniq` of
do Carmo Proposition 4.2).  For every `p` there are radii `β, ρw > 0` such that: any two continuous
intrinsic geodesics `γ₁, γ₂` on open time windows `⊋ [0,1]`, both joining `q₁ ∈ closedBall p β` to a
common `q₂ ∈ closedBall p β`, with initial chart-`p` coordinate velocities `w₁, w₂` of norm `< ρw`,
coincide on `[0,1]`.

Proof: each `γᵢ` coincides with the flow-reading geodesic `gw_{wᵢ}` on a window containing `[0,1]`
(`movingBase_geodesic_eqOn_flow_reading`), so `gw_{wᵢ}(1) = γᵢ 1 = q₂`.  The unique-velocity clause of
the totally-normal `C¹` diffeomorphism (`exists_totallyNormal_c1_diffeo`) forces `w₁ = w₂` — this is
do Carmo's injectivity of `exp_{q₁}` — hence `gw_{w₁} = gw_{w₂}` and `γ₁ = γ₂` on `[0,1]`. -/
theorem exists_movingBase_geodesic_uniqueness (g : RiemannianMetric I M') (p : M') :
    ∃ β ρw : ℝ, 0 < β ∧ 0 < ρw ∧
      ∀ q₁ ∈ closedBall p β, ∀ q₂ ∈ closedBall p β,
        ∀ (γ₁ γ₂ : ℝ → M') (w₁ w₂ : E) (lo₁ hi₁ lo₂ hi₂ : ℝ),
          lo₁ < 0 → 1 < hi₁ →
          IsGeodesicOn (I := I) g γ₁ (Ioo lo₁ hi₁) → ContinuousOn γ₁ (Ioo lo₁ hi₁) →
          γ₁ 0 = q₁ → γ₁ 1 = q₂ →
          HasDerivAt (fun s : ℝ => extChartAt I p (γ₁ s)) w₁ 0 → ‖w₁‖ < ρw →
          lo₂ < 0 → 1 < hi₂ →
          IsGeodesicOn (I := I) g γ₂ (Ioo lo₂ hi₂) → ContinuousOn γ₂ (Ioo lo₂ hi₂) →
          γ₂ 0 = q₁ → γ₂ 1 = q₂ →
          HasDerivAt (fun s : ℝ => extChartAt I p (γ₂ s)) w₂ 0 → ‖w₂‖ < ρw →
          Set.EqOn γ₁ γ₂ (Icc 0 1) := by
  classical
  obtain ⟨W, δ, δ₁, T, Z, Ginv, hWopen, hpW, hWsub, hδpos, hδ₁pos, hTpos, hWchart,
    hmemW, hcover, hGC1, hGinj, hGopen, hGleft, hGright, hGinvC1, hrange, hdiag,
    rF, εF, hrF, hεF, hTεF, hflow⟩ := exists_totallyNormal_c1_diffeo (I := I) g p
  set y₀ : E := extChartAt I p p with hy₀def
  -- the base neighbourhood: `q` inside `W`, and its chart image inside the flow ball `rF`
  set ηy : ℝ := min δ₁ rF with hηydef
  have hηypos : 0 < ηy := lt_min hδ₁pos hrF
  have hnhd : extChartAt I p ⁻¹' ball y₀ ηy ∩ W ∈ 𝓝 p := by
    refine inter_mem ?_ (hWopen.mem_nhds hpW)
    exact (continuousAt_extChartAt (I := I) p).preimage_mem_nhds
      (isOpen_ball.mem_nhds (by rw [hy₀def]; exact mem_ball_self hηypos))
  obtain ⟨β, hβpos, hβsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhd
  -- the velocity radius fits both the diffeo `δ`-ball and the flow-time `rF`-ball
  set ρw : ℝ := min δ (T * rF) with hρwdef
  have hρwpos : 0 < ρw := lt_min hδpos (by positivity)
  refine ⟨β, ρw, hβpos, hρwpos, ?_⟩
  intro q₁ hq₁ q₂ hq₂ γ₁ γ₂ w₁ w₂ lo₁ hi₁ lo₂ hi₂
    hlo₁ hhi₁ hgeo₁ hcont₁ hγ₁0 hγ₁1 hvel₁ hw₁ hlo₂ hhi₂ hgeo₂ hcont₂ hγ₂0 hγ₂1 hvel₂ hw₂
  -- unpack the memberships of `q₁, q₂`
  have hq₁mem : q₁ ∈ extChartAt I p ⁻¹' ball y₀ ηy ∩ W := hβsub hq₁
  have hq₂mem : q₂ ∈ extChartAt I p ⁻¹' ball y₀ ηy ∩ W := hβsub hq₂
  have hq₁W : q₁ ∈ W := hq₁mem.2
  have hq₂W : q₂ ∈ W := hq₂mem.2
  have hq₁src : q₁ ∈ (chartAt H p).source := hWsub hq₁W
  have hq₁dist : dist (extChartAt I p q₁) y₀ < ηy := mem_ball.mp hq₁mem.1
  -- the flow-ball membership `((φ_p q₁, T⁻¹ • w) , …) ∈ closedBall rF` for `‖w‖ < ρw`
  have hmem_of : ∀ w : E, ‖w‖ < ρw →
      ((extChartAt I p q₁, T⁻¹ • w) : E × E) ∈
        closedBall ((extChartAt I p p, (0 : E)) : E × E) rF := by
    intro w hw
    rw [mem_closedBall, Prod.dist_eq]
    refine max_le ?_ ?_
    · exact le_trans hq₁dist.le (le_trans (min_le_right _ _) (le_refl _))
    · rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hTpos.le,
        inv_mul_le_iff₀ hTpos]
      exact le_trans hw.le (min_le_right _ _)
  -- each geodesic coincides with its flow reading on a window containing `[0,1]`
  set gw : E → ℝ → M' := fun w s => (extChartAt I p).symm
    ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) (s * T)).1) with hgwdef
  have hεT1 : (1 : ℝ) < εF / T := (one_lt_div hTpos).mpr hTεF
  have hEqOf : ∀ (γ : ℝ → M') (w : E) (lo hi : ℝ), lo < 0 → 1 < hi →
      IsGeodesicOn (I := I) g γ (Ioo lo hi) → ContinuousOn γ (Ioo lo hi) →
      γ 0 = q₁ → HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 → ‖w‖ < ρw →
      Set.EqOn γ (gw w) (Icc 0 1) := by
    intro γ w lo hi hlo hhi hgeo hcont hγ0 hvel hw
    have hEq := movingBase_geodesic_eqOn_flow_reading (I := I) g p hTpos hTεF hflow
      (hmem_of w hw) hlo (lt_trans one_pos hhi) hgeo hcont hγ0 hq₁src hvel
    have hIccsub : Icc (0 : ℝ) 1 ⊆
        Ioo (max lo (-(εF / T))) (min hi (εF / T)) := by
      intro s hs
      refine ⟨?_, ?_⟩
      · exact lt_of_lt_of_le (max_lt hlo (by linarith)) hs.1
      · exact lt_of_le_of_lt hs.2 (lt_min hhi hεT1)
    exact hEq.mono hIccsub
  have hEq₁ : Set.EqOn γ₁ (gw w₁) (Icc 0 1) :=
    hEqOf γ₁ w₁ lo₁ hi₁ hlo₁ hhi₁ hgeo₁ hcont₁ hγ₁0 hvel₁ hw₁
  have hEq₂ : Set.EqOn γ₂ (gw w₂) (Icc 0 1) :=
    hEqOf γ₂ w₂ lo₂ hi₂ hlo₂ hhi₂ hgeo₂ hcont₂ hγ₂0 hvel₂ hw₂
  -- the flow-reading endpoints hit `q₂`
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hgwend : ∀ w : E, gw w 1 =
      (extChartAt I p).symm ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) T).1) := by
    intro w; simp only [hgwdef, one_mul]
  have hend₁ : (extChartAt I p).symm
      ((Z ((extChartAt I p q₁, T⁻¹ • w₁) : E × E) T).1) = q₂ := by
    rw [← hgwend w₁, ← hEq₁ h1mem, hγ₁1]
  have hend₂ : (extChartAt I p).symm
      ((Z ((extChartAt I p q₁, T⁻¹ • w₂) : E × E) T).1) = q₂ := by
    rw [← hgwend w₂, ← hEq₂ h1mem, hγ₂1]
  -- the unique-velocity clause of the diffeomorphism forces `w₁ = w₂`
  obtain ⟨wc, hwcδ, hwcend, hwcGinv, hwcuniq⟩ := hcover q₁ hq₁W q₂ hq₂W
  have hw₁δ : ‖w₁‖ < δ := lt_of_lt_of_le hw₁ (min_le_left _ _)
  have hw₂δ : ‖w₂‖ < δ := lt_of_lt_of_le hw₂ (min_le_left _ _)
  have hw₁c : w₁ = wc := hwcuniq w₁ hw₁δ hend₁
  have hw₂c : w₂ = wc := hwcuniq w₂ hw₂δ hend₂
  have hww : w₁ = w₂ := hw₁c.trans hw₂c.symm
  -- conclude `γ₁ = γ₂` on `[0,1]`
  intro s hs
  rw [hEq₁ hs, hEq₂ hs, hww]

end Exponential

end Riemannian

end
