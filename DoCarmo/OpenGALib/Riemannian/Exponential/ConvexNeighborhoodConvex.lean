import OpenGALib.Riemannian.Exponential.ConvexNeighborhoodJoin
import OpenGALib.Riemannian.Exponential.ConvexNeighborhoodAdmissible
import OpenGALib.Riemannian.Exponential.ConvexNeighborhood42
import OpenGALib.Riemannian.Exponential.MinimizingGeodesic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Convex neighborhoods: minimizing geodesics with interior in the ball (do Carmo Ch. 3, §4)

This file assembles the convex-neighborhood content of do Carmo's Proposition 4.2 modulo its one
genuine analytic crux. The pieces it composes are all available:

* `exists_convex_join_ball` — the joining geodesic `γ` between any two points of a small
  `closedBall p β`, on an open time window, with the arclength-proportional length
  `ℓ(γ|[0,t]) = √⟨w,w⟩ · t` and the radial upper bound `d(q₁,q₂) ≤ √⟨w,w⟩` (`≤` half of Prop 3.6);
* `edist_segment_of_arclength` — arclength-proportional distance realization propagated from the
  endpoints to the whole segment;
* `exists_forall_minimizing_geodesic_interior_ball` — the interior-arc-in-ball deduction from the
  minimizing property and the conserved speed.

The single remaining input is the matching **lower** bound `d(q₁,q₂) ≥ √⟨w,w⟩` — do Carmo's
statement that short radial geodesics *realize* the distance (Prop 3.6), phrased *base-uniformly*
over the ball of centers. That is the residual crux of `prop:dc-ch3-4-2`: no lower-semicontinuous
normal radius (nor a moving-base Gauss estimate) is yet available. Here it enters as the explicit
hypothesis `Hlb`.

`Hlb` must carry both a **geodesic** hypothesis and an initial-velocity **smallness** bound
`‖w‖ < ρH`: it is exactly do Carmo Prop 3.6 ("a *short geodesic* near `p` realizes the distance
between its endpoints"), stated base-uniformly. These are essential — without them the statement is
unsound: for an arbitrary constant-speed curve `γ` one always has `d(q₁,q₂) ≤ ℓ = length(γ)`, so a
bare `ℓ ≤ d(q₁,q₂)` would force *every* constant-speed curve to be minimizing, which is false on any
manifold of dimension `≥ 2` (a constant-speed loop through `q₁ = q₂` has `ℓ > 0 = d`). The joining
geodesic of `exists_convex_join_ball` supplies precisely the geodesic-plus-small-velocity data `Hlb`
needs, so the reduction stays honest.

Main result: `exists_minimizing_interior_ball_of_lower_bound` — given `Hlb`, every pair of points
of a small `closedBall p β` is joined by a **minimizing** geodesic (arclength-proportional distance
realization) whose open arc lies in the ball. This is the strong-convexity content of Prop 4.2
except the uniqueness clause; combined with `Hlb` it reduces the proposition to that lower bound.
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

/-- **Math.** **Minimizing geodesics with interior in the ball (do Carmo Prop 4.2, modulo the
lower-bound crux and uniqueness).** Suppose the *base-uniform lower bound* `Hlb` holds: there are
radii `βH, ρH > 0` such that every **geodesic** `γ` (on an open window `(lo, hi) ⊋ [0,1]`) joining
two points `q₁, q₂` within `βH` of `p`, with **small** initial chart velocity `w` (`‖w‖ < ρH`) and
constant-speed length `ℓ(γ|[0,t]) = ℓ·t`, has `ℓ ≤ d(q₁, q₂)` (short geodesics realize the distance
— do Carmo's Proposition 3.6, base-uniform). The geodesic and smallness hypotheses are essential:
for an arbitrary constant-speed curve one always has `d(q₁,q₂) ≤ ℓ`, so a bare `ℓ ≤ d(q₁,q₂)` would
force every constant-speed curve minimizing, false on dimension `≥ 2`. Then there is `β > 0` such
that any two points of `closedBall p β` are joined by a geodesic `γ` on `[0,1]` that is *minimizing*
(`d(γ s, γ t) = |s-t| · d(q₁, q₂)`) and whose open arc `γ((0,1))` lies in `closedBall p β`. This is
do Carmo's strong convexity except the uniqueness clause. -/
theorem exists_minimizing_interior_ball_of_lower_bound
    (g : RiemannianMetric I M') (hg : g.IsRiemannianDist) (p : M')
    (Hlb : ∃ βH ρH : ℝ, 0 < βH ∧ 0 < ρH ∧ ∀ (q₁ q₂ : M') (γ : ℝ → M') (w : E)
             (lo hi ℓ : ℝ), 0 ≤ ℓ →
             dist p q₁ ≤ βH → dist p q₂ ≤ βH → lo < 0 → 1 < hi → γ 0 = q₁ → γ 1 = q₂ →
             IsGeodesicOn (I := I) g γ (Ioo lo hi) → ContinuousOn γ (Ioo lo hi) →
             HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 → ‖w‖ < ρH →
             (letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
               ⟨g.toRiemannianMetric⟩
              ∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I γ 0 t
                = ENNReal.ofReal (ℓ * t)) →
             ENNReal.ofReal ℓ ≤ edist q₁ q₂) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ β : ℝ, 0 < β → β ≤ B₀ →
      ∀ q₁ ∈ closedBall p β, ∀ q₂ ∈ closedBall p β,
        ∃ γ : ℝ → M',
          γ 0 = q₁ ∧ γ 1 = q₂ ∧
          IsGeodesicOn (I := I) g γ (Icc 0 1) ∧
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (γ s) (γ t) = |s - t| * dist q₁ q₂) ∧
          γ '' Ioo (0 : ℝ) 1 ⊆ closedBall p β := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  obtain ⟨βH, ρH, hβHpos, hρHpos, Hlb⟩ := Hlb
  obtain ⟨β₀, ρ, hβ₀pos, hρpos, hint⟩ :=
    exists_forall_minimizing_geodesic_interior_ball (I := I) g hg p
  obtain ⟨βj, hβjpos, hβjsrc, hjoin⟩ :=
    exists_convex_join_ball (I := I) g hg p (ρ := min ρ ρH) (lt_min hρpos hρHpos)
  refine ⟨min (min βj β₀) βH, lt_min (lt_min hβjpos hβ₀pos) hβHpos, ?_⟩
  intro β hβpos hβB₀ q₁ hq₁ q₂ hq₂
  -- membership in the various sub-balls
  have hβ_βj : β ≤ βj := le_trans hβB₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hβ_β₀ : β ≤ β₀ := le_trans hβB₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hβ_βH : β ≤ βH := le_trans hβB₀ (min_le_right _ _)
  have hq₁j : q₁ ∈ closedBall p βj := closedBall_subset_closedBall hβ_βj hq₁
  have hq₂j : q₂ ∈ closedBall p βj := closedBall_subset_closedBall hβ_βj hq₂
  -- distance bounds `dist p qᵢ ≤ β`
  have hpq₁ : dist p q₁ ≤ β := by rw [dist_comm]; exact mem_closedBall.mp hq₁
  have hpq₂ : dist p q₂ ≤ β := by rw [dist_comm]; exact mem_closedBall.mp hq₂
  -- the joining geodesic with metric payload
  obtain ⟨γ, w, lo, hi, hlo, hhi, hγ0, hγ1, hwne, hwρ, hgeoIoo, hcontIoo, hd0,
    hint_vel, hlen, hup⟩ := hjoin q₁ hq₁j q₂ hq₂j
  -- split the joining-velocity smallness for the interior deduction and the lower bound
  have hwρ_int : ‖w‖ < ρ := lt_of_lt_of_le hwρ (min_le_left _ _)
  have hwρ_H : ‖w‖ < ρH := lt_of_lt_of_le hwρ (min_le_right _ _)
  set ℓ : ℝ := Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p q₁) w w) with hℓdef
  have hℓnn : 0 ≤ ℓ := Real.sqrt_nonneg _
  -- the lower bound closes the gap: `edist q₁ q₂ = ofReal ℓ`
  have hlow : ENNReal.ofReal ℓ ≤ edist q₁ q₂ :=
    Hlb q₁ q₂ γ w lo hi ℓ hℓnn (le_trans hpq₁ hβ_βH) (le_trans hpq₂ hβ_βH)
      hlo hhi hγ0 hγ1 hgeoIoo hcontIoo hd0 hwρ_H hlen
  have hedist : edist q₁ q₂ = ENNReal.ofReal ℓ := le_antisymm hup hlow
  have hdist : dist q₁ q₂ = ℓ := by
    have h : ENNReal.ofReal (dist q₁ q₂) = ENNReal.ofReal ℓ := by rw [← edist_dist]; exact hedist
    have := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_ofReal hℓnn] at this
  -- `γ` restricted to `[0,1]` is a geodesic
  have hIccsub : Icc (0 : ℝ) 1 ⊆ Ioo lo hi :=
    fun x hx => ⟨lt_of_lt_of_le hlo hx.1, lt_of_le_of_lt hx.2 hhi⟩
  have hgeoIcc : IsGeodesicOn (I := I) g γ (Icc 0 1) := hgeoIoo.mono hIccsub
  have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) :=
    (hgeoIoo.contMDiffOn isOpen_Ioo hcontIoo).mono hIccsub
  -- the minimizing property, propagated from the endpoints
  have hseg : ∀ s t : ℝ, (0 : ℝ) ≤ s → s ≤ t → t ≤ 1 →
      edist (γ s) (γ t) = ENNReal.ofReal (ℓ * (t - s)) := by
    intro s t hs hst ht
    refine edist_segment_of_arclength (I := I) g hℓnn ?_ ?_ ?_ hs hst ht
    · intro u v hu huv hv
      exact OpenGA.HopfRinow.edist_le_pathELength_of_cmdiff
        (hC1.mono (Icc_subset_Icc hu hv)) huv
    · intro u hu; rw [sub_zero]; exact hlen u hu
    · rw [hγ0, hγ1, hedist, sub_zero, mul_one]
  have hmindist : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist q₁ q₂ := by
    intro s hs t ht
    rw [hdist]
    rcases le_total s t with hst | hts
    · have h := hseg s t hs.1 hst ht.2
      have hd : dist (γ s) (γ t) = ℓ * (t - s) := by
        have h' := congrArg ENNReal.toReal h
        rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
          ENNReal.toReal_ofReal (mul_nonneg hℓnn (by linarith))] at h'
      rw [hd, abs_of_nonpos (by linarith : s - t ≤ 0)]; ring
    · have h := hseg t s ht.1 hts hs.2
      have hd : dist (γ s) (γ t) = ℓ * (s - t) := by
        rw [dist_comm]
        have h' := congrArg ENNReal.toReal h
        rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
          ENNReal.toReal_ofReal (mul_nonneg hℓnn (by linarith))] at h'
      rw [hd, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - t)]; ring
  refine ⟨γ, hγ0, hγ1, hgeoIcc, hmindist, ?_⟩
  -- the open arc lies in the ball
  rintro x ⟨t, ht, rfl⟩
  rw [mem_closedBall]
  by_cases hne : q₁ = q₂
  · -- degenerate case: the minimizing geodesic is constant at `q₁`
    have hd0t : dist (γ t) (γ 0) = 0 := by
      have := hmindist t ⟨le_of_lt ht.1, le_of_lt ht.2⟩ 0 ⟨le_rfl, zero_le_one⟩
      rw [hne, dist_self, mul_zero] at this
      exact this
    have hγtq₁ : γ t = q₁ := by rw [← hγ0]; exact (dist_eq_zero.mp hd0t)
    rw [hγtq₁]; exact mem_closedBall.mp hq₁
  · -- non-degenerate: the strict interior deduction
    have hlt : dist p (γ t) < β :=
      hint q₁ q₂ γ w lo hi β hβpos hβ_β₀ hlo hhi hpq₁ hpq₂ (hwne hne)
        hγ0 hγ1 hgeoIoo hcontIoo hmindist hd0 hwρ_int hint_vel t ht
    rw [dist_comm]; exact le_of_lt hlt

/-- **Math.** **Convex neighborhoods (do Carmo Proposition 4.2), reduced to two isolated cruxes.**
Given the base-uniform lower bound `Hlb` (short geodesics of small initial velocity near `p` realize
the distance, `prop:dc-ch3-3-6` base-uniform) and the *local uniqueness* `Huniq` of minimizing
geodesics near `p`
(any two constant-speed distance-realizing geodesics joining the same pair of points near `p`
coincide on `[0,1]` — do Carmo's reading of the injectivity of `exp_{q₁}`), there is `β > 0` such
that the **closed** geodesic ball `closedBall p β` is strongly convex
(`def:dc-ch3-4-2-stronglyconvex`). This is the full Proposition 4.2 for the closed ball, assembled
from the totally-normal joining geodesic and its metric payload; only `Hlb` and `Huniq` remain.

The closed ball is used deliberately: the literal open-ball statement is unsatisfiable at a boundary
diagonal `q₁ = q₂ ∈ ∂ B_β(p)`, where the constant minimizing geodesic's interior `{q₁}` is not in the
*open* ball. -/
theorem exists_stronglyConvex_closedBall_of_lower_bound
    (g : RiemannianMetric I M') (hg : g.IsRiemannianDist) (p : M')
    (Hlb : ∃ βH ρH : ℝ, 0 < βH ∧ 0 < ρH ∧ ∀ (q₁ q₂ : M') (γ : ℝ → M') (w : E)
             (lo hi ℓ : ℝ), 0 ≤ ℓ →
             dist p q₁ ≤ βH → dist p q₂ ≤ βH → lo < 0 → 1 < hi → γ 0 = q₁ → γ 1 = q₂ →
             IsGeodesicOn (I := I) g γ (Ioo lo hi) → ContinuousOn γ (Ioo lo hi) →
             HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 → ‖w‖ < ρH →
             (letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
               ⟨g.toRiemannianMetric⟩
              ∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I γ 0 t
                = ENNReal.ofReal (ℓ * t)) →
             ENNReal.ofReal ℓ ≤ edist q₁ q₂)
    (Huniq : ∃ βU : ℝ, 0 < βU ∧ ∀ (q₁ q₂ : M') (α β' : ℝ → M'),
               dist p q₁ ≤ βU → dist p q₂ ≤ βU →
               α 0 = q₁ → α 1 = q₂ → IsGeodesicOn (I := I) g α (Icc 0 1) →
               (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
                 dist (α s) (α t) = |s - t| * dist q₁ q₂) →
               β' 0 = q₁ → β' 1 = q₂ → IsGeodesicOn (I := I) g β' (Icc 0 1) →
               (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
                 dist (β' s) (β' t) = |s - t| * dist q₁ q₂) →
               Set.EqOn β' α (Icc 0 1)) :
    ∃ β : ℝ, 0 < β ∧ StronglyConvex (I := I) g (closedBall p β) := by
  obtain ⟨B₀, hB₀pos, hcore⟩ :=
    exists_minimizing_interior_ball_of_lower_bound (I := I) g hg p Hlb
  obtain ⟨βU, hβUpos, Huniq⟩ := Huniq
  refine ⟨min B₀ βU, lt_min hB₀pos hβUpos, ?_⟩
  intro q₁ hq₁cl q₂ hq₂cl
  -- the closure of a closed ball is itself
  have hq₁ : q₁ ∈ closedBall p (min B₀ βU) := by
    rwa [isClosed_closedBall.closure_eq] at hq₁cl
  have hq₂ : q₂ ∈ closedBall p (min B₀ βU) := by
    rwa [isClosed_closedBall.closure_eq] at hq₂cl
  obtain ⟨γ, hγ0, hγ1, hgeo, hmin, hinterior⟩ :=
    hcore (min B₀ βU) (lt_min hB₀pos hβUpos) (min_le_left _ _) q₁ hq₁ q₂ hq₂
  -- distance bounds for the uniqueness hypothesis
  have hpq₁U : dist p q₁ ≤ βU :=
    le_trans (by rw [dist_comm]; exact mem_closedBall.mp hq₁) (min_le_right _ _)
  have hpq₂U : dist p q₂ ≤ βU :=
    le_trans (by rw [dist_comm]; exact mem_closedBall.mp hq₂) (min_le_right _ _)
  refine ⟨γ, hγ0, hγ1, hgeo, hmin, hinterior, ?_⟩
  intro γ' hγ'0 hγ'1 hgeo' hmin' _
  exact Huniq q₁ q₂ γ γ' hpq₁U hpq₂U hγ0 hγ1 hgeo hmin hγ'0 hγ'1 hgeo' hmin'
end Exponential

end Riemannian
