/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Geodesic/UniformExistence.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Geodesic.ChartFlow

set_option linter.unusedSectionVars false

/-!
# Uniform-time existence for geodesics with small initial velocity

Picard–Lindelöf applied to the coordinate geodesic spray
`F(x, w) = (w, -Γ_p(w, w)(x))` on `E × E` produces a *local flow*: one family
`Z : E × E → ℝ → E × E` of solutions, defined on a **fixed** time interval
`[-ε, ε]` for **all** initial conditions in a fixed ball around the zero
section, Lipschitz in the initial condition. This is the uniform-in-`v` content
of do Carmo's Proposition 2.7 (Ch. 3): a single interval of definition works
for every initial velocity `‖v‖ ≤ r`.

* `exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt` — reusable
  local-flow package for an autonomous `C^1` field on a Banach space: solutions
  on a fixed `[-ε, ε]` for all initial conditions in `closedBall z₀ r`,
  Lipschitz in the initial condition, with all trajectories confined to any
  prescribed neighbourhood `U` of `z₀`. (The confinement needs no compactness:
  it follows from Lipschitz dependence on the initial condition plus continuity
  of the single centre trajectory.)
* `eq_const_of_hasDerivWithinAt_of_eq_zero` — a solution starting at an
  equilibrium (`f z₀ = 0`) is constant, by Grönwall uniqueness against the
  constant solution.
* `exists_uniform_geodesic_flow` — the spray instantiation: there are `r, ε > 0`
  and a local flow `Z` of the chart-`p` spray such that for every velocity
  `‖v‖ ≤ r`, the open interval `(-ε, ε)` is contained in the maximal interval
  of the geodesic with initial data `(p, v)`, the canonical maximal geodesic is
  computed by the flow (`φ_p(γ(s, p, v)) = (Z (φ_p(p), v) s).1`), the flow is
  Lipschitz in `v`, and the zero-velocity trajectory is constant.

This file feeds the strict differentiability of `exp_p` at `0`
(do Carmo Ch. 3, Prop. 2.9) and the openness of the exponential domain.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace PetersenLib

section GenericFlow

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Math.** **A solution through an equilibrium is constant.** If `f z₀ = 0`,
`f` is Lipschitz on a set `s`, and `α` solves `α' = f(α)` on `[-ε, ε]` with
`α 0 = z₀` and values in `s`, then `α ≡ z₀` on `[-ε, ε]` (Grönwall uniqueness
against the constant solution). -/
theorem eq_const_of_hasDerivWithinAt_of_eq_zero
    {f : F → F} {z₀ : F} {s : Set F} {K : ℝ≥0}
    (hlip : LipschitzOnWith K f s) (heq : f z₀ = 0)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ → F} (hα0 : α 0 = z₀)
    (hd : ∀ t ∈ Icc (-ε) ε, HasDerivWithinAt α (f (α t)) (Icc (-ε) ε) t)
    (hmem : ∀ t ∈ Icc (-ε) ε, α t ∈ s) (hz₀s : z₀ ∈ s)
    {t : ℝ} (ht : t ∈ Icc (-ε) ε) : α t = z₀ := by
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hcont : ContinuousOn α (Icc (-ε) ε) :=
    fun u hu => (hd u hu).continuousWithinAt
  have heqOn : EqOn α (fun _ => z₀) (Icc (-ε) ε) := by
    refine ODE_solution_unique_of_mem_Icc (v := fun _ => f) (s := fun _ => s)
      (fun u _ => hlip) h0mem hcont ?_ (fun u hu => hmem u (Ioo_subset_Icc_self hu))
      continuousOn_const ?_ (fun _ _ => hz₀s) (by simpa using hα0)
    · intro u hu
      exact (hd u (Ioo_subset_Icc_self hu)).hasDerivAt
        (Icc_mem_nhds hu.1 hu.2)
    · intro u hu
      simpa [heq] using (hasDerivAt_const u z₀)
  exact heqOn ht

variable [CompleteSpace F]

/-- **Math.** **Local flow of an autonomous `C^1` field, with confinement.** If
`f` is `C^1` at `z₀`, then for any prescribed neighbourhood `U` of `z₀` there
are `r, ε > 0` and a family `Z` of solutions of `z' = f(z)` on the fixed
interval `[-ε, ε]`, one for each initial condition in `closedBall z₀ r`, which
is Lipschitz in the initial condition and keeps every trajectory inside `U`.
This is the Picard–Lindelöf local flow (do Carmo Ch. 3, Thm 2.2, the uniform
time-of-existence clause), with the confinement obtained from Lipschitz
dependence on the initial condition and continuity of the centre trajectory —
no compactness of balls is used. -/
theorem exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt
    {f : F → F} {z₀ : F} (hf : ContDiffAt ℝ 1 f z₀)
    {U : Set F} (hU : U ∈ 𝓝 z₀) :
    ∃ (r ε : ℝ) (Z : F → ℝ → F) (L : ℝ≥0), 0 < r ∧ 0 < ε ∧
      (∀ z ∈ closedBall z₀ r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z) (f (Z z t)) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ U)) ∧
      (∀ t ∈ Icc (-ε) ε, LipschitzOnWith L (Z · t) (closedBall z₀ r)) := by
  classical
  -- Picard–Lindelöf structure around `z₀`, centred at time `0`
  obtain ⟨ε₁, hε₁, a, r₁, L₀, K, hr₁, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  have hpl0 := hpl 0
  -- the local flow with Lipschitz dependence on the initial condition
  obtain ⟨Z, hZ, L, hLip⟩ :=
    hpl0.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  -- a closed ball inside `U`
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  -- the centre trajectory is continuous at `0` and starts at `z₀`
  have hZ₀ := hZ z₀ (mem_closedBall_self hr₁.le)
  have hIcc0 : (0 : ℝ) ∈ Icc (0 - ε₁) (0 + ε₁) := by
    constructor <;> [linarith; linarith]
  have hcont0 : ContinuousWithinAt (Z z₀) (Icc (0 - ε₁) (0 + ε₁)) 0 := by
    have := (hZ₀.2 0 hIcc0).continuousWithinAt
    exact this
  have hcenter0 : Z z₀ 0 = z₀ := hZ₀.1
  -- choose a small time window on which the centre trajectory stays `δ/2`-close
  have hhalf : (0 : ℝ) < δ / 2 := by positivity
  have hev : ∀ᶠ t in 𝓝[Icc (0 - ε₁) (0 + ε₁)] (0 : ℝ),
      Z z₀ t ∈ ball z₀ (δ / 2) := by
    have : ball z₀ (δ / 2) ∈ 𝓝 (Z z₀ 0) := by
      rw [hcenter0]
      exact ball_mem_nhds z₀ hhalf
    exact hcont0.eventually_mem this
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  -- final radius and time window
  set r : ℝ := min r₁ (δ / (2 * (L + 1))) with hrdef
  set ε : ℝ := min (min ε₁ (η / 2)) 1 with hεdef
  have hrpos : 0 < r := lt_min hr₁ (by positivity)
  have hεpos : 0 < ε := lt_min (lt_min hε₁ (by positivity)) one_pos
  have hεε₁ : ε ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hIccsub : Icc (-ε) ε ⊆ Icc (0 - ε₁) (0 + ε₁) := by
    apply Icc_subset_Icc <;> [linarith; linarith]
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hballsub : closedBall z₀ r ⊆ closedBall z₀ r₁ :=
    closedBall_subset_closedBall hrr₁
  refine ⟨r, ε, Z, L, hrpos, hεpos, ?_, ?_⟩
  · intro z hz
    have hz₁ : z ∈ closedBall z₀ r₁ := hballsub hz
    obtain ⟨hz0, hzd⟩ := hZ z hz₁
    refine ⟨hz0, fun t ht => (hzd t (hIccsub ht)).mono hIccsub, ?_⟩
    -- confinement: Lipschitz in the initial condition + centre trajectory
    intro t ht
    have htmem : t ∈ Icc (0 - ε₁) (0 + ε₁) := hIccsub ht
    have hLipt := hLip t htmem
    have hd1 : dist (Z z t) (Z z₀ t) ≤ L * dist z z₀ := by
      have := hLipt.dist_le_mul z hz₁ z₀ (mem_closedBall_self hr₁.le)
      simpa using this
    have hd1' : dist (Z z t) (Z z₀ t) ≤ L * r := by
      refine hd1.trans ?_
      have : dist z z₀ ≤ r := mem_closedBall.mp hz
      exact mul_le_mul_of_nonneg_left this L.coe_nonneg
    have htη : t ∈ ball (0 : ℝ) η := by
      rw [mem_ball, Real.dist_eq, sub_zero]
      have h1 : |t| ≤ ε := abs_le.mpr ⟨ht.1, ht.2⟩
      have h2 : ε ≤ η / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    have hd2 : Z z₀ t ∈ ball z₀ (δ / 2) := hηsub ⟨htη, htmem⟩
    have hLr : (L : ℝ) * r ≤ δ / 2 := by
      have hrle : r ≤ δ / (2 * ((L : ℝ) + 1)) := min_le_right _ _
      have hpos : (0 : ℝ) < 2 * ((L : ℝ) + 1) := by positivity
      have h1 : (L : ℝ) * r ≤ (L : ℝ) * (δ / (2 * ((L : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hrle L.coe_nonneg
      have h2 : (L : ℝ) * (δ / (2 * ((L : ℝ) + 1))) ≤ δ / 2 := by
        have hc0 : (0 : ℝ) ≤ δ / (2 * ((L : ℝ) + 1)) := by positivity
        have hcδ : δ / (2 * ((L : ℝ) + 1)) * (2 * ((L : ℝ) + 1)) = δ :=
          div_mul_cancel₀ δ (ne_of_gt hpos)
        nlinarith [L.coe_nonneg, hc0, hcδ]
      linarith
    apply hδU
    have : dist (Z z t) z₀ ≤ dist (Z z t) (Z z₀ t) + dist (Z z₀ t) z₀ :=
      dist_triangle _ _ _
    have hlt : dist (Z z t) z₀ < δ := by
      have h2 := mem_ball.mp hd2
      calc dist (Z z t) z₀ ≤ dist (Z z t) (Z z₀ t) + dist (Z z₀ t) z₀ := this
        _ ≤ L * r + dist (Z z₀ t) z₀ := by linarith
        _ < δ / 2 + δ / 2 := by linarith
        _ = δ := by ring
    exact mem_ball.mpr hlt
  · intro t ht
    exact (hLip t (hIccsub ht)).mono hballsub

end GenericFlow

namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** The coordinate geodesic spray vanishes at the zero section:
`F(φ_p(p), 0) = (0, 0)`. -/
lemma geodesicSprayCoord_zero_velocity (g : RiemannianMetric I M) (p : M) (x : E) :
    geodesicSprayCoord (I := I) g p x (0 : E) = (0 : E × E) := by
  rw [geodesicSprayCoord_def, chartChristoffelContraction_zero_left]
  simp

/-- **Math.** The coordinate geodesic spray is `C^1` at the zero section point
`(φ_p(p), 0)`. -/
lemma contDiffAt_geodesicSprayCoord_zero (g : RiemannianMetric I M) (p : M) :
    ContDiffAt ℝ 1 (fun ζ : E × E => geodesicSprayCoord (I := I) g p ζ.1 ζ.2)
      ((extChartAt I p p, (0 : E)) : E × E) := by
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  have hmem : ((extChartAt I p p, (0 : E)) : E × E) ∈
      (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  exact ((contDiffOn_geodesicSprayCoord_prod (I := I) g p).contDiffAt
    (hopen.mem_nhds hmem)).of_le (by norm_num)

/-- **Math.** **Uniform-time local geodesic flow** (the uniform-in-velocity clause
of do Carmo Ch. 3, Prop. 2.7, at a fixed base point). There are `r, ε > 0` and a
local flow `Z` of the coordinate spray at `p` such that:

* for every initial condition in `closedBall (φ_p(p), 0) r` the flow line solves
  the spray ODE on all of `[-ε, ε]` and stays inside the chart target;
* the flow is Lipschitz in the initial condition, uniformly in time;
* the zero-velocity flow line is constant at `(φ_p(p), 0)`;
* for every velocity `‖v‖ ≤ r`: the interval `(-ε, ε)` is contained in the
  maximal interval of the geodesic with initial data `(p, v)`, and the chart
  reading of the canonical maximal geodesic is computed by the flow:
  `φ_p(γ(s, p, v)) = (Z (φ_p(p), v) s).1` for `s ∈ (-ε, ε)`. -/
theorem exists_uniform_geodesic_flow (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε : ℝ) (Z : E × E → ℝ → E × E) (L : ℝ≥0), 0 < r ∧ 0 < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      (∀ t ∈ Icc (-ε) ε, LipschitzOnWith L (Z · t)
        (closedBall ((extChartAt I p p, (0 : E)) : E × E) r)) ∧
      (∀ t ∈ Icc (-ε) ε, Z ((extChartAt I p p, (0 : E)) : E × E) t =
        ((extChartAt I p p, (0 : E)) : E × E)) ∧
      (∀ w : E, ‖w‖ ≤ r →
        Ioo (-ε) ε ⊆
          maximalGeodesicInterval (I := I) g p (w : TangentSpace I p) ∧
        ∀ s ∈ Ioo (-ε) ε,
          extChartAt I p
              (maximalGeodesic (I := I) g p (w : TangentSpace I p) s) =
            (Z ((extChartAt I p p, w) : E × E) s).1) := by
  classical
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  have hf : ContDiffAt ℝ 1
      (fun ζ : E × E => geodesicSprayCoord (I := I) g p ζ.1 ζ.2) z₀ :=
    contDiffAt_geodesicSprayCoord_zero (I := I) g p
  -- Lipschitz region for the spray, for the equilibrium-constancy argument
  obtain ⟨K, sLip, hsLip, hlip⟩ := hf.exists_lipschitzOnWith
  -- confinement region: chart target ∩ Lipschitz region
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  have hmemz₀ : z₀ ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  have hU : ((extChartAt I p).target ×ˢ (univ : Set E)) ∩ sLip ∈ 𝓝 z₀ :=
    Filter.inter_mem (hopen.mem_nhds hmemz₀) hsLip
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip⟩ :=
    exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt hf hU
  refine ⟨r, ε, Z, L, hr, hε, ?_, hLip, ?_, ?_⟩
  · intro z hz
    obtain ⟨h0, hd, hmem⟩ := hflow z hz
    exact ⟨h0, hd, fun t ht => (hmem t ht).1⟩
  · -- the zero-velocity flow line is constant (equilibrium)
    intro t ht
    obtain ⟨h0, hd, hmem⟩ := hflow z₀ (mem_closedBall_self hr.le)
    exact eq_const_of_hasDerivWithinAt_of_eq_zero hlip
      (geodesicSprayCoord_zero_velocity (I := I) g p _) hε h0 hd
      (fun u hu => (hmem u hu).2) (mem_of_mem_nhds hsLip) ht
  · -- transfer to the canonical maximal geodesic via the chart-flow bridge
    intro w hv
    have hzmem : ((extChartAt I p p, w) : E × E) ∈ closedBall z₀ r := by
      rw [mem_closedBall, hz₀def, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      exact max_le hr.le hv
    obtain ⟨h0, hd, hmem⟩ := hflow _ hzmem
    have hdIoo : ∀ s ∈ Ioo (-ε) ε,
        HasDerivAt (Z ((extChartAt I p p, w) : E × E))
          (geodesicSprayCoord (I := I) g p
            (Z ((extChartAt I p p, w) : E × E) s).1
            (Z ((extChartAt I p p, w) : E × E) s).2) s := by
      intro s hs
      exact (hd s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hmemΨ : ∀ s ∈ Ioo (-ε) ε,
        Z ((extChartAt I p p, w) : E × E) s ∈
          (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
      intro s hs
      rw [extChartAt_tangent_target (I := I) p]
      exact (hmem s (Ioo_subset_Icc_self hs)).1
    have h0Ioo : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
    obtain ⟨hwit, hsrc, -⟩ :=
      isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord (I := I) g p
        (w : TangentSpace I p) h0 hdIoo hmemΨ
    refine ⟨subset_maximalGeodesicInterval_of_witness (I := I) hwit isOpen_Ioo
      isPreconnected_Ioo h0Ioo, fun s hs => ?_⟩
    exact extChartAt_maximalGeodesic_of_hasDerivAt_sprayCoord (I := I)
      isOpen_Ioo isPreconnected_Ioo h0Ioo h0 hdIoo hmemΨ hs

end Geodesic

end PetersenLib
