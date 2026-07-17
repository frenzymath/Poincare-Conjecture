import PoincareLib.Ch01.ChartCurvature
import PoincareLib.Ch01.GlobalExp
import OpenGALib.Riemannian.Geodesic.EquationTransfer

/-!
# Poincaré Ch. 1 — regularity of geodesics read in a chart

A geodesic is *defined* by a second-order ODE, and the intrinsic theory only ever
produces it as a `C¹` object: `IsGeodesicOn` asserts that the chart reading is
differentiable with a differentiable derivative, nothing more.  Every quantitative
use of a geodesic beyond first order — the second variation of energy, the Jacobi
operator `t ↦ ℛ(·, γ′(t))γ′(t)` as a *smooth* curve of operators, the smoothness
of a parallel frame — needs more.

This file supplies the missing regularity, by the standard **ODE bootstrap**:

* `contDiffOn_secondOrderODE` — the manifold-free statement.  If `y : ℝ → E`
  satisfies `y″ = −Γ(y)(y′, y′)` on an **open** set `J`, with `Γ` of class `C^∞`
  on an open `U ⊇ y(J)`, then `y` and `y′` are `C^n` on `J` for **every** `n`.
  The induction is one line of mathematics: `y′` is `C^n` (inductive hypothesis)
  forces `y` to be `C^{n+1}`; and then `y″ = −Γ(y)(y′, y′)` is a `C^n` expression
  in `C^n` data, so `y′` is `C^{n+1}` too.

* `contDiffOn_chartReading_of_isGeodesicOn` — the geodesic corollary.  A geodesic
  whose foot stays in the source of a **fixed** chart at `β` over an open set of
  times is `C^n` there, read in that chart, for every `n`; and `contDiffOn_infty`
  packages this as `C^∞` (`contDiffOn_chartReading_infty_of_isGeodesicOn`).  The
  chart data is the real Levi-Civita one, so `Γ` is `chartChristoffelBilin g β`,
  `C^∞` on the interior of the chart target by `contDiffOn_chartChristoffelBilin`.

* `contDiffOn_chartReading_globalGeodesic` — the same statement for the **junction
  curves** `s ↦ globalGeodesic g hg (γ τᵢ) (Y τᵢ) s` of a broken variation.

The transfer from the moving-foot geodesic equation to the fixed chart at `β` is
do Carmo's `HasGeodesicEquationAt.solvesGeodesicODEAt` — the same lemma that
carries the geodesic ODE across charts in the junction-step machinery — so no
gluing or chart-change law is needed: the bootstrap runs entirely inside the one
chart at `β`.

**Why this is the keystone of the second-variation half of
`prop:minimal-geodesic-no-conjugate`.**  The broken-variation route needs `C³`
chart data in three places, and this one lemma supplies all three:

1. the chart reading of the geodesic `γ` itself (the `ŷ` of `chartVariation`);
2. the chart reading of each **junction geodesic** — and note that no homogeneity
   relation `exp_p(s·v) = γ_v(s)` is needed to get it: the junction curve simply
   *is* `globalGeodesic g hg (γ τᵢ) (Y τᵢ)`, the geodesic with the prescribed
   initial data, so its regularity in `s` is this same statement;
3. the smoothness in `t` of the frame Jacobi operator `frameCurvOp g γ e`, which
   is what would upgrade a Jacobi field from `C²` to `C^∞` (not done here).

Blueprint: `def:geodesic`, `prop:minimal-geodesic-no-conjugate`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.3.
-/

open Set Riemannian Riemannian.Geodesic
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

/-! ### The manifold-free bootstrap -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Math.** **ODE bootstrap for an autonomous second-order equation.**  Let
`J ⊆ ℝ` be open, `U ⊆ E` any set carrying a `C^∞` coefficient map
`Γ : E → E →L[ℝ] E →L[ℝ] E`, and let `y : ℝ → E` satisfy, at every `t ∈ J`,

* `y` is differentiable at `t` (with derivative `y′ t`), and
* `y′` is differentiable at `t`, with `y″(t) = −Γ(y t)(y′ t, y′ t)`,

the foot `y t` staying in `U`.  Then **both** `y` and `y′` are `C^n` on `J`, for
every `n`.

*Proof.*  Induction on `n`.  For `n = 0` both are continuous, being
differentiable.  For the step, suppose `y` and `y′` are `C^n` on `J`.

* `y` is differentiable on `J` and its derivative `y′` is `C^n` on `J`; since `J`
  is open, `contDiffOn_succ_iff_deriv_of_isOpen` upgrades `y` to `C^{n+1}`.
* the second derivative is `y″ = −Γ(y)(y′, y′)` on `J`, a composition and two
  `clm_apply`s of data that is `C^n` on `J` — `Γ ∘ y` because `Γ` is `C^∞` on `U`
  and `y` is `C^n` into `U`, and `y′` by the inductive hypothesis.  So `y″` is
  `C^n` on `J`, and the same open-set criterion upgrades `y′` to `C^{n+1}`.  ∎

Note that no completeness, no finite-dimensionality and no uniqueness theory is
used: this is a regularity statement about a *given* solution, not an existence
statement. -/
theorem contDiffOn_secondOrderODE
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {y : ℝ → E} {J : Set ℝ} {U : Set E}
    (hJ : IsOpen J) (hΓ : ContDiffOn ℝ ∞ Γ U)
    (hmem : ∀ t ∈ J, y t ∈ U)
    (hy₁ : ∀ t ∈ J, HasDerivAt y (deriv y t) t)
    (hy₂ : ∀ t ∈ J, HasDerivAt (deriv y) (-(Γ (y t) (deriv y t) (deriv y t))) t)
    (n : ℕ) :
    ContDiffOn ℝ n y J ∧ ContDiffOn ℝ n (deriv y) J := by
  have hdy : DifferentiableOn ℝ y J := fun t ht =>
    (hy₁ t ht).differentiableAt.differentiableWithinAt
  have hddy : DifferentiableOn ℝ (deriv y) J := fun t ht =>
    (hy₂ t ht).differentiableAt.differentiableWithinAt
  -- the second derivative *is* the right-hand side of the ODE, on `J`
  have hdd : ∀ t ∈ J, deriv (deriv y) t = -(Γ (y t) (deriv y t) (deriv y t)) :=
    fun t ht => (hy₂ t ht).deriv
  have hmaps : Set.MapsTo y J U := fun t ht => hmem t ht
  induction n with
  | zero =>
    exact ⟨contDiffOn_zero.mpr hdy.continuousOn, contDiffOn_zero.mpr hddy.continuousOn⟩
  | succ n ih =>
    obtain ⟨ihy, ihdy⟩ := ih
    have hΓn : ContDiffOn ℝ n Γ U := contDiffOn_infty.mp hΓ n
    -- `y″ = −Γ(y)(y′, y′)` is `C^n` on `J`
    have hrhs : ContDiffOn ℝ n (fun t => -(Γ (y t) (deriv y t) (deriv y t))) J :=
      (((hΓn.comp ihy hmaps).clm_apply ihdy).clm_apply ihdy).neg
    have hddy_n : ContDiffOn ℝ n (deriv (deriv y)) J := hrhs.congr hdd
    exact ⟨(contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨hdy, by simp, ihdy⟩,
      (contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨hddy, by simp, hddy_n⟩⟩

end Abstract

/-! ### Geodesics are smooth in every chart containing them -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **A geodesic solves the honest second-order ODE in a fixed chart.**
If `γ` is a geodesic at `t`, is continuous at `t`, and its foot lies in the source
of the chart at `β`, then the chart reading `y = φ_β ∘ γ` satisfies, at `t`,

`y″(t) = −Γ_β(y t)(y′ t, y′ t)`,

with `Γ_β = chartChristoffelBilin g β`.  This is `HasGeodesicEquationAt.solvesGeodesicODEAt`
(do Carmo) with the existential `a` of `SolvesGeodesicODEAt` identified as the
right-hand side, and the Christoffel contraction repackaged as the bilinear-map-valued
`chartChristoffelBilin`. -/
theorem hasDerivAt_deriv_chartReading_of_hasGeodesicEquationAt (g : RiemannianMetric I M)
    {γ : ℝ → M} {t : ℝ} {β : M}
    (hgeo : HasGeodesicEquationAt (I := I) g γ t) (hγc : ContinuousAt γ t)
    (hsrc : γ t ∈ (chartAt H β).source) :
    HasDerivAt (deriv (Geodesic.chartReading (I := I) β γ))
      (-(chartChristoffelBilin (I := I) g β
          (Geodesic.chartReading (I := I) β γ t)
          (deriv (Geodesic.chartReading (I := I) β γ) t)
          (deriv (Geodesic.chartReading (I := I) β γ) t))) t := by
  obtain ⟨-, a, ha, heq⟩ := hgeo.solvesGeodesicODEAt hγc hsrc
  have hΓ : chartChristoffelBilin (I := I) g β
      (Geodesic.chartReading (I := I) β γ t)
      (deriv (Geodesic.chartReading (I := I) β γ) t)
      (deriv (Geodesic.chartReading (I := I) β γ) t)
      = Geodesic.chartChristoffelContraction (I := I) g β
          (deriv (Geodesic.chartReading (I := I) β γ) t)
          (deriv (Geodesic.chartReading (I := I) β γ) t)
          (Geodesic.chartReading (I := I) β γ t) :=
    chartChristoffelBilin_apply (I := I) g β _ _ _
  rw [hΓ, ← eq_neg_of_add_eq_zero_left heq]
  exact ha

/-- **Math.** **A geodesic is `C^n` in any chart containing it.**  Let `J ⊆ ℝ` be
open, `γ` a geodesic on `J` with `γ(J) ⊆ (chartAt H β).source`.  Then the chart
reading `t ↦ φ_β(γ t)` is `C^n` on `J`, for every `n`.

This is `contDiffOn_secondOrderODE` applied to the real Levi-Civita chart data:
the coefficient `Γ_β = chartChristoffelBilin g β` is `C^∞` on the interior of the
chart target (`contDiffOn_chartChristoffelBilin`), which is the whole target since
`(extChartAt I β).target` is open, and the chart reading maps `J` there because
the foot lies in the chart source.

Only the *fixed* chart at `β` appears: the moving-foot geodesic equation is
transferred to it once and for all by `HasGeodesicEquationAt.solvesGeodesicODEAt`,
and the bootstrap then runs inside that single chart. -/
theorem contDiffOn_chartReading_of_isGeodesicOn (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} {β : M} (hJ : IsOpen J)
    (hgeo : IsGeodesicOn (I := I) g γ J)
    (hγc : ∀ t ∈ J, ContinuousAt γ t)
    (hsrc : ∀ t ∈ J, γ t ∈ (chartAt H β).source) (n : ℕ) :
    ContDiffOn ℝ n (Geodesic.chartReading (I := I) β γ) J := by
  have hmem : ∀ t ∈ J, Geodesic.chartReading (I := I) β γ t
      ∈ interior (extChartAt I β).target := by
    intro t ht
    rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
    exact (extChartAt I β).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  have hy₁ : ∀ t ∈ J, HasDerivAt (Geodesic.chartReading (I := I) β γ)
      (deriv (Geodesic.chartReading (I := I) β γ) t) t := by
    intro t ht
    exact ((hgeo t ht).solvesGeodesicODEAt (hγc t ht) (hsrc t ht)).1.self_of_nhds
  have hy₂ : ∀ t ∈ J, HasDerivAt (deriv (Geodesic.chartReading (I := I) β γ))
      (-(chartChristoffelBilin (I := I) g β
          (Geodesic.chartReading (I := I) β γ t)
          (deriv (Geodesic.chartReading (I := I) β γ) t)
          (deriv (Geodesic.chartReading (I := I) β γ) t))) t := fun t ht =>
    hasDerivAt_deriv_chartReading_of_hasGeodesicEquationAt g (hgeo t ht) (hγc t ht) (hsrc t ht)
  exact (contDiffOn_secondOrderODE hJ
    (contDiffOn_chartChristoffelBilin (I := I) g β) hmem hy₁ hy₂ n).1

/-- **Math.** The chart reading of a geodesic is `C^∞` on any open set of times
whose foot stays in the chart source. -/
theorem contDiffOn_chartReading_infty_of_isGeodesicOn (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} {β : M} (hJ : IsOpen J)
    (hgeo : IsGeodesicOn (I := I) g γ J)
    (hγc : ∀ t ∈ J, ContinuousAt γ t)
    (hsrc : ∀ t ∈ J, γ t ∈ (chartAt H β).source) :
    ContDiffOn ℝ ∞ (Geodesic.chartReading (I := I) β γ) J :=
  contDiffOn_infty.mpr fun n =>
    contDiffOn_chartReading_of_isGeodesicOn g hJ hgeo hγc hsrc n

/-- **Math.** The *velocity* of a geodesic, read in a fixed chart, is `C^n` on any
open set of times whose foot stays in the chart source.  (The `y′` half of the
bootstrap; `IsGeodesicOn.contDiffOn_chartReading` is the `y` half.) -/
theorem contDiffOn_deriv_chartReading_of_isGeodesicOn (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} {β : M} (hJ : IsOpen J)
    (hgeo : IsGeodesicOn (I := I) g γ J)
    (hγc : ∀ t ∈ J, ContinuousAt γ t)
    (hsrc : ∀ t ∈ J, γ t ∈ (chartAt H β).source) (n : ℕ) :
    ContDiffOn ℝ n (deriv (Geodesic.chartReading (I := I) β γ)) J := by
  have hmem : ∀ t ∈ J, Geodesic.chartReading (I := I) β γ t
      ∈ interior (extChartAt I β).target := by
    intro t ht
    rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
    exact (extChartAt I β).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  have hy₁ : ∀ t ∈ J, HasDerivAt (Geodesic.chartReading (I := I) β γ)
      (deriv (Geodesic.chartReading (I := I) β γ) t) t := by
    intro t ht
    exact ((hgeo t ht).solvesGeodesicODEAt (hγc t ht) (hsrc t ht)).1.self_of_nhds
  have hy₂ : ∀ t ∈ J, HasDerivAt (deriv (Geodesic.chartReading (I := I) β γ))
      (-(chartChristoffelBilin (I := I) g β
          (Geodesic.chartReading (I := I) β γ t)
          (deriv (Geodesic.chartReading (I := I) β γ) t)
          (deriv (Geodesic.chartReading (I := I) β γ) t))) t := fun t ht =>
    hasDerivAt_deriv_chartReading_of_hasGeodesicEquationAt g (hgeo t ht) (hγc t ht) (hsrc t ht)
  exact (contDiffOn_secondOrderODE hJ
    (contDiffOn_chartChristoffelBilin (I := I) g β) hmem hy₁ hy₂ n).2

end Manifold

/-! ### The junction curves of a broken variation are smooth in a chart -/

section Junction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **The junction curve of a broken variation is `C^n` in any chart.**
The broken variation of `prop:minimal-geodesic-no-conjugate` moves each partition
point `γ(τᵢ)` along the geodesic through it with initial velocity `Y(τᵢ)`; the
route correction of run 0115 is precisely that these junction curves must be
**geodesics**, so that each piece's second-variation boundary term vanishes inside
its own chart.

That junction curve is `s ↦ globalGeodesic g hg (γ τᵢ) (Y τᵢ) s` — no exponential
map and no homogeneity relation `exp_p(s·v) = γ_v(s)` is needed, because
`globalGeodesic p v` *is* the geodesic with `c(0) = p` and `c′(0) = v`, and
`expMapGlobal p v` is merely its value at `s = 1`.  Being a geodesic, its chart
reading is `C^n` wherever it stays in the chart source, by
`contDiffOn_chartReading_of_isGeodesicOn`.

This is what supplies the `ĉ₀`, `ĉ₁` arguments of `PoincareLib.chartVariation` at
the `C³` regularity that `deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`
demands. -/
theorem contDiffOn_chartReading_globalGeodesic (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) (v : TangentSpace I p)
    {β : M} {J : Set ℝ} (hJ : IsOpen J)
    (hsrc : ∀ s ∈ J, globalGeodesic (I := I) g hg p v s ∈ (chartAt H β).source)
    (n : ℕ) :
    ContDiffOn ℝ n
      (Geodesic.chartReading (I := I) β (globalGeodesic (I := I) g hg p v)) J :=
  contDiffOn_chartReading_of_isGeodesicOn g hJ
    (fun t _ => isGeodesic_globalGeodesic (I := I) g hg p v t)
    (fun _ _ => (continuous_globalGeodesic (I := I) g hg p v).continuousAt)
    hsrc n

/-- **Math.** The chart reading of a junction curve is `C^∞` on any open set of
parameters over which it stays in the chart source. -/
theorem contDiffOn_chartReading_globalGeodesic_infty (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) (v : TangentSpace I p)
    {β : M} {J : Set ℝ} (hJ : IsOpen J)
    (hsrc : ∀ s ∈ J, globalGeodesic (I := I) g hg p v s ∈ (chartAt H β).source) :
    ContDiffOn ℝ ∞
      (Geodesic.chartReading (I := I) β (globalGeodesic (I := I) g hg p v)) J :=
  contDiffOn_infty.mpr fun n =>
    contDiffOn_chartReading_globalGeodesic g hg p v hJ hsrc n

end Junction

end PoincareLib

end
