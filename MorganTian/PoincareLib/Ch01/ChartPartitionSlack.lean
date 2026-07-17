/-
Copyright (c) 2026 Archon Horizon. All rights reserved.
Released under Apache 2.0 license.
-/
import PoincareLib.Ch01.JacobiChartTransfer

/-!
# Poincaré Ch. 1, §1.4 — smoothness of the chart reading, and a chart partition with slack

Two pieces of infrastructure needed by the broken second variation.

## (1) Smoothness of `chartVectorRep`

`chartVectorRep γ α J τ = tangentCoordChange I (γ τ) α (γ τ) (J τ)` is the reading, in the
chart at the fixed basepoint `α`, of a field `J` of tangent vectors carried along `γ` at their
own feet.  There is *no* unconditional regularity for it: the `E`-representative `J τ` of a
tangent vector at `γ τ` is taken in the **preferred chart at `γ τ`**, which jumps as `τ` moves,
so `J` alone carries no analytic information.  What *is* true — and is what every consumer
actually has — is that the readings in two charts differ by the derivative of the (smooth)
transition map at the moving foot:

  `chartVectorRep γ α J τ = Dτ_{βα}( x̂_β(τ) ) ( chartVectorRep γ β J τ )`,

by `tangentCoordChange_comp`.  Hence `contDiffOn_chartVectorRep`: **if the reading of the field
in one chart `β` is `C^n`, and the chart-`β` reading of the curve is `C^n`, and the curve stays
in both chart sources, then the reading in any other chart `α` is `C^n`.**  The analytic content
is `contDiffOn_fderiv_chartTransition`: the derivative of the chart transition is `C^∞` on the
(open) overlap, since the transition itself is (`contDiffOn_chartTransition`).

## (2) A chart partition with slack

`exists_geodesic_chart_partition` (`Ch01/ChartPartition.lean`) partitions `[0,1]` so that each
*closed* piece lands in one chart source.  The piece second-variation lemma
(`deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`) needs strictly more: an **open box**
`Ioo (-r) r ×ˢ Ioo (τᵢ - r) (τᵢ₊₁ + r)` mapping into an open `U ⊆ E` (openness is load-bearing
for the `C^∞` bootstrap and for `contDiffOn_succ_iff_deriv_of_isOpen`), and `τᵢ ≠ τᵢ₊₁` (which
`chartVariation` requires).  `exists_chart_partition_slack` produces a **strictly increasing**
partition together with a single slack radius `r > 0` such that even the *enlarged closed*
interval `[τᵢ - r, τᵢ₊₁ + r]` is carried by `γ` into the `i`-th chart source (hence its chart
image into the open chart target `U = (extChartAt I αᵢ).target`).  The engine is the Lebesgue
number of the open cover of the compact interval by the `γ`-preimages of the chart sources: a
uniform grid of mesh `< δ/4` with slack `δ/4` keeps every enlarged piece inside a `δ`-ball.
-/

open Set Metric Riemannian
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### (1) Smoothness of the chart reading of a field along a curve -/

section Smooth

variable [I.Boundaryless]

/-- **Math.** The derivative of the chart transition `τ_{βα} = φ_α ∘ φ_β⁻¹` is `C^n` (indeed
`C^∞`) on the open overlap of the two charts: the transition itself is `C^∞` there
(`contDiffOn_chartTransition`), and differentiating a `C^∞` map on an open set loses one
derivative only. -/
theorem contDiffOn_fderiv_chartTransition (β α : M) (n : ℕ) :
    ContDiffOn ℝ n (fun y => fderiv ℝ (chartTransition (I := I) β α) y)
      (chartTransitionSource (I := I) (M := M) β α) := by
  have hopen : IsOpen (chartTransitionSource (I := I) (M := M) β α) :=
    isOpen_chartTransitionSource (I := I) β α
  have hle : ((n : WithTop ℕ∞) + 1) ≤ ∞ := by
    exact_mod_cast le_top (α := ℕ∞) (a := (n : ℕ∞) + 1)
  exact (contDiffOn_chartTransition (I := I) β α).fderiv_of_isOpen hopen hle

/-- **Math.** **Smoothness of the chart reading of a field along a curve.**
Let `J` be a field of tangent vectors along `γ` (each `J τ` an `E`-representative of a vector at
`γ τ`).  Its readings in two charts `β`, `α` containing the curve are related by the derivative
of the chart transition at the moving foot,
`chartVectorRep γ α J τ = Dτ_{βα}(φ_β(γ τ)) (chartVectorRep γ β J τ)`.
Since the transition derivative is `C^∞` on the overlap, the chart-`α` reading is as smooth as
the chart-`β` reading and the chart-`β` reading of the curve.

The hypotheses are exactly the data a consumer has: a chart `β` in which the field is *given*
(e.g. the solution of the chart Jacobi ODE, cf. `IsJacobiFieldOn` / `JacobiExistence`, whose
chart-`β` reading is literally that solution), the `C^n` chart reading of the geodesic, and the
fact that the piece of the curve lies in both chart sources.  No regularity of `J` itself is
assumed — none is available, since the `E`-representative of `J τ` is taken in the preferred
chart at `γ τ`, which jumps with `τ`. -/
theorem contDiffOn_chartVectorRep {n : ℕ} {γ : ℝ → M} {J : ℝ → E} {α β : M} {s : Set ℝ}
    (hsrcβ : ∀ τ ∈ s, γ τ ∈ (chartAt H β).source)
    (hsrcα : ∀ τ ∈ s, γ τ ∈ (chartAt H α).source)
    (hu : ContDiffOn ℝ n (fun τ => extChartAt I β (γ τ)) s)
    (hJβ : ContDiffOn ℝ n (chartVectorRep (I := I) γ β J) s) :
    ContDiffOn ℝ n (chartVectorRep (I := I) γ α J) s := by
  have hmaps : MapsTo (fun τ => extChartAt I β (γ τ)) s
      (chartTransitionSource (I := I) (M := M) β α) := fun τ hτ =>
    extChartAt_mem_chartTransitionSource (I := I) (hsrcβ τ hτ) (hsrcα τ hτ)
  have hA : ContDiffOn ℝ n
      (fun τ => fderiv ℝ (chartTransition (I := I) β α) (extChartAt I β (γ τ))) s :=
    (contDiffOn_fderiv_chartTransition (I := I) β α n).comp hu hmaps
  refine (hA.clm_apply hJβ).congr ?_
  intro τ hτ
  have hxβ : γ τ ∈ (chartAt H β).source := hsrcβ τ hτ
  have hxα : γ τ ∈ (chartAt H α).source := hsrcα τ hτ
  have hxβ' : γ τ ∈ (extChartAt I β).source := by rw [extChartAt_source]; exact hxβ
  have hxα' : γ τ ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hxα
  have hfd : fderiv ℝ (chartTransition (I := I) β α) (extChartAt I β (γ τ))
      = tangentCoordChange I β α (γ τ) := by
    rw [fderiv_chartTransition (I := I) (hmaps hτ),
      (extChartAt I β).left_inv hxβ']
  have hcomp : tangentCoordChange I β α (γ τ)
      (tangentCoordChange I (γ τ) β (γ τ) (J τ))
      = tangentCoordChange I (γ τ) α (γ τ) (J τ) :=
    tangentCoordChange_comp (I := I)
      ⟨⟨mem_extChartAt_source (I := I) (γ τ), hxβ'⟩, hxα'⟩
  show chartVectorRep (I := I) γ α J τ
      = fderiv ℝ (chartTransition (I := I) β α) (extChartAt I β (γ τ))
          (chartVectorRep (I := I) γ β J τ)
  rw [hfd, chartVectorRep_apply, chartVectorRep_apply, hcomp]

end Smooth

/-! ### (2) The chart partition with slack -/

/-- **Math.** **Chart partition with slack.** Let `γ` be continuous on an open set `O ⊆ ℝ`
containing the compact interval `[a, b]`, `a < b` (in the application: a geodesic, continuous on
all of `ℝ`, and `[a, b]` the parameter interval of the variation).  Then there is a **strictly
increasing** uniform partition `a = τ 0 < τ 1 < ⋯ < τ N = b` of `[a, b]`, a choice of chart
centres `α i`, and a single **slack radius** `r > 0` such that for each piece `i < N` the
*enlarged closed* interval `[τ i - r, τ (i+1) + r]` still lies in `O` and is carried by `γ` into
the source of the chart at `α i` (hence its chart image lies in the chart target).

Strict monotonicity gives `τ i ≠ τ (i+1)` for free — the hypothesis `chartVariation` needs —
and the slack `r` gives the *open* box `Ioo (τ i - r) (τ (i+1) + r)` in the time direction
required by the piece second variation.

The proof is the Lebesgue number `δ` of the open cover of `[a, b]` by the `γ`-preimages
`O ∩ γ⁻¹((chartAt H x).source)` of the chart sources: a uniform grid of mesh `(b - a)/N < δ/4`
with slack `r = δ/4` keeps every enlarged piece `[τ i - r, τ (i+1) + r]` inside the `δ`-ball
around `τ i`, hence inside one member of the cover. -/
theorem exists_chart_partition_slack {γ : ℝ → M} {O : Set ℝ} {a b : ℝ}
    (hab : a < b) (hO : IsOpen O) (hKO : Icc a b ⊆ O) (hγ : ContinuousOn γ O) :
    ∃ (N : ℕ) (τ : ℕ → ℝ) (α : ℕ → M) (r : ℝ),
      0 < N ∧ 0 < r ∧ τ 0 = a ∧ τ N = b ∧
      (∀ i, τ i < τ (i + 1)) ∧
      (∀ i ≤ N, τ i ∈ Icc a b) ∧
      (∀ i < N, ∀ t ∈ Icc (τ i - r) (τ (i + 1) + r),
        t ∈ O ∧ γ t ∈ (chartAt H (α i)).source ∧
          extChartAt I (α i) (γ t) ∈ (extChartAt I (α i)).target) := by
  classical
  have hMne : Nonempty M := ⟨γ a⟩
  -- the open cover of `[a, b]` by the preimages of the chart sources
  set c : M → Set ℝ := fun x => O ∩ γ ⁻¹' (chartAt H x).source with hc
  have hcopen : ∀ x : M, IsOpen (c x) := fun x =>
    hγ.isOpen_inter_preimage hO (chartAt H x).open_source
  have hcover : Icc a b ⊆ ⋃ x : M, c x := fun t ht =>
    mem_iUnion.2 ⟨γ t, hKO ht, mem_chart_source H (γ t)⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hcopen hcover
  -- a grid of mesh `< δ/4`
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (b - a) / δ)
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero] at hN
      have hpos : 0 < 4 * (b - a) / δ := by positivity
      linarith
    · exact h0
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  set h : ℝ := (b - a) / N with hh
  have hhpos : 0 < h := by rw [hh]; positivity
  have hNb : (N : ℝ) * h = b - a := by rw [hh]; field_simp
  have hhδ : h < δ / 4 := by
    have h4 : 4 * (b - a) < δ * N := by
      have := (div_lt_iff₀ hδ).mp hN
      linarith
    rw [hh, div_lt_iff₀ hNR]
    nlinarith [h4]
  set τ : ℕ → ℝ := fun i => a + i * h with hτdef
  set r : ℝ := δ / 4 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hτ0 : τ 0 = a := by simp [hτdef]
  have hτN : τ N = b := by
    simp only [hτdef]
    linarith [hNb]
  have hτmono : ∀ i, τ i < τ (i + 1) := by
    intro i
    simp only [hτdef]
    push_cast
    nlinarith [hhpos]
  have hτmem : ∀ i ≤ N, τ i ∈ Icc a b := by
    intro i hi
    have hiR : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    constructor
    · have : 0 ≤ (i : ℝ) * h := by positivity
      simp only [hτdef]; linarith
    · have : (i : ℝ) * h ≤ (N : ℝ) * h := by nlinarith [hhpos]
      simp only [hτdef]; linarith
  -- for each piece, a chart whose `δ`-ball certificate covers the enlarged piece
  have hex : ∀ i : ℕ, ∃ x : M, i < N → ball (τ i) δ ⊆ c x := by
    intro i
    by_cases hi : i < N
    · obtain ⟨x, hx⟩ := hball (τ i) (hτmem i hi.le)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨Classical.arbitrary M, fun hc => absurd hc hi⟩
  choose α hα using hex
  refine ⟨N, τ, α, r, hNpos, hrpos, hτ0, hτN, hτmono, hτmem, ?_⟩
  intro i hi t ht
  -- the enlarged piece sits in the `δ`-ball around `τ i`
  have hstep : τ (i + 1) = τ i + h := by
    simp only [hτdef]; push_cast; ring
  have htball : t ∈ ball (τ i) δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    obtain ⟨ht1, ht2⟩ := ht
    rw [hstep] at ht2
    constructor
    · rw [hr] at ht1; linarith
    · rw [hr] at ht2; linarith
  have hmem : t ∈ c (α i) := hα i hi htball
  refine ⟨hmem.1, hmem.2, ?_⟩
  exact (extChartAt I (α i)).map_source (by rw [extChartAt_source]; exact hmem.2)

/-- **Math.** The form of the chart partition with slack that the piece second variation
consumes: a strictly increasing partition (so `τ i ≠ τ (i+1)`, the hypothesis of
`chartVariation`) together with a slack `r > 0` such that `γ` carries the **open** enlarged
interval `Ioo (τ i - r) (τ (i+1) + r)` into the `i`-th chart source and its chart reading into
the **interior** of the (extended) chart target — which, the model being boundaryless, is the
open set `U = (extChartAt I (α i)).target` on which the chart metric and Christoffel data are
smooth and metric-compatible. -/
theorem exists_chart_partition_slack_interior [I.Boundaryless] {γ : ℝ → M} {O : Set ℝ} {a b : ℝ}
    (hab : a < b) (hO : IsOpen O) (hKO : Icc a b ⊆ O) (hγ : ContinuousOn γ O) :
    ∃ (N : ℕ) (τ : ℕ → ℝ) (α : ℕ → M) (r : ℝ),
      0 < N ∧ 0 < r ∧ τ 0 = a ∧ τ N = b ∧
      (∀ i, τ i ≠ τ (i + 1)) ∧ (∀ i, τ i < τ (i + 1)) ∧
      (∀ i ≤ N, τ i ∈ Icc a b) ∧
      (∀ i < N, IsOpen (extChartAt I (α i)).target) ∧
      (∀ i < N, ∀ t ∈ Ioo (τ i - r) (τ (i + 1) + r),
        t ∈ O ∧ γ t ∈ (chartAt H (α i)).source ∧
          extChartAt I (α i) (γ t) ∈ interior (extChartAt I (α i)).target) := by
  obtain ⟨N, τ, α, r, hN, hr, hτ0, hτN, hmono, hmem, hpiece⟩ :=
    exists_chart_partition_slack (I := I) hab hO hKO hγ
  refine ⟨N, τ, α, r, hN, hr, hτ0, hτN, fun i => (hmono i).ne, hmono, hmem,
    fun i _ => isOpen_extChartAt_target (α i), ?_⟩
  intro i hi t ht
  obtain ⟨hO', hsrc, htgt⟩ := hpiece i hi t (Ioo_subset_Icc_self ht)
  exact ⟨hO', hsrc, by rwa [(isOpen_extChartAt_target (I := I) (α i)).interior_eq]⟩

end PoincareLib

#print axioms PoincareLib.contDiffOn_fderiv_chartTransition
#print axioms PoincareLib.contDiffOn_chartVectorRep
#print axioms PoincareLib.exists_chart_partition_slack
#print axioms PoincareLib.exists_chart_partition_slack_interior

end
