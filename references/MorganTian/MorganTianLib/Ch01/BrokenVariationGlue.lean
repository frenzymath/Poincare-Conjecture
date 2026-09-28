/-
Copyright (c) 2026 Archon Horizon. All rights reserved.
Released under Apache 2.0 license.
-/
import MorganTianLib.Ch01.BrokenEnergy

/-!
# Poincaré Ch. 1 — gluing a broken chart variation back into a manifold curve

This file supplies the missing bridge in Morgan–Tian's second-variation argument for
`prop:minimal-geodesic-no-conjugate` (half 2: *a minimizing geodesic has nonnegative index
form*).

## The problem

The geodesic `γ : [0, 1] → M` leaves every chart, so the competing variation is built **one
chart per piece** of a partition `0 = τ 0 < τ 1 < ⋯ < τ N = 1`: on the `i`-th piece the
variation is a family `u i : ℝ × ℝ → E` of maps into the *model space* `E`, read in the chart
at a basepoint `β i` (this is `chartVariation`, and it is what `PieceSecondVariation` computes
with).  The energy lower bound `d(p, q)² ≤ 2 E` (`sq_dist_le_sum_chart_energy`, in
`Ch01/BrokenEnergy.lean`) is, however, a statement about a **single curve `σ : ℝ → M`**.  So the
per-piece chart families must first be glued back into one manifold curve.

## The glue

* `pieceIdx τ N t = Nat.findGreatest (fun i => τ i ≤ t) (N - 1)` is the index of the piece that
  owns `t`: the largest `i ≤ N - 1` whose left endpoint is `≤ t`.  For a strictly increasing
  partition it is *exactly* `i` on `[τ i, τ (i+1))` (`pieceIdx_eq_of_mem_Ico`) and `N - 1` at
  the right endpoint `τ N` (`pieceIdx_last`); the right endpoint is the only point where the
  two neighbouring pieces disagree about ownership.

* `brokenPath β u τ N s t = (extChartAt I (β (pieceIdx τ N t))).symm (u (pieceIdx τ N t) (s, t))`
  reads the owning piece's chart family back into `M`.

* `brokenPath_eq_of_mem_Icc` is the heart: under the **junction hypothesis** `hjunc` — the two
  charts produce the *same manifold point* at a shared endpoint `τ (i+1)` — the glued path
  agrees with the `i`-th chart family on the whole **closed** piece `[τ i, τ (i+1)]`, not just on
  the half-open one.  This is precisely the content that makes a *broken* variation a genuine
  (continuous, piecewise-`C¹`) curve: the pieces are only required to match as points of `M`,
  never as points of `E` (the charts differ!).

Everything else is bookkeeping: the glued path lands in the `i`-th chart source
(`brokenPath_mem_source`), its chart reading *is* the chart family (`extChartAt_brokenPath`),
it is `C¹` on each piece (`contMDiffOn_brokenPath`), and its chart-derivative on a piece is the
ordinary derivative of the chart family (`derivWithin_extChartAt_brokenPath`, via the
`derivWithin`/`deriv` bridge `derivWithin_eq_deriv_of_eqOn_Icc`).

The payoff is `sq_dist_le_sum_chartFamily_energy`:

  `d(Φ_s(0), Φ_s(1))² ≤ ∑ᵢ ∫_{τ i}^{τ (i+1)} g_{u i(s,t)}(∂ₜ u i(s,t), ∂ₜ u i(s,t))`,

the energy lower bound stated **entirely in chart data** — the form in which the second
variation `d²/ds²` at `s = 0` can be applied to it.

Blueprint: `prop:minimal-geodesic-no-conjugate`, `claim:second-variation-minimal-geodesic`.
-/

open Set MeasureTheory
open scoped ContDiff Manifold Topology ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

/-! ## Step 1 — the piece index -/

/-- **Math.** The index of the partition piece `[τ i, τ (i+1)]` that owns the time `t`: the largest
`i ≤ N - 1` with `τ i ≤ t`.  Capping at `N - 1` makes the *last* piece own the right endpoint
`τ N` as well, so that `pieceIdx` is defined on the whole closed interval `[τ 0, τ N]`. -/
def pieceIdx (τ : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℕ :=
  Nat.findGreatest (fun i => τ i ≤ t) (N - 1)

/-- **Math.** For a strictly increasing partition, `pieceIdx` really computes the piece: on the
half-open piece `[τ i, τ (i+1))` with `i < N` it returns `i`.

Indeed `i` is a candidate for `Nat.findGreatest` (`τ i ≤ t` and `i ≤ N - 1`), and no larger
`j ≤ N - 1` is, because `τ j ≥ τ (i+1) > t` by monotonicity. -/
theorem pieceIdx_eq_of_mem_Ico {τ : ℕ → ℝ} {N : ℕ} (hmono : ∀ i, τ i < τ (i + 1))
    {i : ℕ} (hi : i < N) {t : ℝ} (ht : t ∈ Ico (τ i) (τ (i + 1))) :
    pieceIdx τ N t = i := by
  have hsm : StrictMono τ := strictMono_nat_of_lt_succ hmono
  rw [pieceIdx, Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => ht.1, ?_⟩
  intro j hij hjN hc
  have hle : τ (i + 1) ≤ τ j := hsm.monotone (by omega)
  have := ht.2
  linarith

/-- **Math.** At the right endpoint `τ N` of the partition the owning piece is the last one,
`N - 1`: it is a candidate (`τ (N-1) ≤ τ N`), and the cap `N - 1` leaves no larger one. -/
theorem pieceIdx_last {τ : ℕ → ℝ} {N : ℕ} (hmono : ∀ i, τ i < τ (i + 1)) (hN : 0 < N) :
    pieceIdx τ N (τ N) = N - 1 := by
  have hsm : StrictMono τ := strictMono_nat_of_lt_succ hmono
  rw [pieceIdx, Nat.findGreatest_eq_iff]
  refine ⟨le_rfl, fun _ => hsm.monotone (by omega), ?_⟩
  intro j hj hjN
  omega

/-! ## Step 2 — a `derivWithin`/`deriv` bridge on a closed interval -/

/-- **Math.** If `f` agrees with `h` on a nondegenerate closed interval and `h` is
differentiable at an interior-or-boundary point `t` of it, then the derivative of `f` *within*
the interval at `t` is the ordinary derivative of `h` at `t`.

Two ingredients: `derivWithin` only sees the values of `f` on the set (`derivWithin_congr`), and
a closed interval has the unique-differentiability property (`uniqueDiffOn_Icc`), so for a
function differentiable at `t` the `derivWithin` collapses to the `deriv`. -/
theorem derivWithin_eq_deriv_of_eqOn_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f h : ℝ → F} {a b : ℝ} (hab : a < b) (heq : EqOn f h (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) (hd : DifferentiableAt ℝ h t) :
    derivWithin f (Icc a b) t = deriv h t := by
  rw [derivWithin_congr heq (heq ht), hd.derivWithin (uniqueDiffOn_Icc hab t ht)]

/-! ## Step 3 — the glued path -/

section Manifold

open Riemannian Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** The **broken variation glued into `M`**.  On the piece owned by `t`
(index `pieceIdx τ N t`)
the chart family `u i : ℝ × ℝ → E` is read back into the manifold through the chart at `β i`.

This is a genuine curve in `M` for every fixed variation parameter `s`; it is *continuous across
a junction* exactly when the two neighbouring chart families agree there **as manifold points**
(hypothesis `hjunc` below), which is all one can ask since the two charts are different. -/
def brokenPath (β : ℕ → M) (u : ℕ → ℝ × ℝ → E) (τ : ℕ → ℝ) (N : ℕ) (s t : ℝ) : M :=
  (extChartAt I (β (pieceIdx τ N t))).symm (u (pieceIdx τ N t) (s, t))

variable {β : ℕ → M} {u : ℕ → ℝ × ℝ → E} {τ : ℕ → ℝ} {N : ℕ} {s : ℝ}

/-- **Math.** **The gluing lemma.**  Assume the chart families match at the junctions *as
manifold points*.  Then on the whole **closed** piece `[τ i, τ (i+1)]` the glued path is the
readback of the `i`-th chart family — even at the right endpoint, which `pieceIdx` assigns to the
*next* piece (or, for the last piece, to the last piece itself).

Proof.  If `t < τ (i+1)` then `pieceIdx τ N t = i` by `pieceIdx_eq_of_mem_Ico` and there is
nothing to do.  If `t = τ (i+1)` there are two cases.  When `i + 1 < N` the point is the left
endpoint of the next piece, so `pieceIdx τ N t = i + 1`, and the junction hypothesis says that
reading `u (i+1)` through the chart at `β (i+1)` gives the same manifold point as reading `u i`
through the chart at `β i`.  When `i + 1 = N` the point is the right endpoint of the partition,
which `pieceIdx` assigns to `N - 1 = i`. -/
theorem brokenPath_eq_of_mem_Icc (hmono : ∀ i, τ i < τ (i + 1)) (hN : 0 < N)
    (hjunc : ∀ i, i + 1 < N →
      (extChartAt I (β (i + 1))).symm (u (i + 1) (s, τ (i + 1)))
        = (extChartAt I (β i)).symm (u i (s, τ (i + 1))))
    {i : ℕ} (hi : i < N) {t : ℝ} (ht : t ∈ Icc (τ i) (τ (i + 1))) :
    brokenPath (I := I) β u τ N s t = (extChartAt I (β i)).symm (u i (s, t)) := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · rw [brokenPath, pieceIdx_eq_of_mem_Ico hmono hi ⟨ht.1, hlt⟩]
  · subst heq
    by_cases hi1 : i + 1 < N
    · have hpi : pieceIdx τ N (τ (i + 1)) = i + 1 :=
        pieceIdx_eq_of_mem_Ico hmono hi1 ⟨le_rfl, hmono (i + 1)⟩
      rw [brokenPath, hpi]
      exact hjunc i hi1
    · have hiN : i + 1 = N := by omega
      have hpi : pieceIdx τ N (τ (i + 1)) = i := by
        rw [hiN, pieceIdx_last hmono hN]
        omega
      rw [brokenPath, hpi]

/-- **Math.** On the `i`-th closed piece the glued path lies in the source of the `i`-th chart:
it is the image under `(extChartAt I (β i)).symm` of a point of the chart *target*. -/
theorem brokenPath_mem_source (hmono : ∀ i, τ i < τ (i + 1)) (hN : 0 < N)
    (hjunc : ∀ i, i + 1 < N →
      (extChartAt I (β (i + 1))).symm (u (i + 1) (s, τ (i + 1)))
        = (extChartAt I (β i)).symm (u i (s, τ (i + 1))))
    (hmem : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), u i (s, t) ∈ (extChartAt I (β i)).target)
    {i : ℕ} (hi : i < N) {t : ℝ} (ht : t ∈ Icc (τ i) (τ (i + 1))) :
    brokenPath (I := I) β u τ N s t ∈ (chartAt H (β i)).source := by
  rw [brokenPath_eq_of_mem_Icc hmono hN hjunc hi ht, ← extChartAt_source (I := I) (β i)]
  exact (extChartAt I (β i)).map_target (hmem i hi t ht)

/-- **Math.** On the `i`-th closed piece the chart-`β i` reading of the glued path is *literally*
the `i`-th chart family: the chart and its inverse cancel on the chart target
(`PartialEquiv.right_inv`). -/
theorem extChartAt_brokenPath (hmono : ∀ i, τ i < τ (i + 1)) (hN : 0 < N)
    (hjunc : ∀ i, i + 1 < N →
      (extChartAt I (β (i + 1))).symm (u (i + 1) (s, τ (i + 1)))
        = (extChartAt I (β i)).symm (u i (s, τ (i + 1))))
    (hmem : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), u i (s, t) ∈ (extChartAt I (β i)).target)
    {i : ℕ} (hi : i < N) {t : ℝ} (ht : t ∈ Icc (τ i) (τ (i + 1))) :
    extChartAt I (β i) (brokenPath (I := I) β u τ N s t) = u i (s, t) := by
  rw [brokenPath_eq_of_mem_Icc hmono hN hjunc hi ht]
  exact (extChartAt I (β i)).right_inv (hmem i hi t ht)

/-- **Math.** The glued path is `C¹` on each closed piece.  On the piece it *is* the composite
`(extChartAt I (β i)).symm ∘ (t ↦ u i (s, t))` of the (smooth) inverse chart with the (`C¹`)
chart family, which maps the piece into the chart target; `ContMDiffOn.congr` then transfers the
smoothness of the composite to `brokenPath` itself via the gluing lemma. -/
theorem contMDiffOn_brokenPath (hmono : ∀ i, τ i < τ (i + 1)) (hN : 0 < N)
    (hjunc : ∀ i, i + 1 < N →
      (extChartAt I (β (i + 1))).symm (u (i + 1) (s, τ (i + 1)))
        = (extChartAt I (β i)).symm (u i (s, τ (i + 1))))
    (hmem : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), u i (s, t) ∈ (extChartAt I (β i)).target)
    {i : ℕ} (hi : i < N)
    (hu : ContDiffOn ℝ 1 (fun t => u i (s, t)) (Icc (τ i) (τ (i + 1)))) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 (brokenPath (I := I) β u τ N s) (Icc (τ i) (τ (i + 1))) := by
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      ((extChartAt I (β i)).symm ∘ fun t => u i (s, t)) (Icc (τ i) (τ (i + 1))) :=
    ContMDiffOn.comp (contMDiffOn_extChartAt_symm (I := I) (n := 1) (β i)) hu.contMDiffOn
      fun t ht => hmem i hi t ht
  exact hcomp.congr fun t ht => brokenPath_eq_of_mem_Icc hmono hN hjunc hi ht

/-- **Math.** The chart derivative of the glued path along a piece is the ordinary time
derivative of the chart family: the two functions agree on the piece (`extChartAt_brokenPath`),
so their `derivWithin`s agree, and the chart family is differentiable, so its `derivWithin`
collapses to its `deriv`. -/
theorem derivWithin_extChartAt_brokenPath (hmono : ∀ i, τ i < τ (i + 1)) (hN : 0 < N)
    (hjunc : ∀ i, i + 1 < N →
      (extChartAt I (β (i + 1))).symm (u (i + 1) (s, τ (i + 1)))
        = (extChartAt I (β i)).symm (u i (s, τ (i + 1))))
    (hmem : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), u i (s, t) ∈ (extChartAt I (β i)).target)
    {i : ℕ} (hi : i < N) (hu : ContDiff ℝ 1 (fun t => u i (s, t)))
    {t : ℝ} (ht : t ∈ Icc (τ i) (τ (i + 1))) :
    derivWithin (fun r => extChartAt I (β i) (brokenPath (I := I) β u τ N s r))
        (Icc (τ i) (τ (i + 1))) t = deriv (fun r => u i (s, r)) t :=
  derivWithin_eq_deriv_of_eqOn_Icc (hmono i)
    (fun _r hr => extChartAt_brokenPath hmono hN hjunc hmem hi hr) ht
    ((hu.differentiable one_ne_zero).differentiableAt)

/-! ## Step 4 — the payoff: the energy lower bound in chart data -/

/-- **Math.** **`d(p, q)² ≤ 2 E` for a broken chart variation.**  Fix the variation parameter
`s`.  Let `u i : ℝ × ℝ → E` be the chart families of a broken variation over a strictly
increasing partition `0 = τ 0 < ⋯ < τ N = 1`, with basepoints `β i`, matching at the junctions as
manifold points (`hjunc`), staying in the chart targets (`hmem`), and `C¹` in time (`hu`).  Then
the squared distance between the two endpoints of the glued curve `Φ_s = brokenPath β u τ N s` is
at most its energy, written **purely in chart data**:

  `d(Φ_s 0, Φ_s 1)² ≤ ∑ᵢ ∫_{τ i}^{τ (i+1)} g_{u i(s,t)}(∂ₜ u i(s,t), ∂ₜ u i(s,t))`.

This is `sq_dist_le_sum_chart_energy` instantiated at the glued curve, with the manifold-side
integrand (`extChartAt ∘ σ` and its `derivWithin`) rewritten into chart-side data by
`extChartAt_brokenPath` and `derivWithin_extChartAt_brokenPath`.

It is the inequality that makes `s = 0` a *minimum* of `s ↦ E(Φ_s)` when the base curve is a
minimizing geodesic (both endpoints being fixed, the left-hand side is the constant `d(p, q)²`,
which the right-hand side attains at `s = 0`).  Hence `E″(0) ≥ 0`, hence `I(V, V) ≥ 0` — the
nonnegativity of the index form of a minimizing geodesic. -/
theorem sq_dist_le_sum_chartFamily_energy
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (hmono : ∀ i, τ i < τ (i + 1)) (hN : 0 < N) (hτ0 : τ 0 = 0) (hτN : τ N = 1)
    (hjunc : ∀ i, i + 1 < N →
      (extChartAt I (β (i + 1))).symm (u (i + 1) (s, τ (i + 1)))
        = (extChartAt I (β i)).symm (u i (s, τ (i + 1))))
    (hmem : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), u i (s, t) ∈ (extChartAt I (β i)).target)
    (hu : ∀ i < N, ContDiff ℝ 1 (fun t => u i (s, t))) :
    dist (brokenPath (I := I) β u τ N s 0) (brokenPath (I := I) β u τ N s 1) ^ 2
      ≤ ∑ i ∈ Finset.range N,
          ∫ t in (τ i)..(τ (i + 1)),
            chartMetricInner (I := I) g (β i) (u i (s, t))
              (deriv (fun r => u i (s, r)) t) (deriv (fun r => u i (s, r)) t) := by
  set σ : ℝ → M := brokenPath (I := I) β u τ N s with hσdef
  have hτle : ∀ i < N, τ i ≤ τ (i + 1) := fun i _ => (hmono i).le
  have hσC : ∀ i < N, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1))) := fun i hi =>
    contMDiffOn_brokenPath hmono hN hjunc hmem hi (hu i hi).contDiffOn
  have hsrc : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), σ t ∈ (chartAt H (β i)).source :=
    fun i hi t ht => brokenPath_mem_source hmono hN hjunc hmem hi ht
  have key := sq_dist_le_sum_chart_energy g hg hτle hτ0 hτN hσC hsrc
  refine key.trans (le_of_eq (Finset.sum_congr rfl ?_))
  intro i hi
  have hi' := Finset.mem_range.mp hi
  refine intervalIntegral.integral_congr ?_
  intro t ht
  rw [uIcc_of_le (hτle i hi')] at ht
  simp only
  rw [extChartAt_brokenPath hmono hN hjunc hmem hi' ht,
    derivWithin_extChartAt_brokenPath hmono hN hjunc hmem hi' (hu i hi') ht]

end Manifold

end MorganTianLib

#print axioms MorganTianLib.pieceIdx_eq_of_mem_Ico
#print axioms MorganTianLib.pieceIdx_last
#print axioms MorganTianLib.derivWithin_eq_deriv_of_eqOn_Icc
#print axioms MorganTianLib.brokenPath_eq_of_mem_Icc
#print axioms MorganTianLib.brokenPath_mem_source
#print axioms MorganTianLib.extChartAt_brokenPath
#print axioms MorganTianLib.contMDiffOn_brokenPath
#print axioms MorganTianLib.derivWithin_extChartAt_brokenPath
#print axioms MorganTianLib.sq_dist_le_sum_chartFamily_energy

end
