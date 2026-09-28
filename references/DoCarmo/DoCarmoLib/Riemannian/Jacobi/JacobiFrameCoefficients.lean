import DoCarmoLib.Riemannian.Jacobi.JacobiSectionalCurvature
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality
import DoCarmoLib.Riemannian.Jacobi.JacobiField

/-!
# The chart Jacobi field read in a parallel orthonormal frame (do Carmo `def:dc-ch5-2-1`)

This file supplies the **chart ↔ frame-coefficient bridge**: it turns the geometric
chart Jacobi pair system `IsJacobiFieldOn` (`∇J = DJ`, `∇DJ = −ℛ(J, u̇)u̇`, of
`Jacobi/PairJacobiField.lean`) into the *scalar* second-order system
`IsJacobiPairOn (jacobiCoefOp …)` (`Jacobi/JacobiEquationODE.lean`) solved by the
coefficients of `J` in a parallel orthonormal frame.

This is do Carmo's move in `def:dc-ch5-2-1` and in the proof of `thm:dc-ch8-2-1`
(E. Cartan): *writing `J(t) = Σᵢ yᵢ(t)eᵢ(t)` along a parallel orthonormal frame, the
Jacobi equation becomes `yⱼ'' + Σᵢ⟨R(eₙ,eᵢ)eₙ,eⱼ⟩yᵢ = 0`.*  Both halves are pure
**metric compatibility** (`hasDerivAt_chartMetricInner_along`) read against a frame with
`∇eⱼ = 0`, so that `d/dt⟨X, eⱼ⟩ = ⟨∇X, eⱼ⟩`:

* `F' = V` is `d/dt⟨J, eⱼ⟩ = ⟨∇J, eⱼ⟩ = ⟨DJ, eⱼ⟩`;
* `V' = −A(t) F` is `d/dt⟨DJ, eⱼ⟩ = ⟨∇DJ, eⱼ⟩ = −⟨ℛ(J,u̇)u̇, eⱼ⟩`, expanded through
  `J = Σᵢ Fᵢ eᵢ` (`frameExpansion`) and the linearity of the curvature operator
  (`chartMetricInner_map_frameCombination_left`).

Before this file the two theories were disjoint: nothing in `DoCarmoLib` discharged the
`IsJacobiPairOn (jacobiCoefOp …)` hypothesis of `ChartCurvatureContraction`'s
`jacobiField_eqOn` / `frameJacobi_ne_zero_of_nonpos`, which were consequently unreachable.

## Main results

* `Riemannian.Jacobi.frameCoeff` — the frame coefficient `Fᵢ(t) = ⟨X(t), eᵢ(t)⟩`
  (do Carmo's `yᵢ`), with `frameCoeff_apply`.
* `Riemannian.Jacobi.hasDerivAt_frameCoeff` — metric compatibility in a parallel frame:
  `d/dt⟨X, eⱼ⟩ = ⟨∇X, eⱼ⟩`.
* `Riemannian.Jacobi.isJacobiPairOn_of_isJacobiFieldOn` — **the bridge**: the frame
  coefficients of an `IsJacobiFieldOn` form an `IsJacobiPairOn` for `jacobiCoefOp`.

The window hypothesis `Icc a b ⊆ Ioo a' b'` is what upgrades the one-sided
`HasDerivWithinAt` data of `IsJacobiFieldOn` to the two-sided derivatives metric
compatibility consumes: every `t ∈ [a,b]` is an interior time of the window `[a',b']`.

A second section then uses the bridge to transfer the Jacobi norm between two manifolds
under do Carmo's `thm:dc-ch8-2-1` curvature hypothesis, **without** constant curvature:

* `Riemannian.Jacobi.IsJacobiPairOn.congr_coeff` — the pair system only reads its
  coefficient on `[a,b]`.
* `Riemannian.Jacobi.jacobiCoefOp_congr` — matching curvature coefficients `aᵢⱼ(t)` give
  literally the same scalar operator on `ι → ℝ`; this is where the curvature hypothesis
  of `thm:dc-ch8-2-1` is consumed.
* `Riemannian.Jacobi.chartMetricInner_frameCombination_self` /
  `Riemannian.Jacobi.chartMetricInner_self_eq_sum_frameCoeff_sq` — orthonormal extraction
  of the norm, `|X|² = Σᵢ Fᵢ²`.
* `Riemannian.Jacobi.chartMetricInner_transfer_of_jacobiCoef_match` — **the Cartan Jacobi
  norm transfer** in variable curvature: matching curvature coefficients plus matching
  initial data give `|J̃(t)| = |J(t)|`.

Blueprint: `def:dc-ch5-2-1`, `lem:dc-ch5-2-1-frame-reduction`, `thm:dc-ch8-2-1`.
-/

open Set
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

-- NOTE: this variable block must mirror `Jacobi/JacobiSectionalCurvature.lean` exactly
-- (`MetricSpace M`, and `CompleteSpace E` left to instance search via finite-dimensionality):
-- `chartCurvatureOp_eq_chartCurvature` is stated there, and any divergence makes its
-- instances diamond against ours and sends `isDefEq` into a heartbeat timeout.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Math.** The frame coefficients `Fᵢ(t) = ⟨X(t), eᵢ(t)⟩` of a coordinate field `X`
along `u`, read against the frame `e` in the chart at `α` (do Carmo's `yᵢ` in
`J(t) = Σᵢ yᵢ(t)eᵢ(t)`). -/
def frameCoeff (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (e : ι → ℝ → E)
    (X : ℝ → E) (t : ℝ) (i : ι) : ℝ :=
  chartMetricInner (I := I) g α (u t) (X t) (e i t)

@[simp] theorem frameCoeff_apply (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (e : ι → ℝ → E) (X : ℝ → E) (t : ℝ) (i : ι) :
    frameCoeff (I := I) g α u e X t i
      = chartMetricInner (I := I) g α (u t) (X t) (e i t) := rfl

/-- **Math.** Metric compatibility, read in a parallel frame: the derivative of the
frame coefficient `⟨X, eⱼ⟩` is the frame coefficient of the covariant derivative,
`d/dt⟨X, eⱼ⟩ = ⟨∇X, eⱼ⟩`, because `∇eⱼ = 0`. -/
theorem hasDerivAt_frameCoeff (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (e : ι → ℝ → E) (X : ℝ → E) {t : ℝ} (j : ι)
    (hu : DifferentiableAt ℝ u t) (hX : DifferentiableAt ℝ X t)
    (he : DifferentiableAt ℝ (e j) t)
    (hG : ∀ p q, DifferentiableAt ℝ (chartGramOnE (I := I) g α p q) (u t))
    (hbase : (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hpar : covariantDerivCoord (I := I) g α u (e j) t = 0) :
    HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) (X s) (e j s))
      (chartMetricInner (I := I) g α (u t) (covariantDerivCoord (I := I) g α u X t) (e j t)) t := by
  have hraw := hasDerivAt_chartMetricInner_along (I := I) g α u X (e j) hu hX he hG hbase
  rw [hpar, chartMetricInner_zero_right, add_zero] at hraw
  exact hraw

/-- **Math.** **The chart ↔ frame-coefficient bridge** for do Carmo's Jacobi field
(`def:dc-ch5-2-1`, the reduction used in `thm:dc-ch8-2-1`).

Let `(J, DJ)` solve the chart Jacobi pair system on a window `[a', b']`
(`IsJacobiFieldOn`: `∇J = DJ`, `∇DJ = −ℛ(J, u̇)u̇`), and let `e` be a parallel
orthonormal frame along the chart curve `u`.  Then the frame coefficients
`Fᵢ = ⟨J, eᵢ⟩`, `Vᵢ = ⟨DJ, eᵢ⟩` solve do Carmo's scalar second-order system
`F' = V`, `V' = −A(t) F` on any `[a, b]` interior to the window — i.e. they form an
`IsJacobiPairOn` for the coefficient operator `jacobiCoefOp`.

This is do Carmo's *"writing `J(t) = Σᵢ yᵢ(t)eᵢ(t)`, the Jacobi equation gives
`yⱼ'' + Σᵢ⟨R(eₙ,eᵢ)eₙ,eⱼ⟩yᵢ = 0`"* — the step that lets the intrinsic Jacobi field be
compared through the abstract ODE uniqueness theory of `JacobiEquationODE`.

The window hypothesis `hsub : Icc a b ⊆ Ioo a' b'` is what upgrades the one-sided
`HasDerivWithinAt` data of `IsJacobiFieldOn` to the two-sided derivatives that metric
compatibility (`hasDerivAt_chartMetricInner_along`) consumes: every `t ∈ [a,b]` is an
*interior* time of the window. -/
theorem isJacobiPairOn_of_isJacobiFieldOn (g : RiemannianMetric I M) (α : M)
    (u J DJ : ℝ → E) (e : ι → ℝ → E) {a b a' b' : ℝ}
    (hsub : Icc a b ⊆ Ioo a' b')
    (hJF : IsJacobiFieldOn (I := I) g α u J DJ a' b')
    (hu : ∀ t ∈ Icc a b, DifferentiableAt ℝ u t)
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target)
    (hG : ∀ t ∈ Icc a b, ∀ p q, DifferentiableAt ℝ (chartGramOnE (I := I) g α p q) (u t))
    (hbase : ∀ t ∈ Icc a b,
      (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (he : ∀ i, ∀ t ∈ Icc a b, DifferentiableAt ℝ (e i) t)
    (hepar : ∀ i, ∀ t ∈ Icc a b, covariantDerivCoord (I := I) g α u (e i) t = 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      chartMetricInner (I := I) g α (u t) (e i t) (e j t) = if i = j then (1 : ℝ) else 0) :
    IsJacobiPairOn (jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e) a b
      (frameCoeff (I := I) g α u e J) (frameCoeff (I := I) g α u e DJ) := by
  classical
  constructor
  · -- `F' = V`: `d/dt⟨J, eⱼ⟩ = ⟨∇J, eⱼ⟩ = ⟨DJ, eⱼ⟩`.
    intro t ht
    rw [hasDerivWithinAt_pi]
    intro j
    have hJd : DifferentiableAt ℝ J t :=
      ((hJF.hasDerivWithinAt_fst t (Ioo_subset_Icc_self (hsub ht))).hasDerivAt
        (Icc_mem_nhds (hsub ht).1 (hsub ht).2)).differentiableAt
    have hraw := hasDerivAt_frameCoeff (I := I) g α u e J j (hu t ht) hJd (he j t ht)
      (hG t ht) (hbase t ht) (hepar j t ht)
    rw [hJF.covariantDerivCoord_fst (hsub ht)] at hraw
    exact hraw.hasDerivWithinAt
  · -- `V' = −A(t) F`: `d/dt⟨DJ, eⱼ⟩ = ⟨∇DJ, eⱼ⟩ = −⟨ℛ(J,u̇)u̇, eⱼ⟩ = −Σᵢ aᵢⱼ Fᵢ`.
    intro t ht
    rw [hasDerivWithinAt_pi]
    intro j
    have hDJd : DifferentiableAt ℝ DJ t :=
      ((hJF.hasDerivWithinAt_snd t (Ioo_subset_Icc_self (hsub ht))).hasDerivAt
        (Icc_mem_nhds (hsub ht).1 (hsub ht).2)).differentiableAt
    have hraw := hasDerivAt_frameCoeff (I := I) g α u e DJ j (hu t ht) hDJd (he j t ht)
      (hG t ht) (hbase t ht) (hepar j t ht)
    rw [hJF.covariantDerivCoord_snd (hsub ht)] at hraw
    -- identify `−⟨ℛ(J,u̇)u̇, eⱼ⟩` with `−(A t (F t)) j`
    have hcurv : chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t)
        = chartCurvatureOp (I := I) g α u t (J t) :=
      (chartCurvatureOp_eq_chartCurvature (I := I) g α u t (J t) (hmem t ht)).symm
    have hexp : J t = ∑ i, chartMetricInner (I := I) g α (u t) (J t) (e i t) • e i t :=
      frameExpansion (I := I) g α (u t) (fun i => e i t) hcard (horth t ht) (J t)
    have hval : chartMetricInner (I := I) g α (u t)
        (-(chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t))) (e j t)
        = -(jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e t
            (frameCoeff (I := I) g α u e J t)) j := by
      rw [chartMetricInner_neg_left, hcurv]
      congr 1
      rw [jacobiCoefOp_apply]
      conv_lhs => rw [hexp]
      rw [chartMetricInner_map_frameCombination_left]
      exact Finset.sum_congr rfl fun i _ => by rw [jacobiCoef, frameCoeff_apply]; ring
    rw [hval] at hraw
    exact hraw.hasDerivWithinAt

/-! ## Transfer of the Jacobi norm under matching curvature coefficients

do Carmo's `thm:dc-ch8-2-1` compares `J` on `M` with `J̃ = φ_t(J)` on `M̃`.  Once both
are read in parallel orthonormal frames, the curvature hypothesis says exactly that the
two coefficient matrices `aᵢⱼ = ⟨R(eₙ,eᵢ)eₙ,eⱼ⟩` agree, hence the two scalar systems are
*the same ODE*; equal initial data then forces equal coefficients, and orthonormality
turns that into equality of the norms `|J̃(t)| = |J(t)|`.

This is the variable-curvature replacement for the closed-form route of
`Jacobi/JacobiConstCurvatureNorm.lean`, whose `metricInner_jacobiField_eq_of_constantCurvature_of_speedSq`
solves `|J(t)|²` in closed form and therefore cannot generalize. -/

section Transfer

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
variable {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-- **Math.** The Jacobi pair system only reads its coefficient on `[a,b]`, so two
coefficient fields agreeing there have the same solutions. -/
theorem IsJacobiPairOn.congr_coeff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A B : ℝ → F →L[ℝ] F} {a b : ℝ} {f v : ℝ → F}
    (h : IsJacobiPairOn A a b f v) (hAB : ∀ t ∈ Icc a b, A t = B t) :
    IsJacobiPairOn B a b f v := by
  refine ⟨h.1, fun t ht => ?_⟩
  rw [← hAB t ht]
  exact h.2 t ht

/-- **Math.** The coefficient operator `A(t)` is determined by the curvature coefficients
`aᵢⱼ(t)`: if two (possibly different) manifolds present the same `aᵢⱼ(t)` in their
respective frames, their scalar systems are literally the same operator on `ι → ℝ`.
This is where do Carmo's curvature hypothesis of `thm:dc-ch8-2-1` is consumed. -/
theorem jacobiCoefOp_congr (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (α : M) (α' : M') (u ubar : ℝ → E) (R R' : ℝ → E →L[ℝ] E) (e ebar : ι → ℝ → E) {t : ℝ}
    (h : ∀ i j, jacobiCoef (I := I) g α u R e i j t
      = jacobiCoef (I := I') g' α' ubar R' ebar i j t) :
    jacobiCoefOp (I := I) g α u R e t = jacobiCoefOp (I := I') g' α' ubar R' ebar t := by
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [h i j]

/-- **Math.** Orthonormal extraction of the norm: in an orthonormal frame,
`⟨Σᵢ cᵢeᵢ, Σⱼ cⱼeⱼ⟩ = Σᵢ cᵢ²`. -/
theorem chartMetricInner_frameCombination_self (g : RiemannianMetric I M) (α : M) (y : E)
    (c : ι → ℝ) (e : ι → E)
    (horth : ∀ i j, chartMetricInner (I := I) g α y (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    chartMetricInner (I := I) g α y (∑ i, c i • e i) (∑ j, c j • e j) = ∑ i, c i * c i := by
  rw [chartMetricInner_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [chartMetricInner_smul_right, chartMetricInner_frameCombination_left _ _ _ _ _ _
    (fun i => horth i j)]

/-- **Math.** The chart norm of a field equals the sum of the squares of its frame
coefficients (`frameExpansion` + orthonormal extraction). -/
theorem chartMetricInner_self_eq_sum_frameCoeff_sq (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) (e : ι → ℝ → E) (X : ℝ → E) {t : ℝ}
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    (horth : ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
      = if i = j then (1 : ℝ) else 0) :
    chartMetricInner (I := I) g α (u t) (X t) (X t)
      = ∑ i, frameCoeff (I := I) g α u e X t i * frameCoeff (I := I) g α u e X t i := by
  have hexp : X t = ∑ i, chartMetricInner (I := I) g α (u t) (X t) (e i t) • e i t :=
    frameExpansion (I := I) g α (u t) (fun i => e i t) hcard horth (X t)
  conv_lhs => rw [hexp]
  exact chartMetricInner_frameCombination_self (I := I) g α (u t)
    (fun i => chartMetricInner (I := I) g α (u t) (X t) (e i t)) (fun i => e i t) horth

/-- **Math.** **The Cartan Jacobi norm transfer** (do Carmo `thm:dc-ch8-2-1`, the analytic
heart), in variable curvature.

Let `(J, DJ)` and `(J̃, D̃J̃)` be chart Jacobi fields along `u` on `M` and along `ū` on `M̃`,
each read in a parallel orthonormal frame, and suppose the **curvature coefficients match**:
`⟨R(u̇,eᵢ)u̇,eⱼ⟩ = ⟨R̃(ū̇,ẽᵢ)ū̇,ẽⱼ⟩` for all `i, j` on `[a,b]` — this is precisely do Carmo's
hypothesis, transported through `φ_t` (see `Jacobi/CartanCurvatureBridge.lean`).  If the
two fields have the same initial frame coefficients and initial frame velocities, then
their norms agree at every time: `|J̃(t)| = |J(t)|`.

The mechanism: matching coefficients make the two scalar systems *the same* ODE
(`jacobiCoefOp_congr`), the bridge `isJacobiPairOn_of_isJacobiFieldOn` puts both fields'
coefficients into it, ODE uniqueness (`IsJacobiPairOn.eqOn`) forces the coefficients to
coincide, and orthonormality reads the norm off the coefficients
(`chartMetricInner_self_eq_sum_frameCoeff_sq`).

Unlike `metricInner_jacobiField_transfer_of_constantCurvature_of_speedSq`, no closed-form
solution and no constant-curvature hypothesis is used. -/
theorem chartMetricInner_transfer_of_jacobiCoef_match
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M') (α : M) (α' : M')
    (u J DJ : ℝ → E) (e : ι → ℝ → E) (ubar Jbar DJbar : ℝ → E) (ebar : ι → ℝ → E)
    {a b a' b' : ℝ}
    (hsub : Icc a b ⊆ Ioo a' b')
    -- the two Jacobi fields
    (hJF : IsJacobiFieldOn (I := I) g α u J DJ a' b')
    (hJFbar : IsJacobiFieldOn (I := I') g' α' ubar Jbar DJbar a' b')
    -- regularity on `M`
    (hu : ∀ t ∈ Icc a b, DifferentiableAt ℝ u t)
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target)
    (hG : ∀ t ∈ Icc a b, ∀ p q, DifferentiableAt ℝ (chartGramOnE (I := I) g α p q) (u t))
    (hbase : ∀ t ∈ Icc a b,
      (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (he : ∀ i, ∀ t ∈ Icc a b, DifferentiableAt ℝ (e i) t)
    (hepar : ∀ i, ∀ t ∈ Icc a b, covariantDerivCoord (I := I) g α u (e i) t = 0)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      chartMetricInner (I := I) g α (u t) (e i t) (e j t) = if i = j then (1 : ℝ) else 0)
    -- regularity on `M̃`
    (hubar : ∀ t ∈ Icc a b, DifferentiableAt ℝ ubar t)
    (hmembar : ∀ t ∈ Icc a b, ubar t ∈ interior (extChartAt I' α').target)
    (hGbar : ∀ t ∈ Icc a b, ∀ p q, DifferentiableAt ℝ (chartGramOnE (I := I') g' α' p q) (ubar t))
    (hbasebar : ∀ t ∈ Icc a b,
      (extChartAt I' α').symm (ubar t) ∈ (trivializationAt E (TangentSpace I') α').baseSet)
    (hebar : ∀ i, ∀ t ∈ Icc a b, DifferentiableAt ℝ (ebar i) t)
    (heparbar : ∀ i, ∀ t ∈ Icc a b, covariantDerivCoord (I := I') g' α' ubar (ebar i) t = 0)
    (horthbar : ∀ t ∈ Icc a b, ∀ i j,
      chartMetricInner (I := I') g' α' (ubar t) (ebar i t) (ebar j t)
        = if i = j then (1 : ℝ) else 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E)
    -- continuity, to run ODE uniqueness
    (hRcont : ContinuousOn (chartCurvatureOp (I := I) g α u) (Icc a b))
    (hecont : ∀ i, ContinuousOn (e i) (Icc a b))
    (hGcont : ∀ p q, ContinuousOn (fun t => chartGramOnE (I := I) g α p q (u t)) (Icc a b))
    -- **do Carmo's curvature hypothesis**, read in the two frames
    (hmatch : ∀ t ∈ Icc a b, ∀ i j,
      jacobiCoef (I := I) g α u (chartCurvatureOp (I := I) g α u) e i j t
        = jacobiCoef (I := I') g' α' ubar (chartCurvatureOp (I := I') g' α' ubar) ebar i j t)
    -- matching initial data
    (hF0 : frameCoeff (I := I) g α u e J a = frameCoeff (I := I') g' α' ubar ebar Jbar a)
    (hV0 : frameCoeff (I := I) g α u e DJ a = frameCoeff (I := I') g' α' ubar ebar DJbar a)
    {t : ℝ} (ht : t ∈ Icc a b) :
    chartMetricInner (I := I') g' α' (ubar t) (Jbar t) (Jbar t)
      = chartMetricInner (I := I) g α (u t) (J t) (J t) := by
  classical
  set A := jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e with hA
  -- both coefficient pairs solve the *same* scalar system `A`
  have hpair : IsJacobiPairOn A a b (frameCoeff (I := I) g α u e J)
      (frameCoeff (I := I) g α u e DJ) :=
    isJacobiPairOn_of_isJacobiFieldOn (I := I) g α u J DJ e hsub hJF hu hmem hG hbase he hepar
      hcard horth
  have hpairbar' := isJacobiPairOn_of_isJacobiFieldOn (I := I') g' α' ubar Jbar DJbar ebar
    hsub hJFbar hubar hmembar hGbar hbasebar hebar heparbar hcard horthbar
  have hpairbar : IsJacobiPairOn A a b (frameCoeff (I := I') g' α' ubar ebar Jbar)
      (frameCoeff (I := I') g' α' ubar ebar DJbar) :=
    hpairbar'.congr_coeff fun s hs =>
      (jacobiCoefOp_congr (I := I) (I' := I') g g' α α' u ubar
        (chartCurvatureOp (I := I) g α u) (chartCurvatureOp (I := I') g' α' ubar) e ebar
        (fun i j => hmatch s hs i j)).symm
  -- ODE uniqueness: equal initial data forces equal coefficients
  have hAcont : ContinuousOn A (Icc a b) :=
    continuousOn_jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e
      hRcont hecont hGcont
  obtain ⟨hFeq, -⟩ := hpair.eqOn hAcont hpairbar hF0 hV0
  -- read the norms off the coefficients
  rw [chartMetricInner_self_eq_sum_frameCoeff_sq (I := I') g' α' ubar ebar Jbar hcard
      (horthbar t ht),
    chartMetricInner_self_eq_sum_frameCoeff_sq (I := I) g α u e J hcard (horth t ht)]
  exact Finset.sum_congr rfl fun i _ => by rw [hFeq ht]

end Transfer

end Riemannian.Jacobi
