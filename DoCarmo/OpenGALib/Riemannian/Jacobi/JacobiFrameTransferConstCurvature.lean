import OpenGALib.Riemannian.Jacobi.JacobiConstantCurvature
import OpenGALib.Riemannian.Jacobi.JacobiFrameTransfer

/-!
# Constant-curvature specialization of the frame-coefficient Jacobi transfer (do Carmo Ch. 8)

In E. Cartan's theorem (do Carmo Ch. 8, `thm:dc-ch8-2-1`) the analytic heart is the
*frame transfer* `jacobiFrameTransfer`: a Jacobi field written in a parallel orthonormal
frame carries over to a second manifold as a Jacobi field, **provided** the two frames have
matching curvature coefficients

  `⟨ℛ(eᵢ, u̇)u̇, eⱼ⟩ = ⟨ℛ̃(ẽᵢ, ū̇)ū̇, ẽⱼ⟩`.

For the general theorem this matching comes from the parallel-transport conjugation
`φ_t = P̃_t ∘ i ∘ P_t⁻¹` and the hypothesis `⟨R(x,y)u,v⟩ = ⟨R̃(φx,φy)φu,φv⟩`.  **In the
constant-curvature case the matching is automatic** — this is exactly what do Carmo's
Corollaries 2.2 and 2.3 (and the space-form Theorem 4.1) use, and it needs *no* φ_t.

The key fact is the chart reading of do Carmo Ch. 4, Lemma 3.4: on a space of constant
sectional curvature `K₀`, the Jacobi operator's chart pairing is the model form

  `⟨ℛ(a, v)v, b⟩ = K₀·(⟨v,v⟩⟨a,b⟩ − ⟨a,v⟩⟨v,b⟩)`   (`chartMetricInner`-of-`chartCurvatureEndo`),

a *manifold-independent* function of the chart inner products of `a, b, v`.  Evaluated on an
orthonormal frame whose distinguished vector is the (unit) velocity `u̇ = e_{n₀}`, every entry
collapses to `K₀·(δᵢⱼ − δ_{i n₀} δ_{n₀ j})`, which depends only on the indices — so two
constant-`K₀` spaces have identical frame-coefficient matrices and the matching hypothesis of
`jacobiFrameTransfer` holds for free.

## Contents

* `chartMetricInner_chartCurvatureEndo_isConstantCurvature` — the chart model form of the
  Jacobi operator's pairing (generalizes the restricted `chartCurvatureOp_isConstantCurvature`
  to arbitrary `a, b` without the `a ⟂ v`, `|v| = 1` hypotheses).
* `chartCurvatureEndo_frameCoef_isConstantCurvature` — the frame-coefficient matrix
  `K₀·(δᵢⱼ − δ_{i n₀} δ_{n₀ j})` for an orthonormal frame with velocity `e_{n₀} = u̇`.
* `jacobiFrameTransfer_isConstantCurvature` — `jacobiFrameTransfer` with the matching
  hypothesis discharged from constant curvature on both sides (no φ_t conjugation).

Blueprint: `lem:dc-ch8-2-1-jacobi-transfer`, `cor:dc-ch8-2-2`, `cor:dc-ch8-2-3`,
`thm:dc-ch8-4-1`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8, Theorem 2.1 and Corollaries 2.2–2.3.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### The chart model form of the Jacobi operator in constant curvature -/

/-- **Math.** **do Carmo Ch. 4, Lemma 3.4 (chart Jacobi-operator form).**  On a manifold of
constant sectional curvature `K₀`, the chart pairing of the Jacobi operator
`a ↦ ℛ(a, v)v` (`chartCurvatureEndo g α y v`) is the constant-curvature *model form*

  `⟨ℛ(a, v)v, b⟩ = K₀·(⟨v, v⟩⟨a, b⟩ − ⟨a, v⟩⟨v, b⟩)`,

all inner products being the chart inner product `chartMetricInner g α y` at `y = φ(q)`.  This
generalizes `chartCurvatureOp_isConstantCurvature` (which fixes `a ⟂ v`, `|v| = 1`) to
arbitrary `a, b, v`; the proof is the same bridge (`curvatureFormAt_chartFrame`) composed with
the pointwise constant-curvature form (`curvatureFormAt_isConstantCurvature`) and the chart
realization of the inner product (`metricInner_chartFrameRealize`), without discarding any of
the four terms. -/
theorem chartMetricInner_chartCurvatureEndo_isConstantCurvature (g : RiemannianMetric I M)
    {K₀ : ℝ} (hK : g.leviCivitaConnection.IsConstantCurvature g K₀) (α : M) (v a b : E)
    {q : M} (hq : q ∈ (chartAt H α).source) {y : E} (hy : y = extChartAt I α q) :
    chartMetricInner (I := I) g α y
        (chartCurvatureEndo (I := I) g α y v a) b
      = K₀ * (chartMetricInner (I := I) g α y v v
              * chartMetricInner (I := I) g α y a b
            - chartMetricInner (I := I) g α y a v
              * chartMetricInner (I := I) g α y v b) := by
  subst hy
  rw [chartCurvatureEndo_apply]
  -- the manifold ↔ chart curvature bridge on the frame realizations of `(a, v, v, b)`
  have hbridge := curvatureFormAt_chartFrame (I := I) g hq a v v b
  -- the pointwise constant-curvature model form on those realizations
  have hcc := curvatureFormAt_isConstantCurvature (I := I) g hK q
    (∑ i, Geodesic.chartCoord (E := E) i a • chartBasisVecFiber (I := I) α i q)
    (∑ i, Geodesic.chartCoord (E := E) i v • chartBasisVecFiber (I := I) α i q)
    (∑ i, Geodesic.chartCoord (E := E) i v • chartBasisVecFiber (I := I) α i q)
    (∑ i, Geodesic.chartCoord (E := E) i b • chartBasisVecFiber (I := I) α i q)
  rw [metricInner_chartFrameRealize (I := I) g hq a v,
      metricInner_chartFrameRealize (I := I) g hq v b,
      metricInner_chartFrameRealize (I := I) g hq v v,
      metricInner_chartFrameRealize (I := I) g hq a b] at hcc
  rw [hcc] at hbridge
  linear_combination hbridge

/-! ### The frame-coefficient matrix is manifold-independent -/

/-- **Math.** **The constant-curvature frame coefficients are the Kronecker matrix.**  Let
`e : ι → E` be an orthonormal frame at `y = φ(q)` for the chart inner product, whose
distinguished vector `e_{n₀} = v` is the velocity.  Then the Jacobi frame coefficients are

  `⟨ℛ(eᵢ, v)v, eⱼ⟩ = K₀·(δᵢⱼ − δ_{i n₀} δ_{n₀ j})`,

which depends only on the indices `i, j, n₀` and the curvature constant `K₀` — **not** on the
manifold, chart or frame.  This is the reason E. Cartan's curvature-matching hypothesis is
automatic in constant curvature: two spaces of the same constant `K₀` produce identical
frame-coefficient matrices, so `jacobiFrameTransfer`'s `hmatch` holds without any
parallel-transport conjugation `φ_t`.  Proof: plug the orthonormal pairings
(`⟨v, v⟩ = ⟨e_{n₀}, e_{n₀}⟩ = 1`, `⟨eᵢ, eⱼ⟩ = δᵢⱼ`, `⟨eᵢ, v⟩ = δ_{i n₀}`,
`⟨v, eⱼ⟩ = δ_{n₀ j}`) into the model form
`chartMetricInner_chartCurvatureEndo_isConstantCurvature`. -/
theorem chartCurvatureEndo_frameCoef_isConstantCurvature (g : RiemannianMetric I M)
    {K₀ : ℝ} (hK : g.leviCivitaConnection.IsConstantCurvature g K₀) (α : M)
    {ι : Type*} [DecidableEq ι] (e : ι → E) (n₀ : ι) (v : E)
    {q : M} (hq : q ∈ (chartAt H α).source) {y : E} (hy : y = extChartAt I α q)
    (hv : e n₀ = v)
    (horth : ∀ i j, chartMetricInner (I := I) g α y (e i) (e j)
      = if i = j then (1 : ℝ) else 0)
    (i j : ι) :
    chartMetricInner (I := I) g α y (chartCurvatureEndo (I := I) g α y v (e i)) (e j)
      = K₀ * ((if i = j then (1 : ℝ) else 0)
            - (if i = n₀ then (1 : ℝ) else 0) * (if n₀ = j then (1 : ℝ) else 0)) := by
  rw [chartMetricInner_chartCurvatureEndo_isConstantCurvature (I := I) g hK α v (e i) (e j) hq hy,
    ← hv, horth n₀ n₀, horth i j, horth i n₀, horth n₀ j, if_pos rfl]
  ring

/-! ### The frame transfer with the matching hypothesis discharged from constant curvature -/

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-- **Math.** **do Carmo Ch. 8, `thm:dc-ch8-2-1` in constant curvature (analytic heart, no
φ_t).**  The frame-coefficient Jacobi transfer `jacobiFrameTransfer` with the curvature-matching
hypothesis discharged automatically: if `M` and `M̃` both have constant sectional curvature
`K₀` (same value), then a Jacobi field `J = Σᵢ yᵢ eᵢ` written in a parallel orthonormal frame
along `γ` (with the velocity `u̇ = e_{n₀}` a distinguished frame vector) carries over to
`J̃ = Σᵢ yᵢ ẽᵢ` on `M̃`, a Jacobi field along `γ̃`, using the **same** scalar coefficients.

Unlike the general E. Cartan theorem this needs **no** parallel-transport conjugation
`φ_t = P̃_t ∘ i ∘ P_t⁻¹`: the matching `⟨ℛ(eᵢ, u̇)u̇, eⱼ⟩ = ⟨ℛ̃(ẽᵢ, ū̇)ū̇, ẽⱼ⟩` holds because
both sides equal the manifold-independent Kronecker matrix `K₀·(δᵢⱼ − δ_{i n₀} δ_{n₀ j})`
(`chartCurvatureEndo_frameCoef_isConstantCurvature`).  This is exactly the mechanism of do
Carmo's Corollaries 2.2 and 2.3 and the space-form Theorem 4.1, which only ever apply Cartan
between two spaces of the *same* constant curvature. -/
theorem jacobiFrameTransfer_isConstantCurvature {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (g : RiemannianMetric I M) (g' : RiemannianMetric I' M') {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (hK' : g'.leviCivitaConnection.IsConstantCurvature g' K₀)
    (α : M) (α' : M') (u ubar : ℝ → E) (y : ι → ℝ → ℝ) (e ebar : ι → ℝ → E) {t : ℝ} (n₀ : ι)
    (hf : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (y i) r)
    (hf2 : ∀ i, DifferentiableAt ℝ (deriv (y i)) t)
    (he : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (e i) r)
    (hpar : ∀ i, ∀ᶠ r in 𝓝 t, covariantDerivCoord (I := I) g α u (e i) r = 0)
    (horth : ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
      = if i = j then (1 : ℝ) else 0)
    (hjac : covariantDerivCoord (I := I) g α u
          (fun r => covariantDerivCoord (I := I) g α u (fun s => ∑ i, y i s • e i s) r) t
        + chartCurvatureEndo (I := I) g α (u t) (deriv u t) (∑ i, y i t • e i t) = 0)
    (hebar : ∀ i, ∀ᶠ r in 𝓝 t, DifferentiableAt ℝ (ebar i) r)
    (hparbar : ∀ i, ∀ᶠ r in 𝓝 t, covariantDerivCoord (I := I') g' α' ubar (ebar i) r = 0)
    (hcardbar : Fintype.card ι = Module.finrank ℝ E)
    (horthbar : ∀ i j, chartMetricInner (I := I') g' α' (ubar t) (ebar i t) (ebar j t)
      = if i = j then (1 : ℝ) else 0)
    (n₀u : e n₀ t = deriv u t) (n₀ubar : ebar n₀ t = deriv ubar t)
    {q : M} (hq : q ∈ (chartAt H α).source) (hu : u t = extChartAt I α q)
    {q' : M'} (hq' : q' ∈ (chartAt H' α').source) (hu' : ubar t = extChartAt I' α' q') :
    covariantDerivCoord (I := I') g' α' ubar
        (fun r => covariantDerivCoord (I := I') g' α' ubar (fun s => ∑ i, y i s • ebar i s) r) t
      + chartCurvatureEndo (I := I') g' α' (ubar t) (deriv ubar t) (∑ i, y i t • ebar i t) = 0 := by
  have hmatch : ∀ i j,
      chartMetricInner (I := I) g α (u t)
          (chartCurvatureEndo (I := I) g α (u t) (deriv u t) (e i t)) (e j t)
        = chartMetricInner (I := I') g' α' (ubar t)
          (chartCurvatureEndo (I := I') g' α' (ubar t) (deriv ubar t) (ebar i t)) (ebar j t) := by
    intro i j
    rw [chartMetricInner_chartCurvatureEndo_isConstantCurvature (I := I) g hK α
          (deriv u t) (e i t) (e j t) hq hu,
        chartMetricInner_chartCurvatureEndo_isConstantCurvature (I := I') g' hK' α'
          (deriv ubar t) (ebar i t) (ebar j t) hq' hu',
        ← n₀u, ← n₀ubar,
        horth n₀ n₀, horth i j, horth i n₀, horth n₀ j,
        horthbar n₀ n₀, horthbar i j, horthbar i n₀, horthbar n₀ j]
  exact jacobiFrameTransfer (I := I) (I' := I') g g' α α' u ubar y e ebar hf hf2 he hpar horth
    hjac hebar hparbar hcardbar horthbar hmatch

end Riemannian.Jacobi

end
