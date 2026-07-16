import OpenGALib.Riemannian.Jacobi.JacobiFrameSmooth
import OpenGALib.Riemannian.Jacobi.JacobiTaylorExpansion

/-!
# The manifold Taylor expansion of `|J(t)|²` (do Carmo Ch. 5, Prop. 2.7)

do Carmo, *Riemannian Geometry*, Ch. 5, §2, Proposition 2.7.  For a Jacobi field `J` along a
geodesic with `J(0) = 0` and `J'(0) = w`,
$$
  |J(t)|^2 = \langle w, w\rangle\, t^2 - \tfrac13\langle R(v, w)v, w\rangle\, t^4 + o(t^4),
  \qquad v = \gamma'(0).
$$
(With `|w| = 1` this is do Carmo's `|J(t)|² = t² − (1/3)K t⁴ + o(t⁴)`.)

The **analytic core** `norm_sq_jacobi_isLittleO_local` (JacobiTaylorExpansion.lean) proves this
for an abstract second-order linear ODE `f'' = −A(t)f` in an inner product space, with
`|J|² = ⟪f, f⟫`.  This file supplies the **manifold instantiation**: read the Jacobi field in a
parallel orthonormal frame `e₁,…,eₙ` along a `C^∞` curve `u`, so that

* the frame coefficients `F(t) = (⟨J, e_i⟩)_i` solve the frame Jacobi system
  `F'' = −A(t)F`, with `A = jacobiCoefOp` the frame curvature (a `C^∞` coefficient once `u` and
  the frame are `C^∞` — the regularity from `JacobiFrameSmooth.lean`);
* `|J(t)|²_g = ‖F(t)‖²` (orthonormality), and the coefficient
  `⟪F'(0), A(0)F'(0)⟫ = ⟨R(v, w)v, w⟩` (`sum_jacobiCoef_quadratic`).

Transferring the `Fin n → ℝ` coefficient data to `EuclideanSpace ℝ (Fin n)` (via the `ℓ²`
continuous linear equivalence, exactly as `frameJacobi_ne_zero_of_nonpos`) then feeds the
abstract core.
-/

open Set Riemannian Filter Asymptotics
open scoped ContDiff Manifold Topology NNReal RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### `C^∞` smoothness of the frame Jacobi coefficient -/

/-- **Math.** **`C^∞` smoothness of the Jacobi coefficient `a_{ij}(t) = ⟨R(u̇, e_i)u̇, e_j⟩`.**
Along a curve `u` and frame fields `e_i, e_j` that are `C^∞` on an open time set `s` staying in
the chart interior, the coefficient `t ↦ jacobiCoef g α u (chartCurvatureOp g α u) e i j t` is
`C^∞`.  It is the chart Gram pairing `chartMetricInner (u t) (R(t) e_i(t)) (e_j(t))`, a sum of
products of the `C^∞` Gram `chartGramOnE ∘ u`, the `C^∞` operator field `chartCurvatureOp`, and
the `C^∞` frame velocities. -/
theorem contDiffOn_infty_jacobiCoef {ι : Type*} (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (e : ι → ℝ → E) (i j : ι) {s : Set ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (hmem : ∀ t ∈ s, u t ∈ interior (extChartAt I α).target)
    (he : ∀ k, ContDiffOn ℝ ∞ (e k) s) :
    ContDiffOn ℝ ∞
      (jacobiCoef (I := I) g α u (chartCurvatureOp (I := I) g α u) e i j) s := by
  have hR : ContDiffOn ℝ ∞ (chartCurvatureOp (I := I) g α u) s :=
    contDiffOn_infty_chartCurvatureOp g α u hs hu hmem
  -- `jacobiCoef i j t = ∑ p q, G_{pq}(u t) · (R(t) e_i(t))_p · (e_j(t))_q`
  have hexpand : (jacobiCoef (I := I) g α u (chartCurvatureOp (I := I) g α u) e i j)
      = fun t => ∑ p, ∑ q,
          chartGramOnE (I := I) g α p q (u t)
            * Geodesic.chartCoord (E := E) p (chartCurvatureOp (I := I) g α u t (e i t))
            * Geodesic.chartCoord (E := E) q (e j t) := by
    funext t; rw [jacobiCoef, chartMetricInner_def]
  rw [hexpand]
  refine ContDiffOn.sum (fun p _ => ContDiffOn.sum (fun q _ => ?_))
  have hG : ContDiffOn ℝ ∞ (fun t => chartGramOnE (I := I) g α p q (u t)) s :=
    (chartGramOnE_contDiffOn (I := I) g α p q).comp hu
      (fun t ht => interior_subset (hmem t ht))
  have hRe : ContDiffOn ℝ ∞
      (fun t => Geodesic.chartCoord (E := E) p (chartCurvatureOp (I := I) g α u t (e i t))) s := by
    have hRei : ContDiffOn ℝ ∞ (fun t => chartCurvatureOp (I := I) g α u t (e i t)) s :=
      hR.clm_apply (he i)
    have := (Geodesic.chartCoordFunctional (E := E) p).contDiff.comp_contDiffOn hRei
    simpa only [Geodesic.chartCoordFunctional_apply] using this
  have hej : ContDiffOn ℝ ∞ (fun t => Geodesic.chartCoord (E := E) q (e j t)) s := by
    have := (Geodesic.chartCoordFunctional (E := E) q).contDiff.comp_contDiffOn (he j)
    simpa only [Geodesic.chartCoordFunctional_apply] using this
  exact (hG.mul hRe).mul hej

/-- **Math.** **`C^∞` smoothness of the Jacobi coefficient operator** `A(t) = (a_{ij}(t))` acting
on `Fin n → ℝ`.  It is a finite sum of the `C^∞` scalar coefficients `a_{ij}`
(`contDiffOn_infty_jacobiCoef`) times constant elementary operators, so it is `C^∞`. -/
theorem contDiffOn_infty_jacobiCoefOp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (e : ι → ℝ → E)
    {s : Set ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (hmem : ∀ t ∈ s, u t ∈ interior (extChartAt I α).target)
    (he : ∀ k, ContDiffOn ℝ ∞ (e k) s) :
    ContDiffOn ℝ ∞
      (jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e) s := by
  unfold jacobiCoefOp
  refine ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun i _ => ?_))
  exact (contDiffOn_infty_jacobiCoef g α u e i j hs hu hmem he).smul contDiffOn_const

/-! ### The manifold Taylor expansion of `|J|²` -/

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **do Carmo Ch. 5, Proposition 2.7 (frame/coordinate form).**  Let `u` be a `C^∞`
curve staying in the chart interior, `e₁,…,eₙ` a `C^∞` parallel orthonormal frame along it, and
`J(t) = Σᵢ Fᵢ(t) eᵢ(t)` a Jacobi field read in the frame — i.e. the coefficients `F` solve the
frame Jacobi system `F'' = −A(t)F`, `A = jacobiCoefOp` the frame curvature — with `J(0) = 0`.
Writing `w = J'(0) = Σᵢ Vᵢ(0) eᵢ(0)` for the initial velocity and `v = γ'(0)`, the squared length
has the fourth-order Taylor expansion
$$
  |J(t)|^2_g = \langle w, w\rangle\, t^2 - \tfrac13\langle R(v, w)v, w\rangle\, t^4 + o(t^4).
$$
(With `|w| = 1`, `⟨w, w⟩ = 1` and this is do Carmo's `|J|² = t² − (1/3)K t⁴ + o(t⁴)`, eq. (3).)

The proof reads `|J(t)|²_g = ‖F(t)‖²` (orthonormality) and transfers the coefficient data to the
Euclidean space `EuclideanSpace ℝ (Fin n)` to feed the abstract analytic core
`norm_sq_jacobi_isLittleO_local`, then identifies `⟨V(0), A(0)V(0)⟩ = ⟨R(v, w)v, w⟩` via
`sum_jacobiCoef_quadratic`.  The frame is `C^∞` by `exists_contDiffOn_parallelOrthoFrame` and the
coefficient `A` by `contDiffOn_infty_jacobiCoefOp`. -/
theorem norm_sq_jacobi_frame_isLittleO (g : RiemannianMetric I M) (p : M) (u : ℝ → E)
    {s : Set ℝ} (hs : IsOpen s) (hconv : Convex ℝ s) (hs0 : (0 : ℝ) ∈ s)
    (hu : ContDiffOn ℝ ∞ u s) (hmem : ∀ t ∈ s, u t ∈ interior (extChartAt I p).target)
    (e : Fin (Module.finrank ℝ E) → ℝ → E)
    (heorth : ∀ t ∈ s, ∀ i j, chartMetricInner (I := I) g p (u t) (e i t) (e j t)
      = if i = j then (1 : ℝ) else 0)
    (heCD : ∀ i, ContDiffOn ℝ ∞ (e i) s)
    {F V : ℝ → Fin (Module.finrank ℝ E) → ℝ} (hFCD : ContDiffOn ℝ ∞ F s)
    (hFV : ∀ t ∈ s, HasDerivAt F (V t) t)
    (hVA : ∀ t ∈ s, HasDerivAt V
      (-(jacobiCoefOp (I := I) g p u (chartCurvatureOp (I := I) g p u) e t) (F t)) t)
    (hF0 : F 0 = 0) :
    (fun t => chartMetricInner (I := I) g p (u t) (∑ i, F t i • e i t) (∑ i, F t i • e i t)
        - (chartMetricInner (I := I) g p (u 0) (∑ i, V 0 i • e i 0) (∑ i, V 0 i • e i 0) * t ^ 2
          - 1 / 3 * chartMetricInner (I := I) g p (u 0)
              (chartCurvatureOp (I := I) g p u 0 (∑ i, V 0 i • e i 0)) (∑ i, V 0 i • e i 0)
            * t ^ 4))
      =o[𝓝 (0 : ℝ)] fun t => t ^ 4 := by
  classical
  haveI hne : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  set A := jacobiCoefOp (I := I) g p u (chartCurvatureOp (I := I) g p u) e with hAdef
  -- the ℓ² continuous linear equivalence `(Fin n → ℝ) ≃L EuclideanSpace ℝ (Fin n)`
  set φ : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (Module.finrank ℝ E) => ℝ)).symm with hφ
  have hInner : ∀ (a c : Fin (Module.finrank ℝ E) → ℝ),
      inner ℝ (φ a) (φ c) = ∑ i, a i * c i := by
    intro a c
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hφ, PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp]
    simp [inner, mul_comm]
  -- transferred data on the Euclidean coefficient space
  set A' : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun t => (φ.toContinuousLinearMap.comp (A t)).comp φ.symm.toContinuousLinearMap with hA'
  set F' : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun t => φ (F t) with hF'
  set V' : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun t => φ (V t) with hV'
  -- smoothness of the coefficient and the solution
  have hAcd : ContDiffOn ℝ ∞ A s := contDiffOn_infty_jacobiCoefOp g p u e hs hu hmem heCD
  have hA'cd : ContDiffOn ℝ ∞ A' s := by
    have h1 : ContDiffOn ℝ ∞ (fun t => (φ.toContinuousLinearMap.comp (A t))) s :=
      (ContinuousLinearMap.compL ℝ (Fin (Module.finrank ℝ E) → ℝ)
        (Fin (Module.finrank ℝ E) → ℝ) (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
        φ.toContinuousLinearMap).contDiff.comp_contDiffOn hAcd
    exact ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      (Fin (Module.finrank ℝ E) → ℝ) (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).flip
      φ.symm.toContinuousLinearMap).contDiff.comp_contDiffOn h1
  have hF'cd : ContDiffOn ℝ ∞ F' s :=
    φ.toContinuousLinearMap.contDiff.comp_contDiffOn hFCD
  have hF'V' : ∀ t ∈ s, HasDerivAt F' (V' t) t := fun t ht => by
    simpa [hF', hV'] using φ.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hFV t ht)
  have hV'A' : ∀ t ∈ s, HasDerivAt V' (-(A' t) (F' t)) t := fun t ht => by
    have h := φ.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hVA t ht)
    have hEq : φ (-(A t) (F t)) = -(A' t) (F' t) := by
      simp only [hA', hF', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply, map_neg]
    simpa [hV', hEq] using h
  have hF'0 : F' 0 = 0 := by simp only [hF', hF0, map_zero]
  -- apply the abstract analytic core
  have hcore := norm_sq_jacobi_isLittleO_local
    (E := EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    hs hconv hs0 hF'cd hA'cd hF'V' hV'A' hF'0
  -- rewrite the abstract inner products as chart quantities
  -- (1) `⟪F' t, F' t⟫ = |J(t)|²_g` on `s`, hence eventually at `𝓝 0`
  have hnormJ : ∀ t ∈ s, (inner ℝ (F' t) (F' t) : ℝ)
      = chartMetricInner (I := I) g p (u t) (∑ i, F t i • e i t) (∑ i, F t i • e i t) := by
    intro t ht
    rw [hF', hInner,
      chartMetricInner_sum_right g p (u t) (∑ i, F t i • e i t) Finset.univ
        (fun j => F t j • e j t)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [chartMetricInner_smul_right,
      chartMetricInner_frameCombination_left g p (u t) (F t) (fun i => e i t) j
        (fun i => heorth t ht i j)]
  -- (2) `⟪V' 0, V' 0⟫ = ⟨w, w⟩_g`
  have hVV : (inner ℝ (V' 0) (V' 0) : ℝ)
      = chartMetricInner (I := I) g p (u 0) (∑ i, V 0 i • e i 0) (∑ i, V 0 i • e i 0) := by
    rw [hV', hInner,
      chartMetricInner_sum_right g p (u 0) (∑ i, V 0 i • e i 0) Finset.univ
        (fun j => V 0 j • e j 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [chartMetricInner_smul_right,
      chartMetricInner_frameCombination_left g p (u 0) (V 0) (fun i => e i 0) j
        (fun i => heorth 0 hs0 i j)]
  -- (3) `⟪V' 0, A' 0 (V' 0)⟫ = ⟨R(v, w)v, w⟩_g`
  have hVAV : (inner ℝ (V' 0) (A' 0 (V' 0)) : ℝ)
      = chartMetricInner (I := I) g p (u 0)
          (chartCurvatureOp (I := I) g p u 0 (∑ i, V 0 i • e i 0)) (∑ i, V 0 i • e i 0) := by
    have hval : (A' 0) (V' 0) = φ (A 0 (V 0)) := by
      simp only [hA', hV', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply]
    rw [hval, hV', hInner]
    have hstep : ∑ i, V 0 i * A 0 (V 0) i
        = ∑ i, ∑ j, jacobiCoef (I := I) g p u (chartCurvatureOp (I := I) g p u) e i j 0
            * V 0 i * V 0 j := by
      rw [hAdef]
      simp_rw [jacobiCoefOp_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hstep, sum_jacobiCoef_quadratic (I := I) g p u (chartCurvatureOp (I := I) g p u) e 0 (V 0)]
  -- assemble
  have hcongr : (fun t => inner ℝ (F' t) (F' t)
        - (inner ℝ (V' 0) (V' 0) * t ^ 2 - 1 / 3 * inner ℝ (V' 0) (A' 0 (V' 0)) * t ^ 4))
      =ᶠ[𝓝 (0 : ℝ)]
      fun t => chartMetricInner (I := I) g p (u t) (∑ i, F t i • e i t) (∑ i, F t i • e i t)
        - (chartMetricInner (I := I) g p (u 0) (∑ i, V 0 i • e i 0) (∑ i, V 0 i • e i 0) * t ^ 2
          - 1 / 3 * chartMetricInner (I := I) g p (u 0)
              (chartCurvatureOp (I := I) g p u 0 (∑ i, V 0 i • e i 0)) (∑ i, V 0 i • e i 0)
            * t ^ 4) := by
    filter_upwards [hs.mem_nhds hs0] with t ht
    rw [hnormJ t ht, hVV, hVAV]
  exact hcore.congr' hcongr (EventuallyEq.refl _ _)

/-- **Math.** **do Carmo Ch. 5, Corollary 2.10 (frame/coordinate form).**  In the situation of
`norm_sq_jacobi_frame_isLittleO`, if in addition `|w|_g = 1` (do Carmo's normalized `|w| = 1`),
the length `|J(t)|_g = \sqrt{|J(t)|²_g}` has the third-order one-sided expansion
$$
  |J(t)|_g = t - \tfrac16\langle R(v, w)v, w\rangle\, t^3 + o(t^3), \qquad t \to 0^+.
$$
(With the sectional-curvature identification `⟨R(v, w)v, w⟩ = K(p, σ)` of `cor:dc-ch5-2-9`, this is
do Carmo's `|J(t)| = t − (1/6)K t³ + õ(t³)`, eq. (6).)  It is the square root of
`norm_sq_jacobi_frame_isLittleO` (with the leading coefficient normalized to `t²`) via the analytic
`√` step `sqrt_isLittleO_of_sq_isLittleO`; the required global nonnegativity is arranged by clamping
`|J|²_g` (which is `≥ 0` on the chart, `chartMetricInner_self_nonneg_of_mem_target`) with `max · 0`. -/
theorem norm_jacobi_frame_isLittleO (g : RiemannianMetric I M) (p : M) (u : ℝ → E)
    {s : Set ℝ} (hs : IsOpen s) (hconv : Convex ℝ s) (hs0 : (0 : ℝ) ∈ s)
    (hu : ContDiffOn ℝ ∞ u s) (hmem : ∀ t ∈ s, u t ∈ interior (extChartAt I p).target)
    (e : Fin (Module.finrank ℝ E) → ℝ → E)
    (heorth : ∀ t ∈ s, ∀ i j, chartMetricInner (I := I) g p (u t) (e i t) (e j t)
      = if i = j then (1 : ℝ) else 0)
    (heCD : ∀ i, ContDiffOn ℝ ∞ (e i) s)
    {F V : ℝ → Fin (Module.finrank ℝ E) → ℝ} (hFCD : ContDiffOn ℝ ∞ F s)
    (hFV : ∀ t ∈ s, HasDerivAt F (V t) t)
    (hVA : ∀ t ∈ s, HasDerivAt V
      (-(jacobiCoefOp (I := I) g p u (chartCurvatureOp (I := I) g p u) e t) (F t)) t)
    (hF0 : F 0 = 0)
    (hw : chartMetricInner (I := I) g p (u 0) (∑ i, V 0 i • e i 0) (∑ i, V 0 i • e i 0) = 1) :
    (fun t => Real.sqrt
          (chartMetricInner (I := I) g p (u t) (∑ i, F t i • e i t) (∑ i, F t i • e i t))
        - (t - 1 / 6 * chartMetricInner (I := I) g p (u 0)
            (chartCurvatureOp (I := I) g p u 0 (∑ i, V 0 i • e i 0)) (∑ i, V 0 i • e i 0) * t ^ 3))
      =o[𝓝[>] (0 : ℝ)] fun t => t ^ 3 := by
  set c : ℝ := 1 / 3 * chartMetricInner (I := I) g p (u 0)
    (chartCurvatureOp (I := I) g p u 0 (∑ i, V 0 i • e i 0)) (∑ i, V 0 i • e i 0) with hc
  have hprop := norm_sq_jacobi_frame_isLittleO g p u hs hconv hs0 hu hmem e heorth heCD
    hFCD hFV hVA hF0
  rw [hw] at hprop
  -- clamp `|J|²_g` to a globally nonnegative function agreeing with it near `0`
  have hgt_nonneg : ∀ t,
      0 ≤ max (chartMetricInner (I := I) g p (u t) (∑ i, F t i • e i t) (∑ i, F t i • e i t)) 0 :=
    fun t => le_max_right _ _
  have hgtexp : (fun t => max
        (chartMetricInner (I := I) g p (u t) (∑ i, F t i • e i t) (∑ i, F t i • e i t)) 0
        - (t ^ 2 - c * t ^ 4)) =o[𝓝 (0 : ℝ)] fun t => t ^ 4 := by
    refine hprop.congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards [hs.mem_nhds hs0] with t ht
    rw [max_eq_left (chartMetricInner_self_nonneg_of_mem_target (I := I) g p
      (interior_subset (hmem t ht)) (∑ i, F t i • e i t))]
    rw [hc]; ring
  have hsqrt := sqrt_isLittleO_of_sq_isLittleO hgt_nonneg hgtexp
  refine hsqrt.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hs.mem_nhds hs0)] with t ht
  rw [max_eq_left (chartMetricInner_self_nonneg_of_mem_target (I := I) g p
    (interior_subset (hmem t ht)) (∑ i, F t i • e i t)), hc]
  ring

end Riemannian.Jacobi

end
