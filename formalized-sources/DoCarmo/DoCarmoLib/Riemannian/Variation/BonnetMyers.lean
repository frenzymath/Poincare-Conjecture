import DoCarmoLib.Riemannian.Variation.IndexForm
import DoCarmoLib.Riemannian.Variation.VelocitySeededFrameAlong
import DoCarmoLib.Riemannian.Variation.ParallelCovariantField
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4RicciSectional
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality
import DoCarmoLib.Riemannian.Jacobi.CartanCurvatureBridge
import DoCarmoLib.Riemannian.Geodesic.HopfRinow
import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodHuniq
import DoCarmoLib.Riemannian.Exponential.MovingBaseExpGlobalSmooth

/-!
# Bonnet–Myers: the index-form computation (do Carmo Ch. 9, §3, `thm:dc-ch9-3-1`)

This file assembles the **geometric heart** of Bonnet–Myers, `thm:dc-ch9-3-1`: along a
minimizing geodesic `γ : [0, 1] → M` of speed `ℓ`, if the Ricci curvature is bounded below by
`1/r² > 0` and `ℓ > π r`, then the sum of the index forms of the fields
`V_j(t) = (\sin \pi t)\,e_j(t)` (`e_j` the parallel orthonormal frame orthogonal to `γ'`) is
strictly negative — do Carmo's

$$\tfrac12\sum_j E_j''(0) = \int_0^1\big((n-1)\pi^2\cos^2\pi t - (\sin^2\pi t)\,\ell^2\,\mathrm{Ric}\big)\,dt < 0.$$

By formula (6) (`lem:dc-ch9-2-10-formula6`) each index form is `½E_j''(0)`; and since `γ`
minimizes energy each `E_j''(0) ≥ 0`, contradicting the strict negativity — so `ℓ ≤ π r`.  That
final second-variation-and-minimality bridge is the concrete exponential variation
(`prop:dc-ch9-2-2` + `prop:dc-ch9-2-8` for `exp`), still open; this file lands everything else.

The index-form value `indexForm_smul_eq` is surface-free: it is a pointwise multilinear
rewrite of `indexForm` for the field `V = φ·e`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §3, Theorem 3.1 (Bonnet–Myers).
-/

open Set Riemannian intervalIntegral MeasureTheory
open scoped ContDiff Manifold Topology Real

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### A real-analysis lemma: the second-order necessary condition at a minimum -/

/-- **Math.** The **second-order necessary condition**: a function `f : ℝ → ℝ` with a local
minimum at `x`, continuous at `x` and twice differentiable there (`HasDerivAt (deriv f) f'' x`),
has `f''(x) ≥ 0`.  Mathlib has only the *sufficient* converse (`isLocalMax_of_deriv_deriv_neg`);
this necessary direction is proved by contradiction from it: if `f'' < 0` then `x` is also a
local *max*, so `f` is locally constant, its derivative is eventually `0`, and by uniqueness
`f'' = 0` — contradicting `f'' < 0`.

This is the fact that turns "a minimizing geodesic makes each `E_j` minimal at `s = 0`" into
`E_j''(0) ≥ 0` in do Carmo's Bonnet–Myers argument (`thm:dc-ch9-3-1`). -/
theorem isLocalMin_deriv_deriv_nonneg {f : ℝ → ℝ} {x f'' : ℝ}
    (hmin : IsLocalMin f x) (hcont : ContinuousAt f x)
    (hf'' : HasDerivAt (deriv f) f'' x) : 0 ≤ f'' := by
  by_contra h
  rw [not_le] at h
  have hderiv0 : deriv f x = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax f x :=
    isLocalMax_of_deriv_deriv_neg (by rw [hf''.deriv]; exact h) hderiv0 hcont
  -- `IsLocalMin ∧ IsLocalMax` ⟹ `f` is locally constant
  have hconst : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmin, hmax] with y hy1 hy2 using le_antisymm hy2 hy1
  -- hence `deriv f` is eventually `0`
  have hderiv_eq : deriv f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.eventuallyEq_nhds] with y hy
    simp [hy.deriv_eq]
  -- `deriv f` therefore has derivative `0` at `x`, forcing `f'' = 0`
  have h0 : HasDerivAt (deriv f) 0 x := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hderiv_eq
  exact h.ne (hf''.unique h0)

/-! ### Fibre multilinearity with model-space fields -/

/- `TangentSpace` is a non-reducible type synonym for the model space.  The
   fields in `indexForm` are model-space valued, so their scalar multiples are
   not syntactically the fibre scalar multiples expected by the metric API.  The
   following small transport lemmas keep that implementation detail out of the
   index-form calculation. -/

theorem metricInner_smul_smul (g : RiemannianMetric I M) (p : M) (c : ℝ)
    (v w : E) :
    g.metricInner p ((c • v : E) : TangentSpace I p) ((c • w : E) : TangentSpace I p) =
      c ^ 2 * g.metricInner p (v : TangentSpace I p) (w : TangentSpace I p) := by
  have hv : c • (v : TangentSpace I p) = ((c • v : E) : TangentSpace I p) := by rfl
  have hw : c • (w : TangentSpace I p) = ((c • w : E) : TangentSpace I p) := by rfl
  have hleft :
      g.metricInner p ((c • v : E) : TangentSpace I p) ((c • w : E) : TangentSpace I p) =
        c * g.metricInner p (v : TangentSpace I p) ((c • w : E) : TangentSpace I p) := by
    simpa only [hv] using g.metricInner_smul_left p c (v : TangentSpace I p)
      ((c • w : E) : TangentSpace I p)
  have hright :
      g.metricInner p (v : TangentSpace I p) ((c • w : E) : TangentSpace I p) =
        c * g.metricInner p (v : TangentSpace I p) (w : TangentSpace I p) := by
    simpa only [hw] using g.metricInner_smul_right p c (v : TangentSpace I p)
      (w : TangentSpace I p)
  rw [hleft, hright]
  ring

theorem curvatureFormAt_smul_snd_fth (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (c : ℝ)
    (v w z q : E) :
    nabla.curvatureFormAt g p (v : TangentSpace I p) ((c • w : E) : TangentSpace I p)
        (z : TangentSpace I p) ((c • q : E) : TangentSpace I p) =
      c ^ 2 * nabla.curvatureFormAt g p (v : TangentSpace I p) (w : TangentSpace I p)
        (z : TangentSpace I p) (q : TangentSpace I p) := by
  have hw : c • (w : TangentSpace I p) = ((c • w : E) : TangentSpace I p) := by rfl
  have hq : c • (q : TangentSpace I p) = ((c • q : E) : TangentSpace I p) := by rfl
  have hfth :
      nabla.curvatureFormAt g p (v : TangentSpace I p) ((c • w : E) : TangentSpace I p)
          (z : TangentSpace I p) ((c • q : E) : TangentSpace I p) =
        c * nabla.curvatureFormAt g p (v : TangentSpace I p) ((c • w : E) : TangentSpace I p)
          (z : TangentSpace I p) (q : TangentSpace I p) := by
    simpa only [hq] using curvatureFormAt_smul_fth g nabla p c
      (v : TangentSpace I p) ((c • w : E) : TangentSpace I p)
      (z : TangentSpace I p) (q : TangentSpace I p)
  have hsnd :
      nabla.curvatureFormAt g p (v : TangentSpace I p) ((c • w : E) : TangentSpace I p)
          (z : TangentSpace I p) (q : TangentSpace I p) =
        c * nabla.curvatureFormAt g p (v : TangentSpace I p) (w : TangentSpace I p)
          (z : TangentSpace I p) (q : TangentSpace I p) := by
    simpa only [hw] using curvatureFormAt_smul_snd g nabla p c
      (v : TangentSpace I p) (w : TangentSpace I p)
      (z : TangentSpace I p) (q : TangentSpace I p)
  rw [hfth, hsnd]
  ring

theorem curvatureFormAt_smul_fst_trd (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (c : ℝ)
    (v w z q : E) :
    nabla.curvatureFormAt g p ((c • v : E) : TangentSpace I p) (w : TangentSpace I p)
        ((c • z : E) : TangentSpace I p) (q : TangentSpace I p) =
      c ^ 2 * nabla.curvatureFormAt g p (v : TangentSpace I p) (w : TangentSpace I p)
        (z : TangentSpace I p) (q : TangentSpace I p) := by
  have hv : c • (v : TangentSpace I p) = ((c • v : E) : TangentSpace I p) := by rfl
  have hz : c • (z : TangentSpace I p) = ((c • z : E) : TangentSpace I p) := by rfl
  have htrd :
      nabla.curvatureFormAt g p ((c • v : E) : TangentSpace I p) (w : TangentSpace I p)
          ((c • z : E) : TangentSpace I p) (q : TangentSpace I p) =
        c * nabla.curvatureFormAt g p ((c • v : E) : TangentSpace I p) (w : TangentSpace I p)
          (z : TangentSpace I p) (q : TangentSpace I p) := by
    simpa only [hz] using curvatureFormAt_smul_trd g nabla p c
      ((c • v : E) : TangentSpace I p) (w : TangentSpace I p)
      (z : TangentSpace I p) (q : TangentSpace I p)
  have hfst :
      nabla.curvatureFormAt g p ((c • v : E) : TangentSpace I p) (w : TangentSpace I p)
          (z : TangentSpace I p) (q : TangentSpace I p) =
        c * nabla.curvatureFormAt g p (v : TangentSpace I p) (w : TangentSpace I p)
          (z : TangentSpace I p) (q : TangentSpace I p) := by
    simpa only [hv] using curvatureFormAt_smul_fst g nabla p c
      (v : TangentSpace I p) (w : TangentSpace I p)
      (z : TangentSpace I p) (q : TangentSpace I p)
  rw [htrd, hfst]
  ring

/-! ### Continuity of curvature coefficients along a parallel frame -/

/-- **Math.** Along a geodesic, the curvature coefficient
`R(γ', W, γ', W)` is continuous when `W` is parallel.  Around each time we
work in one fixed manifold chart.  The geodesic equation makes the chart
velocity continuous, the parallel ODE makes the chart representative of `W`
continuous, and smoothness of the metric and curvature tensor makes their
pairing continuous.  These local statements glue to continuity on the whole
closed interval. -/
theorem continuousOn_velocity_curvature_of_parallel
    (g : RiemannianMetric I M) {W : ℝ → E} {γ : ℝ → M} {a b : ℝ}
    (hW : IsParallelFieldAlongOn (I := I) g γ W a b)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn (I := I) g γ (Set.Icc a b))
    (hγc : ∀ t ∈ Set.Icc a b, ContinuousAt γ t) :
    ContinuousOn (fun t => g.leviCivitaConnection.curvatureFormAt g (γ t)
      (DCVelocity (I := I) γ t) (W t) (DCVelocity (I := I) γ t) (W t))
      (Set.Icc a b) := by
  intro t ht
  have hnhds : γ ⁻¹' (chartAt H (γ t)).source ∈ 𝓝 t :=
    (hγc t ht).preimage_mem_nhds
      ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set c := max a (t - ε / 2) with hc
  set d := min b (t + ε / 2) with hd
  have hsub : Set.Icc c d ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsrc : ∀ τ ∈ Set.Icc c d, γ τ ∈ (chartAt H (γ t)).source := by
    intro τ hτ
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : t - ε / 2 ≤ τ := le_trans (le_max_right _ _) hτ.1
    have h2 : τ ≤ t + ε / 2 := le_trans hτ.2 (min_le_right _ _)
    have habs : |τ - t| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have htcd : t ∈ Set.Icc c d :=
    ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩
  have hnb : Set.Icc c d ∈ 𝓝[Set.Icc a b] t := by
    have hmem : Set.Icc (t - ε / 2) (t + ε / 2) ∈ 𝓝 t :=
      Icc_mem_nhds (by linarith) (by linarith)
    have hinter := inter_mem_nhdsWithin (Set.Icc a b) hmem
    rwa [Set.Icc_inter_Icc] at hinter
  set u : ℝ → E := fun τ => extChartAt I (γ t) (γ τ) with hu_def
  have hu_cont : ContinuousOn u (Set.Icc c d) := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc τ hτ)).comp
        (hγc τ (hsub hτ))).continuousWithinAt
  have hu'_cont : ContinuousOn (deriv u) (Set.Icc c d) := fun τ hτ =>
    (Riemannian.Jacobi.IsGeodesicOn.continuousAt_deriv_extChartAt hgeo
      (hsub hτ) (hγc τ (hsub hτ)) (hsrc τ hτ)).continuousWithinAt
  have hmem : ∀ τ ∈ Set.Icc c d,
      u τ ∈ interior (extChartAt I (γ t)).target := by
    intro τ hτ
    rw [(isOpen_extChartAt_target (I := I) (γ t)).interior_eq]
    exact (extChartAt I (γ t)).map_source
      (by rw [extChartAt_source]; exact hsrc τ hτ)
  have hWrep : ContinuousOn (chartVectorRep (I := I) γ (γ t) W)
      (Set.Icc c d) := by
    intro τ hτ
    exact ((hW.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc) τ hτ).continuousWithinAt
  have hendo : ContinuousOn
      (fun τ => chartCurvatureEndo (I := I) g (γ t) (u τ) (deriv u τ))
      (Set.Icc c d) :=
    continuousOn_chartCurvatureEndo_comp (I := I) g (γ t) hu_cont hu'_cont hmem
  have hmain : ContinuousOn (fun τ => chartMetricInner (I := I) g (γ t) (u τ)
      (chartCurvatureEndo (I := I) g (γ t) (u τ) (deriv u τ)
        (chartVectorRep (I := I) γ (γ t) W τ))
      (chartVectorRep (I := I) γ (γ t) W τ)) (Set.Icc c d) :=
    continuousOn_chartMetricInner_pairing (I := I) g (γ t) hu_cont
      (fun τ hτ => interior_subset (hmem τ hτ)) (hendo.clm_apply hWrep) hWrep
  have hlocal : ContinuousOn (fun τ => g.leviCivitaConnection.curvatureFormAt g (γ τ)
      (DCVelocity (I := I) γ τ) (W τ) (DCVelocity (I := I) γ τ) (W τ))
      (Set.Icc c d) := by
    refine hmain.congr fun τ hτ => ?_
    have hvel := chartVectorRep_velocity (I := I) g (γ t) (hgeo τ (hsub hτ))
      (hγc τ (hsub hτ)) (hsrc τ hτ)
    simp only [chartVectorRep_apply] at hvel
    change tangentCoordChange I (γ τ) (γ t) (γ τ)
      (DCVelocity (I := I) γ τ) =
        deriv (fun s => extChartAt I (γ t) (γ s)) τ at hvel
    have hbridge := chartMetricInner_chartCurvatureEndo_chartVectorRep_eq_curvatureFormAt
      (I := I) g (γ t) (hsrc τ hτ)
        (DCVelocity (I := I) γ τ) (W τ) (W τ)
    rw [hvel] at hbridge
    exact hbridge.symm
  exact (hlocal t htcd).mono_of_mem_nhdsWithin hnb

/-- **Math.** If the geodesic velocity is the nonzero constant multiple
`γ' = ℓ e₀`, continuity of `R(γ',e,γ',e)` gives continuity of the normalized
frame coefficient `R(e₀,e,e₀,e)`. -/
theorem continuousOn_velocitySeeded_curvature
    (g : RiemannianMetric I M) {γ : ℝ → M} {e₀ e : ℝ → E} {a b ℓ : ℝ}
    (hℓ : ℓ ≠ 0)
    (he : IsParallelFieldAlongOn (I := I) g γ e a b)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn (I := I) g γ (Set.Icc a b))
    (hγc : ∀ t ∈ Set.Icc a b, ContinuousAt γ t)
    (hvel : ∀ t ∈ Set.Icc a b,
      DCVelocity (I := I) γ t = (ℓ • e₀ t : TangentSpace I (γ t))) :
    ContinuousOn (fun t => g.leviCivitaConnection.curvatureFormAt g (γ t)
      (e₀ t) (e t) (e₀ t) (e t)) (Set.Icc a b) := by
  have hvcont := continuousOn_velocity_curvature_of_parallel
    (I := I) g he hgeo hγc
  have hscaled : ContinuousOn (fun t => (ℓ ^ 2)⁻¹ *
      g.leviCivitaConnection.curvatureFormAt g (γ t)
        (DCVelocity (I := I) γ t) (e t) (DCVelocity (I := I) γ t) (e t))
      (Set.Icc a b) := continuousOn_const.mul hvcont
  refine hscaled.congr fun t ht => ?_
  rw [hvel t ht, curvatureFormAt_smul_fst_trd]
  field_simp

/-! ### The index form of a scaled parallel field `V = φ·e` -/

/-- **Math.** do Carmo Ch. 9, §3.  The **index form of a scaled field** `V(t) = φ(t)·e(t)`,
whose covariant derivative is `V' = φ'·e` (for `e` parallel), unfolds to
$$I_a(V, V) = \int_a^b\Big((\varphi')^2\,\langle e, e\rangle
  - \varphi^2\,\langle R(\gamma', e)\gamma', e\rangle\Big)\,dt.$$
This is a pointwise multilinear rewrite of `indexForm`: pull the scalars `φ'` and `φ` out of the
metric term (bilinearity) and out of the two `e`-slots of the curvature term
(`curvatureFormAt_smul_snd`/`_fth`).  It needs no parallelism or covariant-pair structure — those
enter only when `e` is a parallel *unit* field, making `⟨e, e⟩ = 1`. -/
theorem indexForm_smul_eq (g : RiemannianMetric I M) (γ : ℝ → M) (e : ℝ → E) (φ : ℝ → ℝ)
    (a b : ℝ) :
    indexForm (I := I) g γ (fun t => φ t • e t) (fun t => deriv φ t • e t) a b
      = ∫ t in a..b, ((deriv φ t) ^ 2 * g.metricInner (γ t) (e t : TangentSpace I (γ t)) (e t)
          - (φ t) ^ 2 * g.leviCivitaConnection.curvatureFormAt g (γ t)
              (DCVelocity (I := I) γ t) (e t) (DCVelocity (I := I) γ t) (e t)) := by
  rw [indexForm_def]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [metricInner_smul_smul, curvatureFormAt_smul_snd_fth]

/-- **Math.** do Carmo Ch. 9, §3, the index form of `V_j = φ·e_j` **evaluated in the
velocity-seeded frame**: if `e` is a `g`-unit field and `γ' = ℓ·e_n` (the frame's distinguished
member, `ℓ = |γ'|`), then
$$I_a(V, V) = \int_a^b\Big((\varphi')^2 - \varphi^2\,\ell^2\,\langle R(e_n, e)e_n, e\rangle\Big)\,dt.$$
The `⟨e, e⟩` factor becomes `1` (orthonormality), and the velocity is pulled out of the two
`γ'`-slots of the curvature term (`γ' = ℓ·e_n`, homogeneity in slots 1 and 3), leaving
`ℓ²⟨R(e_n, e)e_n, e⟩`.  Surface-free: only `indexForm_smul_eq` and multilinearity.  This is do
Carmo's `\sin^2\pi t\,(\pi^2 - \ell^2 K(e_n, e_j))` integrand, with `⟨R(e_n, e)e_n, e⟩` the bare
curvature-form numerator (equal to the sectional curvature `K(e_n, e)` when `e_n ⟂ e` are
orthonormal). -/
theorem indexForm_smul_frame_eq (g : RiemannianMetric I M) (γ : ℝ → M)
    (e en : ℝ → E) (φ : ℝ → ℝ) (ℓ : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hunit : ∀ t ∈ Set.Icc a b, g.metricInner (γ t) (e t : TangentSpace I (γ t)) (e t) = 1)
    (hvel : ∀ t ∈ Set.Icc a b,
      DCVelocity (I := I) γ t = (ℓ • en t : TangentSpace I (γ t))) :
    indexForm (I := I) g γ (fun t => φ t • e t) (fun t => deriv φ t • e t) a b
      = ∫ t in a..b, ((deriv φ t) ^ 2
          - (φ t) ^ 2 * (ℓ ^ 2 * g.leviCivitaConnection.curvatureFormAt g (γ t)
              (en t) (e t) (en t) (e t))) := by
  rw [indexForm_smul_eq]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hab] at ht
  rw [hunit t ht, hvel t ht]
  rw [curvatureFormAt_smul_fst_trd]
  ring

/-! ### do Carmo's contradiction: the summed index form is negative -/

/-- **Math.** The **pure real-analysis core** of do Carmo's Bonnet–Myers contradiction: for any
real `A` and any function `S` continuous on `[0, 1]` with `S(t) > A\pi^2` throughout,
$$\int_0^1\Big(A\,(\pi\cos\pi t)^2 - (\sin\pi t)^2\,S(t)\Big)\,dt < 0.$$
Writing the integrand as `A\pi^2\cos(2\pi t) - (\sin\pi t)^2(S(t) - A\pi^2)`, the first part
integrates to `0` (`∫_0^1 cos(2π t) dt = 0`) and the second is the integral of a function that is
`\ge 0` on `[0,1]` and strictly positive on `(0,1)` (where `\sin\pi t > 0` and `S(t) - A\pi^2 > 0`),
hence strictly positive.  In do Carmo's Bonnet–Myers argument `A = n - 1` and
`S(t) = \ell^2\,\mathrm{Ric}_{\gamma(t)}` — see `sum_indexForm_smul_frame_neg`. -/
theorem integral_frame_sum_lt_zero (A : ℝ) (S : ℝ → ℝ)
    (hScont : ContinuousOn S (Set.Icc 0 1))
    (hS : ∀ t ∈ Set.Icc (0 : ℝ) 1, A * Real.pi ^ 2 < S t) :
    ∫ t in (0 : ℝ)..1,
        (A * (Real.pi * Real.cos (Real.pi * t)) ^ 2 - (Real.sin (Real.pi * t)) ^ 2 * S t) < 0 := by
  have hSuIcc : ContinuousOn S (Set.uIcc (0 : ℝ) 1) := by rwa [Set.uIcc_of_le (by norm_num)]
  set f1 : ℝ → ℝ := fun t => A * Real.pi ^ 2 * Real.cos (2 * Real.pi * t) with hf1
  set f2 : ℝ → ℝ := fun t => (Real.sin (Real.pi * t)) ^ 2 * (S t - A * Real.pi ^ 2) with hf2
  have key : Set.EqOn
      (fun t => A * (Real.pi * Real.cos (Real.pi * t)) ^ 2 - (Real.sin (Real.pi * t)) ^ 2 * S t)
      (fun t => f1 t - f2 t) (Set.uIcc (0 : ℝ) 1) := by
    intro t _
    simp only [hf1, hf2]
    have hc2 : Real.cos (2 * Real.pi * t)
        = Real.cos (Real.pi * t) ^ 2 - Real.sin (Real.pi * t) ^ 2 := by
      rw [show 2 * Real.pi * t = (Real.pi * t) + (Real.pi * t) by ring, Real.cos_add]; ring
    rw [hc2]; ring
  rw [intervalIntegral.integral_congr key]
  have hf1int : IntervalIntegrable f1 volume 0 1 := by
    apply Continuous.intervalIntegrable; simp only [hf1]; fun_prop
  have hf2int : IntervalIntegrable f2 volume 0 1 := by
    apply ContinuousOn.intervalIntegrable; simp only [hf2]
    exact (Continuous.continuousOn (by fun_prop)).mul (hSuIcc.sub continuousOn_const)
  rw [intervalIntegral.integral_sub hf1int hf2int]
  have hint1 : ∫ t in (0 : ℝ)..1, f1 t = 0 := by
    simp only [hf1]; rw [intervalIntegral.integral_const_mul]
    have hcos0 : ∫ t in (0 : ℝ)..1, Real.cos (2 * Real.pi * t) = 0 := by
      have hd : ∀ t : ℝ, HasDerivAt (fun t => Real.sin (2 * Real.pi * t) / (2 * Real.pi))
          (Real.cos (2 * Real.pi * t)) t := by
        intro t
        have h2pi : (2 * Real.pi) ≠ 0 := by positivity
        have h := ((Real.hasDerivAt_sin (2 * Real.pi * t)).comp t
          ((hasDerivAt_id t).const_mul (2 * Real.pi))).div_const (2 * Real.pi)
        simpa [mul_comm, mul_div_assoc, mul_div_cancel_left₀, h2pi] using h
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        (by apply Continuous.intervalIntegrable; fun_prop)]
      have e1 : (2 : ℝ) * Real.pi * 1 = 2 * Real.pi := by ring
      have e0 : (2 : ℝ) * Real.pi * 0 = 0 := by ring
      rw [e1, e0, Real.sin_two_pi, Real.sin_zero]; ring
    rw [hcos0]; ring
  rw [hint1]
  have hint2 : 0 < ∫ t in (0 : ℝ)..1, f2 t := by
    apply intervalIntegral_pos_of_pos_on hf2int _ (by norm_num)
    intro t ht
    simp only [hf2]
    apply mul_pos
    · have hsin : 0 < Real.sin (Real.pi * t) :=
        Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1)
          (by calc Real.pi * t < Real.pi * 1 := mul_lt_mul_of_pos_left ht.2 Real.pi_pos
                _ = Real.pi := mul_one _)
      positivity
    · have := hS t ⟨le_of_lt ht.1, le_of_lt ht.2⟩; linarith
  linarith

/-- **Math.** do Carmo Ch. 9, §3, the heart of the Bonnet–Myers contradiction
(`thm:dc-ch9-3-1`): **the sum of the index forms is strictly negative.**  For fields `e_j` along
`γ : [0, 1] → M` with each `e_j` (`j ≠ n₀`) a `g`-unit field (`hunit`) and velocity
`γ' = ℓ·e_{n₀}` (`hvel`) — in the intended application `e` is the velocity-seeded parallel
orthonormal frame of `exists_velocitySeededParallelOrthoFrameAlongOn`, of which the proof uses
only these two conditions (`e_{n₀}` need not be unit, and no orthogonality among the `e_j` is
assumed) — and with `V_j(t) = (\sin\pi t)\,e_j(t)` and `n ≥ 2` (`hne`: some `j ≠ n₀`),
$$\sum_{j\ne n_0} I_a(V_j, V_j) < 0 \qquad\text{whenever } \pi r < \ell,\ r > 0,$$
provided the raw curvature sum (do Carmo's unnormalized Ricci `Q(e_{n₀}, e_{n₀})`) is bounded
below by `(n-1)/r²` at every `t`.  This packages do Carmo's steps "summing on `j` and using the
definition of Ricci curvature ⇒ `½Σ E_j''(0) < 0`": each summand is `indexForm_smul_frame_eq`
with `φ = \sin\pi t`, and the total integrates to
`∫_0^1 ((n-1)(\pi\cos\pi t)^2 - (\sin\pi t)^2\,\ell^2\,Q)\,dt`, which `integral_frame_sum_lt_zero`
sends below zero because `\ell^2\,Q \ge \ell^2 (n-1)/r^2 > (n-1)\pi^2` when `\ell > \pi r`.

The curvature hypotheses are stated with the raw curvature sum
`∑_{j≠n₀} \langle R(e_{n₀}, e_j)e_{n₀}, e_j\rangle` rather than through `ricciForm`; that sum
equals the unnormalized Ricci form `Q(e_{n₀}, e_{n₀})` by
`ricciForm_self_eq_sum_sectionalCurvature` (`lem:dc-ch9-3-3-ricci-sectional`, for an orthonormal
basis at each `γ(t)`), so `hRic` is do Carmo's `Ric ≥ 1/r²` after clearing the `n-1`
normalization.  Continuity of each curvature term (`hCcont`) holds because the curvature form is
smooth and `γ`, `e` are (piecewise) differentiable; it is taken as a hypothesis here, matching this
chapter's discipline of carrying the analytic side conditions explicitly.

By formula (6) (`lem:dc-ch9-2-10-formula6`) each `I_a(V_j, V_j) = ½E_j''(0)` for the concrete
proper variation with variational field `V_j`; combined with `isLocalMin_deriv_deriv_nonneg`
(a minimizing `γ` forces `E_j''(0) ≥ 0`) this contradicts the strict negativity, giving
`ℓ ≤ π r`.  That last bridge is the concrete exponential variation (`prop:dc-ch9-2-2` +
`prop:dc-ch9-2-8` for `exp`), still open — this lemma is everything up to it. -/
theorem sum_indexForm_smul_frame_neg (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (n₀ : Fin (Module.finrank ℝ E)) (ℓ r : ℝ)
    (hr : 0 < r) (hℓr : Real.pi * r < ℓ)
    (hne : (Finset.univ.erase n₀).Nonempty)
    (hunit : ∀ j ∈ Finset.univ.erase n₀, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      g.metricInner (γ t) (e j t : TangentSpace I (γ t)) (e j t) = 1)
    (hvel : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DCVelocity (I := I) γ t = (ℓ • e n₀ t : TangentSpace I (γ t)))
    (hCcont : ∀ j ∈ Finset.univ.erase n₀,
      ContinuousOn (fun t => g.leviCivitaConnection.curvatureFormAt g (γ t)
        (e n₀ t) (e j t) (e n₀ t) (e j t)) (Set.Icc 0 1))
    (hRic : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((Finset.univ.erase n₀).card : ℝ) / r ^ 2 ≤
        ∑ j ∈ Finset.univ.erase n₀, g.leviCivitaConnection.curvatureFormAt g (γ t)
          (e n₀ t) (e j t) (e n₀ t) (e j t)) :
    ∑ j ∈ Finset.univ.erase n₀,
      indexForm (I := I) g γ (fun t => Real.sin (Real.pi * t) • e j t)
        (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1 < 0 := by
  classical
  have hderiv : deriv (fun t : ℝ => Real.sin (Real.pi * t))
      = fun t => Real.pi * Real.cos (Real.pi * t) := by
    funext t
    have h : HasDerivAt (fun t : ℝ => Real.sin (Real.pi * t))
        (Real.cos (Real.pi * t) * Real.pi) t := by
      simpa using (Real.hasDerivAt_sin (Real.pi * t)).comp t ((hasDerivAt_id t).const_mul Real.pi)
    rw [h.deriv]; ring
  -- step 1: rewrite each index form via the frame formula, with `deriv (sin π·) = π cos π·`
  have step1 : ∀ j ∈ Finset.univ.erase n₀,
      indexForm (I := I) g γ (fun t => Real.sin (Real.pi * t) • e j t)
        (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1
      = ∫ t in (0 : ℝ)..1, ((Real.pi * Real.cos (Real.pi * t)) ^ 2
          - (Real.sin (Real.pi * t)) ^ 2 * (ℓ ^ 2 * g.leviCivitaConnection.curvatureFormAt g (γ t)
              (e n₀ t) (e j t) (e n₀ t) (e j t))) := by
    intro j hj
    rw [indexForm_smul_frame_eq g γ (e j) (e n₀) (fun t => Real.sin (Real.pi * t)) ℓ
      (by norm_num) (hunit j hj) hvel]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hderiv]
  rw [Finset.sum_congr rfl step1]
  -- step 2: swap the finite sum with the integral
  have hint : ∀ j ∈ Finset.univ.erase n₀, IntervalIntegrable
      (fun t => (Real.pi * Real.cos (Real.pi * t)) ^ 2
        - (Real.sin (Real.pi * t)) ^ 2 * (ℓ ^ 2 * g.leviCivitaConnection.curvatureFormAt g (γ t)
            (e n₀ t) (e j t) (e n₀ t) (e j t))) volume 0 1 := by
    intro j hj
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine (Continuous.continuousOn (by fun_prop)).sub (ContinuousOn.mul
      (Continuous.continuousOn (by fun_prop)) (continuousOn_const.mul (hCcont j hj)))
  rw [← intervalIntegral.integral_finsetSum hint]
  -- step 3: collapse the summand to `(n-1)(π cos)² − (sin)²·(ℓ²·∑ Q)`
  have hcombine : Set.EqOn
      (fun t => ∑ j ∈ Finset.univ.erase n₀, ((Real.pi * Real.cos (Real.pi * t)) ^ 2
        - (Real.sin (Real.pi * t)) ^ 2 * (ℓ ^ 2 * g.leviCivitaConnection.curvatureFormAt g (γ t)
            (e n₀ t) (e j t) (e n₀ t) (e j t))))
      (fun t => ((Finset.univ.erase n₀).card : ℝ) * (Real.pi * Real.cos (Real.pi * t)) ^ 2
        - (Real.sin (Real.pi * t)) ^ 2 * (ℓ ^ 2 * ∑ j ∈ Finset.univ.erase n₀,
            g.leviCivitaConnection.curvatureFormAt g (γ t) (e n₀ t) (e j t) (e n₀ t) (e j t)))
      (Set.uIcc (0 : ℝ) 1) := by
    intro t _
    dsimp only
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [intervalIntegral.integral_congr hcombine]
  -- step 4: the arithmetic core
  refine integral_frame_sum_lt_zero _ _ ?_ ?_
  · exact continuousOn_const.mul (continuousOn_finsetSum _ (fun j hj => hCcont j hj))
  · intro t ht
    have hcard : 0 < ((Finset.univ.erase n₀).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    have hr2 : (0 : ℝ) < r ^ 2 := by positivity
    have hRt := hRic t ht
    rw [div_le_iff₀ hr2] at hRt
    have hπr' : Real.pi ^ 2 * r ^ 2 < ℓ ^ 2 := by nlinarith [hℓr, mul_pos Real.pi_pos hr]
    have hsum_pos : 0 < ∑ j ∈ Finset.univ.erase n₀,
        g.leviCivitaConnection.curvatureFormAt g (γ t) (e n₀ t) (e j t) (e n₀ t) (e j t) := by
      nlinarith [hRt, hcard, hr2]
    nlinarith [hRt, hπr', hsum_pos, sq_nonneg Real.pi]

/-- **Math.** do Carmo Ch. 9, §3, the immediate consequence of `sum_indexForm_smul_frame_neg`:
**some** `V_j = (\sin\pi t)\,e_j` has strictly negative index form.  A strictly negative finite
sum has a strictly negative summand.  This is the field do Carmo picks to derive
`E_j''(0) < 0`, contradicting the minimality of `γ` via formula (6) and
`isLocalMin_deriv_deriv_nonneg`. -/
theorem exists_indexForm_smul_frame_neg (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (n₀ : Fin (Module.finrank ℝ E)) (ℓ r : ℝ)
    (hr : 0 < r) (hℓr : Real.pi * r < ℓ)
    (hne : (Finset.univ.erase n₀).Nonempty)
    (hunit : ∀ j ∈ Finset.univ.erase n₀, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      g.metricInner (γ t) (e j t : TangentSpace I (γ t)) (e j t) = 1)
    (hvel : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DCVelocity (I := I) γ t = (ℓ • e n₀ t : TangentSpace I (γ t)))
    (hCcont : ∀ j ∈ Finset.univ.erase n₀,
      ContinuousOn (fun t => g.leviCivitaConnection.curvatureFormAt g (γ t)
        (e n₀ t) (e j t) (e n₀ t) (e j t)) (Set.Icc 0 1))
    (hRic : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((Finset.univ.erase n₀).card : ℝ) / r ^ 2 ≤
        ∑ j ∈ Finset.univ.erase n₀, g.leviCivitaConnection.curvatureFormAt g (γ t)
          (e n₀ t) (e j t) (e n₀ t) (e j t)) :
    ∃ j ∈ Finset.univ.erase n₀,
      indexForm (I := I) g γ (fun t => Real.sin (Real.pi * t) • e j t)
        (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1 < 0 := by
  have hlt : ∑ j ∈ Finset.univ.erase n₀,
      indexForm (I := I) g γ (fun t => Real.sin (Real.pi * t) • e j t)
        (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1
      < ∑ _j ∈ Finset.univ.erase n₀, (0 : ℝ) := by
    rw [Finset.sum_const_zero]
    exact sum_indexForm_smul_frame_neg g γ e n₀ ℓ r hr hℓr hne hunit hvel hCcont hRic
  exact Finset.exists_lt_of_sum_lt hlt

/-! ### The concrete sine exponential variation -/

/-- **Math.** The proper exponential variation used in the Bonnet--Myers
second-variation argument:

`f_j(s,t) = exp_{γ(t)}(s sin(πt)e_j(t))`.

Completeness makes the exponential global, so this is defined for every
`(s,t)`.  The sine factor makes both endpoint curves constant. -/
def bonnetMyersSineVariation (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (γ : ℝ → M) (e : ℝ → E) (x : ℝ × ℝ) : M :=
  Riemannian.Exponential.expMapGlobal (I := I) g hg (γ x.2)
    (x.1 • (Real.sin (Real.pi * x.2) • e x.2))

/-- **Math.** The zero slice of the sine exponential variation is the base
geodesic. -/
@[simp] theorem bonnetMyersSineVariation_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (γ : ℝ → M) (e : ℝ → E) (t : ℝ) :
    bonnetMyersSineVariation (I := I) g hg γ e (0, t) = γ t := by
  rw [bonnetMyersSineVariation, zero_smul]
  change Riemannian.Exponential.expMapGlobal (I := I) g hg (γ t)
    (0 : TangentSpace I (γ t)) = γ t
  exact Riemannian.Exponential.expMapGlobal_zero (I := I) g hg (γ t)

/-- **Math.** The left endpoint curve of the sine variation is constant. -/
@[simp] theorem bonnetMyersSineVariation_left
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (γ : ℝ → M) (e : ℝ → E) (s : ℝ) :
    bonnetMyersSineVariation (I := I) g hg γ e (s, 0) = γ 0 := by
  rw [bonnetMyersSineVariation, mul_zero, Real.sin_zero, zero_smul, smul_zero]
  change Riemannian.Exponential.expMapGlobal (I := I) g hg (γ 0)
    (0 : TangentSpace I (γ 0)) = γ 0
  exact Riemannian.Exponential.expMapGlobal_zero (I := I) g hg (γ 0)

/-- **Math.** The right endpoint curve of the sine variation is constant. -/
@[simp] theorem bonnetMyersSineVariation_right
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (γ : ℝ → M) (e : ℝ → E) (s : ℝ) :
    bonnetMyersSineVariation (I := I) g hg γ e (s, 1) = γ 1 := by
  rw [bonnetMyersSineVariation, mul_one, Real.sin_pi, zero_smul, smul_zero]
  change Riemannian.Exponential.expMapGlobal (I := I) g hg (γ 1)
    (0 : TangentSpace I (γ 1)) = γ 1
  exact Riemannian.Exponential.expMapGlobal_zero (I := I) g hg (γ 1)

/-- **Math.** The variational field of `bonnetMyersSineVariation` along its
zero slice is exactly `sin(πt)e(t)`, read in the chart at the foot `γ(t)`. -/
theorem hasDerivAt_bonnetMyersSineVariation_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (γ : ℝ → M) (e : ℝ → E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => extChartAt I (γ t)
      (bonnetMyersSineVariation (I := I) g hg γ e (s, t)))
      (Real.sin (Real.pi * t) • e t) 0 := by
  simpa only [bonnetMyersSineVariation] using
    Riemannian.Exponential.hasDerivAt_extChartAt_expMapGlobal_smul
      (I := I) g hg (γ t)
        ((Real.sin (Real.pi * t) • e t : E) : TangentSpace I (γ t))

/-- **Math.** Along a parallel field, the concrete Bonnet--Myers sine
variation is genuinely `C^∞` at every point of its zero slice over the interior
of the parallel-transport interval. -/
theorem contMDiffAt_bonnetMyersSineVariation [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {γ : ℝ → M} {e : ℝ → E} {a b t : ℝ}
    (hγc : Continuous γ) (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (he : IsParallelFieldAlongOn (I := I) g γ e a b) (ht : t ∈ Set.Ioo a b) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞
      (bonnetMyersSineVariation (I := I) g hg γ e) (0, t) := by
  exact Riemannian.Exponential.contMDiffAt_expMapGlobal_sine_parallel
    (I := I) g hg hgeo hγc he ht

/-- **Math.** The concrete Bonnet--Myers variation is `C^∞` on one open
product neighbourhood of its full zero slice over `[0,1]`. -/
theorem exists_contMDiffOn_infty_bonnetMyersSineVariation_strip [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {γ : ℝ → M} {e : ℝ → E} {a b : ℝ}
    (hγc : Continuous γ) (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (he : IsParallelFieldAlongOn (I := I) g γ e a b)
    (hsegment : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ J : Set ℝ, IsOpen J ∧ Set.Icc (0 : ℝ) 1 ⊆ J ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (bonnetMyersSineVariation (I := I) g hg γ e) (Set.Ioo (-δ) δ ×ˢ J) := by
  simpa only [bonnetMyersSineVariation] using
    Riemannian.Exponential.exists_contMDiffOn_infty_expMapGlobal_sine_parallel_strip
      (I := I) g hg hgeo hγc he hsegment

/-- **Math.** The concrete Bonnet--Myers variation is `C³` on one open
product neighbourhood of its full zero slice over `[0,1]`.  The time
neighbourhood extends past both endpoints, as required when applying the
proper-variation second-variation formula. -/
theorem exists_contMDiffOn_three_bonnetMyersSineVariation_strip [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {γ : ℝ → M} {e : ℝ → E} {a b : ℝ}
    (hγc : Continuous γ) (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (he : IsParallelFieldAlongOn (I := I) g γ e a b)
    (hsegment : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ J : Set ℝ, IsOpen J ∧ Set.Icc (0 : ℝ) 1 ⊆ J ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3
        (bonnetMyersSineVariation (I := I) g hg γ e) (Set.Ioo (-δ) δ ×ˢ J) := by
  simpa only [bonnetMyersSineVariation] using
    Riemannian.Exponential.exists_contMDiffOn_three_expMapGlobal_sine_parallel_strip
      (I := I) g hg hgeo hγc he hsegment

/-! ### Bonnet--Myers assembly -/

/-- **Math.** The global Ricci lower bound used by the Bonnet--Myers assembly.

`ricciForm` in DoCarmoLib is the unnormalised trace, so the bound is written in the
frame form `(# directions)/r² ≤ Σ⟨R(e₀,eⱼ)e₀,eⱼ⟩`.  Quantifying over every
`g`-orthonormal model frame makes this independent of the frame chosen along a
geodesic, while keeping the normalisation explicit. -/
def HasRicciLowerBound (g : RiemannianMetric I M) (r : ℝ) : Prop :=
  ∀ (p : M) (e : Fin (Module.finrank ℝ E) → E)
    (n₀ : Fin (Module.finrank ℝ E)),
    (∀ i j, g.metricInner p (e i : TangentSpace I p) (e j : TangentSpace I p) =
      if i = j then 1 else 0) →
    ((Finset.univ.erase n₀).card : ℝ) / r ^ 2 ≤
      ∑ j ∈ Finset.univ.erase n₀,
        g.leviCivitaConnection.curvatureFormAt g p
          (e n₀ : TangentSpace I p) (e j : TangentSpace I p)
          (e n₀ : TangentSpace I p) (e j : TangentSpace I p)

/-- **Math.** The data needed to feed the Bonnet--Myers index-form contradiction along
one long, distance-linear geodesic.  The `hindex_nonneg` field is the sole variation
gap: it records the nonnegativity of each index form for the minimizing base curve.
It can be discharged from a proper second variation by
`indexForm_nonneg_of_energyLocalMin` below; no diameter or distance bound is assumed. -/
structure BonnetMyersIndexData (g : RiemannianMetric I M) (γ : ℝ → M) (ℓ : ℝ) where
  e : Fin (Module.finrank ℝ E) → ℝ → E
  n₀ : Fin (Module.finrank ℝ E)
  hne : (Finset.univ.erase n₀).Nonempty
  horth : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
    g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t : TangentSpace I (γ t)) =
      if i = j then 1 else 0
  hunit : ∀ j ∈ Finset.univ.erase n₀, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    g.metricInner (γ t) (e j t : TangentSpace I (γ t)) (e j t) = 1
  hvel : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    DCVelocity (I := I) γ t = (ℓ • e n₀ t : TangentSpace I (γ t))
  hCcont : ∀ j ∈ Finset.univ.erase n₀,
    ContinuousOn (fun t => g.leviCivitaConnection.curvatureFormAt g (γ t)
      (e n₀ t) (e j t) (e n₀ t) (e j t)) (Set.Icc 0 1)
  hindex_nonneg : ∀ j ∈ Finset.univ.erase n₀,
    0 ≤ indexForm (I := I) g γ
      (fun t => Real.sin (Real.pi * t) • e j t)
      (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1

/-- **Math.** The sole analytic fact still needed once the velocity-seeded
parallel orthonormal frame has been constructed geometrically: minimality must
make the index form of every standard sine field nonnegative.  Continuity of
the frame curvature coefficients follows from
`continuousOn_velocitySeeded_curvature`. -/
structure BonnetMyersAnalyticData (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (n₀ : Fin (Module.finrank ℝ E)) where
  hindex_nonneg : ∀ j ∈ Finset.univ.erase n₀,
    0 ≤ indexForm (I := I) g γ
      (fun t => Real.sin (Real.pi * t) • e j t)
      (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1

/-- **Math.** A local energy minimum makes the corresponding index form nonnegative.
This is the short second-variation bridge used by `BonnetMyersIndexData`: if
`E''(0) = 2 I`, then the real second-derivative test gives `0 ≤ I`. -/
theorem indexForm_nonneg_of_energyLocalMin {F : ℝ → ℝ} {Iform : ℝ}
    (hmin : IsLocalMin F 0) (hcont : ContinuousAt F 0)
    (hsecond : HasDerivAt (deriv F) (2 * Iform) 0) : 0 ≤ Iform := by
  have h := isLocalMin_deriv_deriv_nonneg hmin hcont hsecond
  nlinarith

/-- **Math.** Bonnet--Myers (diameter and compactness), with the remaining analytic
variation construction made explicit.

Assume a positive radius `r`, the global unnormalised Ricci bound
`Ric ≥ (n-1)/r²` in `HasRicciLowerBound`, and that every long minimizing geodesic
admits `BonnetMyersIndexData`.  The index-form computation above makes the sum of
the perpendicular index forms strictly negative, while `hindex_nonneg` makes the
same sum nonnegative.  Hopf--Rinow then upgrades the resulting distance bound to
`diam ≤ πr` and compactness.  The only caller-supplied gap is variation/index-form
regularity and nonnegativity; neither the diameter nor a distance upper bound is
assumed. -/
theorem bonnetMyers_diameterBound (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [ConnectedSpace M] [CompleteSpace M]
    {r : ℝ} (hr : 0 < r) (hRic : HasRicciLowerBound (I := I) g r)
    (hvar : ∀ (σ : ℝ → M) (ℓ : ℝ), 0 < ℓ → Real.pi * r < ℓ →
      Riemannian.Geodesic.IsGeodesicOn (I := I) g σ (Set.Icc (0 : ℝ) 1) →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (σ s) (σ t) = |s - t| * ℓ) →
      BonnetMyersIndexData (I := I) g σ ℓ) :
    Metric.diam (Set.univ : Set M) ≤ Real.pi * r ∧ CompactSpace M := by
  have hC : (0 : ℝ) ≤ Real.pi * r := le_of_lt (mul_pos Real.pi_pos hr)
  have hrd : ∀ p q : M, dist p q ≤ Real.pi * r := by
    intro p q
    by_contra h
    rw [not_le] at h
    obtain ⟨σ, hσ0, hσ1, hgeo, hdist⟩ :=
      Riemannian.Geodesic.exists_minimizing_geodesic (I := I) g hg p q
    let ℓ : ℝ := dist p q
    have hℓ : 0 < ℓ := lt_trans (mul_pos Real.pi_pos hr) (by simpa [ℓ] using h)
    have hlong : Real.pi * r < ℓ := by simpa [ℓ] using h
    have hdist' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (σ s) (σ t) = |s - t| * ℓ := by
      intro s hs t ht
      simpa [ℓ] using hdist s hs t ht
    let data : BonnetMyersIndexData (I := I) g σ ℓ := hvar σ ℓ hℓ hlong hgeo hdist'
    have hRic' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ((Finset.univ.erase data.n₀).card : ℝ) / r ^ 2 ≤
          ∑ j ∈ Finset.univ.erase data.n₀,
            g.leviCivitaConnection.curvatureFormAt g (σ t)
              (data.e data.n₀ t) (data.e j t) (data.e data.n₀ t) (data.e j t) := by
      intro t ht
      exact hRic (σ t) (fun i => data.e i t) data.n₀ (data.horth t ht)
    have hneg := sum_indexForm_smul_frame_neg (I := I) g σ data.e data.n₀ ℓ r hr hlong
      data.hne data.hunit data.hvel data.hCcont hRic'
    have hnonneg : 0 ≤ ∑ j ∈ Finset.univ.erase data.n₀,
        indexForm (I := I) g σ
          (fun t => Real.sin (Real.pi * t) • data.e j t)
          (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • data.e j t) 0 1 := by
      exact Finset.sum_nonneg (fun j hj => data.hindex_nonneg j hj)
    linarith
  haveI hProper : ProperSpace M := by
    obtain ⟨p₀⟩ := (inferInstance : Nonempty M)
    exact Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at (I := I) g hg p₀
      ((Riemannian.Geodesic.isGeodesicallyComplete_of_complete (I := I) g hg) p₀)
  refine ⟨Metric.diam_le_of_forall_dist_le hC (fun p _ q _ => hrd p q), ?_⟩
  rw [Metric.compactSpace_iff_isBounded_univ]
  obtain ⟨p₀⟩ := (inferInstance : Nonempty M)
  refine (Metric.isBounded_iff_subset_closedBall p₀).mpr ⟨Real.pi * r, ?_⟩
  intro q hq
  rw [Metric.mem_closedBall, dist_comm]
  exact hrd p₀ q

/-- **Math.** Bonnet--Myers with the parallel-frame construction discharged.

Compared with `bonnetMyers_diameterBound`, this theorem does not ask the caller
to manufacture an orthonormal frame, identify its distinguished member with
the velocity, or prove that a perpendicular direction exists.  Hopf--Rinow
provides a continuous global minimizing geodesic, its speed is the distance it
realizes, and `exists_velocitySeededParallelOrthoFrameAlongOn` supplies the
parallel frame on the enlarged interval `[-1,2]`.  This endpoint room is what
concrete exponential-variation constructions need near `0` and `1`; the index
calculation itself remains on `[0,1]`.  The explicit hypothesis `2 ≤ dim M`
supplies a perpendicular member.  The remaining `hanalytic` premise is exactly
the analytic variation step: nonnegativity of the index forms of `sin(πt)eⱼ`.
Curvature coefficient continuity is derived internally from the geodesic and
parallel-frame data. -/
theorem bonnetMyers_diameterBound_of_analytic (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [ConnectedSpace M] [CompleteSpace M]
    {r : ℝ} (hr : 0 < r) (hdim : 2 ≤ Module.finrank ℝ E)
    (hRic : HasRicciLowerBound (I := I) g r)
    (hanalytic : ∀ (σ : ℝ → M) (ℓ : ℝ), 0 < ℓ → Real.pi * r < ℓ →
      Continuous σ → Riemannian.Geodesic.IsGeodesic (I := I) g σ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (σ s) (σ t) = |s - t| * ℓ) →
      ∀ (e : Fin (Module.finrank ℝ E) → ℝ → E)
        (n₀ : Fin (Module.finrank ℝ E)),
        (∀ i, IsParallelFieldAlongOn (I := I) g σ (e i) (-1) 2) →
        (∀ t ∈ Set.Icc (-1 : ℝ) 2, ∀ i j,
          g.metricInner (σ t) (e i t : TangentSpace I (σ t)) (e j t) =
            if i = j then 1 else 0) →
        (∀ t ∈ Set.Icc (-1 : ℝ) 2,
          DCVelocity (I := I) σ t = (ℓ • e n₀ t : TangentSpace I (σ t))) →
        BonnetMyersAnalyticData (I := I) g σ e n₀) :
    Metric.diam (Set.univ : Set M) ≤ Real.pi * r ∧ CompactSpace M := by
  have hC : (0 : ℝ) ≤ Real.pi * r := le_of_lt (mul_pos Real.pi_pos hr)
  have hrd : ∀ p q : M, dist p q ≤ Real.pi * r := by
    intro p q
    by_contra h
    rw [not_le] at h
    obtain ⟨σ, hσ0, hσ1, hσc, hσgeo, hdist⟩ :=
      Riemannian.Geodesic.exists_minimizing_geodesic_global (I := I) g hg p q
    let ℓ : ℝ := dist p q
    have hℓ : 0 < ℓ := lt_trans (mul_pos Real.pi_pos hr) (by simpa [ℓ] using h)
    have hlong : Real.pi * r < ℓ := by simpa [ℓ] using h
    have hdist' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (σ s) (σ t) = |s - t| * ℓ := by
      intro s hs t ht
      simpa [ℓ] using hdist s hs t ht
    have hspeed : Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g σ 0) = ℓ := by
      have hs := Riemannian.Exponential.sqrt_speedSq_eq_dist_of_minimizing
        (I := I) g hg (lo := (-1 : ℝ)) (hi := (2 : ℝ))
        (q₁ := p) (q₂ := q) (by norm_num) (by norm_num)
        (hσgeo.isGeodesicOn _) hσc.continuousOn hσ0 hσ1 hdist
      simpa [ℓ] using hs
    have hspeedm1 : Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g σ (-1)) = ℓ := by
      rw [(hσgeo.isGeodesicOn Set.univ).speedSq_eq isOpen_univ isPreconnected_univ
        hσc.continuousOn (Set.mem_univ (-1 : ℝ)) (Set.mem_univ (0 : ℝ))]
      exact hspeed
    have hvelm1 : DCVelocity (I := I) σ (-1) ≠ 0 := by
      intro hv
      have hsqm1 : Riemannian.Geodesic.speedSq (I := I) g σ (-1) = 0 := by
        rw [Riemannian.Geodesic.speedSq_def]
        change g.metricInner (σ (-1)) (DCVelocity (I := I) σ (-1))
          (DCVelocity (I := I) σ (-1)) = 0
        rw [hv, g.metricInner_zero_left]
      rw [hsqm1, Real.sqrt_zero] at hspeedm1
      linarith
    obtain ⟨e, n₀, c, hc, hpar, horth, hseed⟩ :=
      exists_velocitySeededParallelOrthoFrameAlongOn (I := I) (a := -1) (b := 2) g (by norm_num)
        (hσgeo.isGeodesicOn _) (fun _ _ => hσc.continuousAt) hvelm1
    have hvelc : ∀ t ∈ Set.Icc (-1 : ℝ) 2,
        DCVelocity (I := I) σ t = (c • e n₀ t : TangentSpace I (σ t)) := by
      intro t ht
      exact ((eq_inv_smul_iff₀ hc.ne').mp (hseed t ht)).symm
    have hc_eq : c = ℓ := by
      have horth0 : g.metricInner (σ 0) (e n₀ 0 : TangentSpace I (σ 0)) (e n₀ 0) = 1 := by
        simpa using horth 0 (by norm_num) n₀ n₀
      have hsq : Riemannian.Geodesic.speedSq (I := I) g σ 0 = c ^ 2 := by
        change g.metricInner (σ 0) (DCVelocity (I := I) σ 0)
          (DCVelocity (I := I) σ 0) = c ^ 2
        rw [hvelc 0 (by norm_num)]
        rw [metricInner_smul_smul, horth0]
        ring
      rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hc] at hspeed
      exact hspeed
    have hvelℓ : ∀ t ∈ Set.Icc (-1 : ℝ) 2,
        DCVelocity (I := I) σ t = (ℓ • e n₀ t : TangentSpace I (σ t)) := by
      simpa only [hc_eq] using hvelc
    have hne : (Finset.univ.erase n₀).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem (Finset.mem_univ n₀), Finset.card_univ,
        Fintype.card_fin]
      omega
    let data : BonnetMyersAnalyticData (I := I) g σ e n₀ :=
      hanalytic σ ℓ hℓ hlong hσc hσgeo hdist' e n₀ hpar horth hvelℓ
    have hCcont : ∀ j ∈ Finset.univ.erase n₀,
        ContinuousOn (fun t => g.leviCivitaConnection.curvatureFormAt g (σ t)
          (e n₀ t) (e j t) (e n₀ t) (e j t)) (Set.Icc 0 1) := by
      intro j hj
      exact (continuousOn_velocitySeeded_curvature (I := I) g hℓ.ne'
        (hpar j) (hσgeo.isGeodesicOn _) (fun _ _ => hσc.continuousAt) hvelℓ).mono
          (by intro t ht; constructor <;> linarith [ht.1, ht.2])
    have hRic' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ((Finset.univ.erase n₀).card : ℝ) / r ^ 2 ≤
          ∑ j ∈ Finset.univ.erase n₀,
            g.leviCivitaConnection.curvatureFormAt g (σ t)
              (e n₀ t) (e j t) (e n₀ t) (e j t) := by
      intro t ht
      exact hRic (σ t) (fun i => e i t) n₀
        (horth t (by constructor <;> linarith [ht.1, ht.2]))
    have hneg := sum_indexForm_smul_frame_neg (I := I) g σ e n₀ ℓ r hr hlong
      hne (fun j _ t ht => by simpa using horth t (by constructor <;> linarith [ht.1, ht.2]) j j)
      (fun t ht => hvelℓ t (by constructor <;> linarith [ht.1, ht.2])) hCcont hRic'
    have hnonneg : 0 ≤ ∑ j ∈ Finset.univ.erase n₀,
        indexForm (I := I) g σ
          (fun t => Real.sin (Real.pi * t) • e j t)
          (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1 := by
      exact Finset.sum_nonneg (fun j hj => data.hindex_nonneg j hj)
    linarith
  haveI hProper : ProperSpace M := by
    obtain ⟨p₀⟩ := (inferInstance : Nonempty M)
    exact Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at (I := I) g hg p₀
      ((Riemannian.Geodesic.isGeodesicallyComplete_of_complete (I := I) g hg) p₀)
  refine ⟨Metric.diam_le_of_forall_dist_le hC (fun p _ q _ => hrd p q), ?_⟩
  rw [Metric.compactSpace_iff_isBounded_univ]
  obtain ⟨p₀⟩ := (inferInstance : Nonempty M)
  refine (Metric.isBounded_iff_subset_closedBall p₀).mpr ⟨Real.pi * r, ?_⟩
  intro q hq
  rw [Metric.mem_closedBall, dist_comm]
  exact hrd p₀ q

end Riemannian.Variation

end
