/- Vendored from DoCarmo `OpenGALib/Riemannian/Exponential/RayGeodesic.lean`.
   Namespace `Riemannian` mapped to `PetersenLib`; engineering infrastructure only,
   not a blueprint node. -/
import PetersenLib.Vendored.OpenGA.Exponential.RayODE
import PetersenLib.Vendored.OpenGA.Geodesic.EquationTransfer

/-!
# Exponential rays are intrinsic geodesics (do Carmo Ch. 3 §2, Ch. 7 §2)

do Carmo, *Riemannian Geometry*, Ch. 3, Prop. 2.7 and the definition of the
exponential map: the ray `t ↦ exp_p(t·u)` *is* the geodesic through `p` with
initial velocity `u`. The exponential-map files state this in the
chart-anchored language (`IsGeodesicOnWithInitial`, `maximalGeodesic`); the
Hopf–Rinow argument (do Carmo Ch. 7, Thm. 2.8) needs it in the *intrinsic*,
moving-chart form `IsGeodesicOn` used by the metric layer: the geodesic-sphere
step produces sphere points `exp_p z` that must then be joined to `p` by an
honest geodesic segment.

`exists_isGeodesicOn_expMap_ray` packages this: there are `ρ > 0` and `b > 1`
such that for every `‖u‖ < ρ` the ray `t ↦ exp_p(t·u)` is defined and stays in
the chart on `|t| < b`, starts at `p` with chart velocity `u`, is continuous,
and satisfies the intrinsic geodesic equation on `(-b, b) ⊃ [0, 1]`.

The proof combines the ray ODE (`exists_expMap_ray_ode_ball`: the chart
reading of `exp_p` is `C²` and its rays solve the chart-`p` geodesic ODE) with
the chart-independence of the geodesic equation
(`SolvesGeodesicODEAt.hasGeodesicEquationAt`).
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

namespace PetersenLib

namespace Exponential

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **Exponential rays are intrinsic geodesics** (do Carmo Ch. 3,
Prop. 2.7 / definition of `exp_p`, in the moving-chart form consumed by the
Hopf–Rinow theorem). There are `ρ > 0` and `b > 1` such that:

* for `‖u‖ < ρ` and `|t| < b` the vector `t·u` is in the exponential domain
  and `exp_p(t·u)` stays in the chart at `p`;
* for every `‖u‖ < ρ`, the ray `γ_u : t ↦ exp_p(t·u)` starts at `p` with chart
  velocity `u` at `t = 0`, is continuous on `(-b, b)`, and satisfies the
  intrinsic geodesic equation (`IsGeodesicOn`, do Carmo Ch. 3, Def. 2.1) on
  `(-b, b)`.

Since `b > 1`, the segment `[0, 1]` — reaching `exp_p u` — is always covered. -/
theorem exists_isGeodesicOn_expMap_ray (g : RiemannianMetric I M) (p : M) :
    ∃ ρ b : ℝ, 0 < ρ ∧ 1 < b ∧
      (∀ (u : E) (t : ℝ), ‖u‖ < ρ → |t| < b →
        ((t • u : E) : TangentSpace I p) ∈ expDomain (I := I) g p ∧
        expMap (I := I) g p ((t • u : E) : TangentSpace I p) ∈
          (chartAt H p).source) ∧
      ∀ u : E, ‖u‖ < ρ →
        (fun t : ℝ => expMap (I := I) g p ((t • u : E) : TangentSpace I p)) 0 = p ∧
        HasDerivAt (fun t : ℝ =>
          extChartAt I p (expMap (I := I) g p ((t • u : E) : TangentSpace I p))) u 0 ∧
        ContinuousOn
          (fun t : ℝ => expMap (I := I) g p ((t • u : E) : TangentSpace I p))
          (Ioo (-b) b) ∧
        IsGeodesicOn (I := I) g
          (fun t : ℝ => expMap (I := I) g p ((t • u : E) : TangentSpace I p))
          (Ioo (-b) b) := by
  classical
  obtain ⟨ρ₀, b, hρ₀, hb, hadm, hC2, hDf0, hode⟩ :=
    exists_expMap_ray_ode_ball (I := I) g p
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  refine ⟨ρ₀ / b, b, by positivity, hb, ?_, ?_⟩
  · intro u t hu ht
    exact hadm u t (hu.trans_le (div_le_self hρ₀.le hb.le)) ht
  intro u hu
  have hu₀ : ‖u‖ < ρ₀ := hu.trans_le (div_le_self hρ₀.le hb.le)
  -- scaled vectors stay in the `C²` ball
  have htu_ball : ∀ t : ℝ, |t| < b → ‖t • u‖ < ρ₀ := by
    intro t ht
    rcases eq_or_ne u 0 with rfl | hne
    · simpa using hρ₀
    · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hne
      calc ‖t • u‖ = |t| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ < b * (ρ₀ / b) := mul_lt_mul'' ht hu (abs_nonneg t) hupos.le
        _ = ρ₀ := by field_simp
  have hsrc_t : ∀ t : ℝ, |t| < b →
      expMap (I := I) g p ((t • u : E) : TangentSpace I p) ∈ (chartAt H p).source :=
    fun t ht => (hadm u t hu₀ ht).2
  -- the chart reading of the ray and its first derivative
  have hderiv : ∀ t : ℝ, |t| < b →
      HasDerivAt (fun s : ℝ =>
          extChartAt I p (expMap (I := I) g p ((s • u : E) : TangentSpace I p)))
        (fderiv ℝ (fun w : E =>
          extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) (t • u) u)
        t := by
    intro t ht
    have hmem : (t • u : E) ∈ ball (0 : E) ρ₀ :=
      mem_ball_zero_iff.mpr (htu_ball t ht)
    have hf_at : HasFDerivAt
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (fderiv ℝ (fun w : E =>
          extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) (t • u))
        (t • u) :=
      ((hC2.contDiffAt (isOpen_ball.mem_nhds hmem)).differentiableAt
        two_ne_zero).hasFDerivAt
    have hsmul : HasDerivAt (fun s : ℝ => s • u) u t := by
      simpa using (hasDerivAt_id t).smul_const u
    simpa using hf_at.comp_hasDerivAt t hsmul
  -- start point
  have hstart : (fun t : ℝ =>
      expMap (I := I) g p ((t • u : E) : TangentSpace I p)) 0 = p := by
    show expMap (I := I) g p (((0 : ℝ) • u : E) : TangentSpace I p) = p
    rw [zero_smul]
    exact expMap_zero (I := I) g p
  -- chart velocity `u` at `t = 0`
  have hvel : HasDerivAt (fun t : ℝ =>
      extChartAt I p (expMap (I := I) g p ((t • u : E) : TangentSpace I p))) u 0 := by
    have h := hderiv 0 (by simpa using hb0)
    rw [zero_smul, hDf0] at h
    simpa using h
  -- continuity of the ray on `(-b, b)`
  have hread_cont : ContinuousOn
      (fun t : ℝ =>
        extChartAt I p (expMap (I := I) g p ((t • u : E) : TangentSpace I p)))
      (Ioo (-b) b) := by
    intro t ht
    exact ((hderiv t (abs_lt.mpr ⟨ht.1, ht.2⟩)).continuousAt).continuousWithinAt
  have hcont : ContinuousOn
      (fun t : ℝ => expMap (I := I) g p ((t • u : E) : TangentSpace I p))
      (Ioo (-b) b) := by
    have hmap : MapsTo
        (fun t : ℝ =>
          extChartAt I p (expMap (I := I) g p ((t • u : E) : TangentSpace I p)))
        (Ioo (-b) b) (extChartAt I p).target := by
      intro t ht
      exact (extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hsrc_t t (abs_lt.mpr ⟨ht.1, ht.2⟩))
    refine (((continuousOn_extChartAt_symm p).comp hread_cont hmap)).congr ?_
    intro t ht
    show expMap (I := I) g p ((t • u : E) : TangentSpace I p)
      = (extChartAt I p).symm
          (extChartAt I p (expMap (I := I) g p ((t • u : E) : TangentSpace I p)))
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hsrc_t t (abs_lt.mpr ⟨ht.1, ht.2⟩))).symm
  refine ⟨hstart, hvel, hcont, ?_⟩
  -- the intrinsic geodesic equation, via the fixed-chart ODE at `p`
  intro t ht
  have ht' : |t| < b := abs_lt.mpr ⟨ht.1, ht.2⟩
  -- the chart-`p` reading of the ray is exactly `s ↦ f(s • u)`
  have hread : chartReading (I := I) p
      (fun s : ℝ => expMap (I := I) g p ((s • u : E) : TangentSpace I p))
      = fun s : ℝ =>
        extChartAt I p (expMap (I := I) g p ((s • u : E) : TangentSpace I p)) := rfl
  -- `deriv` of the reading agrees with the ray velocity on the open interval
  have hderiv_eq : ∀ τ : ℝ, |τ| < b →
      deriv (fun s : ℝ =>
        extChartAt I p (expMap (I := I) g p ((s • u : E) : TangentSpace I p))) τ
      = fderiv ℝ (fun w : E =>
          extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) (τ • u) u :=
    fun τ hτ => (hderiv τ hτ).deriv
  have hIoo_mem : Ioo (-b) b ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
  have hsolves : SolvesGeodesicODEAt (I := I) g p
      (fun s : ℝ => expMap (I := I) g p ((s • u : E) : TangentSpace I p)) t := by
    constructor
    · -- the reading is differentiable near `t`, with derivative `deriv`
      filter_upwards [hIoo_mem] with τ hτ
      rw [hread, hderiv_eq τ (abs_lt.mpr ⟨hτ.1, hτ.2⟩)]
      exact hderiv τ (abs_lt.mpr ⟨hτ.1, hτ.2⟩)
    · -- the second-order chart geodesic ODE, from the ray ODE
      refine ⟨- Geodesic.chartChristoffelContraction (I := I) g p
          (fderiv ℝ (fun w : E =>
            extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) (t • u) u)
          (fderiv ℝ (fun w : E =>
            extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) (t • u) u)
          (extChartAt I p
            (expMap (I := I) g p ((t • u : E) : TangentSpace I p))), ?_, ?_⟩
      · -- the ray ODE gives the derivative of the velocity field
        have hode_t := hode u t hu₀ ht' (htu_ball t ht')
        refine hode_t.congr_of_eventuallyEq ?_
        filter_upwards [hIoo_mem] with τ hτ
        rw [hread, hderiv_eq τ (abs_lt.mpr ⟨hτ.1, hτ.2⟩)]
      · -- `-Γ + Γ = 0` after identifying the velocity and the base point
        rw [hread, hderiv_eq t ht']
        exact neg_add_cancel _
  exact hsolves.hasGeodesicEquationAt
    (hcont.continuousAt hIoo_mem)
    (hsrc_t t ht')

end Exponential

end PetersenLib
