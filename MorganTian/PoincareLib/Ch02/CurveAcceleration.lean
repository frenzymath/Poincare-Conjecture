import PoincareLib.Ch02.CovDerivAlongCurve

/-!
# Morgan–Tian Ch. 2 — existence of the acceleration of a smooth curve

For a smooth curve `γ : ℝ → M`, the velocity field `curveVelocity γ` has a
covariant derivative (its **acceleration** `Dγ'/dt`) at every base time.  This
is the general, non-geodesic companion of
`hasGeodesicEquationAt_iff_hasCovDerivAlongAt_velocity_zero` (which specialises
to `Dγ'/dt = 0`), and the foundational primitive behind the
tangential-acceleration fact `Dγ'/dt ∈ T_{γ}N_c` used in the totally-geodesic
part (item 3) of `lem:parallel-gradient-level-sets`.

The proof reads `γ` in the moving-foot chart: the chart curve
`s ↦ φ_{γ t₀}(γ s)` is `C^∞` at `t₀` (composition of the smooth curve with the
smooth chart), hence twice differentiable there, which is exactly the data the
covariant-derivative predicate `HasCovDerivAlongAt` requires.
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** The chart curve `s ↦ φ_{γ t₀}(γ s)` of a smooth curve is smooth
(`C^∞`) at the base time: it is the composition of the smooth curve `γ` with the
(smooth) extended chart centred at `γ t₀`. -/
theorem contDiffAt_chartLocalCurve {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t₀ : ℝ) :
    ContDiffAt ℝ ∞ (chartLocalCurve (I := I) γ t₀) t₀ := by
  rw [← contMDiffAt_iff_contDiffAt]
  have hsource : (chartAt H (γ t₀)).source ∈ 𝓝 (γ t₀) :=
    (chartAt H (γ t₀)).open_source.mem_nhds (mem_chart_source H (γ t₀))
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I (γ t₀)) (γ t₀) :=
    (contMDiffOn_extChartAt (I := I)).contMDiffAt hsource
  exact hchart.comp t₀ hγ.contMDiffAt

/-- **Math.** **Existence of the acceleration** of a smooth curve: the velocity
field `curveVelocity γ` of a `C^∞` curve `γ` has a covariant derivative
`Dγ'/dt (t₀) ∈ T_{γ t₀}M` at every time `t₀`.  Blueprint
`lem:parallel-gradient-level-sets`, item (3) infrastructure (the acceleration
whose tangency to `N_c` is the content of `eq:tangential-acceleration`). -/
theorem exists_hasCovDerivAlongAt_curveVelocity {g : RiemannianMetric I M}
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t₀ : ℝ) :
    ∃ A : E, HasCovDerivAlongAt (I := I) g γ (curveVelocity (I := I) γ) t₀ A := by
  have hcd : ContDiffAt ℝ 2 (chartLocalCurve (I := I) γ t₀) t₀ :=
    (contDiffAt_chartLocalCurve hγ t₀).of_le (by norm_cast)
  -- the curve stays in the moving-foot chart source near `t₀`
  have hmem : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H (γ t₀)).source := by
    have hsource : (chartAt H (γ t₀)).source ∈ 𝓝 (γ t₀) :=
      (chartAt H (γ t₀)).open_source.mem_nhds (mem_chart_source H (γ t₀))
    exact hγ.continuous.continuousAt.preimage_mem_nhds hsource
  -- first derivative (chart velocity) exists at `t₀`
  have hv : HasDerivAt (chartLocalCurve (I := I) γ t₀)
      (deriv (chartLocalCurve (I := I) γ t₀) t₀) t₀ :=
    (hcd.differentiableAt (by norm_num)).hasDerivAt
  -- the chart curve is differentiable on a neighbourhood of `t₀`
  have hdiff_ev : ∀ᶠ s in 𝓝 t₀, HasDerivAt (chartLocalCurve (I := I) γ t₀)
      (deriv (chartLocalCurve (I := I) γ t₀) s) s := by
    filter_upwards [hcd.eventually (by norm_num)] with s hs
      using (hs.differentiableAt (by norm_num)).hasDerivAt
  -- second derivative (acceleration in coordinates) exists at `t₀`
  have hderiv_diff : DifferentiableAt ℝ (deriv (chartLocalCurve (I := I) γ t₀)) t₀ := by
    have hf2 : ContDiffAt ℝ 1
        (fun x => fderiv ℝ (chartLocalCurve (I := I) γ t₀) x) t₀ :=
      hcd.fderiv_right (by norm_num)
    have hd2 : DifferentiableAt ℝ
        (fun x => fderiv ℝ (chartLocalCurve (I := I) γ t₀) x) t₀ :=
      hf2.differentiableAt (by norm_num)
    have happ : DifferentiableAt ℝ
        (fun x => (fderiv ℝ (chartLocalCurve (I := I) γ t₀) x) 1) t₀ :=
      hd2.clm_apply (differentiableAt_const (1 : ℝ))
    simpa only [fderiv_apply_one_eq_deriv] using happ
  set dV := deriv (deriv (chartLocalCurve (I := I) γ t₀)) t₀ with hdVdef
  refine ⟨dV + chartChristoffelContraction (I := I) g (γ t₀)
      (deriv (chartLocalCurve (I := I) γ t₀) t₀) (curveVelocity (I := I) γ t₀)
      (extChartAt I (γ t₀) (γ t₀)), hmem,
      deriv (chartLocalCurve (I := I) γ t₀) t₀, dV, hv, ?_, rfl⟩
  -- the chart-coordinate velocity field equals the chart-curve derivative near `t₀`
  have hveq : (fun s => chartFieldCoord (I := I) (γ t₀) γ (curveVelocity (I := I) γ) s)
      =ᶠ[𝓝 t₀] fun s => deriv (chartLocalCurve (I := I) γ t₀) s := by
    filter_upwards [hmem.eventually_nhds, hdiff_ev] with s hs hd
    exact chartFieldCoord_curveVelocity_eq (I := I) hs hd
  exact (hderiv_diff.hasDerivAt).congr_of_eventuallyEq hveq

end PoincareLib

end
