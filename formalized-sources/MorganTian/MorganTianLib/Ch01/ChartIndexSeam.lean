import MorganTianLib.Ch01.PieceSecondVariation
import MorganTianLib.Ch01.ChartMetricCompatible
import MorganTianLib.Ch01.FrameCurvatureBridge
import MorganTianLib.Ch01.FrameIndexBridge
import MorganTianLib.Ch01.JacobiExistence

/-!
# Poincaré Ch. 1 — the chart ↔ manifold seam for the index integrand

Two index integrands live in the workspace and, until this file, nothing connected
them.

* The **chart** integrand `chartIndexIntegrand G Γ u t` (`PieceSecondVariation`) is what
  the second variation of energy *produces*
  (`deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`): for a two-parameter chart
  family `u : ℝ × ℝ → E` with `Y = ∂_s u` and `X = ∂_t u`, it is Morgan–Tian's
  `G(∇_t Y, ∇_t Y) − G(ℛ(Y, X)X, Y)`, evaluated on the line `s = 0`.
* The **manifold** integrand `⟨DV, DV⟩_g + ℛ(V, γ′, γ′, V)` is what the frame/index-form
  machinery *consumes* (`indexIntegrand_frameVec`, `FrameIndexBridge`).

The seam is `chartIndexIntegrand_eq_metricIndexIntegrand`: with `G = chartMetricBilin g α`
and `Γ = chartChristoffelBilin g α`, for a chart family whose `s = 0` line is the chart
reading of the geodesic `γ` and whose `∂_s`-field on that line is the chart reading of a
field `V` along `γ` with covariant derivative `DV`,

`chartIndexIntegrand (chartMetricBilin g α) (chartChristoffelBilin g α) u t`
  `= ⟨DV t, DV t⟩_g + ℛ(V t, γ′ t, γ′ t, V t)`.

**The sign.** The chart side *subtracts* `G(ℛ(Y, X)X, Y)` while the manifold side *adds*
the curvature form. That is not an inconsistency: the intrinsic curvature form of the
Levi-Civita connection is *minus* the chart Gram pairing of the chart curvature
(`curvatureFormAt_chartVectorRep`, the do Carmo ↔ Morgan–Tian convention flip), i.e.
`ℛ(V, γ′, γ′, V) = −G(ℛ_chart(V_α, u̇)u̇, V_α)`. Subtracting the chart pairing therefore
*is* adding the intrinsic form. This is isolated in `chartCurvatureTerm_eq_curvatureFormAt`.

Three ingredients, each an existing lemma, plus one genuinely new step:

* `chartMetricBilin_chartVectorRep` — the metric half: the chart Gram pairing of chart
  readings is the intrinsic pairing (`chartMetricInner_tangentCoordChange`);
* `chartCurvatureTerm_eq_curvatureFormAt` — the curvature half
  (`curvatureFormAt_chartVectorRep` + `chartVectorRep_velocity_of_geodesicAt`);
* `covDerivAlong_restrict_snd` — **the new step**: the two-parameter covariant
  `t`-derivative at `(0, t)` is the one-parameter covariant derivative of the restricted
  data along the line `s = 0`. This is the chain rule for the injection `t ↦ (0, t)`, and
  it is what lets `covDerivAlong_chartChristoffelBilin_eq` hand the chart family over to
  DoCarmoLib's `covariantDerivCoord`, hence to the manifold covariant derivative.

The hypothesis "`DV` is the covariant derivative of `V` along `γ`" is expressed in the
form the workspace already uses (`covariantDerivCoord` of the chart readings, exactly as
in `IsJacobiFieldOn.covariantDerivCoord_fst`), and
`covariantDerivCoord_chartVectorRep_of_isJacobiFieldAlongOn` discharges it from
`IsJacobiFieldAlongOn`, so the interface is not vacuous.

Blueprint: `claim:second-variation-minimal-geodesic`, `prop:minimal-geodesic-no-conjugate`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.3–§1.4.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

/-! ### Restricting a two-parameter family to the line `s = 0` -/

section Restriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Math.** The injection `s ↦ (0, s)` of the time axis into the parameter square is
linear, with derivative the direction `dt = (0, 1)`. -/
theorem hasDerivAt_zeroLine (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((0 : ℝ), s)) ((0 : ℝ), (1 : ℝ)) t :=
  (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t)

/-- **Math.** **Restriction of a partial derivative.** The `t`-partial derivative of a
family `f : ℝ × ℝ → E` on the line `s = 0` is the ordinary derivative of the restricted
one-parameter map: `∂_{(0,1)} f (0, t) = (d/dt) f(0, t)`. Chain rule for the linear
injection `t ↦ (0, t)`. -/
theorem deriv_restrict_snd (f : ℝ × ℝ → E) {t : ℝ} (hf : DifferentiableAt ℝ f (0, t)) :
    deriv (fun s : ℝ => f (0, s)) t = fderiv ℝ f ((0 : ℝ), t) ((0 : ℝ), (1 : ℝ)) :=
  (hf.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_zeroLine t)).deriv

/-- **Math.** **Restriction of the covariant derivative.** For a two-parameter family
`u` and a field `W` along it, the covariant `t`-derivative at `(0, t)` — the
two-parameter `covDerivAlong Γ u W (0,1)` of `PieceSecondVariation` — is the
one-parameter covariant derivative `covDerivAlong Γ u₀ W₀ 1` of the restrictions
`u₀ = u(0, ·)`, `W₀ = W(0, ·)` to the line `s = 0`.

Both sides are `∂W + Γ(∂u, W)`; the content is only that the partial derivatives in the
direction `(0, 1)` restrict to ordinary derivatives (`deriv_restrict_snd`). This is the
step that hands a chart *family* over to the one-parameter covariant-derivative
dictionary `covDerivAlong_chartChristoffelBilin_eq`. -/
theorem covDerivAlong_restrict_snd (Γ : E → E →L[ℝ] E →L[ℝ] E) (u W : ℝ × ℝ → E) {t : ℝ}
    (hu : DifferentiableAt ℝ u (0, t)) (hW : DifferentiableAt ℝ W (0, t)) :
    covDerivAlong Γ u W ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), t)
      = covDerivAlong Γ (fun s => u (0, s)) (fun s => W (0, s)) 1 t := by
  rw [covDerivAlong_def, covDerivAlong_def, fderiv_apply_one_eq_deriv,
    fderiv_apply_one_eq_deriv, deriv_restrict_snd u hu, deriv_restrict_snd W hW]

end Restriction

/-! ### The seam -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The metric half of the seam.** The chart Gram pairing (`chartMetricBilin`,
the `G` fed to the chart second variation) of the chart readings of two fields along `γ`,
taken at the chart image of the foot, is their intrinsic metric pairing:
`G(φ(γ t))(V_α(t), W_α(t)) = ⟨V t, W t⟩_g`. This is
`chartMetricInner_tangentCoordChange` — the tangent coordinate change is a `g`-isometry —
read through `chartMetricBilin_apply`. -/
theorem chartMetricBilin_chartVectorRep (g : RiemannianMetric I M) {γ : ℝ → M} {α : M}
    {t : ℝ} (hsrc : γ t ∈ (chartAt H α).source) (V W : ℝ → E) :
    chartMetricBilin (I := I) g α (extChartAt I α (γ t))
        (chartVectorRep (I := I) γ α V t) (chartVectorRep (I := I) γ α W t)
      = g.metricInner (γ t) (V t : TangentSpace I (γ t)) (W t) := by
  rw [chartMetricBilin_apply, chartVectorRep_apply, chartVectorRep_apply,
    chartMetricInner_tangentCoordChange (I := I) g hsrc]

/-- **Math.** **The curvature half of the seam, with its sign.** At a time whose foot lies
in the chart at `α`, the chart curvature term of `chartIndexIntegrand` — the chart Gram
pairing `G(ℛ_chart(V_α, u̇)u̇, V_α)`, with `u̇` the chart velocity of the geodesic — is
**minus** the intrinsic curvature form `ℛ(V, γ′, γ′, V)` of the Levi-Civita connection:

`G(φ(γ t))(ℛ_chart(V_α, u̇)u̇, V_α) = −ℛ(V t, γ′ t, γ′ t, V t)`.

This is exactly why Morgan–Tian's chart integrand *subtracts* the curvature pairing while
the manifold integrand *adds* the curvature form: the sign is the do Carmo ↔ Morgan–Tian
convention flip recorded in `curvatureFormAt_chartVectorRep`. The chart velocity is
recognized as the chart reading of `γ′` by `chartVectorRep_velocity_of_geodesicAt`, which
is where the geodesic equation at `t` is used. -/
theorem chartCurvatureTerm_eq_curvatureFormAt (g : RiemannianMetric I M) {γ : ℝ → M}
    {α : M} {t : ℝ} (hsrc : γ t ∈ (chartAt H α).source)
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ t) (hγc : ContinuousAt γ t)
    (V : ℝ → E) :
    chartMetricBilin (I := I) g α (extChartAt I α (γ t))
        (christoffelCurvature (chartChristoffelBilin (I := I) g α)
          (extChartAt I α (γ t)) (chartVectorRep (I := I) γ α V t)
          (deriv (fun s => extChartAt I α (γ s)) t)
          (deriv (fun s => extChartAt I α (γ s)) t))
        (chartVectorRep (I := I) γ α V t)
      = - curvatureFormAt g g.leviCivitaConnection (γ t) (V t : TangentSpace I (γ t))
          (mfderivVelocity (I := I) (E := E) γ t)
          (mfderivVelocity (I := I) (E := E) γ t) (V t) := by
  have hvel : chartVectorRep (I := I) γ α (mfderivVelocity (I := I) γ) t
      = deriv (fun s => extChartAt I α (γ s)) t :=
    chartVectorRep_velocity_of_geodesicAt (I := I) hgeo hγc hsrc
  have h := curvatureFormAt_chartVectorRep (I := I) g hsrc V
    (mfderivVelocity (I := I) γ) (mfderivVelocity (I := I) γ) V
  rw [hvel] at h
  rw [chartMetricBilin_apply, ← chartCurvature_def, h]
  ring

/-- **Math.** **THE SEAM.**  Let `γ` be a curve satisfying the geodesic equation at `t`,
with foot `γ t` inside the chart at `α`, let `V` be a field along `γ` whose covariant
derivative along `γ` is `DV` (expressed as the workspace always does: the chart reading of
`DV` is `covariantDerivCoord` of the chart readings, cf.
`IsJacobiFieldOn.covariantDerivCoord_fst`), and let `u : ℝ × ℝ → E` be a two-parameter
chart family such that near `t`

* the line `s = 0` is the chart reading of `γ`:  `u(0, s) = φ_α(γ s)`;
* the variation field on that line is the chart reading of `V`:
  `∂_s u(0, s) = V_α(s)`.

Then the **chart** index integrand of the second variation of energy is the **manifold**
index integrand consumed by the index form:

`chartIndexIntegrand (chartMetricBilin g α) (chartChristoffelBilin g α) u t`
`  = ⟨DV t, DV t⟩_g + ℛ(V t, γ′ t, γ′ t, V t)`.

The kinetic term is the metric half (`chartMetricBilin_chartVectorRep`) applied to the
covariant derivative, which the restriction lemma `covDerivAlong_restrict_snd` plus the
one-parameter dictionary `covDerivAlong_chartChristoffelBilin_eq` identify with the chart
reading of `DV`; the curvature term is the curvature half
(`chartCurvatureTerm_eq_curvatureFormAt`), whose sign turns the chart subtraction into the
manifold addition.

This is the identity that glues the second variation of energy (which outputs
`chartIndexIntegrand`, `deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`) to the
frame index form (which inputs `⟨DV, DV⟩_g + ℛ(V, γ′, γ′, V)`, `indexIntegrand_frameVec`).
Blueprint: `claim:second-variation-minimal-geodesic`. -/
theorem chartIndexIntegrand_eq_metricIndexIntegrand (g : RiemannianMetric I M)
    {γ : ℝ → M} {α : M} {V DV : ℝ → E} {u : ℝ × ℝ → E} {t : ℝ}
    (hsrc : γ t ∈ (chartAt H α).source)
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ t) (hγc : ContinuousAt γ t)
    (hu : DifferentiableAt ℝ u ((0 : ℝ), t))
    (hW : DifferentiableAt ℝ (fun q : ℝ × ℝ => fderiv ℝ u q ((1 : ℝ), (0 : ℝ)))
      ((0 : ℝ), t))
    (hline : ∀ᶠ s in 𝓝 t, u ((0 : ℝ), s) = extChartAt I α (γ s))
    (hvar : ∀ᶠ s in 𝓝 t, fderiv ℝ u ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ))
      = chartVectorRep (I := I) γ α V s)
    (hDV : covariantDerivCoord (I := I) g α (fun s => extChartAt I α (γ s))
      (chartVectorRep (I := I) γ α V) t = chartVectorRep (I := I) γ α DV t) :
    chartIndexIntegrand (chartMetricBilin (I := I) g α)
        (chartChristoffelBilin (I := I) g α) u t
      = g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t)
        + curvatureFormAt g g.leviCivitaConnection (γ t) (V t : TangentSpace I (γ t))
            (mfderivVelocity (I := I) (E := E) γ t)
            (mfderivVelocity (I := I) (E := E) γ t) (V t) := by
  -- the restricted line and the restricted variation field
  have e1 : (fun s => u ((0 : ℝ), s)) =ᶠ[𝓝 t] fun s => extChartAt I α (γ s) := hline
  have e2 : (fun s => fderiv ℝ u ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ)))
      =ᶠ[𝓝 t] chartVectorRep (I := I) γ α V := hvar
  have hu0 : u ((0 : ℝ), t) = extChartAt I α (γ t) := e1.eq_of_nhds
  have hY : fderiv ℝ u ((0 : ℝ), t) ((1 : ℝ), (0 : ℝ)) = chartVectorRep (I := I) γ α V t :=
    e2.eq_of_nhds
  -- the chart velocity of the geodesic
  have hX : fderiv ℝ u ((0 : ℝ), t) ((0 : ℝ), (1 : ℝ))
      = deriv (fun s => extChartAt I α (γ s)) t := by
    rw [← deriv_restrict_snd u hu]
    exact e1.deriv_eq
  -- the covariant `t`-derivative of the variation field is the chart reading of `DV`
  have hcov : covDerivAlong (chartChristoffelBilin (I := I) g α) u
      (fun q : ℝ × ℝ => fderiv ℝ u q ((1 : ℝ), (0 : ℝ))) ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), t)
      = chartVectorRep (I := I) γ α DV t := by
    have hcongr : covDerivAlong (chartChristoffelBilin (I := I) g α)
        (fun s => u ((0 : ℝ), s))
        (fun s => fderiv ℝ u ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ))) 1 t
        = covDerivAlong (chartChristoffelBilin (I := I) g α)
          (fun s => extChartAt I α (γ s)) (chartVectorRep (I := I) γ α V) 1 t := by
      rw [covDerivAlong_def, covDerivAlong_def, e1.fderiv_eq, e1.eq_of_nhds,
        e2.fderiv_eq, e2.eq_of_nhds]
    rw [covDerivAlong_restrict_snd _ u _ hu hW, hcongr,
      covDerivAlong_chartChristoffelBilin_eq, hDV]
  rw [chartIndexIntegrand, hcov, hu0, hY, hX,
    chartMetricBilin_chartVectorRep (I := I) g hsrc DV DV,
    chartCurvatureTerm_eq_curvatureFormAt (I := I) g hsrc hgeo hγc V]
  ring

/-- **Math.** A `C²` chart family satisfies the two differentiability side conditions of
the seam automatically (`u` and its `s`-partial `∂_s u` are differentiable), so the seam
takes the form the second variation actually hands it: the family it integrates is `C³`.
Same statement as `chartIndexIntegrand_eq_metricIndexIntegrand`, with `hu`/`hW` replaced
by `ContDiff ℝ 2 u`. -/
theorem chartIndexIntegrand_eq_metricIndexIntegrand_of_contDiff (g : RiemannianMetric I M)
    {γ : ℝ → M} {α : M} {V DV : ℝ → E} {u : ℝ × ℝ → E} {t : ℝ}
    (hsrc : γ t ∈ (chartAt H α).source)
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ t) (hγc : ContinuousAt γ t)
    (hu : ContDiff ℝ 2 u)
    (hline : ∀ᶠ s in 𝓝 t, u ((0 : ℝ), s) = extChartAt I α (γ s))
    (hvar : ∀ᶠ s in 𝓝 t, fderiv ℝ u ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ))
      = chartVectorRep (I := I) γ α V s)
    (hDV : covariantDerivCoord (I := I) g α (fun s => extChartAt I α (γ s))
      (chartVectorRep (I := I) γ α V) t = chartVectorRep (I := I) γ α DV t) :
    chartIndexIntegrand (chartMetricBilin (I := I) g α)
        (chartChristoffelBilin (I := I) g α) u t
      = g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t)
        + curvatureFormAt g g.leviCivitaConnection (γ t) (V t : TangentSpace I (γ t))
            (mfderivVelocity (I := I) (E := E) γ t)
            (mfderivVelocity (I := I) (E := E) γ t) (V t) := by
  have hW : ContDiff ℝ 1 (fun q : ℝ × ℝ => fderiv ℝ u q ((1 : ℝ), (0 : ℝ))) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact chartIndexIntegrand_eq_metricIndexIntegrand (I := I) g hsrc hgeo hγc
    (hu.differentiable (by norm_num) _) (hW.differentiable (by norm_num) _) hline hvar hDV

/-! ### Discharging the covariant-derivative hypothesis -/

/-- **Math.** **The hypothesis `hDV` of the seam is dischargeable.** If `(V, DV)` is a
Jacobi field along `γ` in the manifold sense (`IsJacobiFieldAlongOn` — the predicate the
workspace uses for "`DV` is the covariant derivative of `V` along `γ`", plus the Jacobi
equation), then at any interior time whose neighbourhood in `[a, b]` sits in the chart at
`α`, the chart reading of `DV` is `covariantDerivCoord` of the chart reading of `V`, which
is exactly the form the seam asks for. Localization
(`IsJacobiFieldAlongOn.isJacobiFieldOn_of_mem_source`) followed by
`IsJacobiFieldOn.covariantDerivCoord_fst`. -/
theorem covariantDerivCoord_chartVectorRep_of_isJacobiFieldAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV : ℝ → E} {a b : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ V DV a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {α : M} {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (hsrc : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H α).source)
    {t : ℝ} (ht : t ∈ Ioo c d) :
    covariantDerivCoord (I := I) g α (fun s => extChartAt I α (γ s))
        (chartVectorRep (I := I) γ α V) t = chartVectorRep (I := I) γ α DV t :=
  (hJac.isJacobiFieldOn_of_mem_source hgeo hγc hsub hsrc).covariantDerivCoord_fst ht

end MorganTianLib

#print axioms MorganTianLib.covDerivAlong_restrict_snd
#print axioms MorganTianLib.chartMetricBilin_chartVectorRep
#print axioms MorganTianLib.chartCurvatureTerm_eq_curvatureFormAt
#print axioms MorganTianLib.chartIndexIntegrand_eq_metricIndexIntegrand
#print axioms MorganTianLib.chartIndexIntegrand_eq_metricIndexIntegrand_of_contDiff
#print axioms MorganTianLib.covariantDerivCoord_chartVectorRep_of_isJacobiFieldAlongOn
