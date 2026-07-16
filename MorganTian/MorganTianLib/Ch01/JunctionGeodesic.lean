import MorganTianLib.Ch01.GaussLemma
import MorganTianLib.Ch01.GeodesicRegularity

/-!
# Poincaré Ch. 1 — geodesic hypotheses of the piece second variation, in chart form

The piece second-variation theorem
`MorganTianLib.deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`
consumes three purely **chart-level** hypotheses about the two-parameter family
`u : ℝ × ℝ → E` (with `q = (s, t)`, `∂_s = (1,0)`, `∂_t = (0,1)`):

* `hgeo` : `covDerivAlong Γ u (fun q => fderiv ℝ u q (0,1)) (0,1) (0,t) = 0` — the
  `t`-line at `s = 0` is a geodesic in the chart;
* `hj₀`, `hj₁` : `covDerivAlong Γ u (fun q => fderiv ℝ u q (1,0)) (1,0) (0,τᵢ) = 0` — the
  two **junction curves** `s ↦ u (s, τᵢ)` are geodesics in the chart.

The **manifold** data, by contrast, gives genuine manifold geodesics: `γ` itself, and the
junction curves `globalGeodesic g hg (γ τᵢ) (Y τᵢ)`.  This file bridges the two.

## Contents

*Chart-free restriction (pure chain rule).*
* `deriv_comp_affineLine` — `d/dr (u (a + r • d)) = (∂_d u)(a + r • d)`;
* `covDerivAlong_affineLine` — **the restriction lemma**: for `C²` `u`,
  `covDerivAlong Γ u (∂_d u) d (a + t • d) = covDerivAlong Γ c ċ 1 t` for the slice
  `c r = u (a + r • d)`.  The two-parameter chart geodesic expression along an affine
  line *is* the one-parameter one of the slice.

*Manifold ⟹ chart (the geodesic equation transfers).*
* `covDerivAlong_deriv_chartReading_eq_zero_of_geodesicAt` — a manifold geodesic whose
  foot at time `τ` lies in the source of the chart at `α` satisfies the chart geodesic
  ODE `∇_{u̇}u̇ = 0` **in that chart**, in the `covDerivAlong` form.  This is
  `Geodesic.HasGeodesicEquationAt.solvesGeodesicODEAt` (the chart-change transfer)
  read through `covDerivAlong_chartChristoffelBilin_eq`.

*The three hypotheses.*
* `covDerivAlong_eq_zero_of_geodesic_slice` — the general form: if the slice of `u`
  along the affine line `r ↦ a + r • d` reads a manifold geodesic in the chart at `α`,
  then the chart geodesic expression vanishes at `a + t • d`;
* `covDerivAlong_snd_eq_zero_of_geodesic_tline` — the `hgeo` shape;
* `covDerivAlong_fst_eq_zero_of_geodesic_junction` — the `hj₀`/`hj₁` shape;
* `covDerivAlong_fst_eq_zero_of_globalGeodesic_junction` — the same, applied to the
  actual junction curve `globalGeodesic g hg (γ τ) w`.

The point recorded in the design of the piece lemma is exactly this: the boundary term
of the second variation dies **in every chart**, because the geodesic equation is
chart-independent (`SolvesGeodesicODEAt.transfer`).  No telescoping across pieces, no
chart-change law for the boundary function.

Blueprint: `claim:second-variation-minimal-geodesic`, `prop:minimal-geodesic-no-conjugate`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.3.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

/-! ### Chart-free: restricting the covariant derivative to an affine line

This section is pure calculus in a normed space: no manifold, no metric.  `u : P → E`
is a family, `d : P` a direction, and we compare the directional covariant derivative
of `∂_d u` at a point of the affine line `r ↦ a + r • d` with the one-dimensional
covariant derivative of the restriction of `u` to that line. -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Math.** The affine line `r ↦ a + r • d` has derivative `d`. -/
theorem hasDerivAt_affineLine (a d : P) (t : ℝ) :
    HasDerivAt (fun r : ℝ => a + r • d) d t := by
  simpa using ((hasDerivAt_id t).smul_const d).const_add a

/-- **Math.** **Chain rule along an affine line.** The derivative of the slice
`r ↦ u (a + r • d)` is the directional derivative `(∂_d u)(a + r • d)`. -/
theorem deriv_comp_affineLine {u : P → E} {a d : P} {t : ℝ}
    (hu : DifferentiableAt ℝ u (a + t • d)) :
    deriv (fun r : ℝ => u (a + r • d)) t = fderiv ℝ u (a + t • d) d :=
  (hu.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_affineLine a d t)).deriv

/-- **Math.** **The restriction lemma.** For a `C²` family `u : P → E`, the
two-parameter chart geodesic expression `∇_d (∂_d u)` evaluated at a point
`a + t • d` of an affine line equals the one-parameter expression `∇_1 ċ` of the
slice `c r = u (a + r • d)`.  This is the whole content of "the `t`-line (resp.
the junction curve) is a geodesic in the chart": it is a statement about the
one-dimensional curve, read two-dimensionally. -/
theorem covDerivAlong_affineLine (Γ : E → E →L[ℝ] E →L[ℝ] E) {u : P → E}
    (hu : ContDiff ℝ 2 u) (a d : P) (t : ℝ) :
    covDerivAlong Γ u (fun q => fderiv ℝ u q d) d (a + t • d)
      = covDerivAlong Γ (fun r : ℝ => u (a + r • d))
          (deriv fun r : ℝ => u (a + r • d)) 1 t := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  -- the slice's derivative is the directional derivative, at every time
  have hdc : (deriv fun r : ℝ => u (a + r • d)) = fun r : ℝ => fderiv ℝ u (a + r • d) d := by
    funext r
    exact deriv_comp_affineLine (hu1 _)
  -- `∂_d u` is itself `C¹`, hence differentiable
  have hfd : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hV : Differentiable ℝ fun q : P => fderiv ℝ u q d := fun q =>
    (hfd q).clm_apply (differentiableAt_const d)
  -- the second derivative of the slice is the directional derivative of `∂_d u`
  have hdd : deriv (deriv fun r : ℝ => u (a + r • d)) t
      = fderiv ℝ (fun q : P => fderiv ℝ u q d) (a + t • d) d := by
    rw [hdc]
    exact deriv_comp_affineLine (u := fun q : P => fderiv ℝ u q d) (hV _)
  rw [covDerivAlong_def, covDerivAlong_def]
  have h1 : fderiv ℝ (deriv fun r : ℝ => u (a + r • d)) t 1
      = deriv (deriv fun r : ℝ => u (a + r • d)) t := rfl
  have h2 : fderiv ℝ (fun r : ℝ => u (a + r • d)) t 1
      = deriv (fun r : ℝ => u (a + r • d)) t := rfl
  rw [h1, h2, hdd, hdc]

end Abstract

/-! ### Manifold geodesic ⟹ the chart geodesic ODE, in any chart containing the foot -/

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : RiemannianMetric I M} {γ : ℝ → M} {τ : ℝ}

/-- **Math.** **The geodesic equation in a fixed chart, in `covDerivAlong` form.**
If `γ` is a manifold geodesic at time `τ` (moving-foot equation) and its foot lies
in the source of the chart at `α`, then the chart reading `û = φ_α ∘ γ` satisfies
`∇_{û̇} û̇ = û'' + Γ_α(û̇, û̇)(û) = 0` at `τ`, in the chart at `α` — **any** chart
whose source contains the foot, not just the moving-foot chart.  The chart-change
transfer `Geodesic.SolvesGeodesicODEAt.transfer` is what makes this true, and it is
why the boundary term of the second variation vanishes in every chart. -/
theorem covDerivAlong_deriv_chartReading_eq_zero_of_geodesicAt
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ τ) (hc : ContinuousAt γ τ)
    {α : M} (hsrc : γ τ ∈ (chartAt H α).source) :
    covDerivAlong (chartChristoffelBilin (I := I) g α)
        (fun s => extChartAt I α (γ s))
        (deriv fun s => extChartAt I α (γ s)) 1 τ = 0 := by
  rw [covDerivAlong_chartChristoffelBilin_eq]
  exact covariantDerivCoord_deriv_extChartAt_eq_zero_of_geodesicAt (I := I) h hc hsrc

/-- **Math.** **The conversion lemma.** Let `u : P → E` be a `C²` family which, along
the affine line `r ↦ a + r • d`, is the chart-`α` reading of a manifold geodesic `γ`
(near time `t`).  If the foot `γ t` lies in the source of the chart at `α`, then the
chart geodesic expression `∇_d(∂_d u)` vanishes at the point `a + t • d`.

This is exactly the shape of the hypotheses `hgeo`, `hj₀`, `hj₁` of
`deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`: a *manifold* geodesic
hypothesis on a slice of the family produces the *chart* geodesic ODE. -/
theorem covDerivAlong_eq_zero_of_geodesic_slice {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {u : P → E} (hu : ContDiff ℝ 2 u) {a d : P} {t : ℝ}
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ t) (hc : ContinuousAt γ t)
    {α : M} (hsrc : γ t ∈ (chartAt H α).source)
    (hslice : (fun r : ℝ => u (a + r • d)) =ᶠ[𝓝 t] fun r : ℝ => extChartAt I α (γ r)) :
    covDerivAlong (chartChristoffelBilin (I := I) g α) u
        (fun q => fderiv ℝ u q d) d (a + t • d) = 0 := by
  rw [covDerivAlong_affineLine _ hu a d t]
  set c : ℝ → E := fun r : ℝ => u (a + r • d) with hcdef
  set w : ℝ → E := fun s => extChartAt I α (γ s) with hwdef
  have hd : deriv c =ᶠ[𝓝 t] deriv w := hslice.deriv
  rw [covDerivAlong_def, hslice.eq_of_nhds, hslice.fderiv_eq, hd.eq_of_nhds, hd.fderiv_eq]
  have := covDerivAlong_deriv_chartReading_eq_zero_of_geodesicAt (I := I) h hc hsrc
  rw [covDerivAlong_def] at this
  exact this

end Chart

/-! ### The three hypotheses of the piece second-variation lemma

Here `P = ℝ × ℝ`, `q = (s, t)`, `∂_s = (1,0)`, `∂_t = (0,1)`. -/

section Piece

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : RiemannianMetric I M} {u : ℝ × ℝ → E} {α : M}

/-- **Math.** **The hypothesis `hgeo`.** If the `t`-line at `s = 0` of the chart family
`u` reads a manifold geodesic `γ` in the chart at `α`, and the foot `γ t` lies in the
chart source, then the chart geodesic expression along `∂_t` vanishes at `(0, t)`:
`covDerivAlong Γ u (∂_t u) (0,1) (0,t) = 0`. -/
theorem covDerivAlong_snd_eq_zero_of_geodesic_tline (hu : ContDiff ℝ 2 u) {γ : ℝ → M}
    {t : ℝ} (h : Geodesic.HasGeodesicEquationAt (I := I) g γ t) (hc : ContinuousAt γ t)
    (hsrc : γ t ∈ (chartAt H α).source)
    (hslice : ∀ᶠ r in 𝓝 t, u (0, r) = extChartAt I α (γ r)) :
    covDerivAlong (chartChristoffelBilin (I := I) g α) u
        (fun q => fderiv ℝ u q ((0 : ℝ), (1 : ℝ))) ((0 : ℝ), (1 : ℝ))
        ((0 : ℝ), t) = 0 := by
  have hpt : ((0 : ℝ), t) = ((0 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ)) := by
    simp
  rw [hpt]
  refine covDerivAlong_eq_zero_of_geodesic_slice (I := I) hu h hc hsrc ?_
  filter_upwards [hslice] with r hr
  show u (((0 : ℝ), (0 : ℝ)) + r • ((0 : ℝ), (1 : ℝ))) = extChartAt I α (γ r)
  have hline : (((0 : ℝ), (0 : ℝ)) + r • ((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) = ((0 : ℝ), r) := by
    simp
  rw [hline, hr]

/-- **Math.** **`hgeo`, in exactly the shape the piece lemma wants it.**  If the `t`-line
at `s = 0` reads a *global* manifold geodesic `γ` in the chart at `α`, and the foot stays
in the chart source over `[τ₀, τ₁]`, then
`∀ t ∈ Icc τ₀ τ₁, covDerivAlong Γ u (∂_t u) (0,1) (0,t) = 0` — the hypothesis `hgeo` of
`deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`.

The slice hypothesis is *local around each time of the piece*, not global in `r`, and this
is essential rather than fastidious: the consumer demands `ContDiff ℝ 3 u` on all of
`ℝ × ℝ`, so any real caller must bump-extend `u` off the piece — while `extChartAt I α (γ r)`
is junk as soon as `γ r` leaves `(chartAt H α).source`.  A global identity
`∀ r, u (0, r) = extChartAt I α (γ r)` would therefore be undischargeable together with the
consumer's own smoothness hypothesis.  The neighbourhood form is exactly what the bump
extension (`exists_contDiff_eqOn_of_contDiffOn_Ioo`) delivers. -/
theorem covDerivAlong_snd_eq_zero_of_isGeodesic_tline (hu : ContDiff ℝ 2 u) {γ : ℝ → M}
    {τ₀ τ₁ : ℝ} (hγ : Geodesic.IsGeodesic (I := I) g γ) (hcont : Continuous γ)
    (hsrc : ∀ t ∈ Set.Icc τ₀ τ₁, γ t ∈ (chartAt H α).source)
    (hslice : ∀ t ∈ Set.Icc τ₀ τ₁, ∀ᶠ r in 𝓝 t, u (0, r) = extChartAt I α (γ r)) :
    ∀ t ∈ Set.Icc τ₀ τ₁,
      covDerivAlong (chartChristoffelBilin (I := I) g α) u
        (fun q => fderiv ℝ u q ((0 : ℝ), (1 : ℝ))) ((0 : ℝ), (1 : ℝ))
        ((0 : ℝ), t) = 0 := fun t ht =>
  covDerivAlong_snd_eq_zero_of_geodesic_tline (I := I) hu (hγ.hasGeodesicEquationAt t)
    hcont.continuousAt (hsrc t ht) (hslice t ht)

/-- **Math.** **The hypotheses `hj₀`, `hj₁`.** If the junction curve `s ↦ u (s, τ)` of
the chart family reads a manifold geodesic `c` in the chart at `α`, and the foot `c 0`
lies in the chart source, then the chart geodesic expression along `∂_s` vanishes at
`(0, τ)`: `covDerivAlong Γ u (∂_s u) (1,0) (0,τ) = 0`.  This is what kills the boundary
term of the piece — in its own chart, with no telescoping. -/
theorem covDerivAlong_fst_eq_zero_of_geodesic_junction (hu : ContDiff ℝ 2 u) {c : ℝ → M}
    {τ : ℝ} (h : Geodesic.HasGeodesicEquationAt (I := I) g c 0) (hcont : ContinuousAt c 0)
    (hsrc : c 0 ∈ (chartAt H α).source)
    (hslice : ∀ᶠ r in 𝓝 (0 : ℝ), u (r, τ) = extChartAt I α (c r)) :
    covDerivAlong (chartChristoffelBilin (I := I) g α) u
        (fun q => fderiv ℝ u q ((1 : ℝ), (0 : ℝ))) ((1 : ℝ), (0 : ℝ))
        ((0 : ℝ), τ) = 0 := by
  have hpt : ((0 : ℝ), τ) = ((0 : ℝ), τ) + (0 : ℝ) • ((1 : ℝ), (0 : ℝ)) := by
    simp
  rw [hpt]
  refine covDerivAlong_eq_zero_of_geodesic_slice (I := I) hu h hcont hsrc ?_
  filter_upwards [hslice] with r hr
  show u (((0 : ℝ), τ) + r • ((1 : ℝ), (0 : ℝ))) = extChartAt I α (c r)
  have hline : (((0 : ℝ), τ) + r • ((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) = (r, τ) := by
    simp
  rw [hline, hr]

end Piece

/-! ### The junction curve of a broken variation is a `globalGeodesic` -/

section PieceGlobal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {u : ℝ × ℝ → E} {α : M} (g : RiemannianMetric I M)

/-- **Math.** **The junction hypothesis for the real junction curve.** The junction curve
of a broken variation is `globalGeodesic g hg (γ τ) w` — a genuine manifold geodesic with
prescribed initial data (`expMapGlobal` is merely its value at `s = 1`; no homogeneity
relation is used).  Whenever the chart family `u` reads it along the line `t = τ`, the
piece lemma's hypothesis `hj` holds at `τ`. -/
theorem covDerivAlong_fst_eq_zero_of_globalGeodesic_junction (hg : g.IsRiemannianDist)
    [CompleteSpace M] (hu : ContDiff ℝ 2 u) {p : M} {w : TangentSpace I p} {τ : ℝ}
    (hsrc : p ∈ (chartAt H α).source)
    (hslice : ∀ᶠ r in 𝓝 (0 : ℝ),
      u (r, τ) = extChartAt I α (globalGeodesic (I := I) g hg p w r)) :
    covDerivAlong (chartChristoffelBilin (I := I) g α) u
        (fun q => fderiv ℝ u q ((1 : ℝ), (0 : ℝ))) ((1 : ℝ), (0 : ℝ))
        ((0 : ℝ), τ) = 0 := by
  have h0 : globalGeodesic (I := I) g hg p w 0 = p := globalGeodesic_zero g hg p w
  refine covDerivAlong_fst_eq_zero_of_geodesic_junction (I := I) hu
    ((isGeodesic_globalGeodesic g hg p w).hasGeodesicEquationAt 0)
    (continuous_globalGeodesic g hg p w).continuousAt ?_ hslice
  rw [h0]
  exact hsrc

end PieceGlobal

#print axioms MorganTianLib.covDerivAlong_affineLine
#print axioms MorganTianLib.covDerivAlong_deriv_chartReading_eq_zero_of_geodesicAt
#print axioms MorganTianLib.covDerivAlong_eq_zero_of_geodesic_slice
#print axioms MorganTianLib.covDerivAlong_snd_eq_zero_of_geodesic_tline
#print axioms MorganTianLib.covDerivAlong_snd_eq_zero_of_isGeodesic_tline
#print axioms MorganTianLib.covDerivAlong_fst_eq_zero_of_geodesic_junction
#print axioms MorganTianLib.covDerivAlong_fst_eq_zero_of_globalGeodesic_junction

end MorganTianLib

end
