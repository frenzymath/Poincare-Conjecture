import PetersenLib.Ch05.UniformInjectivityRadius

/-!
# Petersen Ch. 5, §5.5 — the uniform injectivity radius as a diffeomorphism radius

`compactSet_uniformCInftyDiffeo` (`cor:pet-ch5-uniform-injectivity-radius-compact`,
Petersen Cor. 5.5.2) in its full **"diffeomorphism onto its image"** form: for a compact
`K ⊆ M` there is a single `ε > 0` such that for **every** `q ∈ K` the exponential map
`exp_q` is defined on the whole `g`-metric ball `{v | |v|_g < ε}` of `T_qM` and is a
`C^∞` diffeomorphism onto its image.

`PetersenLib.compactSet_uniformInjectivityRadius` (`Ch05/UniformInjectivityRadius.lean`)
proves the *defined + injective* half; this file supplies the smoothness, image-openness
and smooth-inverse clauses that the book's word "diffeomorphism" carries.

## What this file provides

* `continuous_chartMetricInner_fixedBase` / `isOpen_chartMetricInner_ball` — the chart
  Gram quadratic form is continuous in the vector variable, so the `g`-ball read in chart
  fibre coordinates is open in `E`.
* `exists_local_uniformCInftyDiffeo` — the local half: around every `x ∈ M` an open
  `W ∋ x` and `ρ > 0` such that for every `q ∈ W` and **every** `ε ∈ (0, ρ]`, `exp_q` is a
  `C^∞` diffeomorphism of the `g`-ball of radius `ε` onto its (open) image.
* `compactSet_uniformCInftyDiffeo` — the headline corollary.

## Statement conventions, and what is *not* claimed

"Diffeomorphism onto its image" is rendered **unbundled**, as the four clauses `InjOn`,
`ContMDiffOn`, `IsOpen (image)` and "there is a `C^∞` left inverse on the image".  A
bundled `Diffeomorph` is unavailable: `T_qM` carries no `ChartedSpace E` instance, so the
`ContMDiffOn` clause is stated on the domain `E` with the (definitional) coercion
`E → TangentSpace I q`, following `exists_contMDiffOn_expMap_ray`.  The `InjOn` and
`IsOpen` clauses keep the `TangentSpace I q` reading of the landed theorem.

As in `Ch05/UniformInjectivityRadius.lean`, `exp_q` is the **intrinsic** moving-foot
maximal geodesic `geodesicMaximalCurve g q v` at time `1` — *never* `PetersenLib.expMap` /
`expDomain` / `injectivityRadius`, whose chart-anchored domains admit no uniform lower
bound over a compact set and make this statement **false**; see that file's module
docstring and `rem:pet-ch5-injectivity-radius-chart-artifact`.

The local lemma is quantified over **all** `ε ∈ (0, ρ]` rather than stated at the single
radius `ρ`.  This is forced: `InjOn` and `ContMDiffOn` restrict to sub-balls, but
`IsOpen (exp_q '' ball ε)` does **not** follow from `IsOpen (exp_q '' ball ρ)` for `ε ≤ ρ`,
and the compactness step instantiates `ε` at a minimum of finitely many `ρ`'s.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

/-! ## The chart `g`-ball is open -/

/-- **Math.** The chart-`α` Gram quadratic form `w ↦ ⟨w, w⟩_α^y` is continuous on `E` at a
fixed base point `y`.

`continuousOn_chartMetricInner_along` is the same statement along a curve, hard-coded to
`s : Set ℝ`; it cannot be instantiated at `E`.  The proof is the same: expand the pairing
into its finite double sum over the chart Gram matrix, and read off continuity of each
coordinate `w ↦ w^i` from the bundled functional `Geodesic.chartCoordFunctional i`. -/
theorem continuous_chartMetricInner_fixedBase (g : RiemannianMetric I M) (α : M) (y : E) :
    Continuous (fun w : E => chartMetricInner (I := I) g α y w w) := by
  classical
  have hfun : (fun w : E => chartMetricInner (I := I) g α y w w)
      = fun w : E => ∑ i, ∑ j, chartGramOnE (I := I) g α i j y
          * Geodesic.chartCoord (E := E) i w * Geodesic.chartCoord (E := E) j w := by
    funext w; rw [chartMetricInner_def]
  rw [hfun]
  refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
  have hci : Continuous (fun w : E => Geodesic.chartCoord (E := E) i w) := by
    exact (Geodesic.chartCoordFunctional (E := E) i).continuous.congr fun w =>
      Geodesic.chartCoordFunctional_apply i w
  have hcj : Continuous (fun w : E => Geodesic.chartCoord (E := E) j w) := by
    exact (Geodesic.chartCoordFunctional (E := E) j).continuous.congr fun w =>
      Geodesic.chartCoordFunctional_apply j w
  exact (continuous_const.mul hci).mul hcj

/-- **Math.** The `g`-ball of radius `ε`, read in chart-`α` fibre coordinates, is an open
subset of `E`: it is the sublevel set `{w | ⟨w, w⟩_α^y < ε²}` of a continuous function. -/
theorem isOpen_chartMetricInner_ball (g : RiemannianMetric I M) (α : M) (y : E) (ε : ℝ) :
    IsOpen {w : E | chartMetricInner (I := I) g α y w w < ε ^ 2} :=
  isOpen_lt (continuous_chartMetricInner_fixedBase g α y) continuous_const

/-! ## The local uniform diffeomorphism radius -/

/-- **Math.** Petersen Ch. 5 (`cor:pet-ch5-uniform-injectivity-radius-compact`, local
half, full diffeomorphism form): around every `x ∈ M` there are an open `W ∋ x` and a
radius `ρ > 0` such that for **every** foot `q ∈ W` and **every** `ε ∈ (0, ρ]` the
exponential map `v ↦ exp_q v` is injective on the `g`-ball `{v ∈ T_qM | |v|_g < ε}`, is
`C^∞` there, has open image, and admits a `C^∞` left inverse on that image — i.e. it is a
`C^∞` diffeomorphism onto its image, uniformly in `q ∈ W`.

Proof (do Carmo Ch. 3, Thm. 3.7 / Petersen §5.5): the flow package of
`exists_pairMap_hasStrictFDerivAt_equiv_ball_infty` supplies a chart-`x` pair map
`G(y, w) = (y, (Z(y, T⁻¹·w)(T))₁)`, `C^∞` on the admissible set, strictly differentiable
at the zero section `(φ_x x, 0)` with derivative the unipotent shear `(a, b) ↦ (a, a + b)`,
and strictly differentiable with invertible derivative at every point of a ball around it.
The inverse function theorem turns `G` into an open partial homeomorphism `ho` near the
zero section; `ho.symm` is the inverse `Ginv`, `C^∞` on the open image by the `C^r`
inverse function theorem (`OpenPartialHomeomorph.contDiffAt_symm`).

Slicing at a fixed first coordinate `y = φ_x q` exhibits the chart exponential
`w ↦ (Z(y, T⁻¹·w)(T))₁` as a `C^∞` diffeomorphism of the coordinate ball `‖w‖ < δ` onto an
open slice of `G(B)`.  Three conversions produce the statement.  *Intrinsic-ness*: the
package curve is identified with the intrinsic maximal geodesic on the open flow window
(`isGeodesicWithInitialOn_flow_window` + `geodesicMaximalCurve_eqOn`), and the chart is
undone by `(extChartAt I x).symm`, `C^∞` by `contMDiffOn_extChartAt_symm`.  *Velocities*:
`v ↦ w` is the trivialization fibre coordinate at `x`, a continuous linear isomorphism on
`T_qM`, hence `C^∞`.  *Radii*: the `g`-ball must be pushed inside `‖w‖ < δ` **uniformly in
`q`**, which is the uniform Gram eigenvalue bound `exists_forall_le_chartMetricInner` on a
compact `C ⊆ (chartAt H x).source` — this is why `W` is cut down to `interior C`, and it is
the step that makes `ρ` independent of `q`. -/
theorem exists_local_uniformCInftyDiffeo (g : RiemannianMetric I M) (x : M) :
    ∃ (W : Set M) (ρ : ℝ), IsOpen W ∧ x ∈ W ∧ 0 < ρ ∧ ∀ q ∈ W, ∀ ε ∈ Ioc (0 : ℝ) ρ,
      Set.InjOn (fun v : TangentSpace I q => geodesicMaximalCurve (I := I) g q v 1)
        {v : TangentSpace I q | g.metricInner q v v < ε ^ 2} ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞
        (fun w : E => geodesicMaximalCurve (I := I) g q (w : TangentSpace I q) 1)
        {w : E | g.metricInner q (w : TangentSpace I q) (w : TangentSpace I q) < ε ^ 2} ∧
      IsOpen ((fun v : TangentSpace I q => geodesicMaximalCurve (I := I) g q v 1) ''
        {v : TangentSpace I q | g.metricInner q v v < ε ^ 2}) ∧
      ∃ F : M → E,
        ContMDiffOn I 𝓘(ℝ, E) ∞ F
          ((fun v : TangentSpace I q => geodesicMaximalCurve (I := I) g q v 1) ''
            {v : TangentSpace I q | g.metricInner q v v < ε ^ 2}) ∧
        ∀ w : E, g.metricInner q (w : TangentSpace I q) (w : TangentSpace I q) < ε ^ 2 →
          F (geodesicMaximalCurve (I := I) g q (w : TangentSpace I q) 1) = w := by
  classical
  obtain ⟨r, ε₀, T, ρ₀, Z, hr, hε₀, hT, hTε₀, hρ₀, hflow, hZT1, hρ₀sub, hGCinf,
    hstrict, hinv⟩ := exists_pairMap_hasStrictFDerivAt_equiv_ball_infty (I := I) g x
  set y₀ : E := extChartAt I x x with hy₀def
  set z₀ : E × E := ((y₀, (0 : E)) : E × E) with hz₀def
  set G : E × E → E × E :=
    fun z => ((z.1 : E), (Z ((z.1, T⁻¹ • z.2) : E × E) T).1) with hGdef
  set S : Set (E × E) := {z : E × E | ((z.1, T⁻¹ • z.2) : E × E) ∈ ball z₀ r} with hSdef
  have hSopen : IsOpen S :=
    isOpen_ball.preimage (continuous_fst.prodMk (continuous_snd.const_smul T⁻¹))
  -- the strict derivative at the zero section is the unipotent shear, a linear iso
  set shear : (E × E) ≃L[ℝ] E × E := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.snd ℝ E E) - (ContinuousLinearMap.fst ℝ E E)))
    (fun z => by simp [ContinuousLinearMap.prod_apply])
    (fun z => by simp [ContinuousLinearMap.prod_apply]) with hsheardef
  have hshear_coe : (shear : (E × E) →L[ℝ] E × E)
      = (ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)) := rfl
  have hstrict' : HasStrictFDerivAt G
      ((shear : (E × E) ≃L[ℝ] E × E) : (E × E) →L[ℝ] E × E) z₀ := by
    rw [hshear_coe]
    exact hstrict
  -- the inverse function theorem: `G` is an open partial homeomorphism near the zero section
  set ho := hstrict'.toOpenPartialHomeomorph G with hodef
  have hsource : z₀ ∈ ho.source := hstrict'.mem_toOpenPartialHomeomorph_source
  have hcoe : ⇑ho = G := hstrict'.toOpenPartialHomeomorph_coe
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.isOpen_iff.mp ho.open_source z₀ hsource
  -- the working coordinate radii
  set δ₁ : ℝ := min (min ρ₂ ρ₀) r with hδ₁def
  set δ : ℝ := min (min ρ₂ ρ₀) (T * r) with hδdef
  have hδ₁pos : 0 < δ₁ := lt_min (lt_min hρ₂ hρ₀) hr
  have hδpos : 0 < δ := lt_min (lt_min hρ₂ hρ₀) (by positivity)
  set B : Set (E × E) := ball y₀ δ₁ ×ˢ ball (0 : E) δ with hBdef
  have hBopen : IsOpen B := isOpen_ball.prod isOpen_ball
  have hBsource : B ⊆ ho.source := by
    intro z hz
    refine hρ₂sub ?_
    rw [mem_ball, hz₀def, Prod.dist_eq]
    exact max_lt
      (lt_of_lt_of_le hz.1 ((min_le_left _ _).trans (min_le_left _ _)))
      (lt_of_lt_of_le hz.2 ((min_le_left _ _).trans (min_le_left _ _)))
  have hBρ₀ : B ⊆ ball z₀ ρ₀ := by
    intro z hz
    rw [mem_ball, hz₀def, Prod.dist_eq]
    exact max_lt
      (lt_of_lt_of_le hz.1 ((min_le_left _ _).trans (min_le_right _ _)))
      (lt_of_lt_of_le hz.2 ((min_le_left _ _).trans (min_le_right _ _)))
  have hBflow : ∀ z ∈ B, ((z.1, T⁻¹ • z.2) : E × E) ∈ closedBall z₀ r := by
    intro z hz
    rw [mem_closedBall, hz₀def, Prod.dist_eq]
    have hz1 : dist z.1 y₀ ≤ r :=
      le_of_lt (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _))
    refine max_le hz1 ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
    have hz2' : ‖z.2‖ < δ := by
      have := mem_ball.mp hz.2
      rwa [dist_zero_right] at this
    have hz2 : ‖z.2‖ < T * r := lt_of_lt_of_le hz2' (min_le_right _ _)
    rw [inv_mul_le_iff₀ hT]
    linarith [hz2]
  have hBS : B ⊆ S := by
    intro z hz
    show ((z.1, T⁻¹ • z.2) : E × E) ∈ ball z₀ r
    rw [mem_ball, hz₀def, Prod.dist_eq]
    have hz1 : dist z.1 y₀ < r :=
      lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _)
    refine max_lt hz1 ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
    have hz2' : ‖z.2‖ < δ := by
      have := mem_ball.mp hz.2
      rwa [dist_zero_right] at this
    have hz2 : ‖z.2‖ < T * r := lt_of_lt_of_le hz2' (min_le_right _ _)
    rw [inv_mul_lt_iff₀ hT]
    linarith [hz2]
  -- the two-sided inverse of `G` on `B`, and its regularity
  have hGinvG : ∀ z ∈ B, ho.symm (G z) = z := by
    intro z hz
    have := ho.left_inv (hBsource hz)
    rwa [hcoe] at this
  have hGopen : IsOpen (G '' B) := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨D', hD'⟩ := hinv z (hBρ₀ hz)
    rw [← hD'.map_nhds_eq_of_equiv]
    exact image_mem_map (hBopen.mem_nhds hz)
  have hGinvCinf : ContDiffOn ℝ ∞ (⇑ho.symm) (G '' B) := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨D', hD'⟩ := hinv z (hBρ₀ hz)
    have hzsrc : z ∈ ho.source := hBsource hz
    have hwtgt : G z ∈ ho.target := by
      have := ho.map_source hzsrc
      rwa [hcoe] at this
    have hsymm : ho.symm (G z) = z := hGinvG z hz
    have hf' : HasFDerivAt (⇑ho) (D' : (E × E) →L[ℝ] E × E) (ho.symm (G z)) := by
      rw [hsymm, hcoe]
      exact hD'.hasFDerivAt
    have hf : ContDiffAt ℝ ∞ (⇑ho) (ho.symm (G z)) := by
      rw [hsymm, hcoe]
      exact hGCinf.contDiffAt (hSopen.mem_nhds (hBS hz))
    exact (ho.contDiffAt_symm hwtgt hf' hf).contDiffWithinAt
  -- a compact chart neighbourhood of `x`, carrying the uniform Gram eigenvalue bound
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨C, hCmem, hCsub, hCcomp⟩ := local_compact_nhds
    ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  obtain ⟨lam, hlam, hlamle⟩ := exists_forall_le_chartMetricInner (I := I) g hCcomp hCsub
  -- the working neighbourhood
  set W : Set M := ((chartAt H x).source ∩ (extChartAt I x) ⁻¹' (ball y₀ δ₁))
    ∩ interior C with hWdef
  have hWopen : IsOpen W := by
    refine IsOpen.inter ?_ isOpen_interior
    have hc : ContinuousOn (extChartAt I x) (chartAt H x).source := by
      rw [← extChartAt_source (I := I) x]
      exact continuousOn_extChartAt x
    exact hc.isOpen_inter_preimage (chartAt H x).open_source isOpen_ball
  have hxW : x ∈ W := by
    refine ⟨⟨mem_chart_source H x, ?_⟩, mem_interior_iff_mem_nhds.mpr hCmem⟩
    show extChartAt I x x ∈ ball y₀ δ₁
    rw [← hy₀def]
    exact mem_ball_self hδ₁pos
  have hWC : W ⊆ C := fun q hq => interior_subset hq.2
  have hWsrc : W ⊆ (chartAt H x).source := fun q hq => hq.1.1
  refine ⟨W, δ * Real.sqrt lam / 2, hWopen, hxW, by positivity, ?_⟩
  -- a `g`-short vector has a short chart-`x` fibre coordinate, uniformly over `W`
  have hkey : ∀ q ∈ W, ∀ w : E,
      chartMetricInner (I := I) g x (extChartAt I x q) w w < (δ * Real.sqrt lam / 2) ^ 2 →
      ‖w‖ < δ := by
    intro q hq w hw
    have hlow : lam * ‖w‖ ^ 2 ≤ chartMetricInner (I := I) g x (extChartAt I x q) w w :=
      hlamle q (hWC hq) w
    have hsq : (δ * Real.sqrt lam / 2) ^ 2 = δ ^ 2 * lam / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hlam.le]
      ring
    rw [hsq] at hw
    have h1' : lam * ‖w‖ ^ 2 < lam * (δ ^ 2 / 4) := by linarith
    have hw4 : ‖w‖ ^ 2 < δ ^ 2 / 4 := lt_of_mul_lt_mul_left h1' hlam.le
    have hw2 : ‖w‖ ^ 2 < δ ^ 2 := by nlinarith [hδpos]
    nlinarith [norm_nonneg w, hδpos, hw2]
  intro q hq ε hε
  obtain ⟨hεpos, hερ⟩ := hε
  have hqsrc : q ∈ (chartAt H x).source := hWsrc hq
  have hqsrc_x : q ∈ (extChartAt I x).source := by rw [extChartAt_source I]; exact hqsrc
  have hqsrc_q : q ∈ (extChartAt I q).source := mem_extChartAt_source (I := I) q
  set y : E := extChartAt I x q with hydef
  have hyball : y ∈ ball y₀ δ₁ := hq.1.2
  set gy : E → E := fun w : E => (Z ((y, T⁻¹ • w) : E × E) T).1 with hgydef
  -- the fibre coordinate changes at `q`, mutually inverse continuous linear maps
  set cq : E →L[ℝ] E := tangentCoordChange I q x q with hcqdef
  set cx : E →L[ℝ] E := tangentCoordChange I x q q with hcxdef
  have hcxq : ∀ v : TangentSpace I q, cx (cq v) = v := by
    intro v
    rw [hcqdef, hcxdef, tangentCoordChange_comp (I := I) ⟨⟨hqsrc_q, hqsrc_x⟩, hqsrc_q⟩,
      tangentCoordChange_self (I := I) hqsrc_q]
  have hcqx : ∀ w : E, cq (cx w) = w := by
    intro w
    rw [hcqdef, hcxdef, tangentCoordChange_comp (I := I) ⟨⟨hqsrc_x, hqsrc_q⟩, hqsrc_x⟩,
      tangentCoordChange_self (I := I) hqsrc_x]
  -- the intrinsic `g`-length of `v` is the chart-`x` Gram pairing of its fibre coordinate
  have hinner : ∀ v : TangentSpace I q,
      g.metricInner q v v = chartMetricInner (I := I) g x y (cq v) (cq v) := by
    intro v
    have hbridge : g.inner q v v
        = chartMetricInner (I := I) g x (extChartAt I x q)
            ((trivializationAt E (TangentSpace I) x (⟨q, v⟩ : TangentBundle I M)).2)
            ((trivializationAt E (TangentSpace I) x (⟨q, v⟩ : TangentBundle I M)).2) :=
      inner_self_eq_chartMetricInner_trivializationAt (I := I) g
        (α := x) (x := (⟨q, v⟩ : TangentBundle I M)) hqsrc
    exact hbridge
  -- the `g`-ball, read in chart-`x` fibre coordinates: an open ellipsoid inside `ball 0 δ`
  set Eell : Set E := {w : E | chartMetricInner (I := I) g x y w w < ε ^ 2} with hEelldef
  have hEellOpen : IsOpen Eell := isOpen_chartMetricInner_ball (I := I) g x y ε
  have hEellδ : Eell ⊆ ball (0 : E) δ := by
    intro w hw
    refine mem_ball_zero_iff.mpr (hkey q hq w ?_)
    refine lt_of_lt_of_le hw ?_
    nlinarith [hεpos, hερ]
  have hballEell : ∀ v : TangentSpace I q, g.metricInner q v v < ε ^ 2 ↔ cq v ∈ Eell := by
    intro v
    rw [hEelldef, mem_setOf_eq, hinner v]
  -- the flow window, and the identification of the package curve with `exp_q`
  have h1lt : (1 : ℝ) < ε₀ / T := (one_lt_div hT).mpr hTε₀
  have h0J : (0 : ℝ) ∈ Ioo (-(ε₀ / T)) (ε₀ / T) := ⟨by linarith, by linarith⟩
  have h1J : (1 : ℝ) ∈ Ioo (-(ε₀ / T)) (ε₀ / T) := ⟨by linarith, h1lt⟩
  have hmemflow : ∀ w : E, ‖w‖ < δ → ((y, T⁻¹ • w) : E × E) ∈ closedBall z₀ r := by
    intro w hw
    exact hBflow ((y, w)) ⟨hyball, mem_ball_zero_iff.mpr hw⟩
  have hmax : ∀ v : TangentSpace I q, ‖cq v‖ < δ →
      geodesicMaximalCurve (I := I) g q v 1 = (extChartAt I x).symm (gy (cq v)) := by
    intro v hv
    have hmemv : ((extChartAt I x q,
        T⁻¹ • (trivializationAt E (TangentSpace I) x (⟨q, v⟩ : TangentBundle I M)).2) : E × E)
        ∈ closedBall ((extChartAt I x x, (0 : E)) : E × E) r := hmemflow (cq v) hv
    have hivp := isGeodesicWithInitialOn_flow_window (I := I) g x hT hTε₀ hflow hqsrc v hmemv
    have h := geodesicMaximalCurve_eqOn (I := I) g isOpen_Ioo Set.ordConnected_Ioo
      h0J hivp h1J
    show geodesicMaximalCurve (I := I) g q v 1
        = (extChartAt I x).symm ((Z ((y, T⁻¹ • cq v) : E × E) T).1)
    simpa only [one_mul, hydef, hcqdef, tangentCoordChange_def,
      TangentBundle.trivializationAt_apply, extChartAt] using h
  -- the flow endpoint lands in the chart target
  have htgt : ∀ w : E, ‖w‖ < δ → gy w ∈ (extChartAt I x).target := by
    intro w hw
    have hTIcc : T ∈ Icc (-ε₀) ε₀ := ⟨by linarith, hTε₀.le⟩
    exact ((hflow _ (hmemflow w hw)).2.2 T hTIcc).1
  -- the chart exponential slice `gy` is `C^∞` on `ball 0 δ`
  have hgyCinf : ContDiffOn ℝ ∞ gy (ball (0 : E) δ) := by
    have hmaps : MapsTo (fun w : E => ((y, w) : E × E)) (ball (0 : E) δ) S := by
      intro w hw
      exact hBS ⟨hyball, hw⟩
    have hcomp : ContDiffOn ℝ ∞ (fun w : E => G ((y, w) : E × E)) (ball (0 : E) δ) :=
      hGCinf.comp (contDiff_const.prodMk contDiff_id).contDiffOn hmaps
    exact hcomp.snd
  -- the `Ginv` slice inverts `gy` on `ball 0 δ`
  have hgyinv : ∀ w ∈ ball (0 : E) δ, (ho.symm ((y, gy w) : E × E)).2 = w := by
    intro w hw
    have hz : ((y, w) : E × E) ∈ B := ⟨hyball, hw⟩
    have h := hGinvG _ hz
    have hGval : G ((y, w) : E × E) = ((y, gy w) : E × E) := rfl
    rw [hGval] at h
    rw [h]
  -- the image slice of `gy` is the fixed-`y` slice of the open set `G '' B`
  set slice : Set E := {z : E | ((y, z) : E × E) ∈ G '' B} with hslicedef
  have hgyimg : gy '' (ball (0 : E) δ) = slice := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨((y, w) : E × E), ⟨hyball, hw⟩, rfl⟩
    · rintro ⟨z', hz', hGz'⟩
      have h1 : z'.1 = y := congrArg Prod.fst hGz'
      refine ⟨z'.2, hz'.2, ?_⟩
      have h2 : (Z ((z'.1, T⁻¹ • z'.2) : E × E) T).1 = z := congrArg Prod.snd hGz'
      show (Z ((y, T⁻¹ • z'.2) : E × E) T).1 = z
      rw [← h1]
      exact h2
  -- hence the image of the open ellipsoid under `gy` is open
  have hgyEellOpen : IsOpen (gy '' Eell) := by
    have hsliceopen : IsOpen slice := by
      rw [hslicedef]
      exact hGopen.preimage (continuous_const.prodMk continuous_id)
    have hkeyimg : gy '' Eell
        = slice ∩ (fun z : E => (ho.symm ((y, z) : E × E)).2) ⁻¹' Eell := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨hgyimg ▸ ⟨w, hEellδ hw, rfl⟩, ?_⟩
        show (ho.symm ((y, gy w) : E × E)).2 ∈ Eell
        rw [hgyinv w (hEellδ hw)]
        exact hw
      · rintro ⟨hz1, hz2⟩
        rw [← hgyimg] at hz1
        obtain ⟨w, hw, rfl⟩ := hz1
        refine ⟨w, ?_, rfl⟩
        have hz2' : (ho.symm ((y, gy w) : E × E)).2 ∈ Eell := hz2
        rwa [hgyinv w hw] at hz2'
    rw [hkeyimg]
    have hcont : ContinuousOn (fun z : E => (ho.symm ((y, z) : E × E)).2) slice := by
      have h1 : ContinuousOn (fun z : E => ((y, z) : E × E)) slice :=
        (continuous_const.prodMk continuous_id).continuousOn
      have h2 : MapsTo (fun z : E => ((y, z) : E × E)) slice (G '' B) := by
        intro z hz
        rwa [hslicedef] at hz
      exact continuous_snd.comp_continuousOn (hGinvCinf.continuousOn.comp h1 h2)
    exact hcont.isOpen_inter_preimage hsliceopen hEellOpen
  -- the image of the `g`-ball, read in the chart at `x`
  set expq : TangentSpace I q → M :=
    fun v => geodesicMaximalCurve (I := I) g q v 1 with hexpqdef
  set Eball : Set (TangentSpace I q) :=
    {v : TangentSpace I q | g.metricInner q v v < ε ^ 2} with hEballdef
  have hcqEball : ∀ v : TangentSpace I q, v ∈ Eball → ‖cq v‖ < δ := by
    intro v hv
    exact mem_ball_zero_iff.mp (hEellδ ((hballEell v).mp hv))
  have himg : expq '' Eball
      = (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' (gy '' Eell) := by
    ext m
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hshort : ‖cq v‖ < δ := hcqEball v hv
      have hval : expq v = (extChartAt I x).symm (gy (cq v)) := hmax v hshort
      have htgt' : gy (cq v) ∈ (extChartAt I x).target := htgt _ hshort
      constructor
      · rw [hval]
        exact (extChartAt I x).map_target htgt'
      · show extChartAt I x (expq v) ∈ gy '' Eell
        rw [hval, (extChartAt I x).right_inv htgt']
        exact ⟨cq v, (hballEell v).mp hv, rfl⟩
    · rintro ⟨hmsrc, hmimg⟩
      obtain ⟨w, hw, hgw⟩ := hmimg
      refine ⟨cx w, ?_, ?_⟩
      · show g.metricInner q (cx w) (cx w) < ε ^ 2
        rw [hballEell (cx w), hcqx w]
        exact hw
      · have hshort : ‖cq (cx w)‖ < δ := by
          rw [hcqx w]
          exact mem_ball_zero_iff.mp (hEellδ hw)
        show geodesicMaximalCurve (I := I) g q (cx w) 1 = m
        rw [hmax (cx w) hshort, hcqx w, hgw]
        exact (extChartAt I x).left_inv hmsrc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- injectivity: the `Ginv` slice is a left inverse
    intro v₁ hv₁ v₂ hv₂ heq
    have h1 : (ho.symm ((y, gy (cq v₁)) : E × E)).2 = cq v₁ :=
      hgyinv _ (mem_ball_zero_iff.mpr (hcqEball v₁ hv₁))
    have h2 : (ho.symm ((y, gy (cq v₂)) : E × E)).2 = cq v₂ :=
      hgyinv _ (mem_ball_zero_iff.mpr (hcqEball v₂ hv₂))
    have hgeq : gy (cq v₁) = gy (cq v₂) := by
      have e₁ := hmax v₁ (hcqEball v₁ hv₁)
      have e₂ := hmax v₂ (hcqEball v₂ hv₂)
      have h : (extChartAt I x).symm (gy (cq v₁)) = (extChartAt I x).symm (gy (cq v₂)) := by
        rw [← e₁, ← e₂]; exact heq
      have ht₁ : gy (cq v₁) ∈ (extChartAt I x).target := htgt _ (hcqEball v₁ hv₁)
      have ht₂ : gy (cq v₂) ∈ (extChartAt I x).target := htgt _ (hcqEball v₂ hv₂)
      rw [← (extChartAt I x).right_inv ht₁, ← (extChartAt I x).right_inv ht₂, h]
    have hcqeq : cq v₁ = cq v₂ := by rw [← h1, ← h2, hgeq]
    have := congrArg cx hcqeq
    rwa [hcxq v₁, hcxq v₂] at this
  · -- smoothness of `exp_q` on the `g`-ball
    have hlin : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun w : E => cq w)
        {w : E | g.metricInner q (w : TangentSpace I q) (w : TangentSpace I q) < ε ^ 2} :=
      (ContinuousLinearMap.contMDiff cq).contMDiffOn
    have hshort : MapsTo (fun w : E => cq w)
        {w : E | g.metricInner q (w : TangentSpace I q) (w : TangentSpace I q) < ε ^ 2}
        (ball (0 : E) δ) := fun w hw => mem_ball_zero_iff.mpr (hcqEball w hw)
    have hZ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ gy (ball (0 : E) δ) := hgyCinf.contMDiffOn
    have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun w : E => gy (cq w))
        {w : E | g.metricInner q (w : TangentSpace I q) (w : TangentSpace I q) < ε ^ 2} :=
      hZ.comp hlin hshort
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x).symm (extChartAt I x).target :=
      contMDiffOn_extChartAt_symm x
    have htgt' : MapsTo (fun w : E => gy (cq w))
        {w : E | g.metricInner q (w : TangentSpace I q) (w : TangentSpace I q) < ε ^ 2}
        (extChartAt I x).target := fun w hw => htgt _ (hcqEball w hw)
    have hfull := hsymm.comp hcomp htgt'
    exact hfull.congr (fun w hw => hmax w (hcqEball w hw))
  · -- the image is open
    rw [himg]
    have hc : ContinuousOn (extChartAt I x) (chartAt H x).source := by
      rw [← extChartAt_source (I := I) x]
      exact continuousOn_extChartAt x
    rw [extChartAt_source]
    exact hc.isOpen_inter_preimage (chartAt H x).open_source hgyEellOpen
  · -- the smooth left inverse
    refine ⟨fun m => cx ((ho.symm ((y, extChartAt I x m) : E × E)).2), ?_, ?_⟩
    · have hmid : ContDiffOn ℝ ∞
          (fun z : E => cx ((ho.symm ((y, z) : E × E)).2)) slice := by
        have h1 : ContDiffOn ℝ ∞ (fun z : E => ((y, z) : E × E)) slice :=
          (contDiff_const.prodMk contDiff_id).contDiffOn
        have h2 : MapsTo (fun z : E => ((y, z) : E × E)) slice (G '' B) := by
          intro z hz
          rwa [hslicedef] at hz
        have h3 : ContDiffOn ℝ ∞ (fun z : E => ho.symm ((y, z) : E × E)) slice :=
          hGinvCinf.comp h1 h2
        exact cx.contDiff.comp_contDiffOn (contDiff_snd.comp_contDiffOn h3)
      have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I x) (extChartAt I x).source := by
        rw [extChartAt_source]
        exact contMDiffOn_extChartAt
      have hUsrc : expq '' Eball ⊆ (extChartAt I x).source := by
        rw [himg]; exact inter_subset_left
      have hUimg : MapsTo (extChartAt I x) (expq '' Eball) slice := by
        intro m hm
        rw [himg] at hm
        have hmem : extChartAt I x m ∈ gy '' Eell := hm.2
        obtain ⟨w, hw, hgw⟩ := hmem
        rw [← hgyimg]
        exact ⟨w, hEellδ hw, hgw⟩
      exact hmid.contMDiffOn.comp (hchart.mono hUsrc) hUimg
    · intro w hw
      have hshort : ‖cq (w : TangentSpace I q)‖ < δ := hcqEball w hw
      show cx ((ho.symm ((y, extChartAt I x
        (geodesicMaximalCurve (I := I) g q (w : TangentSpace I q) 1)) : E × E)).2) = w
      rw [hmax (w : TangentSpace I q) hshort,
        (extChartAt I x).right_inv (htgt _ hshort),
        hgyinv _ (mem_ball_zero_iff.mpr hshort)]
      exact hcxq w

/-! ## Petersen Cor. 5.5.2, full form -/

/-- **Math.** Petersen Ch. 5, Cor. 5.5.2 (`cor:pet-ch5-uniform-injectivity-radius-compact`):
**a uniform injectivity radius on a compact set.**  For a compact `K ⊆ M` there is a single
`ε > 0` such that for **every** `q ∈ K` the exponential map `exp_q` is defined on the whole
`g`-metric ball `{v ∈ T_qM | |v|_g < ε}` and is a `C^∞` **diffeomorphism onto its image**:
it is injective and `C^∞` on that ball, its image is open, and it has a `C^∞` left inverse
there.

This strengthens `compactSet_uniformInjectivityRadius`, which records the defined and
injective clauses only.  The halves are `uniform_intrinsic_domain` (defined) and
`exists_local_uniformCInftyDiffeo` (diffeomorphism, locally uniform), combined by
compactness: cover `K` by the finitely many neighbourhoods `W_x` carrying a local uniform
diffeomorphism radius `ρ_x`, and take `ε` to be the minimum of the domain radius and the
finitely many `ρ_x`.  The local lemma is applied at the radius `ε` itself — this is what
its `∀ ε ∈ (0, ρ]` quantifier is for, since image-openness does not restrict to sub-balls.

`exp_q` is the **intrinsic** exponential — the moving-foot maximal geodesic
`geodesicMaximalCurve g q v` evaluated at time `1` — not `PetersenLib.expMap`, whose
chart-anchored domain makes this statement false; see the module docstring. -/
theorem compactSet_uniformCInftyDiffeo (g : RiemannianMetric I M)
    {K : Set M} (hK : IsCompact K) :
    ∃ ε > (0 : ℝ), ∀ q ∈ K,
      (∀ v : TangentSpace I q, g.metricInner q v v < ε ^ 2 →
        (1 : ℝ) ∈ geodesicMaximalDomain (I := I) g q v) ∧
      Set.InjOn (fun v : TangentSpace I q => geodesicMaximalCurve (I := I) g q v 1)
        {v : TangentSpace I q | g.metricInner q v v < ε ^ 2} ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞
        (fun w : E => geodesicMaximalCurve (I := I) g q (w : TangentSpace I q) 1)
        {w : E | g.metricInner q (w : TangentSpace I q) (w : TangentSpace I q) < ε ^ 2} ∧
      IsOpen ((fun v : TangentSpace I q => geodesicMaximalCurve (I := I) g q v 1) ''
        {v : TangentSpace I q | g.metricInner q v v < ε ^ 2}) ∧
      ∃ F : M → E,
        ContMDiffOn I 𝓘(ℝ, E) ∞ F
          ((fun v : TangentSpace I q => geodesicMaximalCurve (I := I) g q v 1) ''
            {v : TangentSpace I q | g.metricInner q v v < ε ^ 2}) ∧
        ∀ w : E, g.metricInner q (w : TangentSpace I q) (w : TangentSpace I q) < ε ^ 2 →
          F (geodesicMaximalCurve (I := I) g q (w : TangentSpace I q) 1) = w := by
  classical
  obtain ⟨ε₁, hε₁, hdom⟩ := uniform_intrinsic_domain (I := I) g hK
  choose W ρ hWopen hxW hρ hloc using
    fun x : M => exists_local_uniformCInftyDiffeo (I := I) g x
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨ε₁, hε₁, by simp⟩
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover W
    fun x _ => (hWopen x).mem_nhds (hxW x)
  have htne : t.Nonempty := by
    obtain ⟨q, hq⟩ := hKne
    obtain ⟨x₀, hx₀t, -⟩ := Set.mem_iUnion₂.mp (hcover hq)
    exact ⟨x₀, hx₀t⟩
  have hinf_pos : 0 < t.inf' htne ρ := by
    obtain ⟨x₀, hx₀t, heq⟩ := Finset.exists_mem_eq_inf' htne ρ
    rw [heq]
    exact hρ x₀
  refine ⟨min ε₁ (t.inf' htne ρ), lt_min hε₁ hinf_pos, ?_⟩
  intro q hq
  obtain ⟨x₀, hx₀t, hqW⟩ := Set.mem_iUnion₂.mp (hcover hq)
  have hmin₂ : min ε₁ (t.inf' htne ρ) ≤ ρ x₀ :=
    le_trans (min_le_right _ _) (Finset.inf'_le ρ hx₀t)
  have hmin_pos : 0 < min ε₁ (t.inf' htne ρ) := lt_min hε₁ hinf_pos
  obtain ⟨hInj, hSmooth, hOpen, hInv⟩ :=
    hloc x₀ q hqW (min ε₁ (t.inf' htne ρ)) ⟨hmin_pos, hmin₂⟩
  refine ⟨?_, hInj, hSmooth, hOpen, hInv⟩
  intro v hv
  refine hdom q hq v (lt_of_lt_of_le hv ?_)
  gcongr
  exact min_le_left _ _

end PetersenLib

end
