import DoCarmoLib.Riemannian.Exponential.TotallyNormal
import DoCarmoLib.Riemannian.Geodesic.FlowReadback
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

set_option linter.unusedSectionVars false

/-!
# Totally normal neighborhoods: the C¹-diffeomorphism clause (do Carmo Ch. 3, Theorem 3.7)

`exists_totallyNormal_neighborhood` (`TotallyNormal.lean`) provides the
existence, uniqueness and covering content of do Carmo's Theorem 3.7: a
neighborhood `W ∋ p` and a uniform radius `δ` such that any two points of `W`
are joined by a geodesic segment with a unique chart-velocity parameter in the
`δ`-ball. This file closes the remaining clause of do Carmo's literal
statement — *`exp_q` is a diffeomorphism on `B_δ(0)`* — at the `C¹` level, by
proving that the pair map `G(y, w) = (y, (Z(y, w/T) T)₁)` (do Carmo's
`F(q, v) = (q, exp_q v)` read in the chart at `p`) is a `C¹` diffeomorphism of
a product ball onto an open set:

* `uniform_flow_pairMap_agree` — **two uniform local flows compute the same
  pair map**: the time-`T`-rescaled endpoint `(Z(y, w/T) T)₁` does not depend
  on the flow package `(r, ε, T, Z)`. Both flow segments are continuous
  intrinsic geodesics through `φ_p⁻¹(y)` with chart velocity `w`
  (`isGeodesicOn_uniform_flow_segment_Ioo`), so intrinsic uniqueness
  identifies them (`IsGeodesicOn.eq_uniform_flow_readback`); evaluating at
  time `1` and using injectivity of `φ_p⁻¹` on the chart target equates the
  endpoints. This transports the center derivative computed for one flow
  package (`exists_pairMap_hasStrictFDerivAt`) to the `C¹` package
  (`exists_pairMap_contDiffOn`), which produce *different* flow witnesses.
* `exists_pairMap_hasStrictFDerivAt_equiv_ball` — **the derivative of the pair
  map is invertible at every point of a ball around the zero section** (the
  pair-map analogue of `lem:dc-ch3-2-9-invertible`,
  `exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball`): a single flow
  package carrying the flow clauses, `C¹` regularity of `G` on the admissible
  set, the strict derivative at the center — the unipotent shear
  `(a, b) ↦ (a, a + b)` — and, at every point of a ball around the center, a
  strict derivative realized by a continuous linear *equivalence*: the
  derivative map is continuous on the admissible set and equals the invertible
  shear at the center, so nearby it is the Neumann-series perturbation
  `shear ∘ (1 - t)`, `t = shear⁻¹ ∘ (shear - dG_x)`, `‖t‖ < 1`.
* `exists_totallyNormal_c1_diffeo` — **totally normal neighborhoods with the
  `C¹`-diffeomorphism clause** (do Carmo Ch. 3, Theorem 3.7, complete at `C¹`
  regularity): all clauses of `exists_totallyNormal_neighborhood` (normal
  balls at every center of `W`, covering with unique parameter), and moreover
  on the product ball `B = B_{δ₁}(φ_p(p)) × B_δ(0)` the pair map `G` is `C¹`
  and injective, its image is open, and there is a two-sided inverse `Ginv`
  which is `C¹` on that image — the inverse function theorem
  (`HasStrictFDerivAt.toOpenPartialHomeomorph` at the center for the global
  injectivity, `HasStrictFDerivAt.to_local_left_inverse` at each point for the
  regularity of the inverse). The joining parameter of the covering clause is
  computed by `Ginv`: `w = (Ginv(φ_p(q), φ_p(m)))₂` — the differentiable
  dependence of the joining geodesic on its endpoints (do Carmo's Remark 3.8).
  Slicing at a fixed base point `y = φ_p(q)` exhibits `exp_q` as a `C¹`
  diffeomorphism of the uniform velocity ball `B_δ(0)` onto an open set, for
  every `q ∈ W` simultaneously.
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

/-- **Math.** **Two uniform local flows of the chart-`p` spray compute the same
pair-map endpoint.** If `(r, ε, T, Z)` and `(r', ε', T', Z')` are two uniform
flow packages at `p` (each solving the spray ODE on its time interval with
chart confinement), then for any initial data `(y, w)` admissible for both,
`(Z(y, T⁻¹ • w) T)₁ = (Z'(y, T'⁻¹ • w) T')₁`.

Both time-rescaled flow segments are continuous intrinsic geodesics on an open
window containing `[0, 1]`, starting at `φ_p⁻¹(y)` with chart-`p` velocity `w`
(`isGeodesicOn_uniform_flow_segment_Ioo`); intrinsic uniqueness identifies the
first with the second (`IsGeodesicOn.eq_uniform_flow_readback`), and
evaluating at time `1` — which lies in the overlap window since `T < ε` and
`T' < ε'` — equates the chart readings via injectivity of `φ_p⁻¹` on the chart
target. -/
theorem uniform_flow_pairMap_agree
    (g : RiemannianMetric I M) (p : M) {r ε T r' ε' T' : ℝ}
    {Z Z' : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε) (hT' : 0 < T') (hT'ε' : T' < ε')
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    (hflow' : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r',
      Z' z 0 = z ∧
      (∀ t ∈ Icc (-ε') ε', HasDerivWithinAt (Z' z)
        (geodesicSprayCoord (I := I) g p (Z' z t).1 (Z' z t).2) (Icc (-ε') ε') t) ∧
      (∀ t ∈ Icc (-ε') ε', Z' z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {y w : E}
    (hmem : ((y, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r)
    (hmem' : ((y, T'⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r') :
    (Z ((y, T⁻¹ • w) : E × E) T).1 = (Z' ((y, T'⁻¹ • w) : E × E) T').1 := by
  obtain ⟨hstart, hcont, hgeo, -, hvel0, -⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow hmem
  have hεT : 0 < ε / T := div_pos (hT.trans hTε) hT
  have hε'T' : 0 < ε' / T' := div_pos (hT'.trans hT'ε') hT'
  have hEq := IsGeodesicOn.eq_uniform_flow_readback (p := p)
    hgeo hT' hT'ε' hflow' hmem' hεT hcont hstart hvel0
  -- `1` lies in the overlap window since `T < ε` and `T' < ε'`
  have h1T : (1 : ℝ) < ε / T := (one_lt_div hT).mpr hTε
  have h1T' : (1 : ℝ) < ε' / T' := (one_lt_div hT').mpr hT'ε'
  have h1mem : (1 : ℝ) ∈
      Ioo (-(min (ε / T) (ε' / T'))) (min (ε / T) (ε' / T')) := by
    constructor
    · have h0 : (0 : ℝ) < min (ε / T) (ε' / T') := lt_min hεT hε'T'
      linarith
    · exact lt_min h1T h1T'
  have h1 : (extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (1 * T)).1) =
      (extChartAt I p).symm ((Z' ((y, T'⁻¹ • w) : E × E) (1 * T')).1) :=
    hEq h1mem
  rw [one_mul, one_mul] at h1
  -- both endpoint readings lie in the chart target, where `φ_p⁻¹` is injective
  have hTIcc : T ∈ Icc (-ε) ε := ⟨by linarith, hTε.le⟩
  have hT'Icc : T' ∈ Icc (-ε') ε' := ⟨by linarith, hT'ε'.le⟩
  have htgt : (Z ((y, T⁻¹ • w) : E × E) T).1 ∈ (extChartAt I p).target :=
    ((hflow _ hmem).2.2 T hTIcc).1
  have htgt' : (Z' ((y, T'⁻¹ • w) : E × E) T').1 ∈ (extChartAt I p).target :=
    ((hflow' _ hmem').2.2 T' hT'Icc).1
  exact (extChartAt I p).symm.injOn htgt htgt' h1

/-- **Math.** **The derivative of the pair map is invertible at every point of a
ball around the zero section** (do Carmo Ch. 3, proof of Theorem 3.7; the
pair-map analogue of the invertibility clause `lem:dc-ch3-2-9-invertible`).
There are a flow package `(r, ε, T, Z)` and a radius `ρ > 0` such that:

* the flow clauses hold on the closed `r`-ball around the zero section;
* the pair map fixes the center: `(Z(φ_p(p), 0) T)₁ = φ_p(p)`;
* the `ρ`-ball around the center is admissible: `(x₁, T⁻¹ • x₂)` lies in the
  open flow ball for every `x` in it;
* the pair map `G(y, w) = (y, (Z(y, T⁻¹ • w) T)₁)` is `C¹` on the open set of
  admissible points;
* `G` is strictly differentiable at the center `(φ_p(p), 0)` with derivative
  the unipotent shear `(a, b) ↦ (a, a + b)`;
* at *every* point of the `ρ`-ball around the center, `G` has a strict Fréchet
  derivative realized by a continuous linear *equivalence*.

The center derivative is transported from
`exists_pairMap_hasStrictFDerivAt` — whose flow witness differs — via
`uniform_flow_pairMap_agree`; the derivative map of the `C¹` package
(`exists_pairMap_contDiffOn`) is continuous on the admissible set, so near the
center it stays within Neumann range of the invertible shear:
`dG_x = shear ∘ (1 - t)` with `t = shear⁻¹ ∘ (shear - dG_x)`, `‖t‖ < 1`. -/
theorem exists_pairMap_hasStrictFDerivAt_equiv_ball
    (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T ρ : ℝ) (Z : E × E → ℝ → E × E),
      0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧ 0 < ρ ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      (Z ((extChartAt I p p, (0 : E)) : E × E) T).1 = extChartAt I p p ∧
      (∀ x ∈ ball ((extChartAt I p p, (0 : E)) : E × E) ρ,
        ((x.1, T⁻¹ • x.2) : E × E) ∈
          ball ((extChartAt I p p, (0 : E)) : E × E) r) ∧
      ContDiffOn ℝ 1
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        {x : E × E | ((x.1, T⁻¹ • x.2) : E × E) ∈
          ball ((extChartAt I p p, (0 : E)) : E × E) r} ∧
      HasStrictFDerivAt
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        ((ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
        ((extChartAt I p p, (0 : E)) : E × E) ∧
      (∀ x ∈ ball ((extChartAt I p p, (0 : E)) : E × E) ρ,
        ∃ D' : (E × E) ≃L[ℝ] E × E,
          HasStrictFDerivAt
            (fun x' : E × E => ((x'.1 : E), (Z ((x'.1, T⁻¹ • x'.2) : E × E) T).1))
            (D' : (E × E) →L[ℝ] E × E) x) := by
  classical
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hGC1, -⟩ :=
    exists_pairMap_contDiffOn (I := I) g p
  obtain ⟨ra, εa, Ta, Za, hra, hεa, hTa, hTaεa, hflowa, hzeroa, hstricta⟩ :=
    exists_pairMap_hasStrictFDerivAt (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set G : E × E → E × E :=
    fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) with hGdef
  set Ga : E × E → E × E :=
    fun x => ((x.1 : E), (Za ((x.1, Ta⁻¹ • x.2) : E × E) Ta).1) with hGadef
  -- the two pair maps agree near the zero section
  have hι : Continuous (fun x : E × E => ((x.1, T⁻¹ • x.2) : E × E)) :=
    continuous_fst.prodMk (continuous_snd.const_smul T⁻¹)
  have hιa : Continuous (fun x : E × E => ((x.1, Ta⁻¹ • x.2) : E × E)) :=
    continuous_fst.prodMk (continuous_snd.const_smul Ta⁻¹)
  have hι0 : ((z₀.1, T⁻¹ • z₀.2) : E × E) = z₀ := by
    rw [hz₀def]
    show ((extChartAt I p p, T⁻¹ • (0 : E)) : E × E) = _
    rw [smul_zero]
  have hιa0 : ((z₀.1, Ta⁻¹ • z₀.2) : E × E) = z₀ := by
    rw [hz₀def]
    show ((extChartAt I p p, Ta⁻¹ • (0 : E)) : E × E) = _
    rw [smul_zero]
  have hm : (fun x : E × E => ((x.1, T⁻¹ • x.2) : E × E)) ⁻¹' ball z₀ r
      ∈ 𝓝 z₀ := by
    refine hι.continuousAt.preimage_mem_nhds ?_
    rw [hι0]
    exact ball_mem_nhds z₀ hr
  have hma : (fun x : E × E => ((x.1, Ta⁻¹ • x.2) : E × E)) ⁻¹' ball z₀ ra
      ∈ 𝓝 z₀ := by
    refine hιa.continuousAt.preimage_mem_nhds ?_
    rw [hιa0]
    exact ball_mem_nhds z₀ hra
  have hev : G =ᶠ[𝓝 z₀] Ga := by
    filter_upwards [hm, hma] with x hx hxa
    refine Prod.ext rfl ?_
    exact uniform_flow_pairMap_agree (I := I) g p hT hTε hTa hTaεa hflow hflowa
      (ball_subset_closedBall hx) (ball_subset_closedBall hxa)
  have hstrictG : HasStrictFDerivAt G
      ((ContinuousLinearMap.fst ℝ E E).prod
        ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
      z₀ :=
    hstricta.congr_of_eventuallyEq hev.symm
  -- the pair map fixes the center
  have hZT1 : (Z z₀ T).1 = extChartAt I p p := by
    have h0 : G z₀ = Ga z₀ := hev.self_of_nhds
    have hTaIcc : Ta ∈ Icc (-εa) εa := ⟨by linarith, hTaεa.le⟩
    have hGa0 : Ga z₀ = ((extChartAt I p p, extChartAt I p p) : E × E) := by
      show ((z₀.1 : E), (Za ((z₀.1, Ta⁻¹ • z₀.2) : E × E) Ta).1) = _
      rw [hιa0, hzeroa Ta hTaIcc]
    have hG0 : G z₀ = ((z₀.1 : E), (Z z₀ T).1) := by
      show ((z₀.1 : E), (Z ((z₀.1, T⁻¹ • z₀.2) : E × E) T).1) = _
      rw [hι0]
    have := congrArg Prod.snd ((hG0.symm.trans h0).trans hGa0)
    simpa using this
  -- the admissible set is open and contains the center
  set S : Set (E × E) := {x : E × E | ((x.1, T⁻¹ • x.2) : E × E) ∈ ball z₀ r}
    with hSdef
  have hSopen : IsOpen S := isOpen_ball.preimage hι
  have hz₀S : z₀ ∈ S := by
    show ((z₀.1, T⁻¹ • z₀.2) : E × E) ∈ ball z₀ r
    rw [hι0]
    exact mem_ball_self hr
  -- continuity of the derivative map on the admissible set
  have hcontf : ContinuousOn (fderiv ℝ G) S :=
    hGC1.continuousOn_fderiv_of_isOpen hSopen le_rfl
  -- the shear as a continuous linear equivalence
  set shear : (E × E) ≃L[ℝ] E × E := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.snd ℝ E E) - (ContinuousLinearMap.fst ℝ E E)))
    (fun x => by
      simp [ContinuousLinearMap.prod_apply])
    (fun x => by
      simp [ContinuousLinearMap.prod_apply]) with hsheardef
  have hshear_coe : (shear : (E × E) →L[ℝ] E × E)
      = (ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)) :=
    rfl
  have hfd0 : fderiv ℝ G z₀ = (shear : (E × E) →L[ℝ] E × E) := by
    rw [hshear_coe]
    exact hstrictG.hasFDerivAt.fderiv
  -- the Neumann radius: derivatives within `c₀` of the shear are invertible
  set c₀ : ℝ := (‖(shear.symm : (E × E) →L[ℝ] E × E)‖ + 1)⁻¹ with hc₀def
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    positivity
  have hat : ContinuousAt (fderiv ℝ G) z₀ :=
    hcontf.continuousAt (hSopen.mem_nhds hz₀S)
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.continuousAt_iff.mp hat c₀ hc₀pos
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.isOpen_iff.mp hSopen z₀ hz₀S
  refine ⟨r, ε, T, min ρ₁ ρ₂, Z, hr, hε, hT, hTε, lt_min hρ₁ hρ₂, hflow, hZT1,
    ?_, hGC1, hstrictG, ?_⟩
  · -- the `ρ`-ball is admissible
    intro x hx
    exact hρ₂sub (ball_subset_ball (min_le_right _ _) hx)
  · -- the Neumann perturbation of the shear at every point of the ball
    intro x hx
    have hx₁ : dist x z₀ < ρ₁ := lt_of_lt_of_le (mem_ball.mp hx) (min_le_left _ _)
    have hxS : x ∈ S := hρ₂sub (ball_subset_ball (min_le_right _ _) hx)
    have hstrictx : HasStrictFDerivAt G (fderiv ℝ G x) x :=
      (hGC1.contDiffAt (hSopen.mem_nhds hxS)).hasStrictFDerivAt one_ne_zero
    have hnear : ‖(shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x‖ < c₀ := by
      have h := hball hx₁
      rw [dist_eq_norm, hfd0] at h
      rwa [norm_sub_rev]
    set t : (E × E) →L[ℝ] E × E :=
      (shear.symm : (E × E) →L[ℝ] E × E).comp
        ((shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x) with htdef
    have htnorm : ‖t‖ < 1 := by
      have hle : ‖t‖ ≤ ‖(shear.symm : (E × E) →L[ℝ] E × E)‖ *
          ‖(shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      have h2 : ‖(shear.symm : (E × E) →L[ℝ] E × E)‖ *
          ‖(shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x‖
          ≤ ‖(shear.symm : (E × E) →L[ℝ] E × E)‖ * c₀ :=
        mul_le_mul_of_nonneg_left hnear.le (norm_nonneg _)
      have h3 : ‖(shear.symm : (E × E) →L[ℝ] E × E)‖ * c₀ < 1 := by
        rw [hc₀def, mul_inv_lt_iff₀ (by positivity)]
        linarith [norm_nonneg (shear.symm : (E × E) →L[ℝ] E × E)]
      exact lt_of_le_of_lt (hle.trans h2) h3
    set u : ((E × E) →L[ℝ] E × E)ˣ := Units.oneSub t htnorm with hudef
    refine ⟨(ContinuousLinearEquiv.unitsEquiv ℝ (E × E) u).trans shear, ?_⟩
    have hcoe : (((ContinuousLinearEquiv.unitsEquiv ℝ (E × E) u).trans shear :
        (E × E) ≃L[ℝ] E × E) : (E × E) →L[ℝ] E × E) = fderiv ℝ G x := by
      refine ContinuousLinearMap.ext fun v => ?_
      rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.unitsEquiv_apply]
      have h1 : (u : (E × E) →L[ℝ] E × E) v = v - t v := by
        rw [hudef]
        show (((1 : (E × E) →L[ℝ] E × E) - t) : (E × E) →L[ℝ] E × E) v = v - t v
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
      rw [h1, map_sub]
      have h2 : shear (t v) =
          ((shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x) v := by
        rw [htdef]
        show shear ((shear.symm : (E × E) →L[ℝ] E × E)
          (((shear : (E × E) →L[ℝ] E × E) - fderiv ℝ G x) v)) = _
        rw [ContinuousLinearEquiv.coe_coe]
        exact shear.apply_symm_apply _
      rw [h2, ContinuousLinearMap.sub_apply]
      have h3 : shear v = (shear : (E × E) →L[ℝ] E × E) v := rfl
      rw [h3]
      abel
    rw [hcoe]
    exact hstrictx

/-- **Math.** **Totally normal neighborhoods with the `C¹`-diffeomorphism clause**
(do Carmo Ch. 3, Theorem 3.7, complete at `C¹` regularity). For every `p ∈ M`
there are an open neighborhood `W ∋ p` inside the chart at `p`, radii
`δ, δ₁ > 0`, a time scale `T > 0`, a local geodesic flow `Z` of the chart-`p`
spray, and an inverse map `Ginv : E × E → E × E` such that, writing
`G(y, w) = (y, (Z(y, T⁻¹ • w) T)₁)` for the pair map (do Carmo's
`F(q, v) = (q, exp_q v)` in chart coordinates) and
`B = B_{δ₁}(φ_p(p)) ×ˢ B_δ(0)` for the product ball:

* **(chart bound)** `φ_p(W) ⊆ B_{δ₁}(φ_p(p))`;
* **(normal balls at every center)** for every `q ∈ W` and `‖w‖ < δ`, the
  rescaled flow segment `γ(s) = φ_p⁻¹((Z(φ_p(q), T⁻¹ • w)(sT))₁)` is a
  continuous intrinsic geodesic on `[0, 1]` starting at `q` with chart
  velocity `w` — the geodesic `s ↦ exp_q(sv)` for the velocity `v ∈ T_qM`
  with chart-`p` coordinate `w`;
* **(covering with unique, differentiably-dependent parameter)** any two
  `q, m ∈ W` are joined by such a segment with parameter
  `w = (Ginv(φ_p(q), φ_p(m)))₂`, the *unique* parameter in the `δ`-ball —
  do Carmo's `F⁻¹(q, m) = (q, v)` with differentiable dependence on the
  endpoints (Remark 3.8);
* **(`C¹` diffeomorphism)** on `B` the pair map `G` is `C¹` and injective,
  its image `G(B)` is open, `Ginv` is a two-sided inverse (`Ginv ∘ G = id` on
  `B`, `G ∘ Ginv = id` on `G(B)`), and `Ginv` is `C¹` on `G(B)`;
* **(pairs of `W` lie in the diffeomorphism range)** for all `q, m ∈ W`,
  `(φ_p(q), φ_p(m)) ∈ G(B)`.

Slicing the diffeomorphism clauses at a fixed first coordinate `y = φ_p(q)`
exhibits the chart exponential `w ↦ (Z(y, T⁻¹ • w) T)₁` at any `q ∈ W` as a
`C¹` diffeomorphism of the uniform ball `B_δ(0)` onto an open slice of
`G(B)` — do Carmo's "`exp_q` is a diffeomorphism on `B_δ(0)`", uniformly in
`q ∈ W`, with inverse `z ↦ (Ginv(y, z))₂`. -/
theorem exists_totallyNormal_c1_diffeo (g : RiemannianMetric I M) (p : M) :
    ∃ (W : Set M) (δ δ₁ T : ℝ) (Z : E × E → ℝ → E × E)
      (Ginv : E × E → E × E),
      IsOpen W ∧ p ∈ W ∧ W ⊆ (chartAt H p).source ∧
      0 < δ ∧ 0 < δ₁ ∧ 0 < T ∧
      (∀ q ∈ W, extChartAt I p q ∈ ball (extChartAt I p p) δ₁) ∧
      (∀ q ∈ W, ∀ w : E, ‖w‖ < δ →
        ∃ γ : ℝ → M,
          (∀ s : ℝ, γ s = (extChartAt I p).symm
            ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) (s * T)).1)) ∧
          γ 0 = q ∧
          ContinuousOn γ (Icc 0 1) ∧
          IsGeodesicOn (I := I) g γ (Icc 0 1) ∧
          (∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ (chartAt H p).source ∧
            extChartAt I p (γ s) =
              (Z ((extChartAt I p q, T⁻¹ • w) : E × E) (s * T)).1) ∧
          HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 ∧
          (∀ s ∈ Ioo (0 : ℝ) 1,
            HasDerivAt (fun s : ℝ => extChartAt I p (γ s))
              (T • (Z ((extChartAt I p q, T⁻¹ • w) : E × E) (s * T)).2) s)) ∧
      (∀ q ∈ W, ∀ m ∈ W, ∃ w : E, ‖w‖ < δ ∧
        (extChartAt I p).symm
          ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) T).1) = m ∧
        w = (Ginv ((extChartAt I p q, extChartAt I p m) : E × E)).2 ∧
        ∀ w' : E, ‖w'‖ < δ →
          (extChartAt I p).symm
            ((Z ((extChartAt I p q, T⁻¹ • w') : E × E) T).1) = m →
          w' = w) ∧
      ContDiffOn ℝ 1
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ) ∧
      Set.InjOn
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ) ∧
      IsOpen ((fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ)) ∧
      (∀ x ∈ ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ,
        Ginv ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) = x) ∧
      (∀ z ∈ (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
          '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ),
        (((Ginv z).1 : E), (Z (((Ginv z).1, T⁻¹ • (Ginv z).2) : E × E) T).1) = z) ∧
      ContDiffOn ℝ 1 Ginv
        ((fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
          '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ)) ∧
      (∀ q ∈ W, ∀ m ∈ W,
        ((extChartAt I p q, extChartAt I p m) : E × E) ∈
          (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
            '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ)) ∧
      Ginv ((extChartAt I p p, extChartAt I p p) : E × E)
        = ((extChartAt I p p, (0 : E)) : E × E) ∧
      (∃ (rF εF : ℝ), 0 < rF ∧ 0 < εF ∧ T < εF ∧
        (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) rF,
          Z z 0 = z ∧
          (∀ t ∈ Icc (-εF) εF, HasDerivWithinAt (Z z)
            (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-εF) εF) t) ∧
          (∀ t ∈ Icc (-εF) εF, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))) := by
  classical
  obtain ⟨r, ε, T, ρN, Z, hr, hε, hT, hTε, hρN, hflow, hZT1, hρNsub, hGC1,
    hstrict, hinv⟩ :=
    exists_pairMap_hasStrictFDerivAt_equiv_ball (I := I) g p
  set y₀ : E := extChartAt I p p with hy₀def
  set x₀ : E × E := ((y₀, (0 : E)) : E × E) with hx₀def
  set G : E × E → E × E :=
    fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) with hGdef
  have hTIcc : T ∈ Icc (-ε) ε := ⟨by linarith [hT, hε], hTε.le⟩
  -- the shear as a continuous linear equivalence
  set shear : (E × E) ≃L[ℝ] E × E := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.snd ℝ E E) - (ContinuousLinearMap.fst ℝ E E)))
    (fun x => by
      simp [ContinuousLinearMap.prod_apply])
    (fun x => by
      simp [ContinuousLinearMap.prod_apply]) with hsheardef
  have hshear_coe : (shear : (E × E) →L[ℝ] E × E)
      = (ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)) :=
    rfl
  have hstrict' : HasStrictFDerivAt G
      ((shear : (E × E) ≃L[ℝ] E × E) : (E × E) →L[ℝ] E × E) x₀ := by
    rw [hshear_coe]
    exact hstrict
  -- the inverse function theorem: `G` is a homeomorphism near `x₀`
  set ho := hstrict'.toOpenPartialHomeomorph G with hodef
  have hsource : x₀ ∈ ho.source := hstrict'.mem_toOpenPartialHomeomorph_source
  have hcoe : ⇑ho = G := hstrict'.toOpenPartialHomeomorph_coe
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.isOpen_iff.mp ho.open_source x₀ hsource
  -- the product-ball domain: radii small enough for the IFT source, the
  -- Neumann ball and the flow
  set δ₁ : ℝ := min (min ρ₂ ρN) r with hδ₁def
  set δ : ℝ := min (min ρ₂ ρN) (T * r) with hδdef
  have hδ₁pos : 0 < δ₁ := lt_min (lt_min hρ₂ hρN) hr
  have hδpos : 0 < δ := lt_min (lt_min hρ₂ hρN) (by positivity)
  set B : Set (E × E) := ball y₀ δ₁ ×ˢ ball (0 : E) δ with hBdef
  have hBopen : IsOpen B := isOpen_ball.prod isOpen_ball
  have hBsource : B ⊆ ho.source := by
    intro x hx
    refine hρ₂sub ?_
    rw [mem_ball, hx₀def, Prod.dist_eq]
    exact max_lt
      (lt_of_lt_of_le hx.1 ((min_le_left _ _).trans (min_le_left _ _)))
      (lt_of_lt_of_le hx.2 ((min_le_left _ _).trans (min_le_left _ _)))
  have hBρN : B ⊆ ball x₀ ρN := by
    intro x hx
    rw [mem_ball, hx₀def, Prod.dist_eq]
    exact max_lt
      (lt_of_lt_of_le hx.1 ((min_le_left _ _).trans (min_le_right _ _)))
      (lt_of_lt_of_le hx.2 ((min_le_left _ _).trans (min_le_right _ _)))
  have hBflow : ∀ x ∈ B, ((x.1, T⁻¹ • x.2) : E × E) ∈ closedBall x₀ r := by
    intro x hx
    rw [mem_closedBall, hx₀def, Prod.dist_eq]
    have hx1 : dist x.1 y₀ ≤ r :=
      le_of_lt (lt_of_lt_of_le (mem_ball.mp hx.1) (min_le_right _ _))
    refine max_le hx1 ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
    have hx2' : ‖x.2‖ < δ := by
      have := mem_ball.mp hx.2
      rwa [dist_zero_right] at this
    have hx2 : ‖x.2‖ < T * r := lt_of_lt_of_le hx2' (min_le_right _ _)
    rw [inv_mul_le_iff₀ hT]
    linarith [hx2]
  have hBS : ∀ x ∈ B, x ∈ {x : E × E | ((x.1, T⁻¹ • x.2) : E × E) ∈
      ball x₀ r} := by
    intro x hx
    show ((x.1, T⁻¹ • x.2) : E × E) ∈ ball x₀ r
    rw [mem_ball, hx₀def, Prod.dist_eq]
    have hx1 : dist x.1 y₀ < r :=
      lt_of_lt_of_le (mem_ball.mp hx.1) (min_le_right _ _)
    refine max_lt hx1 ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
    have hx2' : ‖x.2‖ < δ := by
      have := mem_ball.mp hx.2
      rwa [dist_zero_right] at this
    have hx2 : ‖x.2‖ < T * r := lt_of_lt_of_le hx2' (min_le_right _ _)
    rw [inv_mul_lt_iff₀ hT]
    linarith [hx2]
  -- `G x₀ = (y₀, y₀)`
  have hGx₀ : G x₀ = ((y₀, y₀) : E × E) := by
    show ((x₀.1 : E), (Z ((x₀.1, T⁻¹ • x₀.2) : E × E) T).1) = ((y₀, y₀) : E × E)
    have h1 : ((x₀.1, T⁻¹ • x₀.2) : E × E) = x₀ := by
      rw [hx₀def]
      show ((y₀, T⁻¹ • (0 : E)) : E × E) = ((y₀, (0 : E)) : E × E)
      rw [smul_zero]
    rw [h1]
    exact Prod.ext rfl hZT1
  -- `G` maps neighborhoods of `x₀` onto neighborhoods of `(y₀, y₀)`
  have hmapnhds : Filter.map G (𝓝 x₀) = 𝓝 ((y₀, y₀) : E × E) := by
    have := hstrict'.map_nhds_eq_of_equiv
    rwa [hGx₀] at this
  have hB𝓝 : B ∈ 𝓝 x₀ := by
    rw [hBdef, hx₀def]
    exact prod_mem_nhds (ball_mem_nhds _ hδ₁pos) (ball_mem_nhds _ hδpos)
  have hGB : G '' B ∈ 𝓝 ((y₀, y₀) : E × E) := by
    rw [← hmapnhds]
    exact image_mem_map hB𝓝
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hGB
  set η' : ℝ := min η δ₁ with hη'def
  have hη'pos : 0 < η' := lt_min hη hδ₁pos
  -- the totally normal neighborhood
  set W : Set M := (chartAt H p).source ∩ extChartAt I p ⁻¹' ball y₀ η'
    with hWdef
  have hWopen : IsOpen W := by
    have hcont : ContinuousOn (extChartAt I p) (chartAt H p).source := by
      have := continuousOn_extChartAt (I := I) p
      rwa [extChartAt_source] at this
    exact hcont.isOpen_inter_preimage (chartAt H p).open_source isOpen_ball
  have hpW : p ∈ W := by
    refine ⟨mem_chart_source H p, ?_⟩
    show extChartAt I p p ∈ ball y₀ η'
    rw [hy₀def]
    exact mem_ball_self hη'pos
  have hWsub : W ⊆ (chartAt H p).source := inter_subset_left
  have hWchart : ∀ q ∈ W, extChartAt I p q ∈ ball y₀ η' := fun q hq => hq.2
  have hWsrc : ∀ q ∈ W, q ∈ (extChartAt I p).source := by
    intro q hq
    rw [extChartAt_source]
    exact hWsub hq
  have hWflow : ∀ q ∈ W, ∀ w : E, ‖w‖ < δ →
      ((extChartAt I p q, T⁻¹ • w) : E × E) ∈ closedBall x₀ r := by
    intro q hq w hw
    refine hBflow ((extChartAt I p q, w)) ?_
    constructor
    · exact mem_ball.mpr
        (lt_of_lt_of_le (mem_ball.mp (hWchart q hq)) (min_le_right _ _))
    · rw [mem_ball, dist_zero_right]
      exact hw
  -- injectivity of the pair map on the product ball
  have hGinj : Set.InjOn G B := by
    intro a ha b hb hab
    refine ho.injOn (hBsource ha) (hBsource hb) ?_
    show ho a = ho b
    rw [hcoe]
    exact hab
  -- openness of the image: invertible strict derivative at every point of `B`
  have hGopen : IsOpen (G '' B) := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨D', hD'⟩ := hinv x (hBρN hx)
    rw [← hD'.map_nhds_eq_of_equiv]
    exact image_mem_map (hBopen.mem_nhds hx)
  -- the two-sided inverse from the IFT homeomorphism
  have hGinvG : ∀ x ∈ B, ho.symm (G x) = x := by
    intro x hx
    have := ho.left_inv (hBsource hx)
    rwa [hcoe] at this
  have hGGinv : ∀ z ∈ G '' B, G (ho.symm z) = z := by
    rintro z ⟨x, hx, rfl⟩
    rw [hGinvG x hx]
  -- the inverse is `C¹` on the open image
  have hGinvC1 : ContDiffOn ℝ 1 (⇑ho.symm) (G '' B) := by
    have key : ∀ z : E × E, ∃ Dz : (E × E) →L[ℝ] E × E,
        z ∈ G '' B → HasStrictFDerivAt (⇑ho.symm) Dz z := by
      intro z
      by_cases hz : z ∈ G '' B
      · obtain ⟨x, hx, rfl⟩ := hz
        obtain ⟨D', hD'⟩ := hinv x (hBρN hx)
        refine ⟨(D'.symm : (E × E) →L[ℝ] E × E), fun _ => ?_⟩
        have hg : ∀ᶠ x' in 𝓝 x, ho.symm (G x') = x' := by
          filter_upwards [ho.open_source.mem_nhds (hBsource hx)] with x' hx'
          have := ho.left_inv hx'
          rwa [hcoe] at this
        exact hD'.to_local_left_inverse hg
      · exact ⟨0, fun h => absurd h hz⟩
    choose Dz hDz using key
    exact contDiffOn_one_of_forall_hasStrictFDerivAt hGopen
      fun z hz => hDz z hz
  refine ⟨W, δ, δ₁, T, Z, ⇑ho.symm, hWopen, hpW, hWsub, hδpos, hδ₁pos, hT,
    ?_, ?_, ?_, hGC1.mono hBS, hGinj, hGopen, hGinvG, hGGinv, hGinvC1, ?_, ?_,
    ⟨r, ε, hr, hε, hTε, hflow⟩⟩
  · -- chart bound: `φ_p(W) ⊆ B_{δ₁}(φ_p(p))`
    intro q hq
    exact ball_subset_ball (min_le_right _ _) (hWchart q hq)
  · -- descent: normal balls at every center of `W`
    intro q hq w hw
    obtain ⟨hγ0, hγcont, hγgeo, hγchart, hγvel, -⟩ :=
      isGeodesicOn_uniform_flow_segment (I := I) g p hT hTε hflow
        (hWflow q hq w hw)
    obtain ⟨-, -, -, -, -, hγvelIoo⟩ :=
      isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow
        (hWflow q hq w hw)
    have hsub01 : Ioo (0 : ℝ) 1 ⊆ Ioo (-(ε / T)) (ε / T) := by
      have h1 : (1 : ℝ) < ε / T := (one_lt_div hT).mpr hTε
      intro s hs
      exact ⟨by linarith [hs.1, h1], by linarith [hs.2, h1]⟩
    refine ⟨fun s : ℝ => (extChartAt I p).symm
      ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) (s * T)).1),
      fun s => rfl, ?_, hγcont, hγgeo, hγchart, hγvel,
      fun s hs => hγvelIoo s (hsub01 hs)⟩
    rw [hγ0]
    exact (extChartAt I p).left_inv (hWsrc q hq)
  · -- covering with unique, differentiably-dependent parameter
    intro q hq m hm
    set y : E := extChartAt I p q with hydef
    set u : E := extChartAt I p m with hudef
    have hyu : ((y, u) : E × E) ∈ ball ((y₀, y₀) : E × E) η := by
      rw [mem_ball, Prod.dist_eq]
      exact max_lt
        (lt_of_lt_of_le (mem_ball.mp (hWchart q hq)) (min_le_left _ _))
        (lt_of_lt_of_le (mem_ball.mp (hWchart m hm)) (min_le_left _ _))
    obtain ⟨x, hxB, hGx⟩ := hηsub hyu
    have hx1 : x.1 = y := congrArg Prod.fst hGx
    have hw : ‖x.2‖ < δ := by
      have := mem_ball.mp hxB.2
      rwa [dist_zero_right] at this
    have hee : (Z ((y, T⁻¹ • x.2) : E × E) T).1 = u := by
      have h2 : (Z ((x.1, T⁻¹ • x.2) : E × E) T).1 = u := congrArg Prod.snd hGx
      rwa [hx1] at h2
    have hGinvyu : ho.symm ((y, u) : E × E) = x := by
      rw [← hGx]
      exact hGinvG x hxB
    refine ⟨x.2, hw, ?_, ?_, ?_⟩
    · rw [hee, hudef]
      exact (extChartAt I p).left_inv (hWsrc m hm)
    · -- the parameter is computed by the inverse of the pair map
      exact (congrArg Prod.snd hGinvyu).symm
    · -- uniqueness of the parameter in the `δ`-ball
      intro w' hw' hm'
      have hmemw' : ((y, T⁻¹ • w') : E × E) ∈ closedBall x₀ r :=
        hWflow q hq w' hw'
      have hconf' := (hflow _ hmemw').2.2 T hTIcc
      have happ : (Z ((y, T⁻¹ • w') : E × E) T).1 = u := by
        have hrinv : extChartAt I p
            ((extChartAt I p).symm ((Z ((y, T⁻¹ • w') : E × E) T).1))
            = (Z ((y, T⁻¹ • w') : E × E) T).1 :=
          (extChartAt I p).right_inv hconf'.1
        rw [hm'] at hrinv
        rw [← hrinv, hudef]
      have hyB : y ∈ ball y₀ δ₁ := mem_ball.mpr
        (lt_of_lt_of_le (mem_ball.mp (hWchart q hq)) (min_le_right _ _))
      have hxw'B : ((y, w') : E × E) ∈ B := by
        refine ⟨hyB, ?_⟩
        rwa [mem_ball, dist_zero_right]
      have hGeq : G ((y, w') : E × E) = G x := by
        rw [hGx]
        show ((y : E), (Z ((y, T⁻¹ • w') : E × E) T).1) = ((y, u) : E × E)
        rw [happ]
      have hxeq : ((y, w') : E × E) = x := hGinj hxw'B hxB hGeq
      have := congrArg Prod.snd hxeq
      simpa using this
  · -- pairs of `W` lie in the diffeomorphism range
    intro q hq m hm
    refine hηsub ?_
    rw [mem_ball, Prod.dist_eq]
    exact max_lt
      (lt_of_lt_of_le (mem_ball.mp (hWchart q hq)) (min_le_left _ _))
      (lt_of_lt_of_le (mem_ball.mp (hWchart m hm)) (min_le_left _ _))
  · -- diagonal value of the inverse pair map at the center: `Ginv(y₀, y₀) = (y₀, 0)`.
    -- `G(y₀, 0) = (y₀, y₀)` (`hGx₀`), and `Ginv ∘ G = id` on `B ∋ (y₀, 0)` (`hGinvG`).
    have hx₀B : x₀ ∈ B := by
      rw [hBdef, hx₀def]
      exact ⟨mem_ball_self hδ₁pos, mem_ball_self hδpos⟩
    have hinvGx₀ : ho.symm (G x₀) = x₀ := hGinvG x₀ hx₀B
    rw [hGx₀] at hinvGx₀
    simpa only [hx₀def] using hinvGx₀

end Exponential

end Riemannian
