/- Engineering infrastructure for the Petersen Ch. 5 exponential-map chapter: the
   `C^∞` upgrade of the `C¹` pair-map / totally-normal-diffeomorphism package of
   `Exponential/TotallyNormalDiffeo.lean`.  Not a blueprint node. -/
import PetersenLib.Riemannian.Exponential.TotallyNormalDiffeo
import PetersenLib.Riemannian.Geodesic.FlowCInftyDependence
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option linter.unusedSectionVars false

/-!
# Totally normal neighborhoods: the `C^∞`-diffeomorphism clause

`Exponential/TotallyNormalDiffeo.lean` proves that the pair map
`G(y, w) = (y, (Z (y, T⁻¹ • w) T).1)` — the chart reading of
`F(q, v) = (q, exp_q v)` — is a `C¹` diffeomorphism of a product ball onto an
open set.  That `C¹` ceiling was purely an artifact of the engine used there
(`exists_uniform_geodesic_flow_hasStrictFDerivAt`, which only produces a strict
Fréchet derivative of the flow in its initial condition).

Meanwhile `Geodesic/FlowCInftyDependence.lean` provides
`exists_uniform_geodesic_flow_contDiffAt`: a uniform-time local geodesic flow
whose curve family `σ : E × E → C([0, T], E × E)` is `C^∞` in the initial
condition at every point of the open flow ball, with *exactly the same package
shape* as the `C¹` engine.  Swapping the engine upgrades the whole tower to
`C^∞`.  Note that this never needs joint smoothness in `(q, v, t)`: the pair map
evaluates the flow at the *fixed* time `T`, so time never enters as a variable.

Main declarations:

* `exists_pairMap_contDiffOn_infty` — the pair map `G` is `C^∞` on the open set
  of admissible initial conditions, and, sliced at each base point `y`, the chart
  exponential `w ↦ (Z (y, T⁻¹ • w) T).1` is `C^∞` on the uniform velocity ball of
  radius `T·r`.  The composite `G = (fst, fst ∘ ev_T ∘ σ ∘ ι₂)` is built from the
  `C^∞` family `σ`, the *continuous linear* evaluation `ev_T` and the *continuous
  linear* fibre rescaling `ι₂ (y, w) = (y, T⁻¹ • w)`.
* `exists_pairMap_hasStrictFDerivAt_equiv_ball_infty` — the `C^∞` refinement of
  `exists_pairMap_hasStrictFDerivAt_equiv_ball`: the same flow package, the same
  `[[I, 0], [I, I]]` shear derivative at the center, the same Neumann ball of
  invertible strict derivatives, but with `ContDiffOn ℝ ∞ G` in place of
  `ContDiffOn ℝ 1 G`.
* `exists_totallyNormal_cinfty_diffeo` — the `C^∞` refinement of
  `exists_totallyNormal_c1_diffeo`: every clause of that theorem, with both `G`
  and its two-sided inverse `Ginv` upgraded from `C¹` to `C^∞`.  The inverse's
  regularity comes from `OpenPartialHomeomorph.contDiffAt_symm` (equivalently
  `ContDiffAt.to_localInverse`) instead of
  `HasStrictFDerivAt.to_local_left_inverse`.
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

namespace PetersenLib

namespace Exponential

open PetersenLib.Geodesic PetersenLib.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

/-- **Math.** **The pair map is `C^∞` on a ball around the zero section** (the
`C^∞` refinement of `exists_pairMap_contDiffOn`; do Carmo Ch. 3, Theorem 3.7,
the regularity of `F(q, v) = (q, exp_q v)`).  There are a uniform flow `Z` of the
chart-`p` spray and a Picard time `T < ε` such that the pair map
`G(y, w) = (y, (Z (y, T⁻¹ • w) T).1)` is `C^∞` on the open set of admissible
initial conditions, and, slicing at each base point `y`, the chart exponential
`w ↦ (Z (y, T⁻¹ • w) T).1` at `φ_p⁻¹(y)` is `C^∞` on the uniform velocity ball of
radius `T·r`.

The flow's curve family `σ` is `C^∞` in its initial condition on the open flow
ball (`exists_uniform_geodesic_flow_contDiffAt`); evaluation at the fixed time
`T` (`ContinuousMap.evalCLM`) and the fibre rescaling `(y, w) ↦ (y, T⁻¹ • w)` are
continuous *linear* maps, hence `C^∞`, so `G` is `C^∞` by composition, once the
flow reading `Z` is replaced by `σ` near the point (which holds on the whole flow
ball). -/
theorem exists_pairMap_contDiffOn_infty (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E), 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      ContDiffOn ℝ ∞
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        {x : E × E | ((x.1, T⁻¹ • x.2) : E × E) ∈
          ball ((extChartAt I p p, (0 : E)) : E × E) r} ∧
      (∀ y ∈ ball (extChartAt I p p) r,
        ContDiffOn ℝ ∞ (fun w : E => (Z ((y, T⁻¹ • w) : E × E) T).1)
          (ball (0 : E) (T * r))) := by
  classical
  obtain ⟨r, ε, T, Z, L, σ, hT, hr, hε, hTε, hflow, hLip, hmax, hσZ, hD⟩ :=
    exists_uniform_geodesic_flow_contDiffAt (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set tT : Set.Icc (0 : ℝ) T := ⟨T, ⟨hT.le, le_rfl⟩⟩ with htTdef
  set ι₂ : E × E → E × E := fun x => ((x.1 : E), T⁻¹ • x.2) with hι₂def
  set Dι₂ : E × E →L[ℝ] E × E :=
    (ContinuousLinearMap.fst ℝ E E).prod
      (T⁻¹ • ContinuousLinearMap.snd ℝ E E) with hDι₂def
  have hι₂eq : ι₂ = fun x : E × E => Dι₂ x := by
    funext x
    rw [hι₂def, hDι₂def]
    rfl
  have hι₂cont : Continuous ι₂ := by
    rw [hι₂eq]
    exact Dι₂.continuous
  have hι₂smooth : ∀ x : E × E, ContDiffAt ℝ ∞ ι₂ x := by
    intro x
    rw [hι₂eq]
    exact Dι₂.contDiff.contDiffAt
  set G : E × E → E × E :=
    fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) with hGdef
  set S : Set (E × E) := {x : E × E | ι₂ x ∈ ball z₀ r} with hSdef
  have hSopen : IsOpen S := isOpen_ball.preimage hι₂cont
  -- pointwise `C^∞`-ness of `G` on `S`
  have key : ∀ x ∈ S, ContDiffAt ℝ ∞ G x := by
    intro x hx
    -- `σ` is `C^∞` at the rescaled initial condition
    have hσc : ContDiffAt ℝ ∞ σ (ι₂ x) := hD (ι₂ x) hx
    -- evaluation at the fixed time `T` is a continuous linear map, hence `C^∞`
    have heval : ContDiffAt ℝ ∞ (fun y : E × E => σ y tT) (ι₂ x) := by
      have hcomp := ((ContinuousMap.evalCLM ℝ tT).contDiff
        (n := (∞ : ℕ∞ω))).contDiffAt.comp (ι₂ x) hσc
      simpa [Function.comp_def] using hcomp
    have hfstσ : ContDiffAt ℝ ∞ (fun y : E × E => (σ y tT).1) (ι₂ x) := heval.fst
    have hcompσ : ContDiffAt ℝ ∞ (fun x' : E × E => (σ (ι₂ x') tT).1) x :=
      hfstσ.comp x (hι₂smooth x)
    have hGpair : ContDiffAt ℝ ∞
        (fun x' : E × E => ((x'.1 : E), (σ (ι₂ x') tT).1)) x :=
      contDiffAt_fst.prodMk hcompσ
    -- pass from the curve family `σ` back to the flow reading `Z` near `x`
    have hev : G =ᶠ[𝓝 x] (fun x' : E × E => ((x'.1 : E), (σ (ι₂ x') tT).1)) := by
      filter_upwards [hι₂cont.continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds hx)] with x' hx'
      have hx'' : ι₂ x' ∈ closedBall z₀ r := ball_subset_closedBall hx'
      refine Prod.ext rfl ?_
      show (Z ((x'.1, T⁻¹ • x'.2) : E × E) T).1 = (σ (ι₂ x') tT).1
      rw [hσZ _ hx'' tT]
    exact hGpair.congr_of_eventuallyEq hev
  have hGCinf : ContDiffOn ℝ ∞ G S := fun x hx => (key x hx).contDiffWithinAt
  refine ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hGCinf, ?_⟩
  -- slice at a fixed base point `y`
  intro y hy
  have hemb : ContDiff ℝ ∞ (fun w : E => ((y, w) : E × E)) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : MapsTo (fun w : E => ((y, w) : E × E)) (ball (0 : E) (T * r)) S := by
    intro w hw
    show ((y, T⁻¹ • w) : E × E) ∈ ball z₀ r
    rw [mem_ball, hz₀def, Prod.dist_eq]
    refine max_lt (mem_ball.mp hy) ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
    have hw' : ‖w‖ < T * r := by
      have := mem_ball.mp hw
      rwa [dist_zero_right] at this
    rw [inv_mul_lt_iff₀ hT]
    linarith
  have hcomp : ContDiffOn ℝ ∞ (fun w : E => G ((y, w) : E × E))
      (ball (0 : E) (T * r)) :=
    hGCinf.comp hemb.contDiffOn hmaps
  exact hcomp.snd

/-- **Math.** **The `C^∞` refinement of `exists_pairMap_hasStrictFDerivAt_equiv_ball`**
(do Carmo Ch. 3, proof of Theorem 3.7).  There are a flow package `(r, ε, T, Z)`
and a radius `ρ > 0` such that:

* the flow clauses hold on the closed `r`-ball around the zero section;
* the pair map fixes the center: `(Z (φ_p p, 0) T).1 = φ_p p`;
* the `ρ`-ball around the center is admissible;
* the pair map `G(y, w) = (y, (Z (y, T⁻¹ • w) T).1)` is **`C^∞`** on the open set
  of admissible points;
* `G` is strictly differentiable at the center `(φ_p p, 0)` with derivative the
  unipotent shear `(a, b) ↦ (a, a + b)`;
* at *every* point of the `ρ`-ball around the center, `G` has a strict Fréchet
  derivative realized by a continuous linear *equivalence*.

Identical to the `C¹` statement except for the regularity of `G`; the proof is the
same, with `exists_pairMap_contDiffOn_infty` in place of
`exists_pairMap_contDiffOn` as the flow source. -/
theorem exists_pairMap_hasStrictFDerivAt_equiv_ball_infty
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
      ContDiffOn ℝ ∞
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
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hGCinf, -⟩ :=
    exists_pairMap_contDiffOn_infty (I := I) g p
  obtain ⟨ra, εa, Ta, Za, hra, hεa, hTa, hTaεa, hflowa, hzeroa, hstricta⟩ :=
    exists_pairMap_hasStrictFDerivAt (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set G : E × E → E × E :=
    fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) with hGdef
  set Ga : E × E → E × E :=
    fun x => ((x.1 : E), (Za ((x.1, Ta⁻¹ • x.2) : E × E) Ta).1) with hGadef
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
  set S : Set (E × E) := {x : E × E | ((x.1, T⁻¹ • x.2) : E × E) ∈ ball z₀ r}
    with hSdef
  have hSopen : IsOpen S := isOpen_ball.preimage hι
  have hz₀S : z₀ ∈ S := by
    show ((z₀.1, T⁻¹ • z₀.2) : E × E) ∈ ball z₀ r
    rw [hι0]
    exact mem_ball_self hr
  have hone : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast le_of_lt (by exact_mod_cast ENat.coe_lt_top 1 : ((1 : ℕ∞) : ℕ∞ω) < ∞)
  have hcontf : ContinuousOn (fderiv ℝ G) S :=
    hGCinf.continuousOn_fderiv_of_isOpen hSopen hone
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
  set c₀ : ℝ := (‖(shear.symm : (E × E) →L[ℝ] E × E)‖ + 1)⁻¹ with hc₀def
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]
    positivity
  have hat : ContinuousAt (fderiv ℝ G) z₀ :=
    hcontf.continuousAt (hSopen.mem_nhds hz₀S)
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.continuousAt_iff.mp hat c₀ hc₀pos
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.isOpen_iff.mp hSopen z₀ hz₀S
  refine ⟨r, ε, T, min ρ₁ ρ₂, Z, hr, hε, hT, hTε, lt_min hρ₁ hρ₂, hflow, hZT1,
    ?_, hGCinf, hstrictG, ?_⟩
  · intro x hx
    exact hρ₂sub (ball_subset_ball (min_le_right _ _) hx)
  · intro x hx
    have hx₁ : dist x z₀ < ρ₁ := lt_of_lt_of_le (mem_ball.mp hx) (min_le_left _ _)
    have hxS : x ∈ S := hρ₂sub (ball_subset_ball (min_le_right _ _) hx)
    have hstrictx : HasStrictFDerivAt G (fderiv ℝ G x) x :=
      (hGCinf.contDiffAt (hSopen.mem_nhds hxS)).hasStrictFDerivAt (by simp)
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

/-- **Math.** **Totally normal neighborhoods with the `C^∞`-diffeomorphism clause**
(do Carmo Ch. 3, Theorem 3.7, complete at `C^∞` regularity; the `C^∞` refinement of
`exists_totallyNormal_c1_diffeo`).  For every `p ∈ M` there are an open
neighborhood `W ∋ p` inside the chart at `p`, radii `δ, δ₁ > 0`, a time scale
`T > 0`, a local geodesic flow `Z` of the chart-`p` spray, and an inverse map
`Ginv : E × E → E × E` such that, writing `G(y, w) = (y, (Z (y, T⁻¹ • w) T).1)`
for the pair map (do Carmo's `F(q, v) = (q, exp_q v)` in chart coordinates) and
`B = B_{δ₁}(φ_p p) ×ˢ B_δ(0)` for the product ball:

* **(chart bound)** `φ_p(W) ⊆ B_{δ₁}(φ_p p)`;
* **(shear derivative at the center)** `G` is strictly differentiable at
  `(φ_p p, 0)` with derivative the unipotent shear `(a, b) ↦ (a, a + b)`, do
  Carmo's / Petersen's `[[I, 0], [I, I]]`;
* **(normal balls at every center)** for every `q ∈ W` and `‖w‖ < δ`, the rescaled
  flow segment `γ(s) = φ_p⁻¹((Z (φ_p q, T⁻¹ • w) (sT)).1)` is a continuous
  intrinsic geodesic on `[0, 1]` starting at `q` with chart velocity `w` — the
  geodesic `s ↦ exp_q(sv)`;
* **(covering with unique, smoothly-dependent parameter)** any two `q, m ∈ W` are
  joined by such a segment with parameter `w = (Ginv (φ_p q, φ_p m)).2`, the
  *unique* parameter in the `δ`-ball;
* **(`C^∞` diffeomorphism)** on `B` the pair map `G` is `C^∞` and injective, its
  image `G(B)` is open, `Ginv` is a two-sided inverse (`Ginv ∘ G = id` on `B`,
  `G ∘ Ginv = id` on `G(B)`), and `Ginv` is `C^∞` on `G(B)`;
* **(pairs of `W` lie in the diffeomorphism range)** for all `q, m ∈ W`,
  `(φ_p q, φ_p m) ∈ G(B)`.

Slicing the diffeomorphism clauses at a fixed first coordinate `y = φ_p q`
exhibits the chart exponential `w ↦ (Z (y, T⁻¹ • w) T).1` at any `q ∈ W` as a
`C^∞` diffeomorphism of the uniform ball `B_δ(0)` onto an open slice of `G(B)`,
uniformly in `q ∈ W`, with inverse `z ↦ (Ginv (y, z)).2`.

The proof is that of `exists_totallyNormal_c1_diffeo` with the `C^∞` pair-map
package `exists_pairMap_hasStrictFDerivAt_equiv_ball_infty` as source, and with
the regularity of the inverse supplied by `OpenPartialHomeomorph.contDiffAt_symm`
(the `C^r` inverse function theorem) in place of
`HasStrictFDerivAt.to_local_left_inverse`. -/
theorem exists_totallyNormal_cinfty_diffeo (g : RiemannianMetric I M) (p : M) :
    ∃ (W : Set M) (δ δ₁ T : ℝ) (Z : E × E → ℝ → E × E)
      (Ginv : E × E → E × E),
      IsOpen W ∧ p ∈ W ∧ W ⊆ (chartAt H p).source ∧
      0 < δ ∧ 0 < δ₁ ∧ 0 < T ∧
      (∀ q ∈ W, extChartAt I p q ∈ ball (extChartAt I p p) δ₁) ∧
      HasStrictFDerivAt
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        ((ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
        ((extChartAt I p p, (0 : E)) : E × E) ∧
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
          HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0) ∧
      (∀ q ∈ W, ∀ m ∈ W, ∃ w : E, ‖w‖ < δ ∧
        (extChartAt I p).symm
          ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) T).1) = m ∧
        w = (Ginv ((extChartAt I p q, extChartAt I p m) : E × E)).2 ∧
        ∀ w' : E, ‖w'‖ < δ →
          (extChartAt I p).symm
            ((Z ((extChartAt I p q, T⁻¹ • w') : E × E) T).1) = m →
          w' = w) ∧
      ContDiffOn ℝ ∞
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
      ContDiffOn ℝ ∞ Ginv
        ((fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
          '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ)) ∧
      (∀ q ∈ W, ∀ m ∈ W,
        ((extChartAt I p q, extChartAt I p m) : E × E) ∈
          (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
            '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ)) := by
  classical
  obtain ⟨r, ε, T, ρN, Z, hr, hε, hT, hTε, hρN, hflow, hZT1, hρNsub, hGCinf,
    hstrict, hinv⟩ :=
    exists_pairMap_hasStrictFDerivAt_equiv_ball_infty (I := I) g p
  set y₀ : E := extChartAt I p p with hy₀def
  set x₀ : E × E := ((y₀, (0 : E)) : E × E) with hx₀def
  set G : E × E → E × E :=
    fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) with hGdef
  have hTIcc : T ∈ Icc (-ε) ε := ⟨by linarith [hT, hε], hTε.le⟩
  set S : Set (E × E) := {x : E × E | ((x.1, T⁻¹ • x.2) : E × E) ∈ ball x₀ r}
    with hSdef
  have hSopen : IsOpen S :=
    isOpen_ball.preimage (continuous_fst.prodMk (continuous_snd.const_smul T⁻¹))
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
  set ho := hstrict'.toOpenPartialHomeomorph G with hodef
  have hsource : x₀ ∈ ho.source := hstrict'.mem_toOpenPartialHomeomorph_source
  have hcoe : ⇑ho = G := hstrict'.toOpenPartialHomeomorph_coe
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.isOpen_iff.mp ho.open_source x₀ hsource
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
  have hBS : ∀ x ∈ B, x ∈ S := by
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
  have hGx₀ : G x₀ = ((y₀, y₀) : E × E) := by
    show ((x₀.1 : E), (Z ((x₀.1, T⁻¹ • x₀.2) : E × E) T).1) = ((y₀, y₀) : E × E)
    have h1 : ((x₀.1, T⁻¹ • x₀.2) : E × E) = x₀ := by
      rw [hx₀def]
      show ((y₀, T⁻¹ • (0 : E)) : E × E) = ((y₀, (0 : E)) : E × E)
      rw [smul_zero]
    rw [h1]
    exact Prod.ext rfl hZT1
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
  have hGinj : Set.InjOn G B := by
    intro a ha b hb hab
    refine ho.injOn (hBsource ha) (hBsource hb) ?_
    show ho a = ho b
    rw [hcoe]
    exact hab
  have hGopen : IsOpen (G '' B) := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨D', hD'⟩ := hinv x (hBρN hx)
    rw [← hD'.map_nhds_eq_of_equiv]
    exact image_mem_map (hBopen.mem_nhds hx)
  have hGinvG : ∀ x ∈ B, ho.symm (G x) = x := by
    intro x hx
    have := ho.left_inv (hBsource hx)
    rwa [hcoe] at this
  have hGGinv : ∀ z ∈ G '' B, G (ho.symm z) = z := by
    rintro z ⟨x, hx, rfl⟩
    rw [hGinvG x hx]
  -- the inverse is `C^∞` on the open image: the `C^r` inverse function theorem
  have hGinvCinf : ContDiffOn ℝ ∞ (⇑ho.symm) (G '' B) := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨D', hD'⟩ := hinv x (hBρN hx)
    have hxsrc : x ∈ ho.source := hBsource hx
    have hztgt : G x ∈ ho.target := by
      have := ho.map_source hxsrc
      rwa [hcoe] at this
    have hsymm : ho.symm (G x) = x := hGinvG x hx
    have hf' : HasFDerivAt (⇑ho) (D' : (E × E) →L[ℝ] E × E) (ho.symm (G x)) := by
      rw [hsymm, hcoe]
      exact hD'.hasFDerivAt
    have hf : ContDiffAt ℝ ∞ (⇑ho) (ho.symm (G x)) := by
      rw [hsymm, hcoe]
      exact hGCinf.contDiffAt (hSopen.mem_nhds (hBS x hx))
    exact (ho.contDiffAt_symm hztgt hf' hf).contDiffWithinAt
  refine ⟨W, δ, δ₁, T, Z, ⇑ho.symm, hWopen, hpW, hWsub, hδpos, hδ₁pos, hT,
    ?_, hstrict, ?_, ?_, hGCinf.mono hBS, hGinj, hGopen, hGinvG, hGGinv,
    hGinvCinf, ?_⟩
  · intro q hq
    exact ball_subset_ball (min_le_right _ _) (hWchart q hq)
  · intro q hq w hw
    obtain ⟨hγ0, hγcont, hγgeo, hγchart, hγvel, -⟩ :=
      isGeodesicOn_uniform_flow_segment (I := I) g p hT hTε hflow
        (hWflow q hq w hw)
    refine ⟨fun s : ℝ => (extChartAt I p).symm
      ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) (s * T)).1),
      fun s => rfl, ?_, hγcont, hγgeo, hγchart, hγvel⟩
    rw [hγ0]
    exact (extChartAt I p).left_inv (hWsrc q hq)
  · intro q hq m hm
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
    · exact (congrArg Prod.snd hGinvyu).symm
    · intro w' hw' hm'
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
  · intro q hq m hm
    refine hηsub ?_
    rw [mem_ball, Prod.dist_eq]
    exact max_lt
      (lt_of_lt_of_le (mem_ball.mp (hWchart q hq)) (min_le_left _ _))
      (lt_of_lt_of_le (mem_ball.mp (hWchart m hm)) (min_le_left _ _))

end Exponential

end PetersenLib
