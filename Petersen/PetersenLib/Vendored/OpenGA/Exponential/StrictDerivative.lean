/- Vendored from DoCarmo `OpenGALib/Riemannian/Exponential/StrictDerivative.lean`. Namespace `Riemannian` mapped to
   `PetersenLib`; engineering infrastructure only, not a blueprint node. -/
import PetersenLib.Vendored.OpenGA.Geodesic.UniformExistence
import PetersenLib.Vendored.OpenGA.Geodesic.FlowDependence
import PetersenLib.Vendored.OpenGA.Exponential.Ray

set_option linter.unusedSectionVars false

/-!
# Strict differentiability of the exponential map at the origin

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 2.9: `d(exp_p)_0 = id`, and
`exp_p` is a local diffeomorphism at `0`. This file proves the strict-derivative
form of that statement and its topological consequences:

* `fderiv_geodesicSprayCoord_equilibrium` — the linearization of the coordinate
  geodesic spray `F(x, w) = (w, -Γ_p(w, w)(x))` at the zero-section point is the
  two-step nilpotent map `A(u, w) = (w, 0)`: the Christoffel term is quadratic
  in the velocity, so it does not contribute to the derivative at `w = 0`.
* `exists_hasStrictFDerivAt_extChartAt_expMap` — **`exp_p` is strictly
  differentiable at `0` with derivative the identity**, read in the chart at
  `p`; moreover a ball around `0` lies in the exponential domain and its image
  stays in the chart. The proof composes the C¹-dependence-on-initial-conditions
  theorem (`hasStrictFDerivAt_of_picardResidual`, applied to the spray at its
  equilibrium over a short time `T` with `T‖A‖ < 1`) with the geodesic
  homogeneity `γ(1, p, w) = γ(T, p, w/T)` (realized by fibre scaling of the
  flow witness), which trades the fixed evaluation time `1` for the short
  Picard–Lindelöf time `T`. The derivative is computed exactly: since
  `A ∘ A = 0` the Neumann series terminates.
* `map_expMap_nhds` — `exp_p` maps neighbourhoods of `0 ∈ T_pM` exactly onto
  neighbourhoods of `p`: normal-neighbourhood existence at the topological
  level.
* `exists_injOn_expMap` — `exp_p` is injective on a small ball around `0`.

The full `C^∞`-diffeomorphism statement of do Carmo's Proposition 2.9 requires
`C^k` dependence of the geodesic flow on initial conditions and remains open;
the strict-derivative and local-homeomorphism content is complete here.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace PetersenLib
namespace Exponential

open PetersenLib.Geodesic PetersenLib.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** The two-step nilpotent linearization `A(u, w) = (w, 0)` of the geodesic
spray squares to zero. -/
lemma sprayLinearization_comp_self :
    (((ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E)).comp
      ((ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E)))
      = (0 : E × E →L[ℝ] E × E) := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp

set_option maxHeartbeats 800000 in
/-- **Math.** **The linearization of the geodesic spray at the zero section.** At the
equilibrium `(φ_p(p), 0)`, the derivative of `F(x, w) = (w, -Γ_p(w, w)(x))` is the
nilpotent map `A(u, w) = (w, 0)`: the Christoffel contraction is quadratic in `w`,
so its derivative vanishes at `w = 0` (do Carmo Ch. 3, the computation behind
`d(exp_p)_0 = id` in Prop. 2.9). -/
lemma fderiv_geodesicSprayCoord_equilibrium (g : RiemannianMetric I M) (p : M) :
    fderiv ℝ (fun ζ : E × E => geodesicSprayCoord (I := I) g p ζ.1 ζ.2)
        ((extChartAt I p p, (0 : E)) : E × E)
      = (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E) := by
  classical
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g p ζ.1 ζ.2 with hFdef
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  have hmem : z₀ ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  have hFs : ContDiffOn ℝ ∞ F ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g p
  have hFd : HasFDerivAt F (fderiv ℝ F z₀) z₀ :=
    ((hFs.contDiffAt (hopen.mem_nhds hmem)).differentiableAt
      (by simp)).hasFDerivAt
  refine ContinuousLinearMap.ext fun q => ?_
  obtain ⟨u, w⟩ := q
  -- the straight line through the equilibrium in direction `(u, w)`
  set c : ℝ → E × E := fun t => z₀ + t • ((u, w) : E × E) with hcdef
  have hline : HasDerivAt c ((u, w) : E × E) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • ((u, w) : E × E))
        ((1 : ℝ) • ((u, w) : E × E)) 0 := (hasDerivAt_id 0).smul_const _
    simpa [hcdef, one_smul] using h1.const_add z₀
  -- derivative of `F ∘ c` via the chain rule
  have hchain : HasDerivAt (fun t => F (c t)) (fderiv ℝ F z₀ ((u, w) : E × E)) 0 := by
    have hc0 : c 0 = z₀ := by simp [hcdef]
    have hFd' : HasFDerivAt F (fderiv ℝ F z₀) (c 0) := by rw [hc0]; exact hFd
    exact hFd'.comp_hasDerivAt 0 hline
  -- direct computation of the same derivative
  have hcval : ∀ t : ℝ, F (c t) =
      ((t • w : E),
        -((t * t) • chartChristoffelContraction (I := I) g p w w
          (extChartAt I p p + t • u))) := by
    intro t
    have hc1 : (c t).1 = extChartAt I p p + t • u := by
      simp [hcdef, hz₀def, Prod.smul_def]
    have hc2 : (c t).2 = t • w := by
      simp [hcdef, hz₀def, Prod.smul_def]
    show geodesicSprayCoord (I := I) g p (c t).1 (c t).2 = _
    rw [hc1, hc2, geodesicSprayCoord_def,
      chartChristoffelContraction_smul_smul (I := I) g p t w _]
  -- the quadratic coefficient is differentiable in the base slot near `0`
  have hGdiff : DifferentiableAt ℝ
      (fun t : ℝ => chartChristoffelContraction (I := I) g p w w
        (extChartAt I p p + t • u)) 0 := by
    have hslice : DifferentiableAt ℝ
        (fun y : E => chartChristoffelContraction (I := I) g p w w y)
        (extChartAt I p p) := by
      have hmem' : ((extChartAt I p p, w) : E × E) ∈
          (extChartAt I p).target ×ˢ (univ : Set E) :=
        ⟨mem_extChartAt_target p, mem_univ _⟩
      have hF1 : DifferentiableAt ℝ F ((extChartAt I p p, w) : E × E) :=
        (hFs.contDiffAt (hopen.mem_nhds hmem')).differentiableAt (by simp)
      have hin : DifferentiableAt ℝ (fun y : E => ((y, w) : E × E))
          (extChartAt I p p) :=
        differentiableAt_id.prodMk (differentiableAt_const w)
      have hyd : DifferentiableAt ℝ (fun y : E => F (y, w)) (extChartAt I p p) := by
        have h := hF1.comp (extChartAt I p p) hin
        exact h
      have hval : (fun y : E => chartChristoffelContraction (I := I) g p w w y)
          = fun y : E => -((F (y, w)).2) := by
        funext y
        show chartChristoffelContraction (I := I) g p w w y =
          -(geodesicSprayCoord (I := I) g p y w).2
        rw [geodesicSprayCoord_def]
        simp
      rw [hval]
      exact (differentiableAt_snd.comp _ hyd).neg
    have hin2 : DifferentiableAt ℝ (fun t : ℝ => extChartAt I p p + t • u) 0 :=
      (differentiableAt_const _).add (differentiableAt_id.smul_const u)
    have hslice' : DifferentiableAt ℝ
        (fun y : E => chartChristoffelContraction (I := I) g p w w y)
        (extChartAt I p p + (0 : ℝ) • u) := by
      simpa using hslice
    have h := hslice'.comp 0 hin2
    exact h
  -- product rule: `t² • G(t)` has derivative `0` at `t = 0`
  have hdirect : HasDerivAt (fun t => F (c t)) ((w, 0) : E × E) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t • w : E)) w 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have hsq : HasDerivAt (fun t : ℝ => t * t) 0 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))
    have h2 : HasDerivAt (fun t : ℝ =>
        (t * t) • chartChristoffelContraction (I := I) g p w w
          (extChartAt I p p + t • u)) 0 0 := by
      have := hsq.smul hGdiff.hasDerivAt
      simpa using this
    have h2' : HasDerivAt (fun t : ℝ =>
        -((t * t) • chartChristoffelContraction (I := I) g p w w
          (extChartAt I p p + t • u))) 0 0 := by
      simpa using h2.neg
    have hpair := h1.prodMk h2'
    exact hpair.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => hcval t)
  -- uniqueness of the derivative identifies the two computations
  have huniq := hchain.unique hdirect
  rw [huniq]
  simp

set_option maxHeartbeats 1000000 in
/-- **Math.** **`exp_p` is strictly differentiable at `0` with derivative the
identity** (do Carmo Ch. 3, Prop. 2.9, strict-derivative form). There is `ρ > 0`
such that every `w` with `‖w‖ < ρ` lies in the exponential domain, `exp_p(w)`
stays in the chart at `p`, and the chart reading `w ↦ φ_p(exp_p(w))` has the
identity as strict Fréchet derivative at `0`.

Route: the C¹-dependence theorem applied to the geodesic spray at its
zero-section equilibrium over a short time `T` with `T‖A‖ < 1`; the homogeneity
`γ(1, p, w) = γ(T, p, w/T)` (fibre scaling of the flow witness) converts
evaluation at time `1` into evaluation of the Picard–Lindelöf flow at time `T`,
and the nilpotency `A ∘ A = 0` of the spray linearization computes the
derivative exactly. -/
theorem exists_hasStrictFDerivAt_extChartAt_expMap
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      HasStrictFDerivAt
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (ContinuousLinearMap.id ℝ E) 0 := by
  classical
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip, hZzero, hmax⟩ :=
    exists_uniform_geodesic_flow (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g p ζ.1 ζ.2 with hFdef
  set A : E × E →L[ℝ] E × E :=
    (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E) with hAdef
  have hA2 : A.comp A = 0 := sprayLinearization_comp_self
  have hfd : fderiv ℝ F z₀ = A :=
    fderiv_geodesicSprayCoord_equilibrium (I := I) g p
  -- the short Picard time
  set T : ℝ := min (ε / 2) (1 / (2 * (‖A‖ + 1))) with hTdef
  have hT : 0 < T := lt_min (by positivity) (by positivity)
  have hTε : T < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hTA : T * ‖A‖ < 1 := by
    have h1 : T ≤ 1 / (2 * (‖A‖ + 1)) := min_le_right _ _
    have h2 : (0 : ℝ) < 2 * (‖A‖ + 1) := by positivity
    have h3 : T * ‖A‖ ≤ (1 / (2 * (‖A‖ + 1))) * ‖A‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg A)
    have h4 : (1 / (2 * (‖A‖ + 1))) * (2 * (‖A‖ + 1)) = 1 :=
      one_div_mul_cancel (ne_of_gt h2)
    nlinarith [norm_nonneg A]
  have hIccTsub : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := fun t ht =>
    ⟨le_trans (neg_nonpos.mpr hε.le) ht.1, ht.2.trans hTε.le⟩
  have hTIoo : T ∈ Ioo (-ε) ε := ⟨lt_trans (neg_lt_zero.mpr hε) hT, hTε⟩
  set tT : Set.Icc (0 : ℝ) T := ⟨T, ⟨hT.le, le_rfl⟩⟩ with htTdef
  -- the solution family on `C([0,T], E × E)`
  set σ : E × E → C(Set.Icc (0 : ℝ) T, E × E) := fun x =>
    if hx : x ∈ closedBall z₀ r then
      ⟨fun t => Z x t.1, by
        have hcont : ContinuousOn (Z x) (Icc (-ε) ε) := fun s hs =>
          ((hflow x hx).2.1 s hs).continuousWithinAt
        exact hcont.comp_continuous continuous_subtype_val
          fun t => hIccTsub t.2⟩
    else ContinuousMap.const _ z₀ with hσdef
  have hσ_ball : ∀ x, x ∈ closedBall z₀ r → ∀ t : Set.Icc (0 : ℝ) T,
      σ x t = Z x t.1 := by
    intro x hx t
    simp only [hσdef, dif_pos hx]
    rfl
  have hσ0 : σ z₀ = ContinuousMap.const _ z₀ := by
    refine ContinuousMap.ext fun t => ?_
    rw [hσ_ball z₀ (mem_closedBall_self hr.le) t, ContinuousMap.const_apply]
    exact hZzero t.1 (hIccTsub t.2)
  have hσc : ContinuousAt σ z₀ := by
    have hlips : LipschitzOnWith L σ (closedBall z₀ r) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [ContinuousMap.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)]
      intro t
      rw [hσ_ball x hx t, hσ_ball y hy t]
      exact (hLip t.1 (hIccTsub t.2)).dist_le_mul x hx y hy
    exact (hlips.continuousOn.continuousWithinAt
      (mem_closedBall_self hr.le)).continuousAt (closedBall_mem_nhds z₀ hr)
  -- differentiability data for the spray near the equilibrium
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  have hmemz₀ : z₀ ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  have hFs : ContDiffOn ℝ ∞ F ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g p
  obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.isOpen_iff.mp hopen z₀ hmemz₀
  have hd : ∀ x ∈ ball z₀ ρ', HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
    ((hFs.contDiffAt (hopen.mem_nhds (hρ'sub hx))).differentiableAt
      (by simp)).hasFDerivAt
  have hc : ContinuousAt (fderiv ℝ F) z₀ :=
    (hFs.continuousOn_fderiv_of_isOpen hopen (by exact_mod_cast le_top)).continuousAt
      (hopen.mem_nhds hmemz₀)
  have heq : F z₀ = 0 := geodesicSprayCoord_zero_velocity (I := I) g p _
  have hTL : T * ‖fderiv ℝ F z₀‖ < 1 := by rw [hfd]; exact hTA
  -- the flow solutions satisfy the Picard integral equation
  have hσres : ∀ᶠ x in 𝓝 z₀, picardResidual hT.le F (x, σ x) = 0 := by
    filter_upwards [ball_mem_nhds z₀ hr] with x hx
    have hx' : x ∈ closedBall z₀ r := ball_subset_closedBall hx
    obtain ⟨h0, hdZ, hmemZ⟩ := hflow x hx'
    exact picardResidual_eq_zero_of_hasDerivWithinAt hT hFs.continuousOn h0
      (fun t ht => hmemZ t (hIccTsub ht))
      (fun t ht => (hdZ t (hIccTsub ht)).mono hIccTsub)
      (σ x) (fun t => hσ_ball x hx' t)
  -- the explicit derivative from the nilpotent linearization
  set D : E × E →L[ℝ] C(Set.Icc (0 : ℝ) T, E × E) :=
    ContinuousLinearMap.const ℝ (Set.Icc (0 : ℝ) T) + (linearRamp hT.le).comp A
    with hDdef
  have hD : ∀ v : E × E, D v - intervalPrimitive hT.le
      (postcomp (fderiv ℝ F z₀) (D v)) = ContinuousMap.const _ v := by
    intro v
    rw [hfd]
    exact sub_intervalPrimitive_postcomp_ramp hT.le hA2 v
  -- strict differentiability of the flow in its initial condition
  have hmain : HasStrictFDerivAt σ D z₀ :=
    hasStrictFDerivAt_of_picardResidual hT hρ'pos heq hd hc hTL hσ0 hσc hσres hD
  have heval : HasStrictFDerivAt (fun y => σ y tT)
      ((ContinuousMap.evalCLM ℝ tT).comp D) z₀ :=
    (ContinuousMap.evalCLM ℝ tT).hasStrictFDerivAt.comp z₀ hmain
  have hfstσ : HasStrictFDerivAt (fun y => (σ y tT).1)
      ((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)) z₀ :=
    (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.comp z₀ heval
  -- the affine reparametrization `w ↦ (φ_p(p), w/T)`
  set ι : E → E × E := fun w => (extChartAt I p p, T⁻¹ • w) with hιdef
  set Dι : E →L[ℝ] E × E :=
    (0 : E →L[ℝ] E).prod (T⁻¹ • ContinuousLinearMap.id ℝ E) with hDιdef
  have hι : HasStrictFDerivAt ι Dι 0 :=
    (hasStrictFDerivAt_const _ _).prodMk
      (T⁻¹ • ContinuousLinearMap.id ℝ E).hasStrictFDerivAt
  have hι0 : ι 0 = z₀ := by simp [hιdef, hz₀def]
  have hcomp : HasStrictFDerivAt (fun w => (σ (ι w) tT).1)
      (((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι) 0 := by
    have hfstσ' : HasStrictFDerivAt (fun y => (σ y tT).1)
        ((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)) (ι 0) := by
      rw [hι0]; exact hfstσ
    exact hfstσ'.comp 0 hι
  -- the total derivative is the identity
  have hDtot : (((ContinuousLinearMap.fst ℝ E E).comp
      ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι)
      = ContinuousLinearMap.id ℝ E := by
    refine ContinuousLinearMap.ext fun w => ?_
    show ((D (Dι w)) tT).1 = w
    have hval : Dι w = (((0 : E), T⁻¹ • w) : E × E) := by
      simp [hDιdef]
    rw [hval]
    have hDval : D ((((0 : E), T⁻¹ • w)) : E × E)
        = ContinuousMap.const _ ((((0 : E), T⁻¹ • w)) : E × E)
          + linearRamp hT.le ((((T⁻¹ • w : E), (0 : E))) : E × E) := rfl
    rw [hDval]
    show ((((0 : E), T⁻¹ • w) : E × E)
      + (T : ℝ) • ((((T⁻¹ • w : E), (0 : E))) : E × E)).1 = w
    show (0 : E) + (T : ℝ) • (T⁻¹ • w) = w
    rw [zero_add, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  -- identification: the chart reading of `exp_p` is the flow composite
  set ρ : ℝ := r * T with hρdef
  have hρpos : 0 < ρ := by positivity
  have key : ∀ w : E, ‖w‖ < ρ →
      ((w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))
        = (σ (ι w) tT).1) := by
    intro w hw
    set u : E := T⁻¹ • w with hudef
    have hu : ‖u‖ < r := by
      rw [hudef, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
      rw [inv_mul_lt_iff₀ hT]
      rw [hρdef] at hw
      linarith [hw, mul_comm r T]
    have hTu : (T : ℝ) • u = w := smul_inv_smul₀ hT.ne' w
    -- the flow witness for `(p, u)`
    have hzu : ((extChartAt I p p, u) : E × E) ∈ closedBall z₀ r := by
      rw [mem_closedBall, hz₀def, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      exact max_le hr.le hu.le
    obtain ⟨h0u, hdu, hmemu⟩ := hflow _ hzu
    have hdIoo : ∀ s ∈ Ioo (-ε) ε,
        HasDerivAt (Z ((extChartAt I p p, u) : E × E))
          (geodesicSprayCoord (I := I) g p
            (Z ((extChartAt I p p, u) : E × E) s).1
            (Z ((extChartAt I p p, u) : E × E) s).2) s := fun s hs =>
      (hdu s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hmemΨ : ∀ s ∈ Ioo (-ε) ε,
        Z ((extChartAt I p p, u) : E × E) s ∈
          (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
      intro s hs
      rw [extChartAt_tangent_target (I := I) p]
      exact hmemu s (Ioo_subset_Icc_self hs)
    obtain ⟨hwit, hsrc, hchart⟩ :=
      isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord (I := I) g p
        (u : TangentSpace I p) h0u hdIoo hmemΨ
    -- fibre-scale the witness from `(p, u)` to `(p, T • u) = (p, w)`
    have hTu' : (T • (u : TangentSpace I p)) = (w : TangentSpace I p) := by
      show (T • u : E) = w
      exact hTu
    have hwitW : IsGeodesicOnWithInitial (I := I) g
        (fun t => (((extChartAt I.tangent
          (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (Z ((extChartAt I p p, u) : E × E) (T * t))).proj))
        {t : ℝ | T * t ∈ Ioo (-ε) ε} p (w : TangentSpace I p) := by
      obtain ⟨fW, hproj, hf0, hint⟩ := hwit.fiberScale T
      refine ⟨fW, hproj, ?_, hint⟩
      rw [hf0]
      exact congrArg
        (fun v : TangentSpace I p => (⟨p, v⟩ : TangentBundle I M)) hTu'
    have hJ'o : IsOpen {t : ℝ | T * t ∈ Ioo (-ε) ε} :=
      isOpen_Ioo.preimage (continuous_const.mul continuous_id)
    have hJ'eq : {t : ℝ | T * t ∈ Ioo (-ε) ε} = Ioo (-(ε / T)) (ε / T) := by
      ext t
      simp only [mem_setOf_eq, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · rw [← neg_div, div_lt_iff₀ hT]
          nlinarith
        · rw [lt_div_iff₀ hT]
          nlinarith
      · rintro ⟨h1, h2⟩
        rw [← neg_div, div_lt_iff₀ hT] at h1
        rw [lt_div_iff₀ hT] at h2
        exact ⟨by nlinarith, by nlinarith⟩
    have hJ'c : IsPreconnected {t : ℝ | T * t ∈ Ioo (-ε) ε} := by
      rw [hJ'eq]; exact isPreconnected_Ioo
    have h0J' : (0 : ℝ) ∈ {t : ℝ | T * t ∈ Ioo (-ε) ε} := by
      simp only [mem_setOf_eq, mul_zero]
      exact ⟨neg_lt_zero.mpr hε, hε⟩
    have h1J' : (1 : ℝ) ∈ {t : ℝ | T * t ∈ Ioo (-ε) ε} := by
      simp only [mem_setOf_eq, mul_one]
      exact hTIoo
    have hsrcW : ∀ t ∈ {t : ℝ | T * t ∈ Ioo (-ε) ε},
        (((extChartAt I.tangent
          (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (Z ((extChartAt I p p, u) : E × E) (T * t))).proj) ∈
          (chartAt H p).source := fun t ht => hsrc (T * t) ht
    -- the canonical maximal geodesic is computed by the scaled witness
    have hval := maximalGeodesic_eq_witness_of_mem_chart (I := I) hwitW
      hJ'o hJ'c h0J' hsrcW h1J'
    have hdom : (w : TangentSpace I p) ∈ expDomain (I := I) g p := by
      show (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (w : TangentSpace I p)
      exact subset_maximalGeodesicInterval_of_witness (I := I) hwitW
        hJ'o hJ'c h0J' h1J'
    have hexp_eq : expMap (I := I) g p (w : TangentSpace I p)
        = (((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (Z ((extChartAt I p p, u) : E × E) (T * 1))).proj) := by
      show maximalGeodesic (I := I) g p (w : TangentSpace I p) 1 = _
      exact hval
    rw [mul_one] at hexp_eq
    have hTmem : T ∈ Ioo (-ε) ε := hTIoo
    refine ⟨hdom, ?_, ?_⟩
    · rw [hexp_eq]
      exact hsrc T hTmem
    · rw [hexp_eq, hchart T hTmem]
      have hσval : σ (ι w) tT = Z ((extChartAt I p p, u) : E × E) T := by
        have hιw : ι w = ((extChartAt I p p, u) : E × E) := by
          rw [hιdef, hudef]
        rw [hιw, hσ_ball _ hzu tT]
      rw [hσval]
  -- assemble
  refine ⟨ρ, hρpos, fun w hw => (key w hw).1, fun w hw => (key w hw).2.1, ?_⟩
  have hev : (fun w : E => extChartAt I p
      (expMap (I := I) g p (w : TangentSpace I p)))
      =ᶠ[𝓝 (0 : E)] fun w => (σ (ι w) tT).1 := by
    filter_upwards [ball_mem_nhds (0 : E) hρpos] with w hw
    exact (key w (mem_ball_zero_iff.mp hw)).2.2
  have hfinal := hcomp.congr_of_eventuallyEq hev.symm
  rwa [hDtot] at hfinal

/-- **Math.** **`exp_p` maps neighbourhoods of `0` onto neighbourhoods of `p`**
(do Carmo Ch. 3, Prop. 2.9, topological content): the exponential map at `p`
sends the neighbourhood filter of `0 ∈ T_pM` exactly to the neighbourhood filter
of `p`. In particular the image of any neighbourhood of `0` is a neighbourhood
of `p` — the existence of normal neighbourhoods at the topological level. -/
theorem map_expMap_nhds (g : RiemannianMetric I M) (p : M) :
    Filter.map (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
      (𝓝 (0 : E)) = 𝓝 p := by
  obtain ⟨ρ, hρ, hdom, hsrc, hstrict⟩ :=
    exists_hasStrictFDerivAt_extChartAt_expMap (I := I) g p
  have hstrict' : HasStrictFDerivAt
      (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
    rwa [ContinuousLinearEquiv.coe_refl]
  -- the chart reading maps `𝓝 0` to `𝓝 (φ_p p)`
  have hzero : extChartAt I p (expMap (I := I) g p ((0 : E) : TangentSpace I p))
      = extChartAt I p p := by
    have h0 : expMap (I := I) g p ((0 : E) : TangentSpace I p) = p :=
      expMap_zero (I := I) g p
    rw [h0]
  have hmapchart := hstrict'.map_nhds_eq_of_equiv
  rw [hzero] at hmapchart
  -- `exp_p = φ_p⁻¹ ∘ (φ_p ∘ exp_p)` near `0`
  have hev : (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
      =ᶠ[𝓝 (0 : E)] fun w => (extChartAt I p).symm
        (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) := by
    filter_upwards [ball_mem_nhds (0 : E) hρ] with w hw
    rw [PartialEquiv.left_inv]
    rw [extChartAt_source]
    exact hsrc w (mem_ball_zero_iff.mp hw)
  rw [Filter.map_congr hev]
  show Filter.map ((extChartAt I p).symm ∘ fun w : E =>
    extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) (𝓝 (0 : E)) = 𝓝 p
  rw [← Filter.map_map, hmapchart]
  have hsymm := map_extChartAt_symm_nhdsWithin_range (I := I) p
  rwa [I.range_eq_univ, nhdsWithin_univ] at hsymm

/-- **Math.** **`exp_p` is injective near `0`** (do Carmo Ch. 3, Prop. 2.9,
injectivity content): there is `ρ > 0` such that `exp_p` is injective on the
ball of radius `ρ` in `T_pM`, whose points all lie in the exponential domain. -/
theorem exists_injOn_expMap (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ρ) ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) := by
  obtain ⟨ρ₀, hρ₀, hdom, hsrc, hstrict⟩ :=
    exists_hasStrictFDerivAt_extChartAt_expMap (I := I) g p
  have hstrict' : HasStrictFDerivAt
      (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
    rwa [ContinuousLinearEquiv.coe_refl]
  set ho := hstrict'.toOpenPartialHomeomorph
    (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
    with hodef
  have hsource : (0 : E) ∈ ho.source :=
    hstrict'.mem_toOpenPartialHomeomorph_source
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.isOpen_iff.mp ho.open_source 0 hsource
  refine ⟨min ρ₀ ρ₁, lt_min hρ₀ hρ₁, ?_, fun w hw =>
    hdom w (lt_of_lt_of_le hw (min_le_left _ _))⟩
  intro w₁ hw₁ w₂ hw₂ hexp
  have hw₁' : w₁ ∈ ho.source := hball
    (mem_ball_zero_iff.mpr (lt_of_lt_of_le (mem_ball_zero_iff.mp hw₁)
      (min_le_right _ _)))
  have hw₂' : w₂ ∈ ho.source := hball
    (mem_ball_zero_iff.mpr (lt_of_lt_of_le (mem_ball_zero_iff.mp hw₂)
      (min_le_right _ _)))
  have hcoe := hstrict'.toOpenPartialHomeomorph_coe
  refine ho.injOn hw₁' hw₂' ?_
  show ho w₁ = ho w₂
  calc ho w₁
      = extChartAt I p (expMap (I := I) g p (w₁ : TangentSpace I p)) := by
        rw [hodef]; exact congrFun hcoe w₁
    _ = extChartAt I p (expMap (I := I) g p (w₂ : TangentSpace I p)) :=
        congrArg _ hexp
    _ = ho w₂ := by
        rw [hodef]; exact (congrFun hcoe w₂).symm

end Exponential
end PetersenLib
