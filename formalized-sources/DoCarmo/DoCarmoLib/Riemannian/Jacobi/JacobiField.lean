import DoCarmoLib.Riemannian.Jacobi.FrameReduction
import DoCarmoLib.Riemannian.Jacobi.JacobiEquationODE

/-!
# The intrinsic Jacobi field: existence and uniqueness by initial data (do Carmo `def:dc-ch5-2-1`)

This file assembles the three landed sub-lemmas of do Carmo's Jacobi-field definition
`def:dc-ch5-2-1` into the intrinsic existence/uniqueness statement:

* the **parallel orthonormal frame** `e₁(t),…,eₙ(t)` along the geodesic
  (`DoCarmoLib/Riemannian/Jacobi/ParallelFrame.lean`, `lem:dc-ch5-2-1-parallel-frame`);
* the **frame reduction** `J = Σᵢ fᵢ eᵢ ⟺` the scalar system `fⱼ'' + Σᵢ aᵢⱼ fᵢ = 0`
  (`DoCarmoLib/Riemannian/Jacobi/FrameReduction.lean`, `lem:dc-ch5-2-1-frame-reduction`);
* the **abstract second-order linear ODE** `f'' + A(t) f = 0` — existence for arbitrary
  initial data and uniqueness by initial conditions
  (`DoCarmoLib/Riemannian/Jacobi/JacobiEquationODE.lean`, `lem:dc-ch5-2-1-ode`).

Given a parallel orthonormal frame `e` along the chart curve `u` and the chart reading
`R : ℝ → E →L[ℝ] E` of the curvature contraction `w ↦ R(γ',w)γ'`, we package the coupled
scalar system as a single first-order operator `jacobiCoefOp` on the coefficient space
`ι → ℝ`, feed it to `exists_isJacobiPairOn` / `IsJacobiPairOn.eqOn`, and read the solution
back through the frame as `J(t) = Σᵢ fᵢ(t) eᵢ(t)`.  The resulting field satisfies the
intrinsic Jacobi equation `D²J/dt² + R(t)(J) = 0` on the interior of the interval, and is
determined by its initial position and (frame) velocity — do Carmo's *"a Jacobi field is
determined by its initial conditions `J(0), DJ/dt(0)`; there exists a `C^∞` solution."*

The curvature field `R` is kept abstract (a continuous operator field); instantiating it
with the intrinsic curvature `curvatureOperatorAt` read in the fixed chart (the
chart-curvature bridge of
`DoCarmoLib/Riemannian/Connection/ChartCurvatureMovingPoint.lean`) is the remaining step to
close the parent node `def:dc-ch5-2-1` itself.

## Main results

* `Riemannian.Jacobi.jacobiCoefOp` — the coupled scalar system `fⱼ'' + Σᵢ aᵢⱼ fᵢ = 0`
  packaged as an operator field `A(t) : (ι → ℝ) →L[ℝ] (ι → ℝ)`.
* `Riemannian.Jacobi.exists_jacobiField_frame` — **existence**: for any initial data
  `(J₀, w₀)` there is a Jacobi field `J = Σᵢ fᵢ eᵢ` with `J(a) = J₀`, initial frame
  velocity `w₀`, satisfying the intrinsic Jacobi equation on `Ioo a b`.
* `Riemannian.Jacobi.jacobiField_frame_eqOn` — **uniqueness**: two frame Jacobi fields
  whose components share initial position and velocity agree on `[a,b]`.
-/

open Set
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`: the curvature coefficient
`aᵢⱼ(t) = ⟨R(γ',eᵢ)γ', eⱼ⟩` in the chart at `α`, read as the chart inner product of
`R(t)(eᵢ(t))` with `eⱼ(t)`. -/
def jacobiCoef (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (R : ℝ → E →L[ℝ] E)
    (e : ι → ℝ → E) (i j : ι) (t : ℝ) : ℝ :=
  chartMetricInner (I := I) g α (u t) (R t (e i t)) (e j t)

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`: the coupled second-order scalar system
`fⱼ'' + Σᵢ aᵢⱼ(t) fᵢ = 0` packaged as a single continuous linear operator field
`A(t) : (ι → ℝ) →L[ℝ] (ι → ℝ)` on the coefficient space, `A(t) c = (fun k => Σᵢ aᵢₖ(t) cᵢ)`.
This is the coefficient of the first-order companion system of
`DoCarmoLib/Riemannian/Jacobi/JacobiEquationODE.lean`. -/
def jacobiCoefOp (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (R : ℝ → E →L[ℝ] E)
    (e : ι → ℝ → E) (t : ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ∑ j, ∑ i, jacobiCoef (I := I) g α u R e i j t •
    (ContinuousLinearMap.proj i).smulRight (Pi.single j (1 : ℝ))

/-- **Math.** Application formula for the coefficient operator: `(A(t) c) k = Σᵢ aᵢₖ(t) cᵢ`. -/
theorem jacobiCoefOp_apply (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (R : ℝ → E →L[ℝ] E) (e : ι → ℝ → E) (t : ℝ) (c : ι → ℝ) (k : ι) :
    jacobiCoefOp (I := I) g α u R e t c k = ∑ i, jacobiCoef (I := I) g α u R e i k t * c i := by
  classical
  simp only [jacobiCoefOp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_apply]
  -- reduce the outer `j`-sum by `Pi.single j 1 k = if j = k then 1 else 0`
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ k]
  simp [mul_comm]

/-! ## Continuity of the coefficient operator -/

/-- **Math.** The curvature coefficient `aᵢⱼ(t) = ⟨R(t)(eᵢ(t)), eⱼ(t)⟩` is continuous in
`t`, given continuity of the chart Gram entries along `u`, of the curvature field `R`, and
of the frame vectors `eᵢ, eⱼ`. -/
theorem continuousOn_jacobiCoef (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (R : ℝ → E →L[ℝ] E) (e : ι → ℝ → E) {a b : ℝ}
    (hR : ContinuousOn R (Icc a b)) (he : ∀ i, ContinuousOn (e i) (Icc a b))
    (hG : ∀ p q, ContinuousOn (fun t => chartGramOnE (I := I) g α p q (u t)) (Icc a b))
    (i j : ι) :
    ContinuousOn (jacobiCoef (I := I) g α u R e i j) (Icc a b) := by
  have hfun : jacobiCoef (I := I) g α u R e i j = fun t => ∑ p, ∑ q,
      chartGramOnE (I := I) g α p q (u t)
        * Geodesic.chartCoord (E := E) p (R t (e i t))
        * Geodesic.chartCoord (E := E) q (e j t) := by
    funext t; rw [jacobiCoef, chartMetricInner_def]
  rw [hfun]
  refine continuousOn_finset_sum _ fun p _ => continuousOn_finset_sum _ fun q _ => ?_
  have hRei : ContinuousOn (fun t => R t (e i t)) (Icc a b) := hR.clm_apply (he i)
  have hcp : ContinuousOn (fun t => Geodesic.chartCoord (E := E) p (R t (e i t))) (Icc a b) := by
    have := (Geodesic.chartCoordFunctional (E := E) p).continuous.comp_continuousOn hRei
    simpa only [Geodesic.chartCoordFunctional_apply] using this
  have hcq : ContinuousOn (fun t => Geodesic.chartCoord (E := E) q (e j t)) (Icc a b) := by
    have := (Geodesic.chartCoordFunctional (E := E) q).continuous.comp_continuousOn (he j)
    simpa only [Geodesic.chartCoordFunctional_apply] using this
  exact ((hG p q).mul hcp).mul hcq

/-- **Math.** The coefficient operator `A(t)` is continuous, hence bounded on compacts —
supplying the `ContinuousOn A` hypothesis of `exists_isJacobiPairOn`. -/
theorem continuousOn_jacobiCoefOp (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (R : ℝ → E →L[ℝ] E) (e : ι → ℝ → E) {a b : ℝ}
    (hR : ContinuousOn R (Icc a b)) (he : ∀ i, ContinuousOn (e i) (Icc a b))
    (hG : ∀ p q, ContinuousOn (fun t => chartGramOnE (I := I) g α p q (u t)) (Icc a b)) :
    ContinuousOn (jacobiCoefOp (I := I) g α u R e) (Icc a b) := by
  refine continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun i _ => ?_
  exact (continuousOn_jacobiCoef (I := I) g α u R e hR he hG i j).smul continuousOn_const

/-! ## Existence of the intrinsic Jacobi field with prescribed initial data -/

/-- **Math.** Existence of the Jacobi field (do Carmo `def:dc-ch5-2-1`). Along a parallel
orthonormal frame `e₁,…,eₙ` for the chart curve `u` (`lem:dc-ch5-2-1-parallel-frame`), and
for the chart reading `R` of the curvature contraction, every initial pair `(J₀, w₀)`
determines a Jacobi field `J(t) = Σᵢ fᵢ(t) eᵢ(t)`:

* `J(a) = J₀`;
* the components `fᵢ` have initial (within-interval) velocity `⟨w₀, eᵢ(a)⟩`, so that
  `DJ/dt(a) = w₀` (in the parallel frame `DJ/dt = Σᵢ fᵢ' eᵢ`);
* `J` satisfies the intrinsic Jacobi equation `D²J/dt² + R(t)(J) = 0` on the interior
  `(a,b)`.

This is do Carmo's *"given the initial conditions `J(0)`, `DJ/dt(0)`, there exists a
`C^∞` solution defined on `[0,a]`."*  The components `fᵢ` are the coordinates of `J` in the
frame; the frame reduction (`covariantDerivCoord2_add_map_frameCombination_expand`) turns the
intrinsic equation into the scalar system, which the abstract ODE
(`exists_isJacobiPairOn`) solves. -/
theorem exists_jacobiField_frame (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (R : ℝ → E →L[ℝ] E) (e : Fin (Module.finrank ℝ E) → ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hR : ContinuousOn R (Icc a b))
    (hG : ∀ p q, ContinuousOn (fun t => chartGramOnE (I := I) g α p q (u t)) (Icc a b))
    (hframe_ode : ∀ i, ∀ t ∈ Icc a b, HasDerivWithinAt (e i)
      (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (e i t) (u t)) (Icc a b) t)
    (hframe_orth : ∀ t ∈ Icc a b, ∀ i j,
      chartMetricInner (I := I) g α (u t) (e i t) (e j t) = if i = j then (1 : ℝ) else 0)
    (J₀ w₀ : E) :
    ∃ f : Fin (Module.finrank ℝ E) → ℝ → ℝ,
      (∑ i, f i a • e i a = J₀) ∧
      (∀ i, HasDerivWithinAt (f i)
        (chartMetricInner (I := I) g α (u a) w₀ (e i a)) (Icc a b) a) ∧
      (∀ t ∈ Ioo a b,
        covariantDerivCoord (I := I) g α u
            (fun r => covariantDerivCoord (I := I) g α u (fun s => ∑ i, f i s • e i s) r) t
          + R t (∑ i, f i t • e i t) = 0) := by
  classical
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  have he : ∀ i, ContinuousOn (e i) (Icc a b) := fun i t ht => (hframe_ode i t ht).continuousWithinAt
  have hAcont : ContinuousOn (jacobiCoefOp (I := I) g α u R e) (Icc a b) :=
    continuousOn_jacobiCoefOp (I := I) g α u R e hR he hG
  -- solve the coefficient ODE with initial data = frame coordinates of `(J₀, w₀)`
  obtain ⟨F, V, hFa, hVa, hFV⟩ :=
    exists_isJacobiPairOn (E := Fin (Module.finrank ℝ E) → ℝ) hab hAcont
      (fun i => chartMetricInner (I := I) g α (u a) J₀ (e i a))
      (fun i => chartMetricInner (I := I) g α (u a) w₀ (e i a))
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := Fintype.card_fin _
  refine ⟨fun i t => F t i, ?_, ?_, ?_⟩
  · -- `J(a) = J₀`
    have horth_a := hframe_orth a ⟨le_rfl, hab⟩
    have hexp := frameExpansion (I := I) g α (u a) (fun i => e i a) hcard horth_a J₀
    have hval : ∀ i, F a i = chartMetricInner (I := I) g α (u a) J₀ (e i a) :=
      fun i => congrFun hFa i
    calc ∑ i, F a i • e i a
        = ∑ i, chartMetricInner (I := I) g α (u a) J₀ (e i a) • e i a :=
          Finset.sum_congr rfl fun i _ => by rw [hval i]
      _ = J₀ := hexp.symm
  · -- initial velocity of the components
    intro i
    have hderiv : HasDerivWithinAt F (V a) (Icc a b) a := hFV.1 a ⟨le_rfl, hab⟩
    have hproj := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivWithinAt a hderiv
    simp only [Function.comp_def, ContinuousLinearMap.proj_apply] at hproj
    have hval : V a i = chartMetricInner (I := I) g α (u a) w₀ (e i a) := congrFun hVa i
    rw [hval] at hproj
    exact hproj
  · -- Jacobi equation on the interior
    intro t₀ ht₀
    have ht₀Icc : t₀ ∈ Icc a b := Ioo_subset_Icc_self ht₀
    have hIoo_nhds : Ioo a b ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ht₀
    -- interior two-sided derivatives of `F`, `V`, `e`
    have hF_at : ∀ r ∈ Ioo a b, HasDerivAt F (V r) r := fun r hr =>
      (hFV.1 r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
    have hV_at : ∀ r ∈ Ioo a b,
        HasDerivAt V (-(jacobiCoefOp (I := I) g α u R e r) (F r)) r := fun r hr =>
      (hFV.2 r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
    have he_at : ∀ i, ∀ r ∈ Ioo a b, HasDerivAt (e i)
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u r) (e i r) (u r)) r :=
      fun i r hr => (hframe_ode i r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
    -- component derivatives: `(fun t => F t i)' = V · i` on the interior
    have hfi_at : ∀ i, ∀ r ∈ Ioo a b, HasDerivAt (fun t => F t i) (V r i) r := fun i r hr => by
      have := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt r (hF_at r hr)
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using this
    have hfi_deriv_eq : ∀ i,
        (deriv fun t => F t i) =ᶠ[𝓝 t₀] (fun r => V r i) :=
      fun i => Filter.eventually_of_mem hIoo_nhds fun r hr => (hfi_at i r hr).deriv
    have hVi_at : ∀ i, HasDerivAt (fun r => V r i)
        (-(jacobiCoefOp (I := I) g α u R e t₀) (F t₀) i) t₀ := fun i => by
      have := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt t₀ (hV_at t₀ ht₀)
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using this
    -- discharge the hypotheses of the frame-reduction expansion
    have hf : ∀ i, ∀ᶠ r in 𝓝 t₀, DifferentiableAt ℝ (fun t => F t i) r := fun i =>
      Filter.eventually_of_mem hIoo_nhds fun r hr => (hfi_at i r hr).differentiableAt
    have hf2 : ∀ i, DifferentiableAt ℝ (deriv fun t => F t i) t₀ := fun i =>
      (hfi_deriv_eq i).differentiableAt_iff.mpr (hVi_at i).differentiableAt
    have hedif : ∀ i, ∀ᶠ r in 𝓝 t₀, DifferentiableAt ℝ (e i) r := fun i =>
      Filter.eventually_of_mem hIoo_nhds fun r hr => (he_at i r hr).differentiableAt
    have hpar : ∀ i, ∀ᶠ r in 𝓝 t₀,
        covariantDerivCoord (I := I) g α u (e i) r = 0 := fun i =>
      Filter.eventually_of_mem hIoo_nhds fun r hr => by
        rw [covariantDerivCoord_def, (he_at i r hr).deriv]; abel
    have horth := hframe_orth t₀ ht₀Icc
    -- second derivative of the `j`-th component from the ODE
    have hf2_val : ∀ j, deriv (deriv fun t => F t j) t₀
        = -∑ i, jacobiCoef (I := I) g α u R e i j t₀ * F t₀ i := fun j => by
      rw [(hfi_deriv_eq j).deriv_eq, (hVi_at j).deriv, jacobiCoefOp_apply]
    rw [covariantDerivCoord2_add_map_frameCombination_expand (I := I) g α u (fun i t => F t i) e
      (R t₀) hf hf2 hedif hpar hcard horth]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hscalar : deriv (deriv fun t => F t j) t₀
        + ∑ i, F t₀ i * chartMetricInner (I := I) g α (u t₀) (R t₀ (e i t₀)) (e j t₀) = 0 := by
      rw [hf2_val j]
      have hswap : ∀ i, F t₀ i * chartMetricInner (I := I) g α (u t₀) (R t₀ (e i t₀)) (e j t₀)
          = jacobiCoef (I := I) g α u R e i j t₀ * F t₀ i := fun i => by rw [jacobiCoef]; ring
      rw [Finset.sum_congr rfl fun i _ => hswap i]
      ring
    rw [hscalar, zero_smul]

/-! ## Uniqueness of the Jacobi field by its initial data -/

/-- **Math.** Uniqueness of the Jacobi field (do Carmo `def:dc-ch5-2-1`). Two Jacobi fields
`J = Σᵢ fᵢ eᵢ` and `J' = Σᵢ gᵢ eᵢ` along the same parallel frame, whose components solve
the scalar system (`IsJacobiPairOn (jacobiCoefOp …)`) and share initial position and
velocity, agree on all of `[a,b]`.  This is do Carmo's *"a Jacobi field is determined by
its initial conditions `J(0)`, `DJ/dt(0)`"* — read through the frame, uniqueness of the
field reduces to uniqueness of the scalar ODE (`IsJacobiPairOn.eqOn`). -/
theorem jacobiField_frame_eqOn (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (R : ℝ → E →L[ℝ] E) (e : ι → ℝ → E) {a b : ℝ}
    (hR : ContinuousOn R (Icc a b)) (he : ∀ i, ContinuousOn (e i) (Icc a b))
    (hG : ∀ p q, ContinuousOn (fun t => chartGramOnE (I := I) g α p q (u t)) (Icc a b))
    {F V G W : ℝ → ι → ℝ}
    (hFV : IsJacobiPairOn (jacobiCoefOp (I := I) g α u R e) a b F V)
    (hGW : IsJacobiPairOn (jacobiCoefOp (I := I) g α u R e) a b G W)
    (h0 : F a = G a) (h0' : V a = W a) :
    Set.EqOn (fun t => ∑ i, F t i • e i t) (fun t => ∑ i, G t i • e i t) (Icc a b) := by
  have hAcont : ContinuousOn (jacobiCoefOp (I := I) g α u R e) (Icc a b) :=
    continuousOn_jacobiCoefOp (I := I) g α u R e hR he hG
  obtain ⟨hFG, _⟩ := hFV.eqOn hAcont hGW h0 h0'
  intro t ht
  exact Finset.sum_congr rfl fun i _ => by rw [hFG ht]

end Riemannian.Jacobi
