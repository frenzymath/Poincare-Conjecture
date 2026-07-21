import PetersenLib.Ch06.JacobiFields
import PetersenLib.Ch06.CurvatureChartBridgeMoving
import PetersenLib.Ch02.FrameDecomposition
import PetersenLib.Ch03.DistanceFunctions
import PetersenLib.Ch05.DistanceRigidity
import PetersenLib.Ch01.ArcLength

/-!
# Petersen Ch. 6, §6.1 — the along-curve ↔ global Levi-Civita covariant-derivative bridge

`PetersenLib` carries two covariant derivatives of a vector field along a curve `c`, so far
kept apart:

* the **along-curve** derivative `derivAlongCurve g c V` of `Ch06/ConnectionAlongCurve.lean`,
  read coordinate-wise in the canonical chart at the moving foot `c t`
  (`V̇ᵏ + Vⁱ ċʲ Γᵏ_{ij}`);
* the **global** Levi-Civita covariant derivative `(g.leviCivita).cov p v W` of Ch. 2, for a
  globally smooth field `W : Π x, TangentSpace I x`.

This file identifies them.  The crown-jewel lemma
`derivAlongCurve_eq_leviCivita_cov` says that for a *global* smooth field `W`, restricting `W`
along `c` and taking the along-curve derivative reproduces the abstract Levi-Civita
derivative in the velocity direction:

`derivAlongCurve g c (fun τ ↦ W (c τ)) t = (g.leviCivita).cov (c t) (ċ(t)) W`.

## The proof

Everything is set in the **single chart at the moving foot** `α = c t`, so no inter-chart
transport is needed at the base point.  The frame `Z` of
`exists_chartFrame_leviCivita_christoffel_nhds` realises the chart frame `∂_a` on an open
`U ∋ c t` and there carries the chart Christoffel formula for `∇`.

* **Field slot.** `W = Σ_a W^a ∂_a` on `U` with the *smooth* coordinate functions
  `W^a = chartVectorFieldCoeff (c t) W a` (`Ch02/FrameDecomposition.lean`).  Bump-extending
  each to a global smooth scalar `γ_a` and replacing `W` by `Σ_a γ_a Z_a` near `c t`
  (`connection_local_openSet`), the field-slot Leibniz rule
  `AffineConnection.cov_finsetSum_smul_field` expands `∇_{ċ} W` into a derivative term
  `Σ_a (∂_{ċ}γ_a) Z_a` and a Christoffel term `Σ_a γ_a ∇_{ċ} Z_a`.
* **Direction slot.** `ċ = Σ_i ċ^i Z_i(c t)`
  (`sum_chartCoord_smul_chartBasisVecFiber_self`), so `∇_{ċ} Z_a = Σ_i ċ^i ∇_{Z_i} Z_a`
  (`AffineConnection.cov_finsetSum_smul_direction`) and the chart Christoffel formula fires
  (`hZchr`).
* **Derivative term.** The along-curve derivative's coordinate part
  `deriv (chartFieldRep c (c t) (W∘c))` is, near `t`, the derivative of
  `τ ↦ Σ_a γ_a(c τ) e_a`; each `∂_{ċ}γ_a` is the manifold directional derivative
  `dirTangent γ_a ċ` (`hasDerivAt_comp_curve`, via `velocity_comp`), the *same* coefficient
  produced by the field-slot expansion.
* Matching the two Christoffel double sums is `Finset` bookkeeping (`Finset.sum_comm`, `ring`).

## Petersen's Hessian remark

`jacobiField_hess_r` is `rem:pet-ch6-jacobi-hessian-r`: for a unit-speed geodesic `c` with
`ċ = ∇r` (Petersen's radial hypothesis) and a §3.2.4 Jacobi field `J` of `r`
(`L_{∇r}J = 0`), the bridge turns `Ch03/DistanceFunctions.lean`'s
`jacobiField_hessian_metricInner` into `Hess r(J, J) = g(J̇, J)`.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ### Small reusable pieces -/

/-- **Eng.** Linearity of `∇_v X` over a finite sum in the **direction** slot:
`∇_{Σ_i a_i v_i} X = Σ_i a_i ∇_{v_i} X`.  The direction analogue of
`AffineConnection.cov_finsetSum_smul_field`, from `add_direction`/`smul_direction`. -/
theorem AffineConnection.cov_finsetSum_smul_direction (D : AffineConnection I M) (p : M)
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (v : ι → TangentSpace I p)
    (X : Π x : M, TangentSpace I x) :
    D.cov p (∑ i ∈ s, a i • v i) X = ∑ i ∈ s, a i • D.cov p (v i) X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [D.cov_zero_direction]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, D.add_direction, D.smul_direction, ih, Finset.sum_insert hi]

/-- **Math.** On a normed space over itself, the manifold velocity `ċ = dc_t(1)` of a curve
into `M` read in the chart at the foot `c t` is Ch. 6's `curveVelocity`.  Both are the
derivative of the chart reading of `c`; `hasDerivAt_extChartAt_comp_of_hasMFDerivAt` at the
foot chart, with the self-transport collapsing by `tangentCoordChange_self`. -/
theorem velocity_eq_curveVelocity {c : ℝ → M} {t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    velocity (I := I) c t = curveVelocity (I := I) c t := by
  have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) I c t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (velocity (I := I) c t)) :=
    hasMFDerivAt_smulRight_velocity (I := I) hc
  have hsrc : c t ∈ (extChartAt I (c t)).source := mem_extChartAt_source (I := I) (c t)
  have hd := hasDerivAt_extChartAt_comp_of_hasMFDerivAt (p := c t) hmf hsrc
  rw [tangentCoordChange_self hsrc] at hd
  have hcurve : curveVelocity (I := I) c t = deriv (↑(extChartAt I (c t)) ∘ c) t := by
    rw [curveVelocity_def]; rfl
  rw [hcurve, hd.deriv]

/-- **Eng.** Chain rule for a *scalar* function along a curve: for `γ : M → ℝ` differentiable
at `c t` and `c` differentiable at `t`, `τ ↦ γ(c τ)` has derivative the manifold directional
derivative `dirTangent γ (ċ)`.  `velocity_comp` in the target `ℝ`, read as an ordinary
derivative by `velocity_eq_deriv`. -/
theorem hasDerivAt_comp_curve {γ : M → ℝ} {c : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt I 𝓘(ℝ, ℝ) γ (c t)) (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    HasDerivAt (fun τ => γ (c τ)) (dirTangent γ (velocity (I := I) c t)) t := by
  have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ => γ (c τ)) t := hγ.comp t hc
  have hdiff : DifferentiableAt ℝ (fun τ => γ (c τ)) t := hcomp.differentiableAt
  have hval : deriv (fun τ => γ (c τ)) t = dirTangent γ (velocity (I := I) c t) := by
    have h := velocity_comp (I := I) (f := γ) t hγ hc
    rw [velocity_eq_deriv] at h
    exact h
  rw [← hval]
  exact hdiff.hasDerivAt

/-- **Eng.** The chart-frame coordinate of a field at the **centre of its own chart** is the
model-basis coordinate: `chartVectorFieldCoeff α W a α = chartCoord a (W α)`.  Both express
`W α` over the model basis `chartBasisVecFiber α · α = e·` (`chartBasisVecFiber_self`);
uniqueness of basis coordinates. -/
theorem chartVectorFieldCoeff_self (α : M) (W : Π x : M, TangentSpace I x)
    (a : Fin (Module.finrank ℝ E)) :
    chartVectorFieldCoeff (I := I) α W a α = Geodesic.chartCoord (E := E) a (W α) := by
  classical
  have hbase : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' α
  have h := vectorField_eq_sum_chartCoeff (I := I) α W hbase
  simp only [Tensor.chartBasisVecFiber_self] at h
  rw [Geodesic.chartCoord_def]
  have h2 : W α = (Module.finBasis ℝ E).equivFun.symm
      (fun b => chartVectorFieldCoeff (I := I) α W b α) := by
    rw [h]; exact (Module.Basis.equivFun_symm_apply _ _).symm
  have h3 : (Module.finBasis ℝ E).equivFun (W α)
      = fun b => chartVectorFieldCoeff (I := I) α W b α := by
    rw [h2, LinearEquiv.apply_symm_apply]
  have h4 := congrFun h3 a
  rw [Module.Basis.equivFun_apply] at h4
  exact h4.symm

/-! ### The bridge -/

/-- **Math.** Petersen §6.1 — **the along-curve derivative is the global Levi-Civita
covariant derivative in the velocity direction**.  For a globally smooth vector field
`W : Π x, TangentSpace I x`, restricting `W` to a curve `c` (differentiable at `t`) and taking
the along-curve covariant derivative reproduces the abstract Ch. 2 Levi-Civita derivative of
`W` in the velocity direction `ċ(t)`:

`derivAlongCurve g c (fun τ ↦ W (c τ)) t = (g.leviCivita).cov (c t) (ċ(t)) W`.

This is the reusable bridge between Ch. 6's coordinate along-curve calculus and Ch. 2's
Koszul connection.  See the module docstring for the frame-decomposition proof. -/
theorem derivAlongCurve_eq_leviCivita_cov (g : RiemannianMetric I M) {c : ℝ → M}
    {W : Π x : M, TangentSpace I x} (hW : IsSmoothVectorField W) {t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    derivAlongCurve (I := I) g c (fun τ => W (c τ)) t
      = (g.leviCivita).cov (c t) (curveVelocity (I := I) c t) W := by
  classical
  -- velocity identification
  have hvel : velocity (I := I) c t = curveVelocity (I := I) c t := velocity_eq_curveVelocity hc
  -- the frame at α = p = c t
  obtain ⟨Z, U, hUopen, hpU, hUsub, hZframe, hZchr⟩ :=
    exists_chartFrame_leviCivita_christoffel_nhds (I := I) g
      (α := c t) (p := c t) (mem_chart_source H (c t))
  -- the smooth chart-frame coordinate functions of `W`, and their bump-extensions
  set f : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun a => chartVectorFieldCoeff (I := I) (c t) W a with hf
  have hBopen : IsOpen (trivializationAt E (TangentSpace I) (c t)).baseSet :=
    (trivializationAt E (TangentSpace I) (c t)).open_baseSet
  have hctB : c t ∈ (trivializationAt E (TangentSpace I) (c t)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (c t)
  have hf_smooth : ∀ a, ContMDiffOn I 𝓘(ℝ) ∞ (f a)
      (trivializationAt E (TangentSpace I) (c t)).baseSet :=
    fun a => chartVectorFieldCoeff_contMDiffOn (I := I) (c t) hW a
  choose γ hγsmooth hγev using fun a =>
    exists_contMDiff_eventuallyEq (I := I) hBopen (hf_smooth a) hctB
  -- the extended field `W' = Σ_a γ_a Z_a`, smooth, and equal to `W` near `c t`
  set W' : Π x : M, TangentSpace I x := fun q => ∑ a, γ a q • (⇑(Z a) q) with hW'def
  have hterm : ∀ a, IsSmoothVectorField (fun q => γ a q • (⇑(Z a) q)) := fun a => by
    simpa using (SmoothVectorField.smul (γ a) (hγsmooth a) (Z a)).smooth
  have hW' : IsSmoothVectorField W' := isSmoothVectorField_finsetSum Finset.univ _ hterm
  obtain ⟨V, hVsub, hVopen, hctV⟩ := eventually_nhds_iff.mp
    ((eventually_all.mpr (fun a => hγev a)).and
      ((hUopen.eventually_mem hpU).and (hBopen.eventually_mem hctB)))
  have hEqOn : Set.EqOn W W' V := by
    intro q hq
    obtain ⟨hγq, hqU, hqB⟩ := hVsub q hq
    show W q = ∑ a, γ a q • (⇑(Z a) q)
    rw [vectorField_eq_sum_chartCoeff (I := I) (c t) W hqB]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hγq a, hZframe a q hqU]
  -- values at the foot
  have hZct : ∀ a, (⇑(Z a) (c t) : E) = (Module.finBasis ℝ E a : E) := fun a => by
    rw [hZframe a (c t) hpU, Tensor.chartBasisVecFiber_self]
  have hγct : ∀ a, γ a (c t) = Geodesic.chartCoord (E := E) a (W (c t)) := fun a => by
    rw [(hγev a).self_of_nhds]
    exact chartVectorFieldCoeff_self (I := I) (c t) W a
  -- the transport of the chart frame into the chart-`c t` reading is the model basis
  have htrans : ∀ q ∈ (chartAt H (c t)).source, ∀ a,
      tangentCoordChange I q (c t) q (chartBasisVecFiber (I := I) (c t) a q)
        = (Module.finBasis ℝ E a : E) := by
    intro q hq a
    have hq_ct : q ∈ (extChartAt I (c t)).source := by rw [extChartAt_source]; exact hq
    have hq_q : q ∈ (extChartAt I q).source := mem_extChartAt_source (I := I) q
    rw [Tensor.chartBasisVecFiber_eq_tangentCoordChange (I := I) (c t) hq a,
      tangentCoordChange_comp (I := I) (w := c t) (x := q) (y := c t) (z := q)
        ⟨⟨hq_ct, hq_q⟩, hq_ct⟩,
      tangentCoordChange_self hq_ct]
  -- direction decomposition of the velocity into the frame
  have hvel_decomp : curveVelocity (I := I) c t
      = ∑ i, Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t) • (⇑(Z i) (c t)) := by
    conv_lhs =>
      rw [← sum_chartCoord_smul_chartBasisVecFiber_self (I := I) (c t) (curveVelocity (I := I) c t)]
    exact Finset.sum_congr rfl fun i _ => by rw [hZframe i (c t) hpU]
  -- `∇_{ċ} Z_a = Σ_i ċ^i Σ_m Γ_{ia}^m e_m`
  have hcovZ : ∀ a, (g.leviCivita).cov (c t) (curveVelocity (I := I) c t) (⇑(Z a))
      = ∑ i, Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t)
          • ∑ m, chartChristoffel (I := I) g (c t) i a m (extChartAt I (c t) (c t))
              • (Module.finBasis ℝ E m : E) := by
    intro a
    conv_lhs => rw [hvel_decomp]
    rw [AffineConnection.cov_finsetSum_smul_direction]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hZchr i a (c t) hpU]
    exact Finset.sum_congr rfl fun m _ => by rw [hZct m]
  -- LHS derivative term: `deriv (chartFieldRep …) = Σ_a (dirTangent γ_a ċ) e_a`
  have hFrep_ev : chartFieldRep (I := I) c (c t) (fun τ => W (c τ))
      =ᶠ[𝓝 t] fun τ => ∑ a, γ a (c τ) • (Module.finBasis ℝ E a : E) := by
    have hcont : ContinuousAt c t := hc.continuousAt
    have hev : ∀ᶠ τ in 𝓝 t, (∀ a, γ a (c τ) = f a (c τ)) ∧ c τ ∈ U ∧
        c τ ∈ (trivializationAt E (TangentSpace I) (c t)).baseSet := by
      have h1 : ∀ᶠ τ in 𝓝 t, ∀ a, γ a (c τ) = f a (c τ) :=
        hcont.eventually (eventually_all.mpr (fun a => hγev a))
      have h2 : ∀ᶠ τ in 𝓝 t, c τ ∈ U := hcont.eventually_mem (hUopen.mem_nhds hpU)
      have h3 : ∀ᶠ τ in 𝓝 t, c τ ∈ (trivializationAt E (TangentSpace I) (c t)).baseSet :=
        hcont.eventually_mem (hBopen.mem_nhds hctB)
      filter_upwards [h1, h2, h3] with τ hτ1 hτ2 hτ3 using ⟨hτ1, hτ2, hτ3⟩
    filter_upwards [hev] with τ hτ
    obtain ⟨hγτ, hτU, hτB⟩ := hτ
    have hτsrc : c τ ∈ (chartAt H (c t)).source := hUsub hτU
    show tangentCoordChange I (c τ) (c t) (c τ) (W (c τ))
        = ∑ a, γ a (c τ) • (Module.finBasis ℝ E a : E)
    rw [vectorField_eq_sum_chartCoeff (I := I) (c t) W hτB, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, htrans (c τ) hτsrc a, hγτ a]
  have hderiv_lhs : deriv (chartFieldRep (I := I) c (c t) (fun τ => W (c τ))) t
      = ∑ a, dirTangent (γ a) (curveVelocity (I := I) c t) • (Module.finBasis ℝ E a : E) := by
    have hHDcomp : ∀ a, HasDerivAt (fun τ => γ a (c τ))
        (dirTangent (γ a) (curveVelocity (I := I) c t)) t := by
      intro a
      have h := hasDerivAt_comp_curve (I := I) ((hγsmooth a).mdifferentiableAt (by simp)) hc
      rwa [hvel] at h
    have hHD : HasDerivAt (fun τ => ∑ a, γ a (c τ) • (Module.finBasis ℝ E a : E))
        (∑ a, dirTangent (γ a) (curveVelocity (I := I) c t) • (Module.finBasis ℝ E a : E)) t :=
      HasDerivAt.fun_sum (fun a _ => (hHDcomp a).smul_const (Module.finBasis ℝ E a : E))
    exact (hHD.congr_of_eventuallyEq hFrep_ev).deriv
  -- assemble the LHS
  have hL : derivAlongCurve (I := I) g c (fun τ => W (c τ)) t
      = (∑ a, dirTangent (γ a) (curveVelocity (I := I) c t) • (Module.finBasis ℝ E a : E))
        + ∑ m, (∑ i, ∑ j, chartChristoffel (I := I) g (c t) i j m (extChartAt I (c t) (c t))
            * Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t)
            * Geodesic.chartCoord (E := E) j (W (c t))) • (Module.finBasis ℝ E m : E) := by
    rw [derivAlongCurve_def, hderiv_lhs]
    congr 1
  -- assemble the RHS
  have hR : (g.leviCivita).cov (c t) (curveVelocity (I := I) c t) W
      = (∑ a, dirTangent (γ a) (curveVelocity (I := I) c t) • (Module.finBasis ℝ E a : E))
        + ∑ m, (∑ i, ∑ j, chartChristoffel (I := I) g (c t) i j m (extChartAt I (c t) (c t))
            * Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t)
            * Geodesic.chartCoord (E := E) j (W (c t))) • (Module.finBasis ℝ E m : E) := by
    have hcov_eq : (g.leviCivita).cov (c t) (curveVelocity (I := I) c t) W
        = (g.leviCivita).cov (c t) (curveVelocity (I := I) c t) W' :=
      connection_local_openSet (g.leviCivita).toAffineConnection (curveVelocity (I := I) c t)
        hW hW' hVopen hctV hEqOn
    rw [hcov_eq,
      show W' = fun q => ∑ a ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        γ a q • (⇑(Z a) q) from rfl,
      AffineConnection.cov_finsetSum_smul_field (g.leviCivita).toAffineConnection (c t)
        (curveVelocity (I := I) c t) Finset.univ γ (fun a => ⇑(Z a))
        hγsmooth (fun a => (Z a).smooth)]
    -- substitute the per-term values
    have hstep : ∀ a, dirTangent (γ a) (curveVelocity (I := I) c t) • (⇑(Z a) (c t))
          + γ a (c t) • (g.leviCivita).cov (c t) (curveVelocity (I := I) c t) (⇑(Z a))
        = dirTangent (γ a) (curveVelocity (I := I) c t) • (Module.finBasis ℝ E a : E)
          + Geodesic.chartCoord (E := E) a (W (c t))
              • ∑ i, Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t)
                  • ∑ m, chartChristoffel (I := I) g (c t) i a m (extChartAt I (c t) (c t))
                      • (Module.finBasis ℝ E m : E) := by
      intro a
      rw [hZct a, hγct a, hcovZ a]
    rw [Finset.sum_congr rfl (fun a _ => hstep a), Finset.sum_add_distrib]
    congr 1
    -- Christoffel double-sum bookkeeping
    have hB : ∀ a, (∑ i, Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t)
          • ∑ m, chartChristoffel (I := I) g (c t) i a m (extChartAt I (c t) (c t))
              • (Module.finBasis ℝ E m : E))
        = ∑ m, (∑ i, Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t)
            * chartChristoffel (I := I) g (c t) i a m (extChartAt I (c t) (c t)))
          • (Module.finBasis ℝ E m : E) := by
      intro a
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => (Finset.sum_smul).symm
    calc ∑ a, Geodesic.chartCoord (E := E) a (W (c t))
            • ∑ i, Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t)
                • ∑ m, chartChristoffel (I := I) g (c t) i a m (extChartAt I (c t) (c t))
                    • (Module.finBasis ℝ E m : E)
        = ∑ a, ∑ m, (Geodesic.chartCoord (E := E) a (W (c t))
              * ∑ i, Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t)
                  * chartChristoffel (I := I) g (c t) i a m (extChartAt I (c t) (c t)))
            • (Module.finBasis ℝ E m : E) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hB a, Finset.smul_sum]
          exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
      _ = ∑ m, (∑ a, Geodesic.chartCoord (E := E) a (W (c t))
              * ∑ i, Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t)
                  * chartChristoffel (I := I) g (c t) i a m (extChartAt I (c t) (c t)))
            • (Module.finBasis ℝ E m : E) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun m _ => (Finset.sum_smul).symm
      _ = ∑ m, (∑ i, ∑ j, chartChristoffel (I := I) g (c t) i j m (extChartAt I (c t) (c t))
              * Geodesic.chartCoord (E := E) i (curveVelocity (I := I) c t)
              * Geodesic.chartCoord (E := E) j (W (c t))) • (Module.finBasis ℝ E m : E) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          congr 1
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
          ring
  rw [hL, hR]

/-! ### Petersen's Hessian remark -/

/-- **Math.** Petersen §6.1 (p. 255), `rem:pet-ch6-jacobi-hessian-r`.  For a unit-speed
geodesic `c` with `c 0 = p`, writing `r(x) = |xp|`, and a Jacobi field `J` of `r` along `c`
(with `J(0) = 0`, realised by a geodesic variation), as long as `t c'(0)` lies in the
interior of the domain on which `r` is smooth — so that Petersen's **radial condition**
`ċ(t) = ∇r|_{c(t)}` holds — one has

`Hess r(J(t), J(t)) = g(∇_{J(t)} ∇r, J(t)) = g(J̇(t), J(t))`.

The first equality is `Ch03/DistanceFunctions.lean`'s `jacobiField_hessian_metricInner`; the
second is `derivAlongCurve_eq_leviCivita_cov` at `W = J`, feeding the radial condition
`ċ = ∇r` so that `∇_{∇r} J = J̇`.

**Eng.** `J` is taken in the §3.2.4 distance-function sense
(`lieDerivativeVectorField I (∇r) J (c t) = 0`, i.e. `L_{∇r}J = 0`), which is exactly the
condition making `g(∇_J ∇r, J) = g(∇_{∇r} J, J)` (torsion-freeness + shape-operator
symmetry); for a geodesic variation with `J(0) = 0` this is the standard variation-field
fact.  The radial condition `ċ = ∇r` and the smoothness of `r` are carried as Petersen's
stated hypotheses, matching the honest scoping of the sibling `jacobiField_dexp_relation`. -/
theorem jacobiField_hess_r (g : RiemannianMetric I M) {c : ℝ → M} {r : M → ℝ}
    {J : Π x : M, TangentSpace I x} {t : ℝ}
    (hr : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r)) (hJ : IsSmoothVectorField J)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hradial : curveVelocity (I := I) c t = gradient g r (c t))
    (hJacobi : lieDerivativeVectorField I (gradient g r) J (c t) = 0) :
    hessianLieDerivative g r ![J, J] (c t)
      = g.metricInner (c t)
          (derivAlongCurve (I := I) g c (fun τ => J (c τ)) t) (J (c t)) := by
  rw [derivAlongCurve_eq_leviCivita_cov g hJ hc, hradial]
  exact (jacobiField_hessian_metricInner g.leviCivita hr hgradr hJ (c t) hJacobi).1

end PetersenLib

end
