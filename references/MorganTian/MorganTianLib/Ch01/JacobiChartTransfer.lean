import MorganTianLib.Ch01.JacobiManifold
import DoCarmoLib.Riemannian.Connection.ChartChristoffelChange

/-!
# Poincaré Ch. 1, §1.4 — chart-change covariance of the Jacobi pair system

The chart Jacobi pair system `IsJacobiFieldOn` is a *coordinate* expression of
the intrinsic Jacobi equation `∇_X∇_X J + ℛ(J, X)X = 0`; this file proves it
transforms covariantly under a change of chart, so that a chart certificate in
one chart can be transported to any other chart containing the same piece of
the geodesic. This closes the chart-coherence gap that blocked manifold-level
Jacobi-field *existence* (`IsJacobiFieldAlongOn` was designed chart-locally
precisely because this transfer was missing): gluing chart solutions along a
geodesic needs certificates to move between overlapping charts.

Main results:

* `chartFrameSum_eq_tangentCoordChange` — the chart-frame realization
  `∑_a v^a X_a(x)` of coordinates `v` in the chart at `α` is the tangent
  vector `tangentCoordChange I α x x v` (the vector at `x` whose chart-`α`
  reading is `v`);
* `chartMetricInner_coordChange` — the chart Gram pairing is invariant under
  the tangent coordinate change between two charts at a common foot;
* `chartCurvature_coordChange` — **equivariance of the chart curvature**:
  `ℛ_β(Cv, Cw)Cz = C(ℛ_α(v, w)z)` for `C = tangentCoordChange I α β x`,
  obtained by evaluating the manifold ↔ chart curvature bridge
  (`curvatureFormAt_chartFrame`) in both charts against the same intrinsic
  realizations and using positive-definiteness of the chart Gram form —
  no differentiation of the Christoffel transformation law is needed;
* `IsJacobiFieldOn.transfer` — **the chart-change theorem for the Jacobi
  pair system**: along a geodesic lying in the sources of two charts, the
  chart-`α` certificate for `(J, ∇J)` yields the chart-`β` certificate. The
  inhomogeneous second-derivative terms of the transition map produced by
  the product rule cancel against the transformation law of the Christoffel
  contraction (`Riemannian.chartChristoffelContraction_change`), and the
  curvature term transforms by `chartCurvature_coordChange`.

Blueprint: `lem:jacobi-field-coordinates`,
`lem:exponential-differential-jacobi` (existence of `Y_Z`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Riemannian.Tensor Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Composition identities for tangent coordinate changes -/

/-- **Math.** Reading the realization `tangentCoordChange I α x x v` of the
chart-`α` coordinates `v` back into the chart at `β` composes the coordinate
changes: the result is `tangentCoordChange I α β x v`. -/
theorem tangentCoordChange_realize {α β x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (v : E) :
    tangentCoordChange I x β x (tangentCoordChange I α x x v)
      = tangentCoordChange I α β x v :=
  tangentCoordChange_comp (I := I)
    ⟨⟨by rw [extChartAt_source]; exact hxα,
      mem_extChartAt_source (I := I) x⟩,
      by rw [extChartAt_source]; exact hxβ⟩

/-- **Math.** Realizing chart-`α` coordinates at `x` and reading them back in
the chart at `α` is the identity. -/
theorem tangentCoordChange_realize_self {α x : M}
    (hxα : x ∈ (chartAt H α).source) (v : E) :
    tangentCoordChange I x α x (tangentCoordChange I α x x v) = v := by
  rw [tangentCoordChange_realize (I := I) hxα hxα v]
  exact tangentCoordChange_self (I := I)
    (by rw [extChartAt_source]; exact hxα)

/-- **Math.** Realization commutes with the coordinate change: the tangent
vector at `x` realizing the chart-`β` coordinates
`tangentCoordChange I α β x v` is the one realizing the chart-`α`
coordinates `v`. -/
theorem tangentCoordChange_realize_comp {α β x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (v : E) :
    tangentCoordChange I β x x (tangentCoordChange I α β x v)
      = tangentCoordChange I α x x v :=
  tangentCoordChange_comp (I := I)
    ⟨⟨by rw [extChartAt_source]; exact hxα,
      by rw [extChartAt_source]; exact hxβ⟩,
      mem_extChartAt_source (I := I) x⟩

/-- **Math.** The tangent coordinate change from `α` to `β` at a common foot
is inverted by the one from `β` to `α`. -/
theorem tangentCoordChange_left_inv {α β x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (v : E) :
    tangentCoordChange I β α x (tangentCoordChange I α β x v) = v := by
  have h : tangentCoordChange I β α x (tangentCoordChange I α β x v)
      = tangentCoordChange I α α x v :=
    tangentCoordChange_comp (I := I)
      ⟨⟨by rw [extChartAt_source]; exact hxα,
        by rw [extChartAt_source]; exact hxβ⟩,
        by rw [extChartAt_source]; exact hxα⟩
  rw [h]
  exact tangentCoordChange_self (I := I)
    (by rw [extChartAt_source]; exact hxα)

/-! ### Realizations of chart coordinates as tangent vectors -/

/-- **Math.** The chart-frame realization `∑_a v^a X_a(x)` of a coordinate
vector `v : E` in the chart at `α` is the tangent vector at `x` whose
chart-`α` reading is `v`, namely `tangentCoordChange I α x x v`. -/
theorem chartFrameSum_eq_tangentCoordChange {α x : M}
    (hx : x ∈ (chartAt H α).source) (v : E) :
    (∑ a, Geodesic.chartCoord (E := E) a v
        • chartBasisVecFiber (I := I) α a x)
      = (tangentCoordChange I α x x v : TangentSpace I x) := by
  have hb : ∀ a, chartBasisVecFiber (I := I) α a x
      = (tangentCoordChange I α x x (Module.finBasis ℝ E a) :
          TangentSpace I x) := by
    intro a
    rw [chartBasisVecFiber_eq_symm_tangentCoordChange (I := I) x α
      (mem_chart_source H x) hx a,
      trivializationAt_symm_eq_tangentCoordChange (I := I) x
        (mem_chart_source H x)]
    exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) x)
  have hsum : (∑ a, Geodesic.chartCoord (E := E) a v
        • chartBasisVecFiber (I := I) α a x)
      = (∑ a, (tangentCoordChange I α x x
          (Geodesic.chartCoord (E := E) a v • Module.finBasis ℝ E a) :
            TangentSpace I x)) :=
    Finset.sum_congr rfl fun a _ => by
      rw [hb a]
      exact (map_smul (tangentCoordChange I α x x) _ _).symm
  have hlin : (∑ a, (tangentCoordChange I α x x
        (Geodesic.chartCoord (E := E) a v • Module.finBasis ℝ E a) :
          TangentSpace I x))
      = (tangentCoordChange I α x x
          (∑ a, Geodesic.chartCoord (E := E) a v • Module.finBasis ℝ E a) :
            TangentSpace I x) :=
    (map_sum (tangentCoordChange I α x x) _ Finset.univ).symm
  have hrepr : (∑ a, Geodesic.chartCoord (E := E) a v • Module.finBasis ℝ E a)
      = v := by
    simp only [Geodesic.chartCoord_def]
    exact (Module.finBasis ℝ E).sum_repr v
  rw [hsum, hlin, hrepr]

/-! ### Invariance of the chart Gram pairing -/

/-- **Math.** The chart Gram pairing is invariant under the tangent
coordinate change between two charts at a common foot: both sides compute
the intrinsic metric pairing of the realized tangent vectors. -/
theorem chartMetricInner_coordChange (g : RiemannianMetric I M) {α β x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (v w : E) :
    chartMetricInner (I := I) g β (extChartAt I β x)
        (tangentCoordChange I α β x v) (tangentCoordChange I α β x w)
      = chartMetricInner (I := I) g α (extChartAt I α x) v w := by
  have hβ := chartMetricInner_tangentCoordChange (I := I) g hxβ
    ((tangentCoordChange I α x x v : TangentSpace I x))
    ((tangentCoordChange I α x x w : TangentSpace I x))
  have hα := chartMetricInner_tangentCoordChange (I := I) g hxα
    ((tangentCoordChange I α x x v : TangentSpace I x))
    ((tangentCoordChange I α x x w : TangentSpace I x))
  rw [tangentCoordChange_realize (I := I) hxα hxβ v,
    tangentCoordChange_realize (I := I) hxα hxβ w] at hβ
  rw [tangentCoordChange_realize_self (I := I) hxα v,
    tangentCoordChange_realize_self (I := I) hxα w] at hα
  rw [hβ, hα]

/-! ### Equivariance of the chart curvature -/

section Curvature

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Equivariance of the chart curvature under change of chart.**
For a common foot `x` of the charts at `α` and `β` and
`C = tangentCoordChange I α β x`,
`ℛ_β(Cv, Cw)Cz = C(ℛ_α(v, w)z)` at the respective chart images of `x`.
Both sides pair, in the respective chart Gram forms, to the same intrinsic
curvature tensor `curvatureFormAt` evaluated on the same realized tangent
vectors (`curvatureFormAt_chartFrame` in each chart); positive-definiteness
of the chart Gram form then forces equality. -/
theorem chartCurvature_coordChange (g : RiemannianMetric I M) {α β x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (v w z : E) :
    chartCurvature (I := I) g β (extChartAt I β x)
        (tangentCoordChange I α β x v) (tangentCoordChange I α β x w)
        (tangentCoordChange I α β x z)
      = tangentCoordChange I α β x
          (chartCurvature (I := I) g α (extChartAt I α x) v w z) := by
  classical
  -- the two sides pair equally against every β-coordinate test vector
  have hpair : ∀ t : E,
      chartMetricInner (I := I) g β (extChartAt I β x)
          (chartCurvature (I := I) g β (extChartAt I β x)
            (tangentCoordChange I α β x v) (tangentCoordChange I α β x w)
            (tangentCoordChange I α β x z))
          (tangentCoordChange I α β x t)
        = chartMetricInner (I := I) g β (extChartAt I β x)
            (tangentCoordChange I α β x
              (chartCurvature (I := I) g α (extChartAt I α x) v w z))
            (tangentCoordChange I α β x t) := by
    intro t
    have hreal : ∀ e : E,
        (∑ a, Geodesic.chartCoord (E := E) a (tangentCoordChange I α β x e)
            • chartBasisVecFiber (I := I) β a x)
          = ∑ a, Geodesic.chartCoord (E := E) a e
              • chartBasisVecFiber (I := I) α a x := by
      intro e
      rw [chartFrameSum_eq_tangentCoordChange (I := I) hxβ,
        chartFrameSum_eq_tangentCoordChange (I := I) hxα]
      exact tangentCoordChange_realize_comp (I := I) hxα hxβ e
    have hα := curvatureFormAt_chartFrame (I := I) g hxα v w z t
    have hβ := curvatureFormAt_chartFrame (I := I) g hxβ
      (tangentCoordChange I α β x v) (tangentCoordChange I α β x w)
      (tangentCoordChange I α β x z) (tangentCoordChange I α β x t)
    rw [hreal v, hreal w, hreal z, hreal t] at hβ
    have hval : chartMetricInner (I := I) g α (extChartAt I α x)
        (chartCurvature (I := I) g α (extChartAt I α x) v w z) t
        = chartMetricInner (I := I) g β (extChartAt I β x)
            (chartCurvature (I := I) g β (extChartAt I β x)
              (tangentCoordChange I α β x v) (tangentCoordChange I α β x w)
              (tangentCoordChange I α β x z))
            (tangentCoordChange I α β x t) :=
      neg_injective (hα.symm.trans hβ)
    rw [← hval, chartMetricInner_coordChange (I := I) g hxα hxβ
      (chartCurvature (I := I) g α (extChartAt I α x) v w z) t]
  -- specialize to the β-reading of the difference and use definiteness
  set d₁ : E := chartCurvature (I := I) g β (extChartAt I β x)
    (tangentCoordChange I α β x v) (tangentCoordChange I α β x w)
    (tangentCoordChange I α β x z) with hd₁
  set d₂ : E := tangentCoordChange I α β x
    (chartCurvature (I := I) g α (extChartAt I α x) v w z) with hd₂
  by_contra hne
  have hne' : d₁ - d₂ ≠ 0 := sub_ne_zero.2 hne
  have hbase : (extChartAt I β).symm (extChartAt I β x)
      ∈ (trivializationAt E (TangentSpace I) β).baseSet :=
    symm_extChartAt_mem_baseSet (I := I) hxβ
  have hposd : 0 < chartMetricInner (I := I) g β (extChartAt I β x)
      (d₁ - d₂) (d₁ - d₂) :=
    chartMetricInner_pos (I := I) g β hbase hne'
  -- express the test vector `d₁ - d₂` as a coordinate change of some `t`
  have hp := hpair (tangentCoordChange I β α x (d₁ - d₂))
  rw [tangentCoordChange_left_inv (I := I) hxβ hxα (d₁ - d₂)] at hp
  -- ⟨d₁, e⟩ = ⟨d₂, e⟩ for e = d₁ - d₂ forces ⟨d₁ - d₂, d₁ - d₂⟩ = 0
  have hzero : chartMetricInner (I := I) g β (extChartAt I β x)
      (d₁ - d₂) (d₁ - d₂) = 0 := by
    have hrw : d₁ - d₂ = d₁ + -d₂ := by abel
    have hadd : chartMetricInner (I := I) g β (extChartAt I β x)
        (d₁ + -d₂) (d₁ - d₂)
        = chartMetricInner (I := I) g β (extChartAt I β x) d₁ (d₁ - d₂)
          + chartMetricInner (I := I) g β (extChartAt I β x) (-d₂)
            (d₁ - d₂) :=
      chartMetricInner_add_left (I := I) g β _ _ _ _
    have hneg : chartMetricInner (I := I) g β (extChartAt I β x)
        (-d₂) (d₁ - d₂)
        = -chartMetricInner (I := I) g β (extChartAt I β x) d₂ (d₁ - d₂) :=
      chartMetricInner_neg_left (I := I) g β _ _ _
    nth_rewrite 1 [hrw]
    rw [hadd, hneg, hp]
    ring
  exact absurd hzero hposd.ne'

end Curvature

/-! ### The chart-change theorem for the Jacobi pair system -/

section Transfer

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Chart-change covariance of the Jacobi pair system** along a
geodesic. If the piece `γ([a, b])` of a geodesic lies in the sources of the
charts at `α` and at `β`, then the chart-`α` Jacobi certificate for the
intrinsic pair `(J, ∇J)` transfers to the chart at `β`. The chart readings
transform by the (curve-dependent) tangent coordinate change
`C(τ) = tangentCoordChange I α β (γ τ)`; differentiating this relation
produces second-derivative terms of the transition map which cancel against
the inhomogeneous term of the Christoffel transformation law
(`Riemannian.chartChristoffelContraction_change`), while the curvature term
transforms equivariantly (`chartCurvature_coordChange`).

Blueprint: `lem:jacobi-field-coordinates`. -/
theorem IsJacobiFieldOn.transfer
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {α β : M}
    {a b : ℝ}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsrcα : ∀ τ ∈ Icc a b, γ τ ∈ (chartAt H α).source)
    (hsrcβ : ∀ τ ∈ Icc a b, γ τ ∈ (chartAt H β).source)
    (h : IsJacobiFieldOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (chartVectorRep (I := I) γ α J) (chartVectorRep (I := I) γ α DJ) a b) :
    IsJacobiFieldOn (I := I) g β (fun τ => extChartAt I β (γ τ))
      (chartVectorRep (I := I) γ β J) (chartVectorRep (I := I) γ β DJ)
      a b := by
  classical
  -- Shared per-time analytic package: eventual identification of the
  -- β-readings through the transition map, differentiability of the
  -- transition derivative along the curve, and the base-velocity relation.
  have key : ∀ τ ∈ Icc a b,
      (chartVectorRep (I := I) γ β J =ᶠ[𝓝 τ]
        fun σ => fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α J σ)) ∧
      (chartVectorRep (I := I) γ β DJ =ᶠ[𝓝 τ]
        fun σ => fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α DJ σ)) ∧
      HasDerivAt (fun σ => fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)))
        (fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
          (extChartAt I α (γ τ))
          (deriv (fun σ => extChartAt I α (γ σ)) τ)) τ ∧
      deriv (fun σ => extChartAt I β (γ σ)) τ
        = tangentCoordChange I α β (γ τ)
            (deriv (fun σ => extChartAt I α (γ σ)) τ) ∧
      fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
        = tangentCoordChange I α β (γ τ) := by
    intro τ hτ
    have hxα := hsrcα τ hτ
    have hxβ := hsrcβ τ hτ
    have hcτ := hγc τ hτ
    have hyT : extChartAt I α (γ τ)
        ∈ chartTransitionSource (I := I) (M := M) α β :=
      extChartAt_mem_chartTransitionSource (I := I) hxα hxβ
    have hsymm : (extChartAt I α).symm (extChartAt I α (γ τ)) = γ τ :=
      (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hxα)
    -- the fixed-chart geodesic curve is two-sidedly differentiable at τ
    have hu : HasDerivAt (fun σ => extChartAt I α (γ σ))
        (deriv (fun σ => extChartAt I α (γ σ)) τ) τ := by
      have hev := (hgeo τ hτ).eventually_hasDerivAt_extChartAt hcτ hxα
      exact hev.self_of_nhds.differentiableAt.hasDerivAt
    -- first derivative of the transition map at the chart image
    have hTd : HasFDerivAt (chartTransition (I := I) α β)
        (tangentCoordChange I α β (γ τ)) (extChartAt I α (γ τ)) := by
      have h0 := hasFDerivAt_chartTransition (I := I) hyT
      rwa [hsymm] at h0
    -- eventual membership of the feet in both chart sources
    have hev_mem : ∀ᶠ σ in 𝓝 τ,
        γ σ ∈ (chartAt H α).source ∧ γ σ ∈ (chartAt H β).source := by
      have h₁ : γ ⁻¹' (chartAt H α).source ∈ 𝓝 τ :=
        hcτ.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hxα)
      have h₂ : γ ⁻¹' (chartAt H β).source ∈ 𝓝 τ :=
        hcτ.preimage_mem_nhds ((chartAt H β).open_source.mem_nhds hxβ)
      filter_upwards [h₁, h₂] with σ h1 h2
      exact ⟨h1, h2⟩
    -- eventual identification of the β-reading through the transition map
    have hrep : ∀ V : ℝ → E, chartVectorRep (I := I) γ β V =ᶠ[𝓝 τ]
        fun σ => fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α V σ) := by
      intro V
      filter_upwards [hev_mem] with σ hσ
      have hyσ : extChartAt I α (γ σ)
          ∈ chartTransitionSource (I := I) (M := M) α β :=
        extChartAt_mem_chartTransitionSource (I := I) hσ.1 hσ.2
      have hsymmσ : (extChartAt I α).symm (extChartAt I α (γ σ)) = γ σ :=
        (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hσ.1)
      have hfdσ : fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)) = tangentCoordChange I α β (γ σ) := by
        rw [fderiv_chartTransition (I := I) hyσ, hsymmσ]
      show chartVectorRep (I := I) γ β V σ
        = fderiv ℝ (chartTransition (I := I) α β)
            (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α V σ)
      rw [hfdσ, chartVectorRep_apply, chartVectorRep_apply]
      exact (tangentCoordChange_comp (I := I)
        ⟨⟨mem_extChartAt_source (I := I) (γ σ),
          by rw [extChartAt_source]; exact hσ.1⟩,
          by rw [extChartAt_source]; exact hσ.2⟩).symm
    -- derivative of the transition-derivative along the curve
    have hC' : HasDerivAt (fun σ => fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)))
        (fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
          (extChartAt I α (γ τ))
          (deriv (fun σ => extChartAt I α (γ σ)) τ)) τ :=
      (hasFDerivAt_fderiv_chartTransition (I := I) hyT).comp_hasDerivAt τ hu
    -- derivative of the β-reading of the base geodesic
    have huβ : HasDerivAt (fun σ => extChartAt I β (γ σ))
        (tangentCoordChange I α β (γ τ)
          (deriv (fun σ => extChartAt I α (γ σ)) τ)) τ := by
      have hcomp := hTd.comp_hasDerivAt τ hu
      have hcong : (fun σ => extChartAt I β (γ σ)) =ᶠ[𝓝 τ]
          fun σ => chartTransition (I := I) α β (extChartAt I α (γ σ)) := by
        filter_upwards [hev_mem] with σ hσ
        exact (chartTransition_extChartAt (I := I) hσ.1).symm
      exact hcomp.congr_of_eventuallyEq hcong
    exact ⟨hrep J, hrep DJ, hC', huβ.deriv, hTd.fderiv⟩
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_⟩
  · -- first pair equation: `J_β' = DJ_β − Γ_β(u̇_β, J_β)`
    obtain ⟨hJrep, hDJrep, hC', hduβ, hfd⟩ := key τ hτ
    have hxα := hsrcα τ hτ
    have hxβ := hsrcβ τ hτ
    have hJτ : chartVectorRep (I := I) γ β J τ
        = fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
            (chartVectorRep (I := I) γ α J τ) := hJrep.self_of_nhds
    have hDJτ : chartVectorRep (I := I) γ β DJ τ
        = fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
            (chartVectorRep (I := I) γ α DJ τ) := hDJrep.self_of_nhds
    have hval := (hC'.hasDerivWithinAt.clm_apply
      (h.hasDerivWithinAt_fst τ hτ)).congr_of_eventuallyEq
      (hJrep.filter_mono nhdsWithin_le_nhds) hJrep.self_of_nhds
    have heq : chartVectorRep (I := I) γ β DJ τ
        - Geodesic.chartChristoffelContraction (I := I) g β
            (deriv (fun σ => extChartAt I β (γ σ)) τ)
            (chartVectorRep (I := I) γ β J τ) (extChartAt I β (γ τ))
        = fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
            (extChartAt I α (γ τ))
            (deriv (fun σ => extChartAt I α (γ σ)) τ)
            (chartVectorRep (I := I) γ α J τ)
          + fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
            (chartVectorRep (I := I) γ α DJ τ
              - Geodesic.chartChristoffelContraction (I := I) g α
                  (deriv (fun σ => extChartAt I α (γ σ)) τ)
                  (chartVectorRep (I := I) γ α J τ)
                  (extChartAt I α (γ τ))) := by
      rw [hfd, map_sub,
        chartChristoffelContraction_change (I := I) g β α hxβ hxα
          (deriv (fun σ => extChartAt I α (γ σ)) τ)
          (chartVectorRep (I := I) γ α J τ),
        hduβ, hDJτ, hJτ, hfd]
      abel
    rw [heq]
    exact hval
  · -- second pair equation: `DJ_β' = −ℛ_β(J_β, u̇_β)u̇_β − Γ_β(u̇_β, DJ_β)`
    obtain ⟨hJrep, hDJrep, hC', hduβ, hfd⟩ := key τ hτ
    have hxα := hsrcα τ hτ
    have hxβ := hsrcβ τ hτ
    have hJτ : chartVectorRep (I := I) γ β J τ
        = fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
            (chartVectorRep (I := I) γ α J τ) := hJrep.self_of_nhds
    have hDJτ : chartVectorRep (I := I) γ β DJ τ
        = fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
            (chartVectorRep (I := I) γ α DJ τ) := hDJrep.self_of_nhds
    have hval := (hC'.hasDerivWithinAt.clm_apply
      (h.hasDerivWithinAt_snd τ hτ)).congr_of_eventuallyEq
      (hDJrep.filter_mono nhdsWithin_le_nhds) hDJrep.self_of_nhds
    have heq : -(chartCurvature (I := I) g β (extChartAt I β (γ τ))
            (chartVectorRep (I := I) γ β J τ)
            (deriv (fun σ => extChartAt I β (γ σ)) τ)
            (deriv (fun σ => extChartAt I β (γ σ)) τ))
        - Geodesic.chartChristoffelContraction (I := I) g β
            (deriv (fun σ => extChartAt I β (γ σ)) τ)
            (chartVectorRep (I := I) γ β DJ τ) (extChartAt I β (γ τ))
        = fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
            (extChartAt I α (γ τ))
            (deriv (fun σ => extChartAt I α (γ σ)) τ)
            (chartVectorRep (I := I) γ α DJ τ)
          + fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
            (-(chartCurvature (I := I) g α (extChartAt I α (γ τ))
                  (chartVectorRep (I := I) γ α J τ)
                  (deriv (fun σ => extChartAt I α (γ σ)) τ)
                  (deriv (fun σ => extChartAt I α (γ σ)) τ))
              - Geodesic.chartChristoffelContraction (I := I) g α
                  (deriv (fun σ => extChartAt I α (γ σ)) τ)
                  (chartVectorRep (I := I) γ α DJ τ)
                  (extChartAt I α (γ τ))) := by
      rw [hfd, map_sub, map_neg,
        chartChristoffelContraction_change (I := I) g β α hxβ hxα
          (deriv (fun σ => extChartAt I α (γ σ)) τ)
          (chartVectorRep (I := I) γ α DJ τ),
        hduβ, hDJτ, hJτ, hfd,
        ← chartCurvature_coordChange (I := I) g hxα hxβ
          (chartVectorRep (I := I) γ α J τ)
          (deriv (fun σ => extChartAt I α (γ σ)) τ)
          (deriv (fun σ => extChartAt I α (γ σ)) τ)]
      abel
    rw [heq]
    exact hval

end Transfer

end MorganTianLib

end
