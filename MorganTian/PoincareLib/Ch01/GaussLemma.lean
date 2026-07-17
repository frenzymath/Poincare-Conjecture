import PoincareLib.Ch01.JacobiField
import PoincareLib.Ch01.ParallelFrame
import PoincareLib.Ch01.CurvatureSectionalBound
import PoincareLib.Ch01.JacobiManifold
import OpenGALib.Riemannian.Geodesic.EquationTransfer

/-!
# Poincaré Ch. 1 — The Gauss Lemma along a radial geodesic

The **manifold-to-frame bridge**, first half: `lem:geodesic-polar-form`(1).

Morgan–Tian prove the Gauss Lemma `g̃ = dr² + g_ij dθ^i dθ^j` by showing that the
polar coordinate fields `∂_{θ^i}` — which restrict along each radial geodesic
`γ_w(t) = exp_p(t w)` to Jacobi fields vanishing at `t = 0` — stay **orthogonal
to the radial direction** `γ_w'`. That orthogonality is the whole content of the
splitting, and it is proved by a computation *entirely along the geodesic*: for a
Jacobi field `J` along a geodesic with velocity `X`,

`d²/dt² ⟨J, X⟩ = ⟨∇_X∇_X J, X⟩ = -⟨ℛ(J, X)X, X⟩ = 0`,

since `ℛ(J,X,X,X) = 0` by antisymmetry of the curvature tensor in its last two
arguments. Hence `⟨J, X⟩` is an **affine function of `t`**, and for a radial
field (`J(0) = 0` and `∇J(0) ⟂ X`) both coefficients vanish, so `⟨J, X⟩ ≡ 0`.

## Contents

*The curvature input.*
* `chartCurvature_inner_velocity_eq_zero` — `⟨ℛ(X, u)u, u⟩ = 0`, from the
  pointwise antisymmetry `antisymm₃₄` of `curvatureFormAt` through the chart
  bridge `curvatureFormAt_chartFrame`.

*Chart-level core* (against the chart Jacobi pair system `IsJacobiFieldOn`).
* `IsJacobiFieldOn.hasDerivAt_chartInner_snd_velocity` — `d/dt⟨∇J, u̇⟩ = 0`;
* `IsJacobiFieldOn.hasDerivAt_chartInner_fst_velocity` — `d/dt⟨J, u̇⟩ = ⟨∇J, u̇⟩`.

*Manifold level* (chart-free). The radial scalars are packaged as
`innerVelocity g γ V t = ⟨V(t), γ̇(t)⟩_g`, with `mfderivVelocity γ` the velocity
`γ̇ = mfderiv γ 1` read in `E`; `innerVelocity_eq_chartMetricInner_of_geodesicAt`
is the chart formula that makes them computable.
* `IsJacobiFieldAlongOn.innerVelocity_snd_eq` — `⟨∇J, γ̇⟩` is **constant**;
* `IsJacobiFieldAlongOn.innerVelocity_fst_eq` — `⟨J, γ̇⟩` is **affine** in `t`;
* `IsJacobiFieldAlongOn.innerVelocity_fst_eq_zero` /
  `IsJacobiFieldAlongOn.innerVelocity_snd_eq_zero` — **the Gauss Lemma**: a
  *radial* Jacobi field (`J(a) = 0` and `⟨∇J(a), γ̇(a)⟩ = 0`) keeps **both** `J`
  and `∇J` orthogonal to the velocity for all time.

The last statement is what licenses the whole comparison machinery to be run on
the orthogonal complement `w^⊥` of the radial direction: it is the fact under
which the matrix Jacobi field of `PoincareLib.Ch01.JacobiRiccati`
(`IsRadialJacobi`) is an endomorphism family of that *fixed* complement. It is
also the step quoted in the proof of `lem:geodesic-polar-form`(3) as
"perpendicular Jacobi fields stay perpendicular by the linearity argument in (1)".

The geodesic hypothesis enters **only** through the fixed-chart geodesic ODE
(`Geodesic.SolvesGeodesicODEAt`, i.e. `∇_{u̇} u̇ = 0`), so no exponential map, no
polar chart, and no non-singularity assumption is needed here.

Blueprint: `lem:geodesic-polar-form`(1).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.5.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The velocity field of a curve -/

/-- **Math.** The **velocity field** `γ̇(t) = dγ/dt` of a curve, read in the model
space `E` via `TangentSpace I (γ t) = E`. Packaging it as a curve `ℝ → E` lets it
be paired with Jacobi fields (also carried in `E`) by the intrinsic metric
`g.metricInner`, and read in a chart by `chartVectorRep`.

(Named for its `mfderiv` definition, to avoid a clash with the
`TangentSpace`-valued `PoincareLib.curveVelocity` of `Ch02.CovDerivAlongCurve`,
which is defined through the moving-foot chart curve instead. On a geodesic the
two agree, by `Geodesic.HasGeodesicEquationAt.mfderiv_apply_one`.) -/
def mfderivVelocity (γ : ℝ → M) (t : ℝ) : E := (mfderiv 𝓘(ℝ, ℝ) I γ t 1 : E)

@[simp] theorem mfderivVelocity_def (γ : ℝ → M) (t : ℝ) :
    mfderivVelocity (I := I) γ t = (mfderiv 𝓘(ℝ, ℝ) I γ t 1 : E) := rfl

/-- **Math.** The **radial scalar** `⟨V(t), γ̇(t)⟩_g` of a field `V` along `γ`
against the velocity of `γ` — the chart-independent quantity whose vanishing is
the Gauss Lemma. Keeping it as a named `ℝ`-valued function lets the whole
argument be run on scalars. -/
def innerVelocity (g : RiemannianMetric I M) (γ : ℝ → M) (V : ℝ → E) (t : ℝ) : ℝ :=
  g.metricInner (γ t) (V t : TangentSpace I (γ t))
    ((mfderivVelocity (I := I) γ t : E) : TangentSpace I (γ t))

theorem innerVelocity_def (g : RiemannianMetric I M) (γ : ℝ → M) (V : ℝ → E)
    (t : ℝ) :
    innerVelocity (I := I) g γ V t
      = g.metricInner (γ t) (V t : TangentSpace I (γ t))
          ((mfderivVelocity (I := I) γ t : E) : TangentSpace I (γ t)) := rfl

/-! ### The curvature input: `ℛ(X, u, u, u) = 0` -/

section CurvatureInput

open Bundle Riemannian.Tensor

variable [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The curvature term of the Jacobi equation is **orthogonal to the
velocity**: `⟨ℛ(X, u)u, u⟩ = 0` for all coordinate vectors `X, u`.

This is Morgan–Tian's `ℛ(J, X, X, X) = 0`, i.e. the antisymmetry
`R_{ijkl} = −R_{ijlk}` of the curvature tensor in its last two arguments, applied
with those two arguments equal. We obtain it from the pointwise algebraic
curvature form: `curvatureFormAt_chartFrame` identifies the chart pairing with
`−curvatureFormAt g ∇ p (F X) (F u) (F u) (F u)`, and `antisymm₃₄` of
`isAlgCurvatureForm_curvatureFormAt` forces that value to be its own negative.

Blueprint: `lem:geodesic-polar-form`(1), `claim:curvature-symmetries-bianchi`. -/
theorem chartCurvature_inner_velocity_eq_zero [I.Boundaryless]
    (g : RiemannianMetric I M) {α : M} {y : E}
    (hy : y ∈ (extChartAt I α).target) (X u : E) :
    chartMetricInner (I := I) g α y
      (chartCurvature (I := I) g α y X u u) u = 0 := by
  classical
  set p := (extChartAt I α).symm y with hp_def
  have hp : p ∈ (chartAt H α).source := by
    have h := (extChartAt I α).map_target hy
    rwa [extChartAt_source] at h
  have hyp : extChartAt I α p = y := (extChartAt I α).right_inv hy
  set nabla := g.leviCivitaConnection with hnabla
  have hLC : nabla.IsLeviCivita g :=
    nabla.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hB : IsAlgCurvatureForm (curvatureFormAt g nabla p) :=
    isAlgCurvatureForm_curvatureFormAt g nabla hLC p
  set FX : TangentSpace I p :=
    ∑ a, Geodesic.chartCoord (E := E) a X • chartBasisVecFiber (I := I) α a p with hFX
  set Fu : TangentSpace I p :=
    ∑ a, Geodesic.chartCoord (E := E) a u • chartBasisVecFiber (I := I) α a p with hFu
  -- the chart bridge: the chart pairing is minus the pointwise curvature form
  have hbridge : curvatureFormAt g nabla p FX Fu Fu Fu
      = - chartMetricInner (I := I) g α y
          (chartCurvature (I := I) g α y X u u) u := by
    have h := curvatureFormAt_chartFrame (I := I) g hp X u u u
    rwa [hyp] at h
  -- antisymmetry in the last two slots, with those two slots equal
  have hzero : curvatureFormAt g nabla p FX Fu Fu Fu = 0 := by
    have h : curvatureFormAt g nabla p FX Fu Fu Fu
        = - curvatureFormAt g nabla p FX Fu Fu Fu := hB.antisymm₃₄ FX Fu Fu Fu
    linarith
  rw [hzero] at hbridge
  linarith

end CurvatureInput

/-! ### Chart-level core -/

namespace IsJacobiFieldOn

variable {g : RiemannianMetric I M} {α : M} {u J DJ : ℝ → E} {a b : ℝ}

/-- **Math.** At interior times a Jacobi field is differentiable: its chart pair
system provides a one-sided derivative on `Icc a b`, which is a genuine
derivative at interior times. -/
theorem differentiableAt_fst (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    {t : ℝ} (ht : t ∈ Ioo a b) : DifferentiableAt ℝ J t :=
  ((h.hasDerivWithinAt_fst t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)).differentiableAt

/-- **Math.** At interior times the covariant-derivative field of a Jacobi field
is differentiable. -/
theorem differentiableAt_snd (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    {t : ℝ} (ht : t ∈ Ioo a b) : DifferentiableAt ℝ DJ t :=
  ((h.hasDerivWithinAt_snd t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)).differentiableAt

section Gauss

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] {t : ℝ}

/-- **Math.** Along a geodesic, `⟨∇J, u̇⟩` has **vanishing derivative** at `t`:
metric compatibility gives
`d/dt⟨∇J, u̇⟩ = ⟨∇∇J, u̇⟩ + ⟨∇J, ∇u̇⟩ = ⟨−ℛ(J,u̇)u̇, u̇⟩ + 0 = 0`,
the first term vanishing by `chartCurvature_inner_velocity_eq_zero` and the
second because `u` is a geodesic. This is Morgan–Tian's `d²/dt²⟨J,X⟩ = 0`.
Blueprint: `lem:geodesic-polar-form`(1). -/
theorem hasDerivAt_chartInner_snd_velocity
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b) (ht : t ∈ Ioo a b)
    (hu : DifferentiableAt ℝ u t)
    (hu' : DifferentiableAt ℝ (deriv u) t)
    (hgeo : covariantDerivCoord (I := I) g α u (deriv u) t = 0)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (htgt : u t ∈ (extChartAt I α).target)
    (hbase : (extChartAt I α).symm (u t)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) (DJ s) (deriv u s))
      0 t := by
  refine (hasDerivAt_chartMetricInner_along (I := I) g α u DJ (deriv u)
    hu (h.differentiableAt_snd ht) hu' hG hbase).congr_deriv ?_
  rw [h.covariantDerivCoord_snd ht, hgeo, chartMetricInner_zero_right, add_zero,
    chartMetricInner_neg_left,
    chartCurvature_inner_velocity_eq_zero (I := I) g htgt, neg_zero]

/-- **Math.** Along a geodesic, `d/dt⟨J, u̇⟩ = ⟨∇J, u̇⟩` — metric compatibility
together with `∇u̇ = 0`. Blueprint: `lem:geodesic-polar-form`(1). -/
theorem hasDerivAt_chartInner_fst_velocity
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b) (ht : t ∈ Ioo a b)
    (hu : DifferentiableAt ℝ u t)
    (hu' : DifferentiableAt ℝ (deriv u) t)
    (hgeo : covariantDerivCoord (I := I) g α u (deriv u) t = 0)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : (extChartAt I α).symm (u t)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) (J s) (deriv u s))
      (chartMetricInner (I := I) g α (u t) (DJ t) (deriv u t)) t := by
  refine (hasDerivAt_chartMetricInner_along (I := I) g α u J (deriv u)
    hu (h.differentiableAt_fst ht) hu' hG hbase).congr_deriv ?_
  rw [h.covariantDerivCoord_fst ht, hgeo, chartMetricInner_zero_right, add_zero]

end Gauss

end IsJacobiFieldOn

/-! ### The fixed-chart geodesic package

A geodesic satisfies, in *any* chart containing its foot, the second-order chart
ODE `u'' + Γ(u̇, u̇)(u) = 0` (`Geodesic.SolvesGeodesicODEAt`, obtained from the
moving-foot equation by the chart-change transfer). Two consequences are all the
Gauss-lemma computation needs: the chart velocity is differentiable, and the
chart *covariant* acceleration vanishes. -/

section GeodesicChart

variable [I.Boundaryless] {g : RiemannianMetric I M} {γ : ℝ → M} {τ : ℝ}

/-- **Math.** Along a geodesic the fixed-chart velocity `u̇` is differentiable at
every time whose foot lies in the chart: the chart geodesic ODE exhibits `u''`. -/
theorem differentiableAt_deriv_extChartAt_of_geodesicAt
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ τ) (hc : ContinuousAt γ τ)
    {α : M} (hsrc : γ τ ∈ (chartAt H α).source) :
    DifferentiableAt ℝ (deriv (fun s => extChartAt I α (γ s))) τ := by
  obtain ⟨-, acc, hacc, -⟩ :=
    Geodesic.HasGeodesicEquationAt.solvesGeodesicODEAt (I := I) h hc hsrc
  exact hacc.differentiableAt

/-- **Math.** **The geodesic equation in a fixed chart**: the chart covariant
acceleration `∇_{u̇} u̇ = u'' + Γ(u̇, u̇)(u)` of a geodesic vanishes, in any chart
containing the foot. This is the only way the geodesic hypothesis enters the
Gauss Lemma. -/
theorem covariantDerivCoord_deriv_extChartAt_eq_zero_of_geodesicAt
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ τ) (hc : ContinuousAt γ τ)
    {α : M} (hsrc : γ τ ∈ (chartAt H α).source) :
    covariantDerivCoord (I := I) g α (fun s => extChartAt I α (γ s))
      (deriv (fun s => extChartAt I α (γ s))) τ = 0 := by
  obtain ⟨-, acc, hacc, heq⟩ :=
    Geodesic.HasGeodesicEquationAt.solvesGeodesicODEAt (I := I) h hc hsrc
  -- `chartReading α γ` is the eta-expansion of `fun s => extChartAt I α (γ s)`
  have hcr : Geodesic.chartReading (I := I) α γ = fun s => extChartAt I α (γ s) := rfl
  rw [hcr] at hacc heq
  rw [covariantDerivCoord_def, hacc.deriv]
  exact heq

/-- **Math.** The chart reading of the **manifold velocity** `γ̇ = mfderiv γ 1` is
the chart velocity `u̇`: `chartVectorRep γ α γ̇ = u̇`. This identifies the intrinsic
pairing `⟨V, γ̇⟩_g` with the chart Gram pairing `⟨V_α, u̇⟩` used in the chart-level
core above. -/
theorem chartVectorRep_velocity_of_geodesicAt
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ τ) (hc : ContinuousAt γ τ)
    {α : M} (hsrc : γ τ ∈ (chartAt H α).source) :
    chartVectorRep (I := I) γ α (mfderivVelocity (I := I) γ) τ
      = deriv (fun s => extChartAt I α (γ s)) τ := by
  rw [chartVectorRep_apply, mfderivVelocity_def,
    Geodesic.HasGeodesicEquationAt.deriv_extChartAt_eq (I := I) h hc hsrc,
    Geodesic.HasGeodesicEquationAt.mfderiv_apply_one (I := I) h hc]

/-- **Math.** **Chart formula for the radial scalar.** In any chart containing the
foot of a geodesic, `⟨V, γ̇⟩_g` is the chart Gram pairing of the chart reading of
`V` against the chart velocity `u̇`. This is the bridge that lets the chart-level
Gauss computation be read off intrinsically. -/
theorem innerVelocity_eq_chartMetricInner_of_geodesicAt
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ τ) (hc : ContinuousAt γ τ)
    {α : M} (hsrc : γ τ ∈ (chartAt H α).source) (V : ℝ → E) :
    innerVelocity (I := I) g γ V τ
      = chartMetricInner (I := I) g α (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α V τ)
          (deriv (fun s => extChartAt I α (γ s)) τ) := by
  rw [innerVelocity_def,
    metricInner_eq_chartMetricInner_rep (I := I) g hsrc V (mfderivVelocity (I := I) γ),
    chartVectorRep_velocity_of_geodesicAt (I := I) h hc hsrc]

end GeodesicChart

/-! ### The Gauss Lemma at the manifold level

Everything below is phrased with the **scalar** `innerVelocity g γ V = ⟨V, γ̇⟩_g`,
which is chart-independent by
`innerVelocity_eq_chartMetricInner_of_geodesicAt`. -/

namespace IsJacobiFieldAlongOn

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
variable {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ}

/-- **Math.** The two interior derivative identities for the radial scalars
`φ = ⟨J, γ̇⟩` and `ψ = ⟨∇J, γ̇⟩` along a geodesic: `φ' = ψ` and `ψ' = 0`.

This is the chart-level core transported to the manifold: around each interior
time the Jacobi field lives in some chart, where the radial scalars are the chart
Gram pairings against the chart velocity `u̇`
(`innerVelocity_eq_chartMetricInner_of_geodesicAt`), and the chart identities
`hasDerivAt_chartInner_fst_velocity` / `hasDerivAt_chartInner_snd_velocity`
apply. Blueprint: `lem:geodesic-polar-form`(1). -/
private theorem gauss_scalar_derivs
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (innerVelocity (I := I) g γ J)
        (innerVelocity (I := I) g γ DJ t) t ∧
      HasDerivAt (innerVelocity (I := I) g γ DJ) 0 t := by
  have htmem : t ∈ Icc a b := Ioo_subset_Icc_self ht
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hJF⟩ := hJac t htmem
  have hIccnhds : Icc a' b' ∈ 𝓝 t := by
    rwa [nhdsWithin_eq_nhds.2 (Icc_mem_nhds ht.1 ht.2)] at hnbhd
  have htIoo : t ∈ Ioo a' b' := by
    have h := mem_interior_iff_mem_nhds.2 hIccnhds
    rwa [interior_Icc] at h
  -- chart-level regularity at `t`
  have hut : DifferentiableAt ℝ (fun s => extChartAt I α (γ s)) t :=
    hgeo.differentiableAt_extChartAt htmem (hγc t htmem) (hsrc t ht')
  have hud : DifferentiableAt ℝ (deriv (fun s => extChartAt I α (γ s))) t :=
    differentiableAt_deriv_extChartAt_of_geodesicAt (I := I) (hgeo t htmem)
      (hγc t htmem) (hsrc t ht')
  have hgeoc : covariantDerivCoord (I := I) g α (fun s => extChartAt I α (γ s))
      (deriv (fun s => extChartAt I α (γ s))) t = 0 :=
    covariantDerivCoord_deriv_extChartAt_eq_zero_of_geodesicAt (I := I)
      (hgeo t htmem) (hγc t htmem) (hsrc t ht')
  have htgt : extChartAt I α (γ t) ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht')
  have hGdiff : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j)
      (extChartAt I α (γ t)) := fun i j =>
    differentiableAt_chartGramOnE (I := I) g α htgt i j
  have hbase : (extChartAt I α).symm (extChartAt I α (γ t))
      ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    symm_extChartAt_mem_baseSet (I := I) (hsrc t ht')
  -- near `t`, each radial scalar is the chart Gram pairing against `u̇`
  have hev : ∀ V : ℝ → E, innerVelocity (I := I) g γ V
      =ᶠ[𝓝 t] (fun τ => chartMetricInner (I := I) g α (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α V τ)
          (deriv (fun s => extChartAt I α (γ s)) τ)) := by
    intro V
    filter_upwards [hIccnhds] with τ hτ
    exact innerVelocity_eq_chartMetricInner_of_geodesicAt (I := I)
      (hgeo τ (hsub hτ)) (hγc τ (hsub hτ)) (hsrc τ hτ) V
  constructor
  · have hd := hJF.hasDerivAt_chartInner_fst_velocity htIoo hut hud hgeoc hGdiff hbase
    rw [← innerVelocity_eq_chartMetricInner_of_geodesicAt (I := I) (hgeo t htmem)
      (hγc t htmem) (hsrc t ht') DJ] at hd
    exact hd.congr_of_eventuallyEq (hev J)
  · have hd := hJF.hasDerivAt_chartInner_snd_velocity htIoo hut hud hgeoc hGdiff
      htgt hbase
    exact hd.congr_of_eventuallyEq (hev DJ)

/-- **Math.** Continuity on `[a, b]` of a radial scalar `⟨V, γ̇⟩` for `V` a
component of a Jacobi field. -/
private theorem continuousOn_innerVelocity
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {V : ℝ → E} (hV : V = J ∨ V = DJ) :
    ContinuousOn (innerVelocity (I := I) g γ V) (Icc a b) := by
  intro t ht
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hJF⟩ := hJac t ht
  have hrepV : ContinuousOn (chartVectorRep (I := I) γ α V) (Icc a' b') := by
    rcases hV with rfl | rfl
    · exact hJF.continuousOn_fst
    · exact hJF.continuousOn_snd
  have hu : ContinuousOn (fun τ => extChartAt I α (γ τ)) (Icc a' b') := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc τ hτ)).comp
        (hγc τ (hsub hτ))).continuousWithinAt
  have hmem : ∀ τ ∈ Icc a' b', extChartAt I α (γ τ) ∈ (extChartAt I α).target :=
    fun τ hτ => (extChartAt I α).map_source
      (by rw [extChartAt_source]; exact hsrc τ hτ)
  have hudc : ContinuousOn (deriv (fun s => extChartAt I α (γ s))) (Icc a' b') :=
    fun τ hτ => (Geodesic.HasGeodesicEquationAt.continuousAt_deriv_extChartAt
      (I := I) (hgeo τ (hsub hτ)) (hγc τ (hsub hτ))
      (hsrc τ hτ)).continuousWithinAt
  have hform := continuousOn_chartMetricInner_pairing (I := I) g α hu hmem hrepV hudc
  have hcw : ContinuousWithinAt (innerVelocity (I := I) g γ V) (Icc a' b') t := by
    refine (hform t ht').congr ?_ ?_
    · intro τ hτ
      exact innerVelocity_eq_chartMetricInner_of_geodesicAt (I := I)
        (hgeo τ (hsub hτ)) (hγc τ (hsub hτ)) (hsrc τ hτ) V
    · exact innerVelocity_eq_chartMetricInner_of_geodesicAt (I := I)
        (hgeo t (hsub ht')) (hγc t (hsub ht')) (hsrc t ht') V
  exact hcw.mono_of_mem_nhdsWithin hnbhd

/-- **Math.** Along a geodesic, `⟨∇J, γ̇⟩` is **constant** on `[a, b]`.
This is the `d²/dt²⟨J, γ̇⟩ = 0` step of the Gauss Lemma, in intrinsic form.
Blueprint: `lem:geodesic-polar-form`(1). -/
theorem innerVelocity_snd_eq
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    ∀ t ∈ Icc a b, innerVelocity (I := I) g γ DJ t
      = innerVelocity (I := I) g γ DJ a :=
  eqOn_const_of_hasDerivAt_zero_interior
    (continuousOn_innerVelocity hJac hgeo hγc (Or.inr rfl))
    (fun _ ht => (gauss_scalar_derivs hJac hgeo hγc ht).2)

/-- **Math.** **`⟨J, γ̇⟩` is an affine function of `t`** along a geodesic:
`⟨J(t), γ̇(t)⟩ = ⟨J(a), γ̇(a)⟩ + (t − a)·⟨∇J(a), γ̇(a)⟩`.

This is Morgan–Tian's "`⟨J, X⟩` is linear in `t`" — the analytic heart of the
Gauss Lemma: the second derivative vanishes by curvature antisymmetry, so the
first derivative `⟨∇J, γ̇⟩` is constant and `⟨J, γ̇⟩` is affine.
Blueprint: `lem:geodesic-polar-form`(1). -/
theorem innerVelocity_fst_eq
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    ∀ t ∈ Icc a b, innerVelocity (I := I) g γ J t
      = innerVelocity (I := I) g γ J a
        + (t - a) * innerVelocity (I := I) g γ DJ a := by
  set c : ℝ := innerVelocity (I := I) g γ DJ a with hc
  have hFcont : ContinuousOn
      (fun τ => innerVelocity (I := I) g γ J τ - c * (τ - a)) (Icc a b) :=
    (continuousOn_innerVelocity hJac hgeo hγc (Or.inl rfl)).sub
      (continuousOn_const.mul ((continuous_id.sub continuous_const).continuousOn))
  have hF0 : ∀ t ∈ Ioo a b, HasDerivAt
      (fun τ => innerVelocity (I := I) g γ J τ - c * (τ - a)) 0 t := by
    intro t ht
    have hψ := innerVelocity_snd_eq hJac hgeo hγc t (Ioo_subset_Icc_self ht)
    have h1 := (gauss_scalar_derivs hJac hgeo hγc ht).1
    rw [hψ, ← hc] at h1
    have h2 : HasDerivAt (fun s : ℝ => c * (s - a)) c t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul c
    have h3 := h1.sub h2
    rwa [sub_self] at h3
  have hconst := eqOn_const_of_hasDerivAt_zero_interior hFcont hF0
  intro t ht
  have ht' := hconst t ht
  simp only [sub_self, mul_zero, sub_zero] at ht'
  linarith

/-- **Math.** **The Gauss Lemma** (`lem:geodesic-polar-form`(1)), orthogonality
half, at the manifold level. A **radial** Jacobi field along a geodesic — one
that vanishes at the centre (`J(a) = 0`) and whose covariant derivative there is
orthogonal to the radial direction (`⟨∇J(a), γ̇(a)⟩ = 0`) — stays orthogonal to
the velocity for all time: `⟨J(t), γ̇(t)⟩ = 0` on `[a, b]`.

Applied to the polar coordinate fields `J_i = ∂γ̃/∂θ^i` (which vanish at the
centre, and whose initial covariant derivatives `∂v/∂θ^i` are tangent to the unit
sphere and hence orthogonal to `v`), this is exactly Morgan–Tian's
`g̃(∂_r, ∂_{θ^i}) = 0`, i.e. the splitting `g̃ = dr² + g_ij dθ^i ⊗ dθ^j`. -/
theorem innerVelocity_fst_eq_zero
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hJa : J a = 0)
    (hDJa : innerVelocity (I := I) g γ DJ a = 0) :
    ∀ t ∈ Icc a b, innerVelocity (I := I) g γ J t = 0 := by
  intro t ht
  have hJ0 : innerVelocity (I := I) g γ J a = 0 := by
    rw [innerVelocity_def, hJa]
    exact g.metricInner_zero_left (γ a) _
  rw [innerVelocity_fst_eq hJac hgeo hγc t ht, hJ0, hDJa, mul_zero, add_zero]

/-- **Math.** **The Gauss Lemma**, companion half: for a radial Jacobi field the
**covariant derivative** `∇J` also stays orthogonal to the velocity,
`⟨∇J(t), γ̇(t)⟩ = 0` on `[a, b]` (immediate from constancy of `⟨∇J, γ̇⟩`).

Together with `innerVelocity_fst_eq_zero` this says that the radial Jacobi
*pair* `(J, ∇J)` lies, at every time, in the orthogonal complement of the radial
direction — the fact that lets the matrix Jacobi field of
`PoincareLib.Ch01.JacobiRiccati` be set up on the fixed complement `w^⊥`. -/
theorem innerVelocity_snd_eq_zero
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hDJa : innerVelocity (I := I) g γ DJ a = 0) :
    ∀ t ∈ Icc a b, innerVelocity (I := I) g γ DJ t = 0 := by
  intro t ht
  rw [innerVelocity_snd_eq hJac hgeo hγc t ht, hDJa]

end IsJacobiFieldAlongOn

end PoincareLib
