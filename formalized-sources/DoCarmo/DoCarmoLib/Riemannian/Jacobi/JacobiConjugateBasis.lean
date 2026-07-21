import DoCarmoLib.Riemannian.Jacobi.JacobiVelocityField
import DoCarmoLib.Riemannian.Jacobi.JacobiExistence

/-!
# do Carmo Ch. 5, §3, Corollary 3.10 — a basis of `𝒥^⊥` restricts to a basis of `γ'(t)^⊥`

Let `γ : [0, L] → M` be a geodesic and `𝒥^⊥` the space of Jacobi fields with `J(0) = 0`,
`J'(0) ⟂ γ'(0)` (do Carmo `cor:dc-ch5-3-8`, dimension `n − 1`).  If `γ(L)` is **not**
conjugate to `γ(0)`, then the endpoint evaluation `J ↦ J(L)` carries a basis
`{J_1, …, J_{n-1}}` of `𝒥^⊥` to a basis of the intrinsic orthogonal complement
`γ'(L)^⊥ ⊂ T_{γ(L)}M`.

Under the initial-velocity parametrization of Jacobi fields with `J(0) = 0`
(`jacobiEndpointOfVel`, `Θ : J'(0) ↦ J(L)`):

* `𝒥^⊥` is `W = ker(velocityFunctional g (γ 0) γ'(0))` (do Carmo `cor:dc-ch5-3-8`);
* `γ'(L)^⊥` is `WL = ker(velocityFunctional g (γ L) γ'(L))`;
* `Θ` maps `W` into `WL` (`jacobiEndpointOfVel_mem_velocityPerp`): the new **intrinsic
  moving-base pairing** `metricInner_jacobiJ_velocity_eq_zero` upgrades do Carmo
  `cor:dc-ch5-3-8` from the fixed-chart form (`chartMetricInner_jacobi_velocity_eq_zero_iff`)
  to the intrinsic `⟨J(t), γ'(t)⟩_g` at the moving foot, via the localization
  `IsJacobiFieldAlongOn.isJacobiFieldOn_of_mem_source` and the chart↔intrinsic bridges
  `metricInner_eq_chartMetricInner_rep`, `chartVectorRep_velocity`;
* `Θ` is injective on all of `E` (`injective_jacobiEndpointOfVel_iff_not_conjugate`, from
  non-conjugacy), and `dim W = n − 1 = dim WL` (`finrank_velocityPerp_eq`), so the restriction
  `W → WL` is a **linear isomorphism** (`jacobiConjugateEquiv`); hence a basis of `W` maps to a
  basis of `WL` (`jacobiConjugateBasis`).

Blueprint: `cor:dc-ch5-3-10`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 5, Corollary 3.10.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

variable {g : RiemannianMetric I M} {γ : ℝ → M} {L : ℝ}

/-! ### The intrinsic moving-base pairing `⟨J(t), γ'(t)⟩ = 0` (upgrade of Cor. 3.8) -/

/-- **Math.** **do Carmo Ch. 5, Corollary 3.8, intrinsic moving-base form.**  Let `J` be the
Jacobi field along the geodesic `γ` with initial data `(J(0), J'(0)) = (0, w)`.  If the initial
velocity is tangentially orthogonal, `⟨w, γ'(0)⟩_g = 0`, then the intrinsic pairing with the
velocity vanishes at **every** foot: `⟨J(t), γ'(t)⟩_g = 0` for all `t ∈ [0, L]`.

This upgrades the fixed-chart affine law (`chartMetricInner_jacobi_velocity_eq_zero_iff`) to the
moving base point `γ(t)`.  The manifold field localizes to the chart at `β` (whose source
contains `γ([0, L])`) by `IsJacobiFieldAlongOn.isJacobiFieldOn_of_mem_source`; the chart Gram
pairing equals the intrinsic one (`metricInner_eq_chartMetricInner_rep`) and the chart velocity
`u̇` reads the intrinsic velocity `γ'` (`chartVectorRep_velocity`); the fixed-chart Cor. 3.8
`⟨J, u̇⟩ ≡ 0` then transfers back to the feet. -/
theorem metricInner_jacobiJ_velocity_eq_zero
    (hab : (0 : ℝ) < L) (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγc : ∀ t ∈ Icc (0 : ℝ) L, ContinuousAt γ t)
    {β : M} (hsrc : ∀ τ ∈ Icc (0 : ℝ) L, γ τ ∈ (chartAt H β).source)
    {w : E} (hw : velocityFunctional (I := I) g (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1) w = 0) :
    ∀ t ∈ Icc (0 : ℝ) L,
      velocityFunctional (I := I) g (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (jacobiJ hab hgeo hγc (0, w) t) = 0 := by
  set J : ℝ → E := jacobiJ hab hgeo hγc (0, w) with hJ
  set DJ : ℝ → E := jacobiDJ hab hgeo hγc (0, w) with hDJ
  have hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 L := jacobiJ_isJacobiField hab hgeo hγc (0, w)
  -- localize to the single chart `β`
  have hJFon : IsJacobiFieldOn (I := I) g β (fun τ => extChartAt I β (γ τ))
      (chartVectorRep (I := I) γ β J) (chartVectorRep (I := I) γ β DJ) 0 L :=
    hJac.isJacobiFieldOn_of_mem_source hgeo hγc subset_rfl hsrc
  -- chart reading of `J` vanishes at `0` (since `J 0 = 0`)
  have hJ0chart : chartVectorRep (I := I) γ β J 0 = 0 := by
    simp only [chartVectorRep_apply, hJ, jacobiJ_zero]
    exact (tangentCoordChange I (γ 0) β (γ 0)).map_zero
  -- pointwise: the tangential-velocity pairing of any field `f` equals its chart Gram pairing
  have hconv : ∀ f : ℝ → E, ∀ t ∈ Icc (0 : ℝ) L,
      velocityFunctional (I := I) g (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (f t)
        = chartMetricInner (I := I) g β (Geodesic.chartReading (I := I) β γ t)
            (chartVectorRep (I := I) γ β f t) (deriv (Geodesic.chartReading (I := I) β γ) t) := by
    intro f t ht
    have htsrc : γ t ∈ (chartAt H β).source := hsrc t ht
    have hgeqt : Geodesic.HasGeodesicEquationAt (I := I) g γ t := hgeo.hasGeodesicEquationAt ht
    have hvel : deriv (Geodesic.chartReading (I := I) β γ) t
        = chartVectorRep (I := I) γ β (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1) t :=
      (chartVectorRep_velocity g β hgeqt (hγc t ht) htsrc).symm
    rw [velocityFunctional_apply, Geodesic.chartReading_def, hvel,
      ← metricInner_eq_chartMetricInner_rep (I := I) g htsrc f (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1)]
  -- the fixed-chart Cor. 3.8: chart pairing vanishes at `0`, hence everywhere
  have hiff := chartMetricInner_jacobi_velocity_eq_zero_iff (I := I) g β hab hgeo hγc hsrc hJFon
    hJ0chart
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hab.le⟩
  have hLHS : chartMetricInner (I := I) g β (Geodesic.chartReading (I := I) β γ 0)
      (chartVectorRep (I := I) γ β DJ 0) (deriv (Geodesic.chartReading (I := I) β γ) 0) = 0 := by
    rw [← hconv DJ 0 h0mem]
    have hDJ0 : DJ 0 = w := by rw [hDJ, jacobiDJ_zero]
    rw [hDJ0]; exact hw
  have hall := hiff.1 hLHS
  intro t ht
  rw [hconv J t ht]
  exact hall t ht

/-! ### `Θ` maps `𝒥^⊥` into `γ'(L)^⊥` -/

/-- **Math.** The endpoint map `Θ : J'(0) ↦ J(L)` sends the tangential-orthogonal subspace
`𝒥^⊥ = ker(velocityFunctional g (γ 0) γ'(0))` into `γ'(L)^⊥ = ker(velocityFunctional g (γ L)
γ'(L))`: for `⟨w, γ'(0)⟩ = 0` the Jacobi field `J` with `J(0) = 0`, `J'(0) = w` has
`⟨J(L), γ'(L)⟩ = 0` (`metricInner_jacobiJ_velocity_eq_zero`). -/
theorem jacobiEndpointOfVel_mem_velocityPerp
    (hab : (0 : ℝ) < L) (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγc : ∀ t ∈ Icc (0 : ℝ) L, ContinuousAt γ t)
    {β : M} (hsrc : ∀ τ ∈ Icc (0 : ℝ) L, γ τ ∈ (chartAt H β).source)
    {w : E}
    (hw : w ∈ LinearMap.ker (velocityFunctional (I := I) g (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1))) :
    jacobiEndpointOfVel hab hgeo hγc w
      ∈ LinearMap.ker (velocityFunctional (I := I) g (γ L) (mfderiv 𝓘(ℝ, ℝ) I γ L 1)) := by
  rw [LinearMap.mem_ker] at hw ⊢
  rw [jacobiEndpointOfVel_apply]
  exact metricInner_jacobiJ_velocity_eq_zero hab hgeo hγc hsrc hw L (right_mem_Icc.2 hab.le)

/-! ### Corollary 3.10 — the endpoint map restricts to an isomorphism `𝒥^⊥ ≃ γ'(L)^⊥` -/

/-- **Math.** **The endpoint map carries `𝒥^⊥` *onto* `γ'(L)^⊥`.**  For a non-conjugate,
non-constant geodesic, `Θ : J'(0) ↦ J(L)` maps the hyperplane `𝒥^⊥ = ker(velocityFunctional
g (γ 0) γ'(0))` bijectively onto `γ'(L)^⊥ = ker(velocityFunctional g (γ L) γ'(L))`: it maps in
(`jacobiEndpointOfVel_mem_velocityPerp`), is injective (`injective_...`), and both hyperplanes
have dimension `n − 1` (`finrank_velocityPerp_eq`), so the image (of full dimension `n − 1`) is
all of `γ'(L)^⊥`. -/
theorem jacobiEndpointOfVel_map_velocityPerp_eq
    (hab : (0 : ℝ) < L) (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγc : ∀ t ∈ Icc (0 : ℝ) L, ContinuousAt γ t)
    {β : M} (hsrc : ∀ τ ∈ Icc (0 : ℝ) L, γ τ ∈ (chartAt H β).source)
    (hv0 : mfderiv 𝓘(ℝ, ℝ) I γ 0 1 ≠ 0) (hvL : mfderiv 𝓘(ℝ, ℝ) I γ L 1 ≠ 0)
    (hnc : ¬ IsConjugatePointAt (I := I) g γ L) :
    Submodule.map (jacobiEndpointOfVel hab hgeo hγc)
        (LinearMap.ker (velocityFunctional (I := I) g (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)))
      = LinearMap.ker (velocityFunctional (I := I) g (γ L) (mfderiv 𝓘(ℝ, ℝ) I γ L 1)) := by
  have hΘinj : Function.Injective (jacobiEndpointOfVel hab hgeo hγc) :=
    (injective_jacobiEndpointOfVel_iff_not_conjugate hab hgeo hγc).2 hnc
  refine Submodule.eq_of_le_of_finrank_le ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    exact fun x hx => jacobiEndpointOfVel_mem_velocityPerp hab hgeo hγc hsrc hx
  · rw [(Submodule.equivMapOfInjective _ hΘinj _).symm.finrank_eq,
      finrank_velocityPerp_eq (I := I) g hv0, finrank_velocityPerp_eq (I := I) g hvL]

/-- **Math.** **do Carmo Ch. 5, Corollary 3.10 (endpoint form).**  If `γ(L)` is not conjugate to
`γ(0)` and the geodesic is non-constant at both ends (`γ'(0) ≠ 0`, `γ'(L) ≠ 0`), the endpoint
evaluation `Θ : J'(0) ↦ J(L)` restricts to a **linear isomorphism** from `𝒥^⊥` (Jacobi fields
with `J(0) = 0`, `J'(0) ⟂ γ'(0)`) onto `γ'(L)^⊥`. -/
def jacobiConjugateEquiv
    (hab : (0 : ℝ) < L) (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγc : ∀ t ∈ Icc (0 : ℝ) L, ContinuousAt γ t)
    {β : M} (hsrc : ∀ τ ∈ Icc (0 : ℝ) L, γ τ ∈ (chartAt H β).source)
    (hv0 : mfderiv 𝓘(ℝ, ℝ) I γ 0 1 ≠ 0) (hvL : mfderiv 𝓘(ℝ, ℝ) I γ L 1 ≠ 0)
    (hnc : ¬ IsConjugatePointAt (I := I) g γ L) :
    (LinearMap.ker (velocityFunctional (I := I) g (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)))
      ≃ₗ[ℝ] (LinearMap.ker (velocityFunctional (I := I) g (γ L) (mfderiv 𝓘(ℝ, ℝ) I γ L 1))) :=
  (Submodule.equivMapOfInjective (jacobiEndpointOfVel hab hgeo hγc)
      ((injective_jacobiEndpointOfVel_iff_not_conjugate hab hgeo hγc).2 hnc) _).trans
    (LinearEquiv.ofEq _ _ (jacobiEndpointOfVel_map_velocityPerp_eq hab hgeo hγc hsrc hv0 hvL hnc))

/-- **Math.** The underlying tangent vector of `jacobiConjugateEquiv x` is the endpoint value
`Θ (x) = J_{(0, x)}(L)`. -/
@[simp] theorem jacobiConjugateEquiv_coe
    (hab : (0 : ℝ) < L) (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγc : ∀ t ∈ Icc (0 : ℝ) L, ContinuousAt γ t)
    {β : M} (hsrc : ∀ τ ∈ Icc (0 : ℝ) L, γ τ ∈ (chartAt H β).source)
    (hv0 : mfderiv 𝓘(ℝ, ℝ) I γ 0 1 ≠ 0) (hvL : mfderiv 𝓘(ℝ, ℝ) I γ L 1 ≠ 0)
    (hnc : ¬ IsConjugatePointAt (I := I) g γ L)
    (x : LinearMap.ker (velocityFunctional (I := I) g (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1))) :
    ((jacobiConjugateEquiv hab hgeo hγc hsrc hv0 hvL hnc x : E))
      = jacobiEndpointOfVel hab hgeo hγc (x : E) := by
  simp only [jacobiConjugateEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Submodule.coe_equivMapOfInjective_apply]

/-- **Math.** **do Carmo Ch. 5, Corollary 3.10.**  A basis `{J_1, …, J_{n-1}}` of `𝒥^⊥`
restricts, under the endpoint evaluation `J ↦ J(L)`, to a basis of `γ'(L)^⊥`: for any basis `b`
of `𝒥^⊥ = ker(velocityFunctional g (γ 0) γ'(0))`, pushing through the isomorphism
`jacobiConjugateEquiv` yields a basis of `γ'(L)^⊥ = ker(velocityFunctional g (γ L) γ'(L))` whose
underlying tangent vectors are the endpoint values `J_i(L) = jacobiEndpointOfVel (b i)`. -/
theorem jacobiConjugateBasis
    (hab : (0 : ℝ) < L) (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγc : ∀ t ∈ Icc (0 : ℝ) L, ContinuousAt γ t)
    {β : M} (hsrc : ∀ τ ∈ Icc (0 : ℝ) L, γ τ ∈ (chartAt H β).source)
    (hv0 : mfderiv 𝓘(ℝ, ℝ) I γ 0 1 ≠ 0) (hvL : mfderiv 𝓘(ℝ, ℝ) I γ L 1 ≠ 0)
    (hnc : ¬ IsConjugatePointAt (I := I) g γ L)
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ
      (LinearMap.ker (velocityFunctional (I := I) g (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)))) :
    ∃ c : Module.Basis ι ℝ
      (LinearMap.ker (velocityFunctional (I := I) g (γ L) (mfderiv 𝓘(ℝ, ℝ) I γ L 1))),
      ∀ i, (c i : E) = jacobiEndpointOfVel hab hgeo hγc (b i : E) := by
  refine ⟨b.map (jacobiConjugateEquiv hab hgeo hγc hsrc hv0 hvL hnc), fun i => ?_⟩
  rw [Module.Basis.map_apply, jacobiConjugateEquiv_coe]

end Riemannian.Jacobi

end
