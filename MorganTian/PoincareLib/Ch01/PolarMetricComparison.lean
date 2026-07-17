import PoincareLib.Ch01.ComparisonGeometric
import PoincareLib.Ch01.ExpLocalDiffeo
import PoincareLib.Ch01.JacobiInterior
import PoincareLib.Ch01.JacobiRestriction

/-!
# Poincaré Ch. 1, §1.4 — the polar bridge: `exp_p^* g ≤ (sn_k(r)/r)² ·` (flat metric)

This file closes the **polar-coordinate identification** of `lem:geodesic-polar-form`(1) — the
node that has stood between the finished comparison-geometry cores and the blueprint statements
of `SCC`, `thm:ricci-curvature-comparison` and `thm:bishop-gromov`.

## What Morgan–Tian write, and what we prove

Morgan–Tian state the metric half of the sectional-curvature comparison in geodesic polar
coordinates `(r, θ)` on a cone in `T_p M`:

  `g_{ij}(r, θ) ≤ sn_k²(r) · ĝ_{ij}(θ)`,

`ĝ` the round metric of the unit sphere of `T_p M`. Read literally this needs coordinates
`θ¹,…,θ^{n-1}` on a sphere — an atlas Lean has no reason to want. But the inequality is a
statement about the **pullback metric** `exp_p^* g` alone, and in that form it needs no sphere
chart at all: writing a point of the cone as `r · u` with `u` a unit vector, and a tangent
vector there as `Z ∈ T_p M`, it says exactly

  `|d(exp_p)_{r·u}(Z)|²_g ≤ (sn_k(r)/r)² · |Z|²_g`.                                     (★)

(The `1/r` is the usual polar bookkeeping: the coordinate field `∂_{θⁱ}` at radius `r` is the
image of a vector of length `r` in `T_p M`, so Morgan–Tian's `sn_k²(r) ĝ_{ij}` becomes
`(sn_k(r)/r)²` once `Z` is measured in `T_pM` rather than on the sphere of radius `r`.)

That is `expDifferential_metricInner_le_of_not_conjugate` below, and it is the whole content of
part (1): the coordinate fields `∂_{θⁱ}` of the polar chart *are* the Jacobi fields vanishing at
`p` (`lem:exponential-differential-jacobi`), and the comparison for those is already proved.

## The proof, in one line

Compose the two theorems that were already in hand, across a unit-speed rescaling:

* `sectional_curvature_comparison_of_not_conjugate` (`ComparisonGeometric`) bounds a Jacobi field
  along a **unit-speed** geodesic: `|K(r)|² ≤ sn_k(r)²·|∇K(0)|²`;
* `hasFDerivAt_chartReading_expMapGlobal` (`lem:exponential-differential-jacobi`) identifies
  `d(exp_p)_v(Z)` with `Y_Z(1)`, `Y_Z` the Jacobi field along `γ_v` with `Y_Z(0) = 0`,
  `∇Y_Z(0) = Z`.

The two speak about different geodesics — `γ_u` at unit speed, `γ_{r·u}` at speed `r` — and the
bridge is `JacobiRescale`: with `γ_{r·u} = γ_u(r·−)` (`globalGeodesic_smul`), the Jacobi field
`K` along `γ_u` with `∇K(0) = r⁻¹·Z` rescales to `Y_Z = K(r·−)` along `γ_{r·u}`, whose data at
`0` is `r·(r⁻¹·Z) = Z` — so `d(exp_p)_{r·u}(Z) = Y_Z(1) = K(r)`, and (★) is the unit-speed bound
read at parameter `r`, with `|∇K(0)|² = r⁻²|Z|²` supplying the `1/r²`.

The only genuinely new ingredient is that the comparison theorem's Jacobi clause quantifies over
fields on the *whole* interval `[a, b]` with `a < 0 < b`, while rescaling naturally produces one
on `[0, r]`. We therefore build `K` on `[a, b]` from the outset, with data prescribed at the
**interior** time `0` (`exists_isJacobiFieldAlongOn_mem`, `JacobiInterior`) — precisely the
lemma the previous session built for this purpose — and restrict it to `[0, r]` afterwards.

## What this unlocks

`SCC`'s metric half now holds in the form the blueprint states it, about `exp_p` and not merely
about an abstract Jacobi field; the same statement is the pointwise input that
`thm:ricci-curvature-comparison` integrates (`√det g ≤ sn_k^{n-1}`) and that `thm:bishop-gromov`
integrates once more in `r`.

Blueprint: `lem:geodesic-polar-form`(1), `thm:sectional-curvature-comparison`,
`lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Riemannian Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]

/-- **Math.** **The polar bridge: `g_{ij}(r, θ) ≤ sn_k²(r) ĝ_{ij}(θ)`, coordinate-free**
(`lem:geodesic-polar-form`(1) together with the metric half of `SCC`).

Let `u ∈ T_p M` be a **unit** vector (the polar direction `θ`), let `0 < r < r₀`, and suppose the
unit-speed geodesic `γ_u` has, on the whole parameter range `(0, r₀)`,

* **no conjugate point** of `p` (`hnc`), and
* every sectional curvature bounded below by `−k` (`hsec`).

Then `exp_p` is differentiable at `r·u`, and its differential there **contracts by the factor
`sn_k(r)/r`** relative to the model: for every `Z ∈ T_p M`,

  `|d(exp_p)_{r·u}(Z)|²_g ≤ (sn_k(r)/r)² · |Z|²_g`.

The left side is the pullback metric `(exp_p^* g)_{r·u}(Z, Z)`, read — as everywhere in this
development — through the Gram form of a chart `ζ` around `exp_p(r·u)`; the chart drops out of
the statement's meaning by `metricInner_eq_chartMetricInner_rep`.

This is Morgan–Tian's `g_{ij}(r, θ) ≤ sn_k²(r) ĝ_{ij}(θ)`: their `∂_{θⁱ}` at the polar point
`(r, θ)` is `d(exp_p)_{r·u}(Zᵢ)` for `Zᵢ` an orthonormal basis of `u^⊥`, and the round metric
contributes the `r²` that turns `sn_k²(r)` into `(sn_k(r)/r)²`. No sphere chart is needed to say
it, and none is used to prove it.

Blueprint: `lem:geodesic-polar-form`, `thm:sectional-curvature-comparison`. -/
theorem expDifferential_metricInner_le_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k r r₀ : ℝ} (hk : 0 ≤ k) (hr : 0 < r) (hrr₀ : r < r₀)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hnc : ∀ s ∈ Ioo (0 : ℝ) r₀,
      ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
    (hsec : ∀ s ∈ Ioo (0 : ℝ) r₀,
      ∀ w₁ w₂ : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s),
        -k ≤ sectionalCurvatureAt g g.leviCivitaConnection
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) w₁ w₂) :
    ∃ (ζ : M) (D : E →L[ℝ] E),
      expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D (r • u) ∧
      ∀ Z : E,
        chartMetricInner (I := I) g ζ
            (extChartAt I ζ (expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p)))
            (D Z) (D Z)
          ≤ (snK k r / r) ^ 2
              * g.metricInner p (Z : TangentSpace I p) (Z : TangentSpace I p) := by
  classical
  have hr₀ : 0 < r₀ := hr.trans hrr₀
  have hrne : r ≠ 0 := ne_of_gt hr
  -- the unit-speed geodesic in the direction `u`
  set γ : ℝ → M := globalGeodesic (I := I) g hg p (u : TangentSpace I p) with hγdef
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p (u : TangentSpace I p)
  have hγgeo : IsGeodesic (I := I) g γ := isGeodesic_globalGeodesic g hg p (u : TangentSpace I p)
  have hγcont : Continuous γ := continuous_globalGeodesic g hg p (u : TangentSpace I p)
  -- `γ` is unit-speed at time `0`, hence — speed being constant along a geodesic — at every time
  have hspeed0 : Geodesic.speedSq (I := I) g γ 0 = 1 := by
    rw [hγdef, speedSq_globalGeodesic g hg p (u : TangentSpace I p), hu]
  have hspeedAll : ∀ t : ℝ, Geodesic.speedSq (I := I) g γ t = 1 := by
    intro t
    rw [← hspeed0]
    exact IsGeodesicOn.speedSq_eq (I := I) (hγgeo.isGeodesicOn univ) isOpen_univ
      isPreconnected_univ hγcont.continuousOn (mem_univ t) (mem_univ 0)
  -- the comparison interval `[a, b] = [-1, r₀ + 1]`: `0` and `r` are interior, as SCC demands
  set a : ℝ := -1 with hadef
  set b : ℝ := r₀ + 1 with hbdef
  have ha0 : a < 0 := by rw [hadef]; norm_num
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hgeoOn : IsGeodesicOn (I := I) g γ (Icc a b) := fun t _ => hγgeo t
  have hγc : ∀ t ∈ Icc a b, ContinuousAt γ t := fun t _ => hγcont.continuousAt
  have hspeed : ∀ t ∈ Icc a b,
      g.metricInner (γ t) (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) = 1 := fun t _ => hspeedAll t
  -- the sectional-curvature comparison, in its geometric-hypothesis form
  obtain ⟨e, 𝒥, 𝒥', C, hRJ, horth, hvel, _hcol, h1, _h2⟩ :=
    sectional_curvature_comparison_of_not_conjugate (I := I) (g := g) (γ := γ)
      (a := a) (b := b) (B := r₀) (r₀ := r₀) (k := k)
      hab hgeoOn hγc hspeed ha0 hr₀ (by rw [hbdef]; linarith) hk le_rfl hnc hsec
  -- the differential of `exp_p` at `r·u`, with its Jacobi-field identification
  obtain ⟨α, ζ, D, _hpα, hζ, hFD, hjac⟩ :=
    hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p ((r • u : E))
  -- `γ_{r·u} = γ_u(r·−)`: rescaling the initial vector rescales time
  have hsmul : globalGeodesic (I := I) g hg p ((r • u : E)) = fun s => γ (r * s) :=
    globalGeodesic_smul g hg p (u : TangentSpace I p) r
  -- the foot `exp_p(r·u)` of the differential is `γ r`
  have hfoot : expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) = γ r := by
    show globalGeodesic (I := I) g hg p ((r • u : E)) 1 = γ r
    rw [hsmul]
    simp
  have hsrc : γ r ∈ (chartAt H ζ).source := by rw [← hfoot]; exact hζ
  refine ⟨ζ, D, hζ, hFD, ?_⟩
  intro Z
  -- the Jacobi field along the **unit-speed** `γ`, with data `K(0) = 0`, `∇K(0) = r⁻¹·Z`,
  -- prescribed at the interior time `0` — this is what `JacobiInterior` was built for
  have h0mem : (0 : ℝ) ∈ Icc a b := ⟨ha0.le, by rw [hbdef]; linarith⟩
  obtain ⟨K, DK, hK, hK0, hDK0⟩ :=
    exists_isJacobiFieldAlongOn_mem (I := I) (g := g) (γ := γ) (a := a) (b := b)
      hab hgeoOn hγc h0mem (0 : E) ((r⁻¹ • Z : E))
  -- restrict it to `[0, r]` and stretch by `r`: a Jacobi field along `γ_{r·u}` on `[0, 1]`
  have hKr : IsJacobiFieldAlongOn (I := I) g γ K DK 0 (r * 1) := by
    rw [mul_one]
    exact hK.mono ha0.le hr (by rw [hbdef]; linarith)
  have hJ : IsJacobiFieldAlongOn (I := I) g (fun s => γ (r * s))
      (fun s => K (r * s)) (fun s => r • DK (r * s)) 0 1 := hKr.comp_mul_left hr
  rw [← hsmul] at hJ
  -- its data at time `0` is `(0, Z)`, so it is *the* field computing `d(exp_p)_{r·u}(Z)`
  have hJ0 : (fun s => K (r * s)) 0 = 0 := by simpa [mul_zero] using hK0
  have hDJ0 : (fun s => r • DK (r * s)) 0 = Z := by
    show r • DK (r * 0) = Z
    rw [mul_zero, hDK0]
    show (r • (r⁻¹ • Z) : E) = Z
    rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
  -- `d(exp_p)_{r·u}(Z) = Y_Z(1) = K(r)`
  have hDZ : D Z = chartVectorRep (I := I) γ ζ K r := by
    have h := hjac (fun s => K (r * s)) (fun s => r • DK (r * s)) hJ hJ0
    rw [hDJ0] at h
    rw [h]
    simp [chartVectorRep_apply, hsmul]
  -- the chart Gram form of `d(exp_p)_{r·u}(Z)` is the intrinsic `|K(r)|²_g`
  have hchart : chartMetricInner (I := I) g ζ
      (extChartAt I ζ (expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p)))
      (D Z) (D Z)
      = g.metricInner (γ r) (K r : TangentSpace I (γ r)) (K r) := by
    rw [hfoot, hDZ]
    exact (metricInner_eq_chartMetricInner_rep (I := I) g (γ := γ) (α := ζ) (τ := r) hsrc K K).symm
  rw [hchart]
  -- the unit-speed comparison at parameter `r`, with `|∇K(0)|² = r⁻²·|Z|²`
  have hcmp := h1 K DK hK hK0 r ⟨hr, hrr₀⟩
  rw [hγ0, hDK0] at hcmp
  have hsm : g.metricInner p ((r⁻¹ • Z : E) : TangentSpace I p) ((r⁻¹ • Z : E) : TangentSpace I p)
      = (r⁻¹ * r⁻¹) * g.metricInner p (Z : TangentSpace I p) (Z : TangentSpace I p) :=
    metricInner_smul_self (I := I) g p r⁻¹ (Z : TangentSpace I p)
  rw [hsm] at hcmp
  refine hcmp.trans (le_of_eq ?_)
  field_simp

/-! ### The form with no conjugate-point hypothesis at all -/

/-- **Math.** **The polar metric comparison from curvature bounds alone.** The same conclusion as
`expDifferential_metricInner_le_of_not_conjugate`, but with the no-conjugate-point hypothesis
*discharged*: it suffices that the sectional curvature along `γ_u` is **two-sidedly** bounded,

  `−k ≤ K(P) ≤ K_up`,  with  `√K_up · r₀ ≤ π`

(Morgan–Tian's `r₀ ≤ π/√K_up`, with `π/√0 = +∞`). Then for every `0 < r < r₀` and every
`Z ∈ T_p M`,

  `|d(exp_p)_{r·u}(Z)|²_g ≤ (sn_k(r)/r)² · |Z|²_g`.

The upper bound enters only through the Sturm comparison
(`not_isConjugatePointAt_of_sectionalCurvatureAt_le`), which forbids a conjugate point before
`π/√K_up`; the lower bound `−k` is what the comparison itself consumes. So the hypotheses are now
purely curvature bounds along `γ_u` — nothing about Jacobi fields, conjugate points, or
minimality is asked of the caller.

This is *a* shape in which `SCC` can be applied, but it is **not Morgan–Tian's**: they get the
no-conjugate-point condition from *minimality* of `γ`, not from an upper curvature bound.  That
route is now available too — `prop:minimal-geodesic-no-conjugate` is proved, and
`expDifferential_metricInner_le_of_minimizing` (`Ch01/ComparisonMinimizing.lean`) states this
estimate under the book's own hypotheses, asking the caller for **no upper curvature bound**.
Prefer that form when the geodesic is known to minimize; prefer this one when it is not (it is
what `lem:local-diffeomorphism-bounded-curvature` wants).

Blueprint: `lem:geodesic-polar-form`, `thm:sectional-curvature-comparison`,
`lem:local-diffeomorphism-bounded-curvature`. -/
theorem expDifferential_metricInner_le_of_sectionalCurvature
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k Kup r r₀ : ℝ} (hk : 0 ≤ k) (hKup : 0 ≤ Kup)
    (hr : 0 < r) (hrr₀ : r < r₀) (hπ : Real.sqrt Kup * r₀ ≤ Real.pi)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hsecLow : ∀ s ∈ Ioo (0 : ℝ) r₀,
      ∀ w₁ w₂ : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s),
        -k ≤ sectionalCurvatureAt g g.leviCivitaConnection
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) w₁ w₂)
    (hsecUp : ∀ s ∈ Icc (0 : ℝ) r₀,
      ∀ w₁ w₂ : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s),
        sectionalCurvatureAt g g.leviCivitaConnection
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) w₁ w₂ ≤ Kup) :
    ∃ (ζ : M) (D : E →L[ℝ] E),
      expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D (r • u) ∧
      ∀ Z : E,
        chartMetricInner (I := I) g ζ
            (extChartAt I ζ (expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p)))
            (D Z) (D Z)
          ≤ (snK k r / r) ^ 2
              * g.metricInner p (Z : TangentSpace I p) (Z : TangentSpace I p) := by
  classical
  set γ : ℝ → M := globalGeodesic (I := I) g hg p (u : TangentSpace I p) with hγdef
  have hγgeo : IsGeodesic (I := I) g γ := isGeodesic_globalGeodesic g hg p (u : TangentSpace I p)
  have hγcont : Continuous γ := continuous_globalGeodesic g hg p (u : TangentSpace I p)
  -- `γ` is unit-speed at every time
  have hspeed0 : Geodesic.speedSq (I := I) g γ 0 = 1 := by
    rw [hγdef, speedSq_globalGeodesic g hg p (u : TangentSpace I p), hu]
  have hspeedAll : ∀ t : ℝ, Geodesic.speedSq (I := I) g γ t = 1 := by
    intro t
    rw [← hspeed0]
    exact IsGeodesicOn.speedSq_eq (I := I) (hγgeo.isGeodesicOn univ) isOpen_univ
      isPreconnected_univ hγcont.continuousOn (mem_univ t) (mem_univ 0)
  -- the Sturm comparison forbids a conjugate point at any `s < r₀ ≤ π/√K_up`
  have hnc : ∀ s ∈ Ioo (0 : ℝ) r₀, ¬ IsConjugatePointAt (I := I) g γ s := by
    intro s hs
    have hsπ : Real.sqrt Kup * s < Real.pi := by
      rcases eq_or_lt_of_le (Real.sqrt_nonneg Kup) with hK0 | hK0
      · rw [← hK0, zero_mul]; exact Real.pi_pos
      · exact lt_of_lt_of_le (by nlinarith [hs.2]) hπ
    refine not_isConjugatePointAt_of_sectionalCurvatureAt_le (I := I) (g := g) (γ := γ)
      hs.1 hKup hsπ (fun t _ => hγgeo t) (fun t _ => hγcont.continuousAt)
      (fun t _ => hspeedAll t) (fun t ht => ?_)
    exact hsecUp t ⟨ht.1, ht.2.trans hs.2.le⟩
  exact expDifferential_metricInner_le_of_not_conjugate (I := I) g hg p hk hr hrr₀ hu hnc hsecLow

end PoincareLib

end
