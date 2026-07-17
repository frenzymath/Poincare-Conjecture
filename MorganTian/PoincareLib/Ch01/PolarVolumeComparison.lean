import PoincareLib.Ch01.PolarMetricComparison

/-!
# Poincaré Ch. 1, §1.4 — the polar bridge, volume half: `|det d(exp_p)| ≤ (sn_k(r)/r)^{n-1}`

This file is the **volume** companion of `PolarMetricComparison`, and it closes part (4) of
`lem:geodesic-polar-form` — the polar volume density — by the same move that closed part (1):
*state it about `exp_p` itself, and the sphere chart disappears.*

## What Morgan–Tian write, and what we prove

Morgan–Tian's Ricci comparison bounds the polar volume element in geodesic polar coordinates
`(r, θ)`,

  `√(det g(r, θ)) ≤ sn_k(r)^{n-1}`,

which read literally asks for coordinates `θ¹,…,θ^{n-1}` on a sphere, a Gram determinant
`det g_{ij}`, and its comparison with the round `det ĝ_{ij}`. None of that is needed. The
quantity `√(det g/det ĝ)` is nothing but the **Jacobian of `exp_p`** measured between the flat
inner product `g_p` on `T_pM` and `g` at the foot: writing the polar point as `r·u` with `u` a
unit vector,

  `det d(exp_p)_{r·u} ≤ (sn_k(r)/r)^{n-1}`.                                            (★)

That is `expDifferential_det_le_of_not_conjugate` below.

## Why the exponent is `n - 1`, and where the `r` went

The radial direction is *not* distorted: by the Gauss lemma the radial column of the matrix
Jacobi field is `𝒥(r)u = r·u`, so the frame reading of `d(exp_p)_{r·u}` fixes `u`. Only the
`n-1` directions orthogonal to `u` are stretched, each by at most `sn_k(r)/r`. This is exactly
the bookkeeping already built into `polarDensity 𝒥 r = det 𝒥(r)/r` — the division by `r`
removes the radial column — and it is why `polarDensity_le_snK_pow` carries the exponent `n-1`
rather than `n`.

Concretely: the frame reading of `d(exp_p)_{r·u}` is `r⁻¹ • 𝒥(r)` (see below), so

  `det d(exp_p)_{r·u} = r^{-n}·det 𝒥(r) = r^{-(n-1)}·(det 𝒥(r)/r) = r^{-(n-1)}·polarDensity 𝒥 r`

and `polarDensity 𝒥 r ≤ sn_k(r)^{n-1}` gives (★) on the nose. Cross-check against the blueprint:
the flat polar volume of `T_pM` is `r^{n-1} dr dθ`, so Morgan–Tian's density is
`λ = r^{n-1}·det d(exp_p)_{r·u} ≤ sn_k(r)^{n-1}` — `lem:volume-element-comparison`, recovered.

## The proof, and the identity that carries it

The whole content is the **frame reading** of the differential:

  `d(exp_p)_{r·u}`, read in the `g`-orthonormal frame `e` (at `T_pM` for the source, at
  `T_{γ(r)}M` for the target), **is** `r⁻¹ • 𝒥(r)`,

`𝒥` the matrix Jacobi field of the comparison theorem. It follows from two facts already in
hand, exactly as in the metric half:

* `hasFDerivAt_chartReading_expMapGlobal` (`lem:exponential-differential-jacobi`) says
  `d(exp_p)_{r·u}(Z) = Y_Z(1)` for `Y_Z` the Jacobi field with `Y_Z(0) = 0`, `∇Y_Z(0) = Z`;
* the **column clause** of `ricci_curvature_comparison_of_not_conjugate` says `𝒥(t)` is the map
  `∇J(0) ↦ J(t)` in the frame — precisely what identifies the existentially bound `𝒥` with
  something geometric. (Without it this theorem could not be stated, let alone proved.)

Rescaling the unit-speed field `K` with `∇K(0) = r⁻¹·Z` to the speed-`r` geodesic gives
`d(exp_p)_{r·u}(Z) = K(r)`, whose frame vector is `𝒥(r)(r⁻¹·x)` — i.e. `(r⁻¹ • 𝒥(r))(x)`.
The determinant bound is then pure arithmetic on `LinearMap.det_smul`.

## What this unlocks

Together with `PolarMetricComparison` this completes the *pointwise* polar bridge: both halves of
`lem:geodesic-polar-form` that the comparison theorems need are now statements about `exp_p`.
What remains for `thm:bishop-gromov` on the manifold is the *integration* step (polar/coarea
`Vol B(p,R) = ∫_{S} ∫_0^R λ`, cut-locus truncation, model volume) — the radial core of that
integration, `bishop_gromov_radial`, is already proved.

Blueprint: `lem:geodesic-polar-form`(4), `lem:volume-element-comparison`,
`thm:ricci-curvature-comparison`, `thm:bishop-gromov`.

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

/-- The coefficient space of a `g`-orthonormal frame. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The standard orthonormal basis of the coefficient space. -/
local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-! ### Homogeneity of the frame lift -/

/-- **Math.** The frame lift `x ↦ ∑ᵢ xᵢ·Eᵢ(t)` is homogeneous: `lift(c·x) = c·lift(x)`.

Needed to turn the Jacobi datum `∇K(0) = r⁻¹·Z` (prescribed in `T_pM`) into the coefficient
datum `r⁻¹·x` (read in the frame), which is where the factor `r⁻¹` in `r⁻¹ • 𝒥(r)` comes from. -/
theorem frameLift_smul (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t c : ℝ) (x : 𝔼) :
    frameLift (I := I) g γ e t (c • x) = c • frameLift (I := I) g γ e t x := by
  classical
  show (∑ i, ⟪(𝔟 i : 𝔼), c • x⟫ • (e i t : TangentSpace I (γ t)))
      = c • ∑ i, ⟪(𝔟 i : 𝔼), x⟫ • (e i t : TangentSpace I (γ t))
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, mul_smul]

/-! ### The volume half of the polar bridge -/

/-- **Math.** **The polar volume comparison: `√(det g(r,θ)) ≤ sn_k^{n-1}(r)`, coordinate-free**
(`lem:geodesic-polar-form`(4) with the volume half of `thm:ricci-curvature-comparison`).

Let `u ∈ T_pM` be a **unit** vector (the polar direction `θ`), let `0 < r < r₀`, and suppose the
unit-speed geodesic `γ_u` has, on `(0, r₀)`,

* **no conjugate point** of `p` (`hnc`), and
* the **Ricci lower bound** `Ric(γ', γ') ≥ −(n−1)k` (`hric`).

Then the differential of `exp_p` at `r·u`, read in a `g`-orthonormal frame along `γ_u` (source
frame at `T_pM`, target frame at `T_{γ_u(r)}M`), is an endomorphism `Φ` of the coefficient space
with

  `0 < det Φ ≤ (sn_k(r)/r)^{n-1}`.

The frame-reading clause pins `Φ` to the actual differential `D` of `exp_p`: `Φ` is not merely
*some* operator with a small determinant, it *is* `d(exp_p)_{r·u}` read through the frames — and
since `frameVec`/`frameLift` are `g`-isometries onto `𝔼` (`metricInner_frameLift`, and the
orthonormality clause returned here), `det Φ` is the honest Riemannian Jacobian, independent of
which orthonormal frame was chosen up to sign, and positive.

This is Morgan–Tian's `√(det g(r, θ)) ≤ sn_k^{n-1}(r)`: their volume density
`λ(r,θ) = √(det g/det ĝ)` is `r^{n-1}·det d(exp_p)_{r·u}`, the `r^{n-1}` being the flat polar
Jacobian of `T_pM`. No sphere chart is needed to say it, and none is used to prove it.

Blueprint: `lem:geodesic-polar-form`, `lem:volume-element-comparison`,
`thm:ricci-curvature-comparison`. -/
theorem expDifferential_det_le_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k r r₀ : ℝ} (hk : 0 ≤ k) (hr : 0 < r) (hrr₀ : r < r₀)
    (hdim : 2 ≤ finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hnc : ∀ s ∈ Ioo (0 : ℝ) r₀,
      ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
    (hric : ∀ s ∈ Icc (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k)
        ≤ ricciAt g g.leviCivitaConnection hLC
            (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)) :
    ∃ (ζ : M) (D : E →L[ℝ] E) (e : Fin (finrank ℝ E) → ℝ → E) (Φ : 𝔼 →L[ℝ] 𝔼),
      -- `D` is the differential of `exp_p` at `r·u`, read in a chart `ζ` around `exp_p(r·u)`
      expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D (r • u) ∧
      -- `e` is a `g`-orthonormal frame along `γ_u`: this is what makes `det Φ` the Jacobian
      (∀ t ∈ Icc (-1 : ℝ) (r₀ + 1), ∀ i j,
        g.metricInner (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t)
          (e i t : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t))
          (e j t) = if i = j then 1 else 0) ∧
      -- `Φ` **is** `D` read in the frames — the clause that makes the bound below non-vacuous
      (∀ x : 𝔼, Φ x =
        frameVec (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e
          (fun _ => tangentCoordChange I ζ
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
              (D (frameLift (I := I) g
                    (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e 0 x)))
          r) ∧
      -- the Jacobian is positive and dominated by the model one
      0 < LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼) ∧
      LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼) ≤ (snK k r / r) ^ (finrank ℝ E - 1) := by
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
  -- the comparison interval `[a, b] = [-1, r₀ + 1]`: `0` and `r` are interior, as the theorem asks
  set a : ℝ := -1 with hadef
  set b : ℝ := r₀ + 1 with hbdef
  have ha0 : a < 0 := by rw [hadef]; norm_num
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hBb : r₀ < b := by rw [hbdef]; linarith
  have hgeoOn : IsGeodesicOn (I := I) g γ (Icc a b) := fun t _ => hγgeo t
  have hγc : ∀ t ∈ Icc a b, ContinuousAt γ t := fun t _ => hγcont.continuousAt
  have hspeed : ∀ t ∈ Icc a b,
      g.metricInner (γ t) (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) = 1 := fun t _ => hspeedAll t
  -- the Ricci comparison, in its geometric-hypothesis form
  obtain ⟨e, 𝒥, 𝒥', C, hRJ, horth, hvel, hcol, _htr, _hanti, _hlim, hvol⟩ :=
    ricci_curvature_comparison_of_not_conjugate (I := I) (g := g) (γ := γ)
      (a := a) (b := b) (B := r₀) (r₀ := r₀) (k := k)
      hab hgeoOn hγc hspeed ha0 hr₀ hBb hk le_rfl hdim
      hLC hnc hric
  -- no conjugate point ⇒ the matrix Jacobi field is invertible, so its determinant is positive
  have hunit : ∀ s ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 s) := fun s hs =>
    isUnit_of_not_isConjugatePointAt (I := I) hab hgeoOn hγc horth hcol ha0 hBb hs.1
      hs.2.le (hnc s hs)
  -- the differential of `exp_p` at `r·u`, with its Jacobi-field identification
  obtain ⟨α, ζ, D, _hpα, hζ, hFD, hjac⟩ :=
    hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p ((r • u : E))
  -- `γ_{r·u} = γ_u(r·−)`: rescaling the initial vector rescales time
  have hsmul : globalGeodesic (I := I) g hg p ((r • u : E)) = fun s => γ (r * s) :=
    globalGeodesic_smul g hg p (u : TangentSpace I p) r
  have hfoot : expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) = γ r := by
    show globalGeodesic (I := I) g hg p ((r • u : E)) 1 = γ r
    rw [hsmul]
    simp
  have hsrc : γ r ∈ (chartAt H ζ).source := by rw [← hfoot]; exact hζ
  have h0mem : (0 : ℝ) ∈ Icc a b := ⟨ha0.le, by rw [hbdef]; linarith⟩
  refine ⟨ζ, D, e, r⁻¹ • 𝒥 r, hζ, hFD, horth, ?_, ?_, ?_⟩
  · -- **the frame reading of `d(exp_p)_{r·u}` is `r⁻¹ • 𝒥(r)`**
    intro x
    set Z : E := frameLift (I := I) g γ e 0 x with hZdef
    -- the Jacobi field along the **unit-speed** `γ`, with data `K(0) = 0`, `∇K(0) = r⁻¹·Z`,
    -- prescribed at the interior time `0`
    obtain ⟨K, DK, hK, hK0, hDK0⟩ :=
      exists_isJacobiFieldAlongOn_mem (I := I) (g := g) (γ := γ) (a := a) (b := b)
        hab hgeoOn hγc h0mem (0 : E) ((r⁻¹ • Z : E))
    -- restrict to `[0, r]` and stretch by `r`: a Jacobi field along `γ_{r·u}` on `[0, 1]`
    have hKr : IsJacobiFieldAlongOn (I := I) g γ K DK 0 (r * 1) := by
      rw [mul_one]
      exact hK.mono ha0.le hr (by rw [hbdef]; linarith)
    have hJ : IsJacobiFieldAlongOn (I := I) g (fun s => γ (r * s))
        (fun s => K (r * s)) (fun s => r • DK (r * s)) 0 1 := hKr.comp_mul_left hr
    rw [← hsmul] at hJ
    have hJ0 : (fun s => K (r * s)) 0 = 0 := by simpa [mul_zero] using hK0
    have hDJ0 : (fun s => r • DK (r * s)) 0 = Z := by
      show r • DK (r * 0) = Z
      rw [mul_zero, hDK0]
      show (r • (r⁻¹ • Z) : E) = Z
      rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
    -- `d(exp_p)_{r·u}(Z) = Y_Z(1) = K(r)`, in the chart `ζ`
    have hDZ : D Z = chartVectorRep (I := I) γ ζ K r := by
      have h := hjac (fun s => K (r * s)) (fun s => r • DK (r * s)) hJ hJ0
      rw [hDJ0] at h
      rw [h]
      simp [chartVectorRep_apply, hsmul]
    -- reading the chart back gives the intrinsic vector `K(r)`
    have hread : tangentCoordChange I ζ (γ r) (γ r) (D Z) = K r := by
      rw [hDZ, chartVectorRep_apply]
      exact tangentCoordChange_readback (I := I) hsrc (K r)
    -- the column clause: `𝒥(r)` maps `∇K(0)` to `K(r)`, in the frame
    have hcolK := hcol K DK hK hK0 r ⟨hr.le, hrr₀.le⟩
    -- the frame vector of the datum `∇K(0) = r⁻¹·Z` is `r⁻¹·x`
    have hlift : (DK 0 : TangentSpace I (γ 0)) = frameLift (I := I) g γ e 0 (r⁻¹ • x) := by
      rw [hDK0, frameLift_smul, hZdef]
    have hfv0 : frameVec (I := I) g γ e DK 0 = r⁻¹ • x :=
      frameVec_frameLift (I := I) (horth 0 h0mem) (r⁻¹ • x) DK hlift
    -- assemble
    have hfun : (fun _ : ℝ => tangentCoordChange I ζ (γ r) (γ r) (D Z)) = (fun _ : ℝ => K r) := by
      funext s
      exact hread
    rw [hfun, ContinuousLinearMap.smul_apply]
    show r⁻¹ • 𝒥 r x = frameVec (I := I) g γ e K r
    rw [hcolK, hfv0, map_smul]
  · -- **positivity of the Jacobian**
    have hdet : LinearMap.det (((r⁻¹ • 𝒥 r : 𝔼 →L[ℝ] 𝔼) : 𝔼 →ₗ[ℝ] 𝔼))
        = (r⁻¹) ^ (finrank ℝ E) * volumeElement 𝒥 r := by
      rw [ContinuousLinearMap.coe_smul, LinearMap.det_smul, finrank_coeffSpace (E := E)]
      rfl
    rw [hdet]
    exact mul_pos (pow_pos (inv_pos.2 hr) _)
      (volumeElement_pos hRJ le_rfl hunit r ⟨hr, hrr₀⟩)
  · -- **the Jacobian bound `det Φ ≤ (sn_k(r)/r)^{n-1}`**
    have hdet : LinearMap.det (((r⁻¹ • 𝒥 r : 𝔼 →L[ℝ] 𝔼) : 𝔼 →ₗ[ℝ] 𝔼))
        = (r⁻¹) ^ (finrank ℝ E) * volumeElement 𝒥 r := by
      rw [ContinuousLinearMap.coe_smul, LinearMap.det_smul, finrank_coeffSpace (E := E)]
      rfl
    -- the volume element comparison: `det 𝒥(r)/r ≤ sn_k(r)^{n-1}`
    have hbound : volumeElement 𝒥 r ≤ r * snK k r ^ (finrank ℝ E - 1) := by
      have h := hvol r ⟨hr, hrr₀⟩
      rw [polarDensity, div_le_iff₀ hr] at h
      linarith
    -- `r^{-n} = r^{-(n-1)}·r^{-1}`
    have hpow : (r⁻¹ : ℝ) ^ (finrank ℝ E) = (r⁻¹) ^ (finrank ℝ E - 1) * r⁻¹ := by
      conv_lhs => rw [show finrank ℝ E = (finrank ℝ E - 1) + 1 by omega]
      rw [pow_succ]
    have hinvpos : (0 : ℝ) < (r⁻¹) ^ (finrank ℝ E - 1) := pow_pos (inv_pos.2 hr) _
    have hstep : r⁻¹ * volumeElement 𝒥 r ≤ snK k r ^ (finrank ℝ E - 1) := by
      calc r⁻¹ * volumeElement 𝒥 r
          ≤ r⁻¹ * (r * snK k r ^ (finrank ℝ E - 1)) :=
            mul_le_mul_of_nonneg_left hbound (inv_pos.2 hr).le
        _ = snK k r ^ (finrank ℝ E - 1) := by field_simp
    rw [hdet, hpow, mul_assoc]
    calc (r⁻¹ : ℝ) ^ (finrank ℝ E - 1) * (r⁻¹ * volumeElement 𝒥 r)
        ≤ (r⁻¹) ^ (finrank ℝ E - 1) * snK k r ^ (finrank ℝ E - 1) :=
          mul_le_mul_of_nonneg_left hstep hinvpos.le
      _ = (snK k r / r) ^ (finrank ℝ E - 1) := by rw [← mul_pow, ← div_eq_inv_mul]

/-! ### The form with no conjugate-point hypothesis at all -/

/-- **Math.** **The polar volume comparison from curvature bounds alone.** The same conclusion as
`expDifferential_det_le_of_not_conjugate`, but with the no-conjugate-point hypothesis
*discharged*: besides the Ricci lower bound `Ric ≥ −(n−1)k` that the comparison itself consumes,
it suffices that the sectional curvature along `γ_u` is bounded **above**,

  `K(P) ≤ K_up`,  with  `√K_up · r₀ ≤ π`

(Morgan–Tian's `r₀ ≤ π/√K_up`, with `π/√0 = +∞`). Then for every `0 < r < r₀`,

  `0 < det d(exp_p)_{r·u} ≤ (sn_k(r)/r)^{n-1}`.

The upper bound enters only through the Sturm comparison
(`not_isConjugatePointAt_of_sectionalCurvatureAt_le`), which forbids a conjugate point before
`π/√K_up`. So the hypotheses are now purely curvature bounds along `γ_u` — nothing about Jacobi
fields, conjugate points or minimality is asked of the caller.

This is *a* shape in which the volume comparison can be applied, but it is **not Morgan–Tian's**:
they get the no-conjugate-point condition from *minimality* of `γ`, not from an upper curvature
bound — and an upper bound is a genuine extra assumption, one the Ricci comparison never makes.
That route is now available: `prop:minimal-geodesic-no-conjugate` is proved, and
`expDifferential_det_le_of_minimizing` (`Ch01/ComparisonMinimizing.lean`) states this estimate
under the book's own hypotheses — minimality plus the *lower* Ricci bound, nothing else.

Blueprint: `lem:exp-pullback-volume-comparison`, `lem:volume-element-comparison`,
`thm:ricci-curvature-comparison`. -/
theorem expDifferential_det_le_of_sectionalCurvature
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k Kup r r₀ : ℝ} (hk : 0 ≤ k) (hKup : 0 ≤ Kup)
    (hr : 0 < r) (hrr₀ : r < r₀) (hπ : Real.sqrt Kup * r₀ ≤ Real.pi)
    (hdim : 2 ≤ finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hsecUp : ∀ s ∈ Icc (0 : ℝ) r₀,
      ∀ w₁ w₂ : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s),
        sectionalCurvatureAt g g.leviCivitaConnection
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) w₁ w₂ ≤ Kup)
    (hric : ∀ s ∈ Icc (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k)
        ≤ ricciAt g g.leviCivitaConnection hLC
            (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)) :
    ∃ (ζ : M) (D : E →L[ℝ] E) (e : Fin (finrank ℝ E) → ℝ → E) (Φ : 𝔼 →L[ℝ] 𝔼),
      expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D (r • u) ∧
      (∀ t ∈ Icc (-1 : ℝ) (r₀ + 1), ∀ i j,
        g.metricInner (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t)
          (e i t : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t))
          (e j t) = if i = j then 1 else 0) ∧
      (∀ x : 𝔼, Φ x =
        frameVec (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e
          (fun _ => tangentCoordChange I ζ
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
              (D (frameLift (I := I) g
                    (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e 0 x)))
          r) ∧
      0 < LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼) ∧
      LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼) ≤ (snK k r / r) ^ (finrank ℝ E - 1) := by
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
  exact expDifferential_det_le_of_not_conjugate (I := I) g hg p hk hr hrr₀ hdim hLC hu hnc hric

end PoincareLib

end
