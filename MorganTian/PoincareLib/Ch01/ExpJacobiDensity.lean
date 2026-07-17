import PoincareLib.Ch01.ComparisonMinimizing
import PoincareLib.Ch01.FrameLiftDeterminant

/-!
# Poincaré Ch. 1, §1.4 — the Riemannian Jacobian as a single antitone radial density

This file surfaces the matrix Jacobi datum `𝒥` that `FrameLiftDeterminant` (gap `(a'3)`) kept
hidden.  `FrameLiftDeterminant.expRiemannianJacobian_smul_factor_of_not_conjugate` proves, for a
*single* radius `r`, that `ρ_p(r·u) = √(det gᵢⱼ(p)) · det Φ` with `0 < det Φ ≤ (sn_k(r)/r)^{n-1}`,
but the `Φ` it returns is bound to a fresh Jacobi datum obtained *inside* that call, so the datum
changes with `r` and one cannot say the *ratio* is monotone.  `thm:bishop-gromov` needs a single
datum whose polar density ratio is antitone across all radii, tied pointwise to `ρ_p`.

The obstruction is purely bookkeeping: the frame reading `Φ = r⁻¹ • 𝒥(r)` of `d(exp_p)_{r·u}` is
proved in `PolarVolumeComparison.expDifferential_det_le_of_not_conjugate` but never exported with
`𝒥` in hand.  We factor that step out (`frameRead_eq_smul_jacobi`), so it takes the Jacobi datum as
input, and then run it against the *one* datum returned by
`ricci_curvature_comparison_of_not_conjugate` — the same datum whose antitone ratio and `→ 1`
normalisation that theorem already delivers.  The result is `expRiemannianJacobian_polarDensity_*`:

  `∃ 𝒥, (ν(t)/sn_k(t)^{n-1} antitone) ∧ (→ 1) ∧ ∀ t, ρ_p(t·u) = √(det g_p) · (ν(t)/t^{n-1})`,

with `ν = polarDensity 𝒥`.  This is the pointwise input `Ch01/BishopGromovBall.lean`'s
`bishop_gromov_ball` consumes, now bound to a genuine per-direction radial density.

Blueprint: `thm:bishop-gromov` (item `(a'3)`, "surface `𝒥`"), `lem:volume-element-comparison`.
-/

open Set Filter Riemannian Module Matrix
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic Riemannian.Tensor

-- Diamond-free model-space block (see `FrameLiftDeterminant`): no standalone `[NormedSpace ℝ E]`,
-- so every `NormedSpace ℝ E` slot of a referenced frame lemma is filled by
-- `InnerProductSpace.toNormedSpace`, collapsing the model-space instance diamond.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ### The frame reading of `d(exp_p)_{r·u}`, with the Jacobi datum in hand -/

/-- **Math.** **The frame reading of `d(exp_p)_{r·u}` is `r⁻¹ • 𝒥(r)`** — the step factored out of
`PolarVolumeComparison.expDifferential_det_le_of_not_conjugate` so the matrix Jacobi datum `𝒥` is
an *input*, not an existentially bound output.

Given the `g`-orthonormal frame `e` along `γ_u` and a matrix Jacobi datum `𝒥` satisfying the
**column clause** `frameVec J t = 𝒥(t)(frameVec ∇J 0)` for every Jacobi field with `J 0 = 0`
(exactly the data `ricci_curvature_comparison_of_not_conjugate` returns), the differential of
`exp_p` at `r·u`, read in the frame, is `r⁻¹ • 𝒥(r)`.  This is `lem:exponential-differential-jacobi`
composed with the column clause and the time rescaling `γ_{r·u} = γ_u(r·−)`.

Blueprint: `lem:geodesic-polar-form`(4), `thm:bishop-gromov` (item `(a'3)`). -/
theorem frameRead_eq_smul_jacobi
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {r₀ : ℝ} {u : E}
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (𝒥 : ℝ → 𝔼 →L[ℝ] 𝔼)
    (horth : ∀ t ∈ Icc (-1 : ℝ) (r₀ + 1), ∀ i j,
      g.metricInner (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t)
        (e i t : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t)) (e j t)
        = if i = j then 1 else 0)
    (hcol : ∀ J DJ : ℝ → E,
      IsJacobiFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p))
        J DJ (-1) (r₀ + 1) → J 0 = 0 →
      ∀ t ∈ Icc (0 : ℝ) r₀,
        frameVec (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e J t
          = 𝒥 t (frameVec (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e DJ 0))
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀) :
    ∃ (ζ : M) (D : E →L[ℝ] E),
      expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D (r • u) ∧
      (∀ x : 𝔼, (r⁻¹ • 𝒥 r) x =
        frameVec (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e
          (fun _ => tangentCoordChange I ζ
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
              (D (frameLift (I := I) g
                    (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e 0 x)))
          r) := by
  classical
  have hr₀ : 0 < r₀ := hr.trans hrr₀
  have hrne : r ≠ 0 := ne_of_gt hr
  set γ : ℝ → M := globalGeodesic (I := I) g hg p (u : TangentSpace I p) with hγdef
  have hγgeo : IsGeodesic (I := I) g γ := isGeodesic_globalGeodesic g hg p (u : TangentSpace I p)
  have hγcont : Continuous γ := continuous_globalGeodesic g hg p (u : TangentSpace I p)
  set a : ℝ := -1 with hadef
  set b : ℝ := r₀ + 1 with hbdef
  have ha0 : a < 0 := by rw [hadef]; norm_num
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have hgeoOn : IsGeodesicOn (I := I) g γ (Icc a b) := fun t _ => hγgeo t
  have hγc : ∀ t ∈ Icc a b, ContinuousAt γ t := fun t _ => hγcont.continuousAt
  obtain ⟨α, ζ, D, _hpα, hζ, hFD, hjac⟩ :=
    hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p ((r • u : E))
  have hsmul : globalGeodesic (I := I) g hg p ((r • u : E)) = fun s => γ (r * s) :=
    globalGeodesic_smul g hg p (u : TangentSpace I p) r
  have hfoot : expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) = γ r := by
    show globalGeodesic (I := I) g hg p ((r • u : E)) 1 = γ r
    rw [hsmul]; simp
  have hsrc : γ r ∈ (chartAt H ζ).source := by rw [← hfoot]; exact hζ
  have h0mem : (0 : ℝ) ∈ Icc a b := ⟨ha0.le, by rw [hbdef]; linarith⟩
  refine ⟨ζ, D, hζ, hFD, ?_⟩
  intro x
  set Z : E := frameLift (I := I) g γ e 0 x with hZdef
  obtain ⟨K, DK, hK, hK0, hDK0⟩ :=
    exists_isJacobiFieldAlongOn_mem (I := I) (g := g) (γ := γ) (a := a) (b := b)
      hab hgeoOn hγc h0mem (0 : E) ((r⁻¹ • Z : E))
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
  have hDZ : D Z = chartVectorRep (I := I) γ ζ K r := by
    have h := hjac (fun s => K (r * s)) (fun s => r • DK (r * s)) hJ hJ0
    rw [hDJ0] at h
    rw [h]
    simp [chartVectorRep_apply, hsmul]
  have hread : tangentCoordChange I ζ (γ r) (γ r) (D Z) = K r := by
    rw [hDZ, chartVectorRep_apply]
    exact tangentCoordChange_readback (I := I) hsrc (K r)
  have hcolK := hcol K DK hK hK0 r ⟨hr.le, hrr₀.le⟩
  have hlift : (DK 0 : TangentSpace I (γ 0)) = frameLift (I := I) g γ e 0 (r⁻¹ • x) := by
    rw [hDK0, frameLift_smul, hZdef]
  have hfv0 : frameVec (I := I) g γ e DK 0 = r⁻¹ • x :=
    frameVec_frameLift (I := I) (horth 0 h0mem) (r⁻¹ • x) DK hlift
  have hfun : (fun _ : ℝ => tangentCoordChange I ζ (γ r) (γ r) (D Z)) = (fun _ : ℝ => K r) := by
    funext s
    exact hread
  rw [hfun, ContinuousLinearMap.smul_apply]
  show r⁻¹ • 𝒥 r x = frameVec (I := I) g γ e K r
  rw [hcolK, hfv0, map_smul]

/-! ### The Riemannian Jacobian along one geodesic as a single antitone density -/

/-- **Math.** **`thm:bishop-gromov` gap `(a'3)`, single-datum form (no-conjugate hypothesis).**
For a unit vector `u` at `p` whose radial geodesic `γ_u` is free of conjugate points on `(0, r₀)`
and carries `Ric ≥ −(n−1)k`, there is *one* matrix Jacobi datum `𝒥` such that

* the polar density ratio `ν(t)/sn_k(t)^{n-1}` (`ν = polarDensity 𝒥`) is **non-increasing** on
  `(0, r₀)` and tends to `1` at `0⁺` — the Bishop–Gromov radial comparison, and
* for every `t ∈ (0, r₀)` the Riemannian Jacobian of `exp_p` factors through *that* density:

    `ρ_p(t·u) = √(det gᵢⱼ(p)) · (ν(t)/t^{n-1})`.

The first two clauses come verbatim from `ricci_curvature_comparison_of_not_conjugate`; the third is
`frameRead_eq_smul_jacobi` (frame reading `Φ = t⁻¹·𝒥(t)`) fed into
`expRiemannianJacobian_smul_eq_of_frameRead` (the frame bridge `ρ_p = √det g_p · det Φ`), with
`det(t⁻¹·𝒥(t)) = t^{-n}·det 𝒥(t) = ν(t)/t^{n-1}` by `LinearMap.det_smul`.

Blueprint: `thm:bishop-gromov` (item `(a'3)`), `lem:volume-element-comparison`. -/
theorem expRiemannianJacobian_polarDensity_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k r₀ : ℝ} {u : E} (hk : 0 ≤ k) (hr₀ : 0 < r₀)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hnc : ∀ s ∈ Ioo (0 : ℝ) r₀,
      ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
    (hric : ∀ s ∈ Icc (0 : ℝ) r₀,
      -(((Module.finrank ℝ E : ℝ) - 1) * k)
        ≤ ricciAt g g.leviCivitaConnection hLC
            (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)) :
    ∃ (e : Fin (Module.finrank ℝ E) → ℝ → E) (𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼) (C : ℝ),
      IsRadialJacobi (frameCurvOp (I := I) g
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e) 𝒥 𝒥' r₀ C ∧
      AntitoneOn (fun t => polarDensity 𝒥 t / snK k t ^ (Module.finrank ℝ E - 1)) (Ioo 0 r₀) ∧
      Tendsto (fun t => polarDensity 𝒥 t / snK k t ^ (Module.finrank ℝ E - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) r₀, 0 < polarDensity 𝒥 t) ∧
      (∀ t ∈ Ioo (0 : ℝ) r₀,
        expRiemannianJacobian (I := I) g hg p (t • u)
          = Real.sqrt ((chartGramMatrix (I := I) g p p).det)
              * (polarDensity 𝒥 t / t ^ (Module.finrank ℝ E - 1))) := by
  classical
  have hγgeo : IsGeodesic (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) :=
    isGeodesic_globalGeodesic g hg p (u : TangentSpace I p)
  have hγcont : Continuous (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) :=
    continuous_globalGeodesic g hg p (u : TangentSpace I p)
  have hspeed0 : Geodesic.speedSq (I := I) g
      (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) 0 = 1 := by
    rw [speedSq_globalGeodesic g hg p (u : TangentSpace I p), hu]
  have hspeedAll : ∀ t : ℝ, Geodesic.speedSq (I := I) g
      (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) t = 1 := by
    intro t
    rw [← hspeed0]
    exact IsGeodesicOn.speedSq_eq (I := I) (hγgeo.isGeodesicOn univ) isOpen_univ
      isPreconnected_univ hγcont.continuousOn (mem_univ t) (mem_univ 0)
  have hab : (-1 : ℝ) < r₀ + 1 := by linarith
  have hgeoOn : IsGeodesicOn (I := I) g
      (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) (Icc (-1) (r₀ + 1)) :=
    fun t _ => hγgeo t
  have hγc : ∀ t ∈ Icc (-1 : ℝ) (r₀ + 1),
      ContinuousAt (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) t :=
    fun t _ => hγcont.continuousAt
  have hspeed : ∀ t ∈ Icc (-1 : ℝ) (r₀ + 1),
      g.metricInner (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t)
        (mfderivVelocity (I := I) (E := E)
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) t)
        (mfderivVelocity (I := I) (E := E)
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) t) = 1 :=
    fun t _ => hspeedAll t
  obtain ⟨e, 𝒥, 𝒥', C, hRJ, horth, hvel, hcol, _htr, hanti, hlim, hvol⟩ :=
    ricci_curvature_comparison_of_not_conjugate (I := I) (g := g)
      (γ := globalGeodesic (I := I) g hg p (u : TangentSpace I p))
      (a := -1) (b := r₀ + 1) (B := r₀) (r₀ := r₀) (k := k)
      hab hgeoOn hγc hspeed (by norm_num) hr₀ (by linarith) hk le_rfl hdim hLC hnc hric
  have hunit : ∀ s ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 s) := fun s hs =>
    isUnit_of_not_isConjugatePointAt (I := I) hab hgeoOn hγc horth hcol (by norm_num)
      (by linarith) hs.1 hs.2.le (hnc s hs)
  have hpos : ∀ t ∈ Ioo (0 : ℝ) r₀, 0 < polarDensity 𝒥 t := fun t ht =>
    div_pos (volumeElement_pos hRJ le_rfl hunit t ht) ht.1
  refine ⟨e, 𝒥, 𝒥', C, hRJ, hanti, hlim, hpos, ?_⟩
  intro t ht
  obtain ⟨ζ, D, hsrc, hFD, hΦ⟩ :=
    frameRead_eq_smul_jacobi (I := I) g hg p e 𝒥 horth hcol ht.1 ht.2
  have htmem : t ∈ Icc (-1 : ℝ) (r₀ + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h0mem : (0 : ℝ) ∈ Icc (-1 : ℝ) (r₀ + 1) := ⟨by norm_num, by linarith⟩
  have hdetpos : 0 < LinearMap.det (((t⁻¹ • 𝒥 t : 𝔼 →L[ℝ] 𝔼) : 𝔼 →ₗ[ℝ] 𝔼)) := by
    rw [ContinuousLinearMap.coe_smul, LinearMap.det_smul, finrank_coeffSpace (E := E)]
    exact mul_pos (pow_pos (inv_pos.2 ht.1) _) (volumeElement_pos hRJ le_rfl hunit t ht)
  have hbridge := expRiemannianJacobian_smul_eq_of_frameRead (I := I) g hg p hsrc hFD
    (horth 0 h0mem) (horth t htmem) hΦ hdetpos
  rw [hbridge]
  congr 1
  -- `det (t⁻¹ • 𝒥 t) = polarDensity 𝒥 t / t ^ (n-1)`
  have htne : t ≠ 0 := ne_of_gt ht.1
  have hpowne : (t : ℝ) ^ (Module.finrank ℝ E - 1) ≠ 0 := pow_ne_zero _ htne
  have hpowt : (t : ℝ) ^ Module.finrank ℝ E = t ^ (Module.finrank ℝ E - 1) * t := by
    conv_lhs => rw [show Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1 by omega]
    rw [pow_succ]
  rw [ContinuousLinearMap.coe_smul, LinearMap.det_smul, finrank_coeffSpace (E := E),
    polarDensity, volumeElement, inv_pow, hpowt]
  field_simp

/-- **Math.** **`thm:bishop-gromov` gap `(a'3)`, single-datum form under Morgan–Tian's hypotheses.**
The same conclusion as `expRiemannianJacobian_polarDensity_of_not_conjugate`, with the
no-conjugate-point hypothesis discharged by *minimality* of `γ_u` on `[0, r₀)`
(`prop:minimal-geodesic-no-conjugate`) — the book's own hypothesis, no upper curvature bound.

Blueprint: `thm:bishop-gromov` (item `(a'3)`), `prop:minimal-geodesic-no-conjugate`. -/
theorem expRiemannianJacobian_polarDensity_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k r₀ : ℝ} {u : E} (hk : 0 ≤ k) (hr₀ : 0 < r₀)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s))
    (hric : ∀ s ∈ Icc (0 : ℝ) r₀,
      -(((Module.finrank ℝ E : ℝ) - 1) * k)
        ≤ ricciAt g g.leviCivitaConnection hLC
            (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)) :
    ∃ (e : Fin (Module.finrank ℝ E) → ℝ → E) (𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼) (C : ℝ),
      IsRadialJacobi (frameCurvOp (I := I) g
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e) 𝒥 𝒥' r₀ C ∧
      AntitoneOn (fun t => polarDensity 𝒥 t / snK k t ^ (Module.finrank ℝ E - 1)) (Ioo 0 r₀) ∧
      Tendsto (fun t => polarDensity 𝒥 t / snK k t ^ (Module.finrank ℝ E - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) r₀, 0 < polarDensity 𝒥 t) ∧
      (∀ t ∈ Ioo (0 : ℝ) r₀,
        expRiemannianJacobian (I := I) g hg p (t • u)
          = Real.sqrt ((chartGramMatrix (I := I) g p p).det)
              * (polarDensity 𝒥 t / t ^ (Module.finrank ℝ E - 1))) :=
  expRiemannianJacobian_polarDensity_of_not_conjugate (I := I) g hg p hk hr₀ hdim hLC hu
    (not_isConjugatePointAt_of_minimizing_radial_Ioo (I := I) g hg p hu hmin) hric

end PoincareLib

end

#print axioms PoincareLib.frameRead_eq_smul_jacobi
#print axioms PoincareLib.expRiemannianJacobian_polarDensity_of_not_conjugate
#print axioms PoincareLib.expRiemannianJacobian_polarDensity_of_minimizing
