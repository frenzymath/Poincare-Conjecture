import MorganTianLib.Ch01.PolarVolumeComparison
import MorganTianLib.Ch01.FrameChartDeterminant

/-!
# Morgan–Tian Ch. 1, §1.4 — the frame-lift determinant assembly (BG gap `(a'3)`)

`FrameChartDeterminant.lean` proved the linear-algebra **kernel** of Bishop–Gromov gap `(a'3)`: for a
`g`-orthonormal frame `f` at `x`, `(det((finBasis).toMatrix f))² · det(chartGramMatrix g x x) = 1`.
This file is the **assembly** that turns that kernel, together with the frame reading of `d(exp_p)`
produced by `PolarVolumeComparison.expDifferential_det_le_of_not_conjugate`, into the pointwise
identity

  `ρ_p(r·u)  =  √(det gᵢⱼ(p)) · det Φ`,

where `ρ_p = expRiemannianJacobian` is the chart-coordinate Jacobian density of `exp_p`, `Φ` is the
frame reading of `d(exp_p)_{r·u}` (an endomorphism of the coefficient space `𝔼`), and
`C_p = √(det gᵢⱼ(p))` is the metric volume of the chart-coordinate cube at `p`.

## The determinant chain

Write `γ` for the unit-speed geodesic in the direction `u`, `q = γ(r) = exp_p(r·u)`, and let `L_t`
be the `g`-orthonormal frame lift `𝔼 ≃ T_{γ(t)}M`.  The frame reading unfolds to a composite

  `Φ  =  L_r⁻¹ ∘ Rd ∘ D ∘ L₀`,      `Rd = tangentCoordChange ζ→(γr)`,  `D = d(exp_p)` in chart `ζ`.

Its determinant factors (`LinearMap.det_conj` + `LinearMap.det_comp`) as

  `det Φ = det(Rd) · det(D) · det(L_r⁻¹ ∘ L₀)`,   `det(L_r⁻¹ ∘ L₀) = det M₀ / det M_r`,

where `M_t = (finBasis).toMatrix (fun i => e i t)` is the frame matrix.  The kernel gives
`(det M_t)² · det(chartGram g (γt)(γt)) = 1`, so `|det M_t| = 1/√(det g_{γt})`; and the
determinant transformation law (`sqrt_chartGramMatrix_det_change`, `abs_det_tangentCoordChange_mul`)
gives `|det Rd| = √(det g_ζ)/√(det g_{γr})`.  Multiplying,

  `√(det g_p) · |det Φ| = |det D| · √(det g_ζ) = ρ_p(r·u)`,

and since `det Φ > 0` the absolute value drops, giving the stated identity.

## Why this is the last algebraic step of `(a'3)`

Combined with `det Φ = r^{-n} · det 𝒥(r) = polarDensity 𝒥 r / r^{n-1}` (the frame reading of
`expDifferential_det_le_of_not_conjugate`), this makes the manifold Jacobian density `ρ_p` a fixed
constant `C_p` times the radial polar density `polarDensity 𝒥` whose monotone/normalized ratio is
already controlled by `BishopGromov.bishop_gromov_radial`.

Blueprint: `thm:bishop-gromov` (item `(a'3)`), `lem:volume-element-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Riemannian Module Matrix
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic Riemannian.Tensor

-- Diamond-free model-space block: no standalone `[NormedSpace ℝ E]`.  The frame machinery
-- (`frameLift`, `frameVec`, `expDifferential_det_le_of_not_conjugate`) is defined in a block with a
-- standalone `[NormedSpace ℝ E]`; referencing it here fills that slot with
-- `InnerProductSpace.toNormedSpace`, so the model-space diamond collapses.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-! ### The frame lift as a linear equivalence -/

/-- **Math.** The frame lift `x ↦ ∑ᵢ xᵢ·eᵢ(t)`, packaged as a linear map `𝔼 →ₗ E` (the codomain is
the model space `E`, not the type-synonym `T_{γt}M`, so that the frame lifts at different times share
one codomain and their determinants compose). Linearity is `inner_add_right`/`add_smul` (additivity)
and `frameLift_smul` (homogeneity). -/
def frameLiftLM (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) : 𝔼 →ₗ[ℝ] E where
  toFun x := frameLift (I := I) g γ e t x
  map_add' x y := by
    show frameLift (I := I) g γ e t (x + y)
      = frameLift (I := I) g γ e t x + frameLift (I := I) g γ e t y
    simp only [frameLift, inner_add_right, add_smul]
    exact Finset.sum_add_distrib
  map_smul' c x := by
    show frameLift (I := I) g γ e t (c • x) = c • frameLift (I := I) g γ e t x
    exact frameLift_smul (I := I) g γ e t c x

@[simp] theorem frameLiftLM_apply (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) (x : 𝔼) :
    frameLiftLM (I := I) g γ e t x = frameLift (I := I) g γ e t x := rfl

/-- **Math.** The coefficient map at a single point `w ↦ ∑ᵢ ⟨w, eᵢ(t)⟩_g·bᵢ`, packaged as a linear
map `E →ₗ 𝔼`.  It is the inverse of `frameLiftLM` on a `g`-orthonormal frame.  Built as a sum of
`smulRight`s of the flipped metric form, so linearity is automatic. -/
def frameVecLM (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) : E →ₗ[ℝ] 𝔼 :=
  ∑ i, LinearMap.smulRight
    (((metricBilin (I := I) g (γ t)).flip (e i t)) : E →ₗ[ℝ] ℝ) (𝔟 i : 𝔼)

theorem frameVecLM_apply (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) (w : E) :
    frameVecLM (I := I) g γ e t w = frameVec (I := I) g γ e (fun _ => w) t := by
  simp only [frameVecLM, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply]
  rfl

/-- **Math.** The frame lift is a linear **equivalence** `𝔼 ≃ E` on a `g`-orthonormal frame,
with inverse the coefficient map `frameVecLM`.  The two round-trip identities are
`frameLift_frameVec` and `frameVec_frameLift`. -/
def frameLiftEquiv (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ)
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0) : 𝔼 ≃ₗ[ℝ] E :=
  LinearEquiv.ofLinear (frameLiftLM (I := I) g γ e t) (frameVecLM (I := I) g γ e t)
    (by
      refine LinearMap.ext fun w => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, frameLiftLM_apply, frameVecLM_apply,
        LinearMap.id_apply]
      exact frameLift_frameVec (I := I) horth (fun _ => w))
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, frameLiftLM_apply, frameVecLM_apply,
        LinearMap.id_apply]
      exact frameVec_frameLift (I := I) horth x (fun _ => frameLift (I := I) g γ e t x) rfl)

@[simp] theorem frameLiftEquiv_apply (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ)
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0) (x : 𝔼) :
    frameLiftEquiv (I := I) g γ e t horth x = frameLift (I := I) g γ e t x := rfl

@[simp] theorem frameLiftEquiv_symm_apply (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ)
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0) (w : E) :
    (frameLiftEquiv (I := I) g γ e t horth).symm w = frameVec (I := I) g γ e (fun _ => w) t := by
  show frameVecLM (I := I) g γ e t w = _
  exact frameVecLM_apply (I := I) g γ e t w

/-- **Math.** The frame lift sends the `j`-th standard basis vector to the `j`-th frame vector:
`frameLift t bⱼ = eⱼ(t)`, since `⟨bᵢ, bⱼ⟩ = δᵢⱼ`. -/
theorem frameLift_basisFun (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) (j : Fin (Module.finrank ℝ E)) :
    frameLift (I := I) g γ e t (𝔟 j) = (e j t : TangentSpace I (γ t)) := by
  classical
  show ∑ i, ⟪(𝔟 i : 𝔼), (𝔟 j : 𝔼)⟫ • (e i t : TangentSpace I (γ t)) = _
  simp only [basisFun_inner, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- **Math.** The underlying linear map of `frameLiftEquiv` is `frameLiftLM` (by `ofLinear`). -/
theorem frameLiftEquiv_toLinearMap (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ)
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0) :
    (frameLiftEquiv (I := I) g γ e t horth).toLinearMap = frameLiftLM (I := I) g γ e t := rfl

/-- **Math.** The matrix of the frame lift, in the standard basis of `𝔼` and the model basis
`finBasis` of `T_{γt}M`, is the **frame matrix** `M_t = (finBasis).toMatrix (fun i => eᵢ(t))`
— the change-of-basis matrix from the frame to the coordinate frame. -/
theorem toMatrix_frameLiftLM (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
        (Module.finBasis ℝ E) (frameLiftLM (I := I) g γ e t)
      = (Module.finBasis ℝ E).toMatrix (fun i => e i t) := by
  ext i j
  rw [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis]
  exact congrArg (fun v => (Module.finBasis ℝ E).repr v i) (frameLift_basisFun (I := I) g γ e t j)

/-! ### The pointwise `(a'3)` identity -/

/-- **Math.** **Bishop–Gromov gap `(a'3)`, pointwise.** The chart-coordinate Jacobian density
`ρ_p = expRiemannianJacobian` of `exp_p` at `r·u` equals the constant `C_p = √(det gᵢⱼ(p))` times
the determinant of the frame reading `Φ` of `d(exp_p)_{r·u}`:

  `ρ_p(r·u) = √(det gᵢⱼ(p)) · det Φ`.

The hypotheses are exactly the data returned by `expDifferential_det_le_of_not_conjugate`: a chart
`ζ` around `exp_p(r·u)`, the differential `D` of `exp_p` there, a `g`-orthonormal frame `e` along
the geodesic (at the endpoints `0` and `r`), the frame-reading formula for `Φ`, and positivity of
`det Φ` (which fixes the sign in the change of frames).

Proof: read `ρ_p` in the chart `ζ` (`hasRiemannianJacobianOn_expMapGlobal`) as `|det D|·√(det g_ζ)`;
unfold `Φ = L_r⁻¹ ∘ Rd ∘ D ∘ L₀` and take determinants (`LinearMap.det_conj`, `LinearMap.det_comp`);
substitute the frame-matrix kernel `|det M_t|·√(det g_{γt}) = 1`
(`finBasisFrameMatrix_det_sq_mul_chartGramMatrix_det`) at `t = 0, r` and the readback
`|det Rd|·√(det g_{γr}) = √(det g_ζ)` (`sqrt_chartGramMatrix_det_change`,
`abs_det_tangentCoordChange_mul`).  The chain collapses to `√(det g_p)·det Φ = |det D|·√(det g_ζ)`.

Blueprint: `thm:bishop-gromov` (item `(a'3)`). -/
theorem expRiemannianJacobian_smul_eq_of_frameRead
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {r : ℝ} {u : E} {ζ : M} {D : E →L[ℝ] E}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {Φ : 𝔼 →L[ℝ] 𝔼}
    (hsrc : expMapGlobal (I := I) g hg p ((r • u : E)) ∈ (chartAt H ζ).source)
    (hFD : HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D (r • u))
    (horth0 : ∀ i j,
      g.metricInner (globalGeodesic (I := I) g hg p (u : TangentSpace I p) 0)
        (e i 0 : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) 0)) (e j 0)
      = if i = j then 1 else 0)
    (horthr : ∀ i j,
      g.metricInner (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
        (e i r : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)) (e j r)
      = if i = j then 1 else 0)
    (hΦ : ∀ x : 𝔼, Φ x =
      frameVec (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e
        (fun _ => tangentCoordChange I ζ
            (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
            (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
            (D (frameLift (I := I) g
                  (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e 0 x)))
        r)
    (hdetpos : 0 < LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼)) :
    expRiemannianJacobian (I := I) g hg p (r • u)
      = Real.sqrt ((chartGramMatrix (I := I) g p p).det) * LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼) := by
  classical
  set γ : ℝ → M := globalGeodesic (I := I) g hg p (u : TangentSpace I p) with hγ
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p (u : TangentSpace I p)
  have hfoot : expMapGlobal (I := I) g hg p ((r • u : E)) = γ r := by
    have hsmul : globalGeodesic (I := I) g hg p ((r • u : E)) = fun s => γ (r * s) :=
      globalGeodesic_smul g hg p (u : TangentSpace I p) r
    show globalGeodesic (I := I) g hg p ((r • u : E)) 1 = γ r
    rw [hsmul]; simp
  have hαsrc : expMapGlobal (I := I) g hg p ((r • u : E)) ∈ (extChartAt I ζ).source := by
    rw [extChartAt_source]; exact hsrc
  have hsrcγ : γ r ∈ (chartAt H ζ).source := hfoot ▸ hsrc
  -- self-chart trivialization baseSet membership, for the Gram-determinant positivity
  have hbase : ∀ x : M, x ∈ (trivializationAt E (TangentSpace I) x).baseSet := fun x => by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x
  -- STEP E: read `ρ_p` in the chart `ζ`
  have hERJ : expRiemannianJacobian (I := I) g hg p (r • u)
      = |D.det| * Real.sqrt ((chartGramMatrix (I := I) g ζ (γ r)).det) := by
    obtain ⟨D', hD', heq⟩ :=
      hasRiemannianJacobianOn_expMapGlobal (I := I) g hg p Set.univ ζ (r • u) (Set.mem_univ _) hαsrc
    rw [heq]
    have hDD : D' = D := (hasFDerivWithinAt_univ.mp hD').unique hFD
    rw [hDD]
    congr 1
    rw [chartVolumeDensity, (extChartAt I ζ).left_inv hαsrc, hfoot]
  -- the frame lift equivalences at the endpoints
  set L₀ := frameLiftEquiv (I := I) g γ e 0 horth0 with hL0
  set Lr := frameLiftEquiv (I := I) g γ e r horthr with hLr
  set M₀ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    (Module.finBasis ℝ E).toMatrix (fun i => e i 0) with hM0def
  set Mr : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    (Module.finBasis ℝ E).toMatrix (fun i => e i r) with hMrdef
  -- kernel: `|det M_t|·√(det g_{γt}) = 1`
  have hM0 : |M₀.det| * Real.sqrt ((chartGramMatrix (I := I) g (γ 0) (γ 0)).det) = 1 :=
    abs_det_mul_sqrt_det_eq_one (chartGramMatrix_det_pos (I := I) g (γ 0) (hbase (γ 0)))
      (finBasisFrameMatrix_det_sq_mul_chartGramMatrix_det (I := I) g (γ 0) horth0)
  have hMr : |Mr.det| * Real.sqrt ((chartGramMatrix (I := I) g (γ r) (γ r)).det) = 1 :=
    abs_det_mul_sqrt_det_eq_one (chartGramMatrix_det_pos (I := I) g (γ r) (hbase (γ r)))
      (finBasisFrameMatrix_det_sq_mul_chartGramMatrix_det (I := I) g (γ r) horthr)
  have hMrne : Mr.det ≠ 0 := by
    intro h; rw [h, abs_zero, zero_mul] at hMr; exact zero_ne_one hMr
  -- readback: `|det Rd|·√(det g_{γr}) = √(det g_ζ)`
  have hread : |LinearMap.det ((tangentCoordChange I ζ (γ r) (γ r) : E →L[ℝ] E) : E →ₗ[ℝ] E)|
      * Real.sqrt ((chartGramMatrix (I := I) g (γ r) (γ r)).det)
      = Real.sqrt ((chartGramMatrix (I := I) g ζ (γ r)).det) := by
    have hchange := sqrt_chartGramMatrix_det_change (I := I) g ζ (γ r) hsrcγ (mem_chart_source H (γ r))
    have hrecip := abs_det_tangentCoordChange_mul (I := I) ζ (γ r) hsrcγ (mem_chart_source H (γ r))
    rw [hchange, ← mul_assoc, hrecip, one_mul]
  -- `Φ` as the composite of the frame lifts, the readback and the differential
  have hΦeq : (Φ : 𝔼 →ₗ[ℝ] 𝔼)
      = Lr.symm.toLinearMap ∘ₗ
          ((tangentCoordChange I ζ (γ r) (γ r) : E →ₗ[ℝ] E) ∘ₗ (D : E →ₗ[ℝ] E)) ∘ₗ L₀.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    simp only [hL0, hLr, ContinuousLinearMap.coe_coe, LinearMap.comp_apply, LinearEquiv.coe_coe,
      frameLiftEquiv_apply, frameLiftEquiv_symm_apply, hΦ]
  -- determinant of `Φ`
  have hdetΦ : LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼)
      = LinearMap.det ((tangentCoordChange I ζ (γ r) (γ r) : E →ₗ[ℝ] E) ∘ₗ (D : E →ₗ[ℝ] E))
          * LinearMap.det (Lr.symm.toLinearMap ∘ₗ L₀.toLinearMap) := by
    rw [hΦeq]
    have hsplit : Lr.symm.toLinearMap ∘ₗ
          ((tangentCoordChange I ζ (γ r) (γ r) : E →ₗ[ℝ] E) ∘ₗ (D : E →ₗ[ℝ] E)) ∘ₗ L₀.toLinearMap
        = (Lr.symm.toLinearMap ∘ₗ
            ((tangentCoordChange I ζ (γ r) (γ r) : E →ₗ[ℝ] E) ∘ₗ (D : E →ₗ[ℝ] E))
              ∘ₗ Lr.toLinearMap)
            ∘ₗ (Lr.symm.toLinearMap ∘ₗ L₀.toLinearMap) := by
      refine LinearMap.ext fun x => ?_
      have hcancel : Lr.toLinearMap (Lr.symm.toLinearMap (L₀.toLinearMap x)) = L₀.toLinearMap x := by
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      simp only [LinearMap.comp_apply, hcancel]
    rw [hsplit, LinearMap.det_comp]
    congr 1
    have hconj := LinearMap.det_conj
      ((tangentCoordChange I ζ (γ r) (γ r) : E →ₗ[ℝ] E) ∘ₗ (D : E →ₗ[ℝ] E)) Lr.symm
    rw [LinearEquiv.symm_symm] at hconj
    exact hconj
  -- determinant of the frame-change factor `L_r⁻¹ ∘ L₀`
  have hdetLL : LinearMap.det (Lr.symm.toLinearMap ∘ₗ L₀.toLinearMap) = M₀.det * (Mr.det)⁻¹ := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis,
      LinearMap.toMatrix_comp (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
        (Module.finBasis ℝ E) (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis,
      Matrix.det_mul]
    have hL₀mat : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
        (Module.finBasis ℝ E) L₀.toLinearMap = M₀ := by
      rw [hL0, frameLiftEquiv_toLinearMap, toMatrix_frameLiftLM]
    have hLrmat : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
        (Module.finBasis ℝ E) Lr.toLinearMap = Mr := by
      rw [hLr, frameLiftEquiv_toLinearMap, toMatrix_frameLiftLM]
    have hXinv : (LinearMap.toMatrix (Module.finBasis ℝ E)
        (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis Lr.symm.toLinearMap).det
          = (Mr.det)⁻¹ := by
      have hprod : Mr * (LinearMap.toMatrix (Module.finBasis ℝ E)
          (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis Lr.symm.toLinearMap)
          = 1 := by
        rw [← hLrmat, ← LinearMap.toMatrix_comp (Module.finBasis ℝ E)
          (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis (Module.finBasis ℝ E)]
        have hid : Lr.toLinearMap ∘ₗ Lr.symm.toLinearMap = LinearMap.id := by
          refine LinearMap.ext fun y => ?_
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
            LinearMap.id_apply]
        rw [hid, LinearMap.toMatrix_id]
      have hdd : Mr.det * (LinearMap.toMatrix (Module.finBasis ℝ E)
          (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis Lr.symm.toLinearMap).det
          = 1 := by rw [← Matrix.det_mul, hprod, Matrix.det_one]
      rw [inv_eq_one_div, eq_div_iff hMrne]; linarith [hdd]
    rw [hL₀mat, hXinv, mul_comm]
  -- express `det Φ` with all determinants in absolute-value form, using `det Φ > 0`
  have hΦval : LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼)
      = |LinearMap.det ((tangentCoordChange I ζ (γ r) (γ r) : E →L[ℝ] E) : E →ₗ[ℝ] E)|
          * |D.det| * |M₀.det| * (|Mr.det|)⁻¹ := by
    have hDD2 : |LinearMap.det ((D : E →ₗ[ℝ] E))| = |D.det| := rfl
    rw [← abs_of_pos hdetpos, hdetΦ, hdetLL, LinearMap.det_comp, abs_mul, abs_mul, abs_mul,
      abs_inv, hDD2]
    ring
  have hmrinv : (|Mr.det|)⁻¹ = Real.sqrt ((chartGramMatrix (I := I) g (γ r) (γ r)).det) :=
    inv_eq_of_mul_eq_one_right hMr
  -- assemble
  rw [hERJ, show (chartGramMatrix (I := I) g p p) = chartGramMatrix (I := I) g (γ 0) (γ 0)
      from by rw [hγ0], hΦval, hmrinv]
  symm
  calc Real.sqrt ((chartGramMatrix (I := I) g (γ 0) (γ 0)).det)
        * (|LinearMap.det ((tangentCoordChange I ζ (γ r) (γ r) : E →L[ℝ] E) : E →ₗ[ℝ] E)|
          * |D.det| * |M₀.det| * Real.sqrt ((chartGramMatrix (I := I) g (γ r) (γ r)).det))
      = |D.det|
          * (|LinearMap.det ((tangentCoordChange I ζ (γ r) (γ r) : E →L[ℝ] E) : E →ₗ[ℝ] E)|
            * Real.sqrt ((chartGramMatrix (I := I) g (γ r) (γ r)).det))
          * (|M₀.det| * Real.sqrt ((chartGramMatrix (I := I) g (γ 0) (γ 0)).det)) := by ring
    _ = |D.det| * Real.sqrt ((chartGramMatrix (I := I) g ζ (γ r)).det) * 1 := by rw [hread, hM0]
    _ = |D.det| * Real.sqrt ((chartGramMatrix (I := I) g ζ (γ r)).det) := by ring

/-- **Math.** **Bishop–Gromov gap `(a'3)`, from the comparison hypotheses.** Under the hypotheses of
`expDifferential_det_le_of_not_conjugate` (unit-speed geodesic `γ_u` free of conjugate points on
`(0, r₀)`, with `Ric ≥ −(n−1)k`), the chart-coordinate Jacobian density `ρ_p = expRiemannianJacobian`
of `exp_p` at `r·u` factors as

  `ρ_p(r·u) = √(det gᵢⱼ(p)) · det Φ`,   `0 < det Φ ≤ (sn_k(r)/r)^{n-1}`,

for the frame reading `Φ` of `d(exp_p)_{r·u}`.  In particular `ρ_p(r·u) ≤ √(det gᵢⱼ(p))·(sn_k(r)/r)^{n-1}`.
This exposes `ρ_p` as the constant `C_p = √(det gᵢⱼ(p))` times the honest frame Jacobian, which is
`det 𝒥(r)/r^n = polarDensity 𝒥 r / r^{n-1}` — the radial density whose monotone/normalized ratio
`BishopGromov.bishop_gromov_radial` controls. It is the pointwise input to the manifold Bishop–Gromov.

Blueprint: `thm:bishop-gromov` (item `(a'3)`). -/
theorem expRiemannianJacobian_smul_factor_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k r r₀ : ℝ} (hk : 0 ≤ k) (hr : 0 < r) (hrr₀ : r < r₀)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hnc : ∀ s ∈ Set.Ioo (0 : ℝ) r₀,
      ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
    (hric : ∀ s ∈ Set.Icc (0 : ℝ) r₀,
      -(((Module.finrank ℝ E : ℝ) - 1) * k)
        ≤ ricciAt g g.leviCivitaConnection hLC
            (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)) :
    ∃ Φ : 𝔼 →L[ℝ] 𝔼,
      0 < LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼) ∧
      LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼) ≤ (snK k r / r) ^ (Module.finrank ℝ E - 1) ∧
      expRiemannianJacobian (I := I) g hg p (r • u)
        = Real.sqrt ((chartGramMatrix (I := I) g p p).det) * LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼) := by
  obtain ⟨ζ, D, e, Φ, hsrc, hFD, horth, hΦ, hdetpos, hdetle⟩ :=
    expDifferential_det_le_of_not_conjugate (I := I) g hg p hk hr hrr₀ hdim hLC hu hnc hric
  have hr₀ : 0 < r₀ := hr.trans hrr₀
  have h0mem : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) (r₀ + 1) := ⟨by norm_num, by linarith⟩
  have hrmem : r ∈ Set.Icc (-1 : ℝ) (r₀ + 1) := ⟨by linarith, by linarith⟩
  exact ⟨Φ, hdetpos, hdetle,
    expRiemannianJacobian_smul_eq_of_frameRead (I := I) g hg p hsrc hFD
      (horth 0 h0mem) (horth r hrmem) hΦ hdetpos⟩

end MorganTianLib

end
