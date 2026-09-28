import MorganTianLib.Ch01.BallVolume
import MorganTianLib.Ch01.BishopGromovBall
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Morgan–Tian Ch. 1, §1.4 — transport of the tangent space to Euclidean coordinates

`thm:bishop-gromov` compares the Riemannian ball volume `μ_g(B(p,r))` against the model volume.  The
volume comparison engine (`Ch01/BishopGromovBall.lean`) works over a *normed* space with an additive
Haar measure and the **norm** ball `B(0,r)`; the Riemannian ball, on the other hand, is expressed
(`Ch01/BallVolume.lean`) as an integral over `{v ∈ U_p : |v|_g < r}`, the **`g_p`-metric** ball in
`T_pM`.  To feed one into the other we need a linear identification of `T_pM ≅ E` with the Euclidean
model `𝔼 = EuclideanSpace ℝ (Fin n)` that turns the `g_p`-inner product into the Euclidean one — a
`g_p`-orthonormal frame, packaged as a linear equivalence

  `L : 𝔼 ≃ₗ[ℝ] E`,      `g_p(L x, L y) = ⟪x, y⟫`.

This is the **transport-through-`L`** step of `thm:bishop-gromov`.  Under `L`, the Euclidean ball
`B(0,r) ⊆ 𝔼` maps onto the `g_p`-ball `{v : |v|_g < r} ⊆ E`, and the pushforward `L_*volume` is an
additive Haar measure on `E`, giving the change-of-variables bridge between the two integrals.

The construction is diamond-free: `g_p = g.metricInner p` is packaged as a `LinearMap.BilinForm ℝ E`
and diagonalized via `LinearMap.BilinForm.exists_orthogonal_basis` (mathlib), then normalized.  No
`InnerProductSpace` instance is ever installed on `T_pM`/`E`, so the model-space instance diamond
([[poincare-model-space-instance-diamond]]) never arises.

Blueprint: `thm:bishop-gromov` (item `(a'2)`/`(a'3)` assembly).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Riemannian Module MeasureTheory Measure Metric
open scoped ContDiff Manifold Topology ENNReal RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

open Riemannian.Geodesic

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ### The metric as a bilinear form -/

/-- **Math.** The metric `g_p = g.metricInner p` packaged as a `LinearMap.BilinForm ℝ E` (domain the
model space `E`, not the type-synonym `T_pM`), so that mathlib's diagonalization machinery applies.
(This is a variant of `Ch01/FrameChartDeterminant.metricBilin`, which lands in `T_pM →ₗ T_pM →ₗ ℝ`;
here the `E`-domain and the `mk₂` presentation make `LinearMap.map_smul₂` fire cleanly below.) -/
def gpBilin (g : RiemannianMetric I M) (p : M) : LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun v w : E => g.metricInner p v w)
    (fun v₁ v₂ w => g.metricInner_add_left p v₁ v₂ w)
    (fun c v w => g.metricInner_smul_left p c v w)
    (fun v w₁ w₂ => g.metricInner_add_right p v w₁ w₂)
    (fun c v w => g.metricInner_smul_right p c v w)

@[simp]
theorem gpBilin_apply (g : RiemannianMetric I M) (p : M) (v w : E) :
    gpBilin (I := I) g p v w = g.metricInner p v w := rfl

theorem gpBilin_isSymm (g : RiemannianMetric I M) (p : M) :
    LinearMap.IsSymm (gpBilin (I := I) g p) :=
  LinearMap.BilinForm.isSymm_iff.mp ⟨fun v w => g.metricInner_comm p v w⟩

theorem gpBilin_self_pos (g : RiemannianMetric I M) (p : M) {v : E} (hv : v ≠ 0) :
    0 < gpBilin (I := I) g p v v := by
  rw [gpBilin_apply]
  exact g.metricInner_self_pos p v hv

/-! ### A `g_p`-orthonormal basis -/

/-- **Math.** An orthogonal basis of `E` for `g_p`, from mathlib's diagonalization. -/
def metricOrthoBasis₀ (g : RiemannianMetric I M) (p : M) :
    Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  Classical.choose (LinearMap.BilinForm.exists_orthogonal_basis (gpBilin_isSymm (I := I) g p))

theorem metricOrthoBasis₀_isOrthoᵢ (g : RiemannianMetric I M) (p : M) :
    LinearMap.IsOrthoᵢ (gpBilin (I := I) g p) (metricOrthoBasis₀ (I := I) g p) :=
  Classical.choose_spec (LinearMap.BilinForm.exists_orthogonal_basis (gpBilin_isSymm (I := I) g p))

theorem metricOrthoBasis₀_self_pos (g : RiemannianMetric I M) (p : M)
    (i : Fin (Module.finrank ℝ E)) :
    0 < gpBilin (I := I) g p (metricOrthoBasis₀ (I := I) g p i) (metricOrthoBasis₀ (I := I) g p i) :=
  gpBilin_self_pos (I := I) g p ((metricOrthoBasis₀ (I := I) g p).ne_zero i)

/-- **Math.** The normalizing scalar `(√ g_p(vᵢ, vᵢ))⁻¹`, as a unit. -/
def metricOrthoUnit (g : RiemannianMetric I M) (p : M) (i : Fin (Module.finrank ℝ E)) : ℝˣ :=
  Units.mk0 (Real.sqrt (gpBilin (I := I) g p (metricOrthoBasis₀ (I := I) g p i)
      (metricOrthoBasis₀ (I := I) g p i)))⁻¹
    (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (metricOrthoBasis₀_self_pos (I := I) g p i))))

/-- **Math.** A **`g_p`-orthonormal basis** of `E`, obtained by normalizing the orthogonal basis. -/
def metricOrthoBasis (g : RiemannianMetric I M) (p : M) :
    Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  (metricOrthoBasis₀ (I := I) g p).unitsSMul (metricOrthoUnit (I := I) g p)

theorem metricOrthoBasis_apply (g : RiemannianMetric I M) (p : M)
    (i : Fin (Module.finrank ℝ E)) :
    metricOrthoBasis (I := I) g p i =
      (Real.sqrt (gpBilin (I := I) g p (metricOrthoBasis₀ (I := I) g p i)
        (metricOrthoBasis₀ (I := I) g p i)))⁻¹ • metricOrthoBasis₀ (I := I) g p i := by
  rw [metricOrthoBasis, Basis.unitsSMul_apply]
  rfl

/-- **Math.** The basis is `g_p`-orthonormal: `g_p(eᵢ, eⱼ) = δᵢⱼ`. -/
theorem metricOrthoBasis_metricInner (g : RiemannianMetric I M) (p : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.metricInner p (metricOrthoBasis (I := I) g p i) (metricOrthoBasis (I := I) g p j)
      = if i = j then 1 else 0 := by
  rw [← gpBilin_apply (I := I) g p, metricOrthoBasis_apply, metricOrthoBasis_apply,
    LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hx : (0:ℝ) ≤ gpBilin (I := I) g p (metricOrthoBasis₀ (I := I) g p i)
        (metricOrthoBasis₀ (I := I) g p i) := (metricOrthoBasis₀_self_pos (I := I) g p i).le
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hx,
      inv_mul_cancel₀ (ne_of_gt (metricOrthoBasis₀_self_pos (I := I) g p i))]
  · rw [if_neg hij, metricOrthoBasis₀_isOrthoᵢ (I := I) g p hij, mul_zero, mul_zero]

/-! ### The Euclidean equivalence `L` -/

/-- **Math.** The **`g_p`-orthonormal linear equivalence** `L : 𝔼 ≃ₗ[ℝ] E`, sending the standard
Euclidean basis to the `g_p`-orthonormal basis.  It turns the Euclidean inner product into `g_p`:
`g_p(L x, L y) = ⟪x, y⟫` (`gpEuclideanEquiv_metricInner`). -/
def gpEuclideanEquiv (g : RiemannianMetric I M) (p : M) : 𝔼 ≃ₗ[ℝ] E :=
  (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.equiv
    (metricOrthoBasis (I := I) g p) (Equiv.refl _)

@[simp]
theorem gpEuclideanEquiv_basisFun (g : RiemannianMetric I M) (p : M)
    (i : Fin (Module.finrank ℝ E)) :
    gpEuclideanEquiv (I := I) g p (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ i)
      = metricOrthoBasis (I := I) g p i := by
  rw [gpEuclideanEquiv, ← OrthonormalBasis.coe_toBasis, Basis.equiv_apply, Equiv.refl_apply]

/-- **Math.** **`L` is a `g_p`-isometry**: it carries the Euclidean inner product to `g_p`,
`g_p(L x, L y) = ⟪x, y⟫`. -/
theorem gpEuclideanEquiv_metricInner (g : RiemannianMetric I M) (p : M) (x y : 𝔼) :
    g.metricInner p (gpEuclideanEquiv (I := I) g p x) (gpEuclideanEquiv (I := I) g p y)
      = @inner ℝ 𝔼 _ x y := by
  have key : (gpBilin (I := I) g p).compl₁₂ (gpEuclideanEquiv (I := I) g p).toLinearMap
        (gpEuclideanEquiv (I := I) g p).toLinearMap
      = innerₗ 𝔼 := by
    refine (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.ext fun i => ?_
    refine (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.ext fun j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, OrthonormalBasis.coe_toBasis,
      gpEuclideanEquiv_basisFun, gpBilin_apply, innerₗ_apply_apply]
    rw [metricOrthoBasis_metricInner]
    exact (orthonormal_iff_ite.mp
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).orthonormal i j).symm
  have := LinearMap.congr_fun (LinearMap.congr_fun key x) y
  simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, gpBilin_apply,
    innerₗ_apply_apply] using this

/-- **Math.** `L` carries the Euclidean norm to the `g_p`-metric norm `|L x|_g = ‖x‖`. -/
theorem gpEuclideanEquiv_metricNorm (g : RiemannianMetric I M) (p : M) (x : 𝔼) :
    Real.sqrt (g.metricInner p (gpEuclideanEquiv (I := I) g p x) (gpEuclideanEquiv (I := I) g p x))
      = ‖x‖ := by
  rw [gpEuclideanEquiv_metricInner, real_inner_self_eq_norm_mul_norm,
    Real.sqrt_mul_self (norm_nonneg x)]

/-- **Math.** The preimage of the `g_p`-ball under `L` is the Euclidean ball: `L⁻¹{|v|_g<r} = B(0,r)`.
This is the identification that lets the Euclidean-ball volume engine speak about `g_p`-balls. -/
theorem gpEuclideanEquiv_preimage_metricBall (g : RiemannianMetric I M) (p : M) (r : ℝ) :
    gpEuclideanEquiv (I := I) g p ⁻¹'
        {v : E | Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r}
      = Metric.ball (0 : 𝔼) r := by
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, gpEuclideanEquiv_metricNorm, Metric.mem_ball,
    dist_zero_right]

/-! ### The pushforward Haar measure and change of variables -/

/-- **Math.** `L` as a homeomorphism (finite-dimensional, so automatically continuous both ways). -/
def gpEuclideanEquivL (g : RiemannianMetric I M) (p : M) : 𝔼 ≃L[ℝ] E :=
  (gpEuclideanEquiv (I := I) g p).toContinuousLinearEquiv

@[simp]
theorem gpEuclideanEquivL_coe (g : RiemannianMetric I M) (p : M) :
    ⇑(gpEuclideanEquivL (I := I) g p) = gpEuclideanEquiv (I := I) g p := rfl

/-- **Math.** The **pushforward of Lebesgue measure** `L_*volume`: an additive Haar measure on `E`,
the reference measure with respect to which the Riemannian volume infinitesimally agrees with
Lebesgue at `p`. -/
def gpHaar (g : RiemannianMetric I M) (p : M) : Measure E :=
  Measure.map (gpEuclideanEquiv (I := I) g p) volume

instance gpHaar_isAddHaar (g : RiemannianMetric I M) (p : M) :
    (gpHaar (I := I) g p).IsAddHaarMeasure := by
  rw [gpHaar, ← gpEuclideanEquivL_coe (I := I) g p]
  exact (gpEuclideanEquivL (I := I) g p).isAddHaarMeasure_map volume

/-- **Math.** `L` as a measurable equivalence, for the change-of-variables lemma. -/
def gpEuclideanEquivM (g : RiemannianMetric I M) (p : M) : 𝔼 ≃ᵐ E :=
  (gpEuclideanEquivL (I := I) g p).toHomeomorph.toMeasurableEquiv

@[simp]
theorem gpEuclideanEquivM_coe (g : RiemannianMetric I M) (p : M) :
    ⇑(gpEuclideanEquivM (I := I) g p) = gpEuclideanEquiv (I := I) g p := rfl

/-- **Math.** The **transported exp-Jacobian density** on the Euclidean model `𝔼`: `ρ_p ∘ L`,
extended by `0` off the (transported) segment domain `{y : 1 < cut(L y)}`.  This is the density `ρ̃`
that `Ch01/BishopGromovBall.lean`'s `expBallVolume`/`bishop_gromov_ball` consume. -/
def transportedJacobian (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) : 𝔼 → ℝ :=
  fun x => {y : 𝔼 | 1 < cutTime (I := I) g hg p (gpEuclideanEquiv (I := I) g p y)}.indicator
    (fun y => expRiemannianJacobian (I := I) g hg p (gpEuclideanEquiv (I := I) g p y)) x

/-- **Math.** **The `expBallVolume` reconciliation** — the second remaining piece of
`thm:bishop-gromov`.  With the reference Haar measure taken to be `L_*volume`, the honest Riemannian
ball volume equals the Euclidean-model ball integral of the transported density:

  `μ_g(B(p,r)) = ∫_{B(0,r) ⊆ 𝔼} ρ̃ = expBallVolume volume ρ̃ r`,

`ρ̃ = transportedJacobian`.  The proof is the change of variables through the `g_p`-isometry `L`
applied to gap `(a'2)` (`riemannianMeasure_ball_eq_lintegral_segmentDomain`): `L` carries the
Euclidean ball to the `g_p`-ball and `L_*volume` back to `volume`.

Blueprint: `thm:bishop-gromov` (`expBallVolume` reconciliation). -/
theorem riemannianMeasure_ball_eq_lintegral_transported
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M] (p : M) (r : ℝ) :
    riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r)
      = ∫⁻ x in Metric.ball (0 : 𝔼) r,
          ENNReal.ofReal (transportedJacobian (I := I) g hg p x) ∂volume := by
  classical
  set L := gpEuclideanEquiv (I := I) g p with hL
  set Le := gpEuclideanEquivM (I := I) g p with hLe
  set S : Set 𝔼 := {y : 𝔼 | 1 < cutTime (I := I) g hg p (L y)} with hS
  have hgp : gpHaar (I := I) g p = Measure.map Le volume := by
    rw [gpHaar, hLe, gpEuclideanEquivM_coe]
  -- gap (a'2): the Riemannian ball volume as the Jacobian integral over the segment domain
  rw [riemannianMeasure_ball_eq_lintegral_segmentDomain (μ := gpHaar (I := I) g p) g hg p r, hgp]
  -- change of variables through the measurable equivalence `Le`
  rw [MeasurableEquiv.restrict_map Le volume, lintegral_map_equiv _ Le]
  -- identify the preimage: `Le⁻¹' ({1<cut} ∩ {|v|_g<r}) = S ∩ B(0,r)`
  have hpre : Le ⁻¹' ({v : E | 1 < cutTime (I := I) g hg p v} ∩
        {v : E | Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r})
      = S ∩ Metric.ball (0 : 𝔼) r := by
    rw [Set.preimage_inter,
      show Le ⁻¹' {v : E | Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r}
        = Metric.ball (0 : 𝔼) r from gpEuclideanEquiv_preimage_metricBall (I := I) g p r]
    rfl
  rw [hpre]
  -- measurability of the transported segment domain and the ball
  have hSmeas : MeasurableSet S :=
    (gpEuclideanEquivL (I := I) g p).continuous.measurable
      (measurableSet_segmentDomain (I := I) g hg p)
  have hballmeas : MeasurableSet (Metric.ball (0 : 𝔼) r) := measurableSet_ball
  -- the transported density is the `S`-indicator of `ρ_p ∘ L`
  have hRHS : ∀ x, ENNReal.ofReal (transportedJacobian (I := I) g hg p x)
      = S.indicator (fun y => ENNReal.ofReal (expRiemannianJacobian (I := I) g hg p (L y))) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, transportedJacobian, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, transportedJacobian, Set.indicator_of_notMem hx,
        ENNReal.ofReal_zero]
  rw [setLIntegral_congr_fun hballmeas (fun x _ => hRHS x), setLIntegral_indicator hSmeas]
  rfl

/-- **Math.** **The `expBallVolume` reconciliation, packaged for the volume-comparison engine.**
With the reference Haar measure `L_*volume`, the Riemannian ball volume is exactly the
`expBallVolume` (of `Ch01/BishopGromovBall.lean`) of the transported density on the Euclidean model:

  `μ_g(B(p,r)) = expBallVolume volume ρ̃ r`.

This is the form `bishop_gromov_ball`/`bishop_gromov_ball_ratio` consume directly.  (For the
`r → 0⁺` normalization to `1`, note `ρ̃(0) = expRiemannianJacobian … 0 = √det gᵢⱼ(p) =: C_p`, a
positive constant that factors out of the *ratio's monotonicity* but rescales its limit; the honest
normalization uses `C_p⁻¹ • L_*volume`.) -/
theorem riemannianMeasure_ball_eq_expBallVolume
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M] (p : M) (r : ℝ) :
    riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r)
      = expBallVolume (volume : Measure 𝔼) (transportedJacobian (I := I) g hg p) r :=
  riemannianMeasure_ball_eq_lintegral_transported (I := I) g hg p r

end MorganTianLib

end
