import MorganTianLib.Ch01.VolumeComparison
import MorganTianLib.Ch01.VectorSturm
import MorganTianLib.Ch01.BishopGromovBall
import MorganTianLib.Ch01.RiemannianCone

/-!
# Morgan--Tian Ch. 1: remaining polar, Rauch, cone, and model-volume facades

This file records the parts of the remaining Chapter 1 nodes which are already
available in the frame/ODE library. The polar statements are deliberately
written in the parallel-frame language used by the comparison engines: this is
the coordinate-free core of geodesic polar coordinates, and does not pretend
that a sphere atlas or a global normal-ball theorem has been formalized.

The Rauch statement is the vector Sturm comparison in its natural form. The
last section gives the algebraic block model for a cone curvature operator and
the abstract radial chart-integral identity. The global injectivity-radius/volume
theorems require additional manifold measure and Cheeger--Gromov--Taylor
infrastructure and are therefore not asserted here.
-/

open Set Filter Topology MeasureTheory Module
open scoped RealInnerProductSpace ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

/-! ### The frame form of geodesic polar geometry -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [Nontrivial E] [FiniteDimensional ℝ E]
variable {ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E} {b C : ℝ}

/-- **Math.** Frame form of `lem:geodesic-polar-form`(2)--(4).

For a radial matrix Jacobi field, away from conjugate points, the shape
operator is differentiable and symmetric, satisfies the Riccati equation, and
has the Euclidean small-radius asymptotic. The determinant density has the
Jacobi derivative formula and the normalized small-radius limit. These are
the coordinate-free polar identities consumed by the comparison theorems.
-/
theorem geodesic_polar_frame_form
    (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {r₀ : ℝ} (hr₀ : r₀ ≤ b)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r)) :
    (∀ r ∈ Ioo (0 : ℝ) r₀,
      HasDerivAt (shapeOp 𝒥 𝒥')
        (-(ℛ r) - shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r) r) ∧
    (∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X Y : E,
      ⟪shapeOp 𝒥 𝒥' r X, Y⟫ = ⟪X, shapeOp 𝒥 𝒥' r Y⟫) ∧
    Tendsto (fun r => shapeOp 𝒥 𝒥' r - r⁻¹ • ContinuousLinearMap.id ℝ E)
      (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    (∀ r ∈ Ioo (0 : ℝ) r₀,
      HasDerivAt (polarDensity 𝒥)
        (polarDensity 𝒥 r *
          (LinearMap.trace ℝ E ↑(shapeOp 𝒥 𝒥' r) - 1 / r)) r) ∧
    Tendsto (fun r => volumeElement 𝒥 r / r ^ finrank ℝ E)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hasDerivAt_shapeOp_of_lt h hr₀ hunit
  · exact shapeOp_symm_of_lt h hb hr₀ hunit
  · exact tendsto_shapeOp_sub_inv_smul_id h hb
  · intro r hr
    exact hasDerivAt_polarDensity h
      ⟨hr.1, lt_of_lt_of_le hr.2 hr₀⟩ (hunit r hr)
  · exact tendsto_volumeElement_div_pow h hb

/-- **Math.** The frame-level volume-element comparison
(`lem:volume-element-comparison`).

Under the radial Ricci lower bound and absence of conjugate points, the polar
density divided by `sn_k^(n-1)` is antitone, tends to `1` at the centre, and is
bounded above by the model density. This is the exact analytic content of the
blueprint lemma, with the determinant's radial column removed by
`polarDensity`.
-/
theorem volume_element_comparison_frame
    (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k r₀ : ℝ} (hk : 0 ≤ k) (hr₀ : r₀ ≤ b) (hdim : 2 ≤ finrank ℝ E)
    {u : E} (hu : ‖u‖ = 1) (hRu : ∀ t ∈ Icc (0 : ℝ) b, ℛ t u = 0)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k) ≤ LinearMap.trace ℝ E ↑(ℛ r)) :
    AntitoneOn (fun r => polarDensity 𝒥 r / snK k r ^ (finrank ℝ E - 1))
        (Ioo 0 r₀) ∧
    Tendsto (fun r => polarDensity 𝒥 r / snK k r ^ (finrank ℝ E - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    (∀ r ∈ Ioo (0 : ℝ) r₀,
      polarDensity 𝒥 r ≤ snK k r ^ (finrank ℝ E - 1)) := by
  exact ⟨antitoneOn_polarDensity_div_snK_pow h hb hk hr₀ hdim hu hRu hunit hric,
    tendsto_polarDensity_div_snK_pow h hb hk hdim,
    polarDensity_le_snK_pow h hb hk hr₀ hdim hu hRu hunit hric⟩

/-! ### Rauch lower comparison -/

/-- **Math.** Vector Rauch lower comparison in a parallel frame.

This is the lower Rauch estimate in the form needed for a column of a matrix
Jacobi field. It is a direct facade for the already proved vector Sturm
comparison, so all hypotheses (upper curvature inequality, initial slope, and
the first positive-model zero bound) are explicit.
-/
theorem rauch_lower_vector
    {K T c C₀ : ℝ} (hK : 0 ≤ K) (hπ : Real.sqrt K * T < Real.pi)
    {V V' V'' : ℝ → E}
    (hVc : ContinuousOn V (Icc 0 T))
    (hd1 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V (V' t) t)
    (hd2 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V' (V'' t) t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) T,
      -(K * ‖V t‖ ^ 2) ≤ ⟪V'' t, V t⟫)
    (hbounded : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖V' t‖ ≤ C₀)
    (hslope : Tendsto (fun t => ‖V t‖ / t) (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    ∀ t ∈ Ioc (0 : ℝ) T, c * sinK K t ≤ ‖V t‖ := by
  exact vector_sturm_comparison hK hπ hVc hd1 hd2 hjac hbounded hslope

/-- **Math.** The corresponding no-conjugate-point consequence of Rauch lower
comparison: a column with nonzero initial slope cannot vanish before the first
positive zero of `sinK`.
-/
theorem rauch_lower_vector_ne_zero
    {K T c C₀ : ℝ} (hK : 0 ≤ K) (hπ : Real.sqrt K * T < Real.pi)
    {V V' V'' : ℝ → E}
    (hVc : ContinuousOn V (Icc 0 T))
    (hd1 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V (V' t) t)
    (hd2 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V' (V'' t) t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) T,
      -(K * ‖V t‖ ^ 2) ≤ ⟪V'' t, V t⟫)
    (hbounded : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖V' t‖ ≤ C₀)
    (hc : 0 < c)
    (hslope : Tendsto (fun t => ‖V t‖ / t) (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    ∀ t ∈ Ioc (0 : ℝ) T, V t ≠ 0 := by
  exact vector_sturm_ne_zero hK hπ hVc hd1 hd2 hjac hbounded hc hslope

/-- **Math.** Matrix-Jacobi form of `lem:rauch-lower`(2).

Let `𝒥` be the radial matrix Jacobi field and assume the radial curvature
operator is bounded above by `K`. Before the first zero of the spherical model
function, every column of `𝒥` is at least as long as its model column:

`sinK K r * ‖w‖ ≤ ‖𝒥(r)w‖`.

The proof applies `rauch_lower_vector` to the column `r ↦ 𝒥(r)w`. Its two
derivatives and its velocity bound come from the Jacobi ODE, while the initial
slope is the small-time polar asymptotic.
-/
theorem rauch_lower_matrix_norm
    (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {K T : ℝ} (hK : 0 ≤ K) (hTb : T ≤ b)
    (hπ : Real.sqrt K * T < Real.pi)
    (hcurv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ X : E,
      ⟪ℛ t X, X⟫ ≤ K * ‖X‖ ^ 2) :
    ∀ t ∈ Ioc (0 : ℝ) T, ∀ w : E,
      ‖w‖ * sinK K t ≤ ‖𝒥 t w‖ := by
  intro t ht w
  have hT0 : 0 < T := lt_of_lt_of_le ht.1 ht.2
  have hcol : IsJacobiSolOn ℛ 0 b (fun s => 𝒥 s w) (fun s => 𝒥' s w) :=
    h.sol.apply w
  have hsub : Icc (0 : ℝ) T ⊆ Icc (0 : ℝ) b :=
    Icc_subset_Icc le_rfl hTb
  have hVc : ContinuousOn (fun s => 𝒥 s w) (Icc (0 : ℝ) T) :=
    hcol.continuousOn_fst.mono hsub
  have hd1 : ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun q => 𝒥 q w) (𝒥' s w) s := by
    intro s hs
    have hsb : s < b := lt_of_lt_of_le hs.2 hTb
    exact (hcol.hasDerivWithinAt_fst s ⟨hs.1.le, hsb.le⟩).hasDerivAt
      (Icc_mem_nhds hs.1 hsb)
  have hd2 : ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun q => 𝒥' q w) (-((ℛ s) (𝒥 s w))) s := by
    intro s hs
    have hsb : s < b := lt_of_lt_of_le hs.2 hTb
    exact (hcol.hasDerivWithinAt_snd s ⟨hs.1.le, hsb.le⟩).hasDerivAt
      (Icc_mem_nhds hs.1 hsb)
  have hjac : ∀ s ∈ Ioo (0 : ℝ) T,
      -(K * ‖𝒥 s w‖ ^ 2) ≤ ⟪-((ℛ s) (𝒥 s w)), 𝒥 s w⟫ := by
    intro s hs
    rw [inner_neg_left]
    exact neg_le_neg (hcurv s hs (𝒥 s w))
  have hy0 : (fun s => 𝒥 s w) 0 = 0 := by
    change 𝒥 0 w = 0
    rw [h.fst_zero]
    simp
  have hbdd_all : ∀ s ∈ Icc (0 : ℝ) b,
      ‖𝒥' s w‖ ≤ ‖w‖ * Real.exp (max 1 C * b) := by
    have hbound := hcol.norm_snd_le h.curv_bound hy0
    simpa [h.snd_one] using hbound
  have hbounded : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖𝒥' s w‖ ≤ ‖w‖ * Real.exp (max 1 C * b) := by
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < b :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hb)
    filter_upwards [self_mem_nhdsWithin, hev] with s (hs0 : 0 < s) hsb
    exact hbdd_all s ⟨hs0.le, hsb.le⟩
  have hslope : Tendsto (fun s => ‖𝒥 s w‖ / s)
      (𝓝[>] (0 : ℝ)) (𝓝 ‖w‖) := tendsto_norm_jacobi_div_self h hb w
  exact rauch_lower_vector hK hπ hVc hd1 hd2 hjac hbounded hslope t ht

/-- **Math.** Bilinear-metric form of `lem:rauch-lower`(2): under the same
upper radial-curvature bound,
`sinK K r ^ 2 * ‖w‖ ^ 2 ≤ ‖𝒥(r)w‖ ^ 2`.
-/
theorem rauch_lower_matrix_sq
    (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {K T : ℝ} (hK : 0 ≤ K) (hTb : T ≤ b)
    (hπ : Real.sqrt K * T < Real.pi)
    (hcurv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ X : E,
      ⟪ℛ t X, X⟫ ≤ K * ‖X‖ ^ 2) :
    ∀ t ∈ Ioc (0 : ℝ) T, ∀ w : E,
      sinK K t ^ 2 * ‖w‖ ^ 2 ≤ ‖𝒥 t w‖ ^ 2 := by
  intro t ht w
  have hle := rauch_lower_matrix_norm h hb hK hTb hπ hcurv t ht w
  have hsin : 0 ≤ sinK K t :=
    (sinK_pos K t hK ht.1
      (lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)) hπ)).le
  have hleft : 0 ≤ ‖w‖ * sinK K t := mul_nonneg (norm_nonneg w) hsin
  have hright : 0 ≤ ‖𝒥 t w‖ := norm_nonneg _
  have hprod : 0 ≤ (‖𝒥 t w‖ - ‖w‖ * sinK K t) *
      (‖𝒥 t w‖ + ‖w‖ * sinK K t) :=
    mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hright hleft)
  nlinarith

/-! ### An algebraic cone block

The geometric curvature calculation needs a separate Levi--Civita and warped
product development; the declarations here isolate the resulting linear
algebra without asserting that calculation.
-/

section ConeBlock

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℝ V] [NormedSpace ℝ W]

/-- **Math.** The block operator occurring in the curvature operator of a metric cone.
The first component is the tangential block and the second is the radial block.
-/
def coneCurvatureBlock (s : ℝ) (A : V →L[ℝ] V) :
    (V × W) →L[ℝ] (V × W) :=
  ((s ^ 2 • A).comp (ContinuousLinearMap.fst ℝ V W)).prod
    ((0 : W →L[ℝ] W).comp (ContinuousLinearMap.snd ℝ V W))

@[simp] theorem coneCurvatureBlock_apply (s : ℝ) (A : V →L[ℝ] V)
    (x : V × W) : coneCurvatureBlock s A x = ((s ^ 2 • A) x.1, 0) := by
  rfl

/-- **Math.** Tangential eigenpairs of the cone block scale by `s²`; every radial vector
is a zero eigenvector. This is the precise algebraic content of the block
diagonal display in `prop:cone-curvature` and the zero-eigenvalue part of
`cor:cone-eigenvalues`.
-/
theorem coneCurvatureBlock_eigenpair
    {s eigenvalue : ℝ} (A : V →L[ℝ] V) {x : V}
    (hx : A x = eigenvalue • x) (y : W) :
    coneCurvatureBlock s A (x, (0 : W)) =
        (s ^ 2 * eigenvalue) • (x, (0 : W)) ∧
    coneCurvatureBlock s A (0, y) = (0 : V × W) := by
  constructor
  · rw [coneCurvatureBlock_apply]
    change (s ^ 2 • A x, (0 : W)) =
      (s ^ 2 * eigenvalue) • (x, (0 : W))
    rw [hx]
    ext <;> simp [mul_smul]
  · rw [coneCurvatureBlock_apply]
    simp

end ConeBlock

/-! ### The model polar-volume identity -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Math.** Abstract radial chart-integral identity for the comparison density.
It is the spherical factor times the integral of `snK^(n-1)`. This records the
reusable polar calculation; it does not identify `modelBallVolume` with the
Riemannian measure of a ball in a model manifold. The geometric identification
from `lem:model-polar-isometry` remains a separate obligation.
-/
theorem model_polar_volume_identity (k r : ℝ) :
    modelBallVolume μ k r =
      μ.toSphere univ * ∫⁻ t in Ioo (0 : ℝ) r,
        ENNReal.ofReal (snK k t ^ (finrank ℝ E - 1)) := by
  exact modelBallVolume_eq μ k r

end MorganTianLib
