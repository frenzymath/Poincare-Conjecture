import MorganTianLib.Ch01.PolarVolumeComparison
import MorganTianLib.Ch01.ExpRiemannianJacobian
import MorganTianLib.Ch02.CovDerivAlongCurve

/-!
# Morgan–Tian Ch. 1, §1.4 — the frame ↔ chart Gram-determinant bridge (BG gap `(a'3)`)

`PolarVolumeComparison.expDifferential_det_le_of_not_conjugate` reads the differential of `exp_p`
in a **`g`-orthonormal frame** and produces an endomorphism `Φ` of the coefficient space with
`det Φ = r⁻ⁿ · det 𝒥(r)`.  `ExpRiemannianJacobian.expRiemannianJacobian` reads the *same*
differential in **chart coordinates** and produces `ρ_p = |det D| · √(det gᵢⱼ)`.  These are the two
faces of the exponential Jacobian, and Bishop–Gromov gap `(a'3)` is the identity between them:

  `ρ_p(v)  =  det Φ · √(det gᵢⱼ(p))`.

The difference is a single constant `C_p = √(det gᵢⱼ(p))`, the volume of the chart coordinate cube
in the `g`-metric at `p`: the frame Jacobian `det Φ` measures against a `g`-orthonormal source/target
volume, the chart Jacobian `ρ_p` against the coordinate cube.  Since both sides equal that constant
times the *radial* volume density `polarDensity 𝒥`, the antitone/normalized ratio proved radially
in `BishopGromov.lean` transfers to the honest `μ_g(B(p,r))` of `BallVolume.lean`.

## The mathematical kernel (this file, Layer A)

The genuinely new content, absent from mathlib, is the **orthonormal-frame ↔ chart-Gram
determinant** identity.  If `f` is a `g`-orthonormal frame at `x` and `c` is the chart-coordinate
basis (`chartBasisFamily`), then the change-of-basis matrix `M = c.toMatrix f` satisfies
`Mᵀ · G · M = 1` where `G = chartGramMatrix g α x` — because the Gram matrix of the *image* basis
is the congruence of the Gram matrix of the source basis, and the image (orthonormal) Gram is the
identity.  Taking determinants,

  `(det M)² · det G = 1`,     hence     `|det M| · √(det G) = 1`.

This is `abs_det_chartFrameMatrix_mul_sqrt_chartGramMatrix_det`.  The supporting facts are:

* `metricInner_gram_conj` — the Gram-conjugation `Gram(v) = (b.toMatrix v)ᵀ · Gram(b) · (b.toMatrix v)`
  for the metric bilinear form, any basis `b` and family `v`;
* `chartGramMatrix_self_eq_metricInner_finBasis` — at a point's *own* chart the chart Gram matrix is
  the Gram of the model basis, `chartGramMatrix g α α i j = g_α(εᵢ, εⱼ)` (from
  `trivializationAt_symm_self`), the linchpin that lets the source volume `C_p` be read off the
  coordinate frame directly.

Blueprint: `thm:bishop-gromov` (item `(a'3)`), `lem:volume-element-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Matrix Module Riemannian Riemannian.Tensor
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

/-! ### The abstract linear-algebra kernel -/

section Kernel

variable {n : ℕ}

/-- **Math.** **Gram-conjugation for a bilinear form.** For a basis `b` of a real vector space `V`,
a family `v : Fin n → V`, and a bilinear form `B : V →ₗ V →ₗ ℝ`, the Gram matrix of `v` is the
congruence of the Gram matrix of `b` by the change-of-basis matrix `b.toMatrix v`:

  `Gram(v) = (b.toMatrix v)ᵀ · Gram(b) · (b.toMatrix v)`.

Proof: expand `v i = ∑ₖ (b.toMatrix v)ₖᵢ • b k` and use bilinearity of `B`. -/
theorem bilinGram_eq_conj {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis (Fin n) ℝ V) (v : Fin n → V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    (Matrix.of fun i j => B (v i) (v j))
      = (b.toMatrix v)ᵀ * (Matrix.of fun i j => B (b i) (b j)) * (b.toMatrix v) := by
  ext i j
  have hvi : v i = ∑ k, (b.toMatrix v) k i • b k := by
    simp only [Module.Basis.toMatrix_apply]; exact (Module.Basis.sum_repr b (v i)).symm
  have hvj : v j = ∑ l, (b.toMatrix v) l j • b l := by
    simp only [Module.Basis.toMatrix_apply]; exact (Module.Basis.sum_repr b (v j)).symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  conv_lhs => rw [hvi, hvj]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x_1 _ => ?_
  ring

/-- **Math.** **The determinant kernel of `(a'3)`.** If `Mᵀ · G · M = 1` then
`(det M)² · det G = 1`. -/
theorem sq_det_mul_det_eq_one {G M : Matrix (Fin n) (Fin n) ℝ} (h : Mᵀ * G * M = 1) :
    (M.det) ^ 2 * G.det = 1 := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  nlinarith [hd]

/-- **Math.** The `√`-form of the kernel: from `(det M)² · det G = 1` with `det G > 0`,
`|det M| · √(det G) = 1`. -/
theorem abs_det_mul_sqrt_det_eq_one {G M : Matrix (Fin n) (Fin n) ℝ} (hGpos : 0 < G.det)
    (h : (M.det) ^ 2 * G.det = 1) : |M.det| * Real.sqrt G.det = 1 := by
  have hM2 : (M.det) ^ 2 = (G.det)⁻¹ := by field_simp at h ⊢; linarith [h]
  have hsq : |M.det| = Real.sqrt ((M.det) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
  rw [hsq, hM2, ← Real.sqrt_mul (by positivity), inv_mul_cancel₀ (by positivity), Real.sqrt_one]

end Kernel

/-! ### The metric bilinear form and its Gram matrix -/

-- Diamond-free model-space block (see `ExpContinuity`): no standalone `[NormedSpace ℝ E]`.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The metric bilinear form `(v, w) ↦ g_x(v, w)` at `x`, as a `LinearMap`, so that the
abstract Gram-conjugation `bilinGram_eq_conj` applies to it. -/
def metricBilin (g : RiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  (ContinuousLinearMap.coeLM ℝ).comp (g.inner x).toLinearMap

@[simp] theorem metricBilin_apply (g : RiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    metricBilin (I := I) g x v w = g.metricInner x v w := rfl

/-- **Math.** The chart Gram matrix is the metric Gram matrix of the chart-coordinate basis
`chartBasisFamily`. -/
theorem chartGramMatrix_eq_metricInner_chartBasisFamily (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    Riemannian.Tensor.chartGramMatrix (I := I) g α x
      = Matrix.of fun i j => g.metricInner x
          (Riemannian.Tensor.chartBasisFamily (I := I) α hx i)
          (Riemannian.Tensor.chartBasisFamily (I := I) α hx j) := by
  ext i j
  rw [Riemannian.Tensor.chartGramMatrix_apply, Matrix.of_apply,
    Riemannian.Tensor.chartBasisFamily_apply, Riemannian.Tensor.chartBasisFamily_apply,
    g.metricInner_apply]

/-- **Math.** **The self-chart linchpin.** At a point's *own* chart, evaluated at the point, the
chart Gram matrix is the Gram matrix of the model basis `finBasis` under `g`:

  `chartGramMatrix g α α i j = g_α(εᵢ, εⱼ)`,   `εᵢ = finBasis ℝ E i`.

This lets the source volume constant `C_p = √(det gᵢⱼ(p))` be read off the coordinate frame. -/
theorem chartGramMatrix_self_eq_metricInner_finBasis (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    Riemannian.Tensor.chartGramMatrix (I := I) g α α i j
      = g.metricInner α ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j) := by
  rw [Riemannian.Tensor.chartGramMatrix_apply, g.metricInner_apply,
    chartBasisVecFiber_self (I := I) α i, chartBasisVecFiber_self (I := I) α j]

/-! ### The orthonormal-frame ↔ chart-Gram determinant identity (reusable keystone) -/

/-- **Math.** **Orthonormal frame vs chart-Gram, squared-determinant form.** If `f` is a
`g`-orthonormal frame at `x` and `M = c.toMatrix f` is its change-of-basis matrix against the
chart-coordinate basis `c = chartBasisFamily`, then `(det M)² · det(chartGramMatrix) = 1`.

Proof: the Gram matrix of `f` is `Mᵀ · (chartGramMatrix) · M` (Gram-conjugation); the Gram matrix
of an orthonormal frame is `1`; take determinants. -/
theorem chartFrameMatrix_det_sq_mul_chartGramMatrix_det (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {f : Fin (Module.finrank ℝ E) → TangentSpace I x}
    (horth : ∀ i j, g.metricInner x (f i) (f j) = if i = j then 1 else 0) :
    (((Riemannian.Tensor.chartBasisFamily (I := I) α hx).toMatrix f).det) ^ 2
        * (Riemannian.Tensor.chartGramMatrix (I := I) g α x).det = 1 := by
  set b := Riemannian.Tensor.chartBasisFamily (I := I) α hx with hb
  have hconj := bilinGram_eq_conj b f (metricBilin (I := I) g x)
  simp only [metricBilin_apply] at hconj
  have hfid : (Matrix.of fun i j => g.metricInner x (f i) (f j)) = (1 : Matrix _ _ ℝ) := by
    ext i j; rw [Matrix.of_apply, horth i j, Matrix.one_apply]
  have hmid : (Matrix.of fun i j => g.metricInner x (b i) (b j))
      = Riemannian.Tensor.chartGramMatrix (I := I) g α x :=
    (chartGramMatrix_eq_metricInner_chartBasisFamily (I := I) g α hx).symm
  rw [hfid, hmid] at hconj
  exact sq_det_mul_det_eq_one hconj.symm

/-- **Math.** **Orthonormal frame vs chart-Gram, `√`-determinant form** — the reusable keystone of
Bishop–Gromov gap `(a'3)`:

  `|det(c.toMatrix f)| · √(det gᵢⱼ(x)) = 1`,

for `f` a `g`-orthonormal frame at `x` and `c = chartBasisFamily` the chart-coordinate basis.
Equivalently `|det(c.toMatrix f)| = 1/√(det gᵢⱼ(x))`: the coordinate volume of a `g`-orthonormal
parallelepiped is the reciprocal of the metric volume of the coordinate cube. -/
theorem abs_chartFrameMatrix_det_mul_sqrt_chartGramMatrix_det (g : RiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {f : Fin (Module.finrank ℝ E) → TangentSpace I x}
    (horth : ∀ i j, g.metricInner x (f i) (f j) = if i = j then 1 else 0) :
    |((Riemannian.Tensor.chartBasisFamily (I := I) α hx).toMatrix f).det|
        * Real.sqrt (Riemannian.Tensor.chartGramMatrix (I := I) g α x).det = 1 :=
  abs_det_mul_sqrt_det_eq_one (Riemannian.Tensor.chartGramMatrix_det_pos (I := I) g α hx)
    (chartFrameMatrix_det_sq_mul_chartGramMatrix_det (I := I) g α hx horth)

/-- **Math.** **Orthonormal frame vs self-chart Gram, in the model basis.** Same as
`chartFrameMatrix_det_sq_mul_chartGramMatrix_det`, but the change-of-basis matrix is taken against
the *model* basis `finBasis` (using the self-chart linchpin
`chartGramMatrix_self_eq_metricInner_finBasis`), and the Gram matrix is the point's own chart Gram
`chartGramMatrix g x x`.  This is the form the `frameLift`-determinant assembly consumes: the
`finBasis` change-of-basis matrix is exactly `LinearMap.toMatrix 𝔟 finBasis` of the frame lift. -/
theorem finBasisFrameMatrix_det_sq_mul_chartGramMatrix_det (g : RiemannianMetric I M) (x : M)
    {f : Fin (Module.finrank ℝ E) → TangentSpace I x}
    (horth : ∀ i j, g.metricInner x (f i) (f j) = if i = j then 1 else 0) :
    (((Module.finBasis ℝ E).toMatrix f).det) ^ 2
        * (Riemannian.Tensor.chartGramMatrix (I := I) g x x).det = 1 := by
  have hconj := bilinGram_eq_conj (Module.finBasis ℝ E) f (metricBilin (I := I) g x)
  have hfid : (Matrix.of fun i j => (metricBilin (I := I) g x) (f i) (f j))
      = (1 : Matrix _ _ ℝ) := by
    ext i j; rw [Matrix.of_apply, metricBilin_apply, horth i j, Matrix.one_apply]
  have hmid : (Matrix.of fun i j => (metricBilin (I := I) g x)
        ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j))
      = Riemannian.Tensor.chartGramMatrix (I := I) g x x := by
    ext i j
    rw [Matrix.of_apply, metricBilin_apply,
      chartGramMatrix_self_eq_metricInner_finBasis (I := I) g x i j]
  have key : (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
      = ((Module.finBasis ℝ E).toMatrix f)ᵀ
          * Riemannian.Tensor.chartGramMatrix (I := I) g x x
          * (Module.finBasis ℝ E).toMatrix f := by
    rw [← hfid, ← hmid]; exact hconj
  exact sq_det_mul_det_eq_one key.symm

end MorganTianLib

end
