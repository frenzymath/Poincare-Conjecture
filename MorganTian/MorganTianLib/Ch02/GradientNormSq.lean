import MorganTianLib.Ch01.SecondCov
import MorganTianLib.Ch02.Gradient
import MorganTianLib.Ch02.Laplacian
import MorganTianLib.Ch02.HessianNormSq

/-!
# Morgan–Tian Ch. 2 — first derivatives of `|∇f|²`

The scalar function `|∇f|² = ⟨(∇f)^*, (∇f)^*⟩` and its first-order calculus,
the opening moves of the Bochner formula (blueprint
`lem:laplacian-square-norm-one-form`, Step 2, in gradient-field form):

* `metricNormSq g X = ⟨X, X⟩_g` — the square norm of a smooth vector field,
  a smooth scalar function (`contMDiff_metricNormSq`);
* `dir_metricNormSq` — for a metric-compatible connection,
  `Y(|X|²) = 2⟨∇_Y X, X⟩` (the blueprint's dual-metric compatibility
  `eq:dual-metric-compat` specialized to `α = β`, read through the musical
  isomorphism);
* `dir_metricNormSq_gradientField` — for the Levi-Civita connection and
  `G = (∇f)^*`, `Y(|G|²) = 2⟨∇_G G, Y⟩`: by the gradient formula for the
  Hessian, `⟨∇_Y G, G⟩ = Hess(f)(Y, G)`, which equals `Hess(f)(G, Y)` by
  symmetry of the Hessian and reads back as `⟨∇_G G, Y⟩`;
* `gradientAt_metricNormSq_gradientField` /
  `gradientField_metricNormSq_gradientField` — consequently
  `∇(|∇f|²) = 2 ∇_G G` (pointwise and as smooth vector fields), by
  non-degeneracy of the metric;
* `hessian_metricNormSq_gradientField` / `hessianAt_metricNormSq_gradientField`
  — one derivative further: `Hess(|∇f|²)(X, Y) = 2⟨∇_X (∇_G G), Y⟩`, the form
  whose metric trace is `Δ|∇f|²`. Combined with the second-covariant-derivative
  engine of `MorganTianLib.Ch01.SecondCov` (Ricci commutation), this is the
  input to the Bochner formula `lem:function-bochner-formula`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
(blueprint `lem:laplacian-square-norm-one-form`).
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The **square norm** `|X|² = ⟨X, X⟩_g` of a smooth vector field,
as a scalar function on `M`. For `X = (∇f)^*` this is Morgan–Tian's `|∇f|²`.
Blueprint: `lem:laplacian-square-norm-one-form`. -/
def metricNormSq (g : RiemannianMetric I M) (X : SmoothVectorField I M) :
    M → ℝ :=
  fun q => g.metricInner q (X q) (X q)

/-- **Math.** `|X|²` is a smooth function: the metric pairing of smooth
tangent-bundle sections is smooth
(`Riemannian.RiemannianMetric.metricInner_contMDiffWithinAt`).
Blueprint: `lem:laplacian-square-norm-one-form`. -/
theorem contMDiff_metricNormSq (g : RiemannianMetric I M)
    (X : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (metricNormSq g X) := by
  intro x
  have h := g.metricInner_contMDiffWithinAt (v := fun y => X y)
    (w := fun y => X y) (s := Set.univ) (x := x)
    ((X.smooth x).contMDiffWithinAt) ((X.smooth x).contMDiffWithinAt)
  rw [contMDiffWithinAt_univ] at h
  exact h

/-- **Math.** For a connection compatible with the metric,
`Y(|X|²) = 2⟨∇_Y X, X⟩`: compatibility gives
`Y⟨X, X⟩ = ⟨∇_Y X, X⟩ + ⟨X, ∇_Y X⟩`, and the two terms agree by symmetry of
the metric. This is the blueprint's dual-metric compatibility
`eq:dual-metric-compat` with `α = β`, read through the musical isomorphism.
Blueprint: `lem:laplacian-square-norm-one-form` (Step 2). -/
theorem dir_metricNormSq {g : RiemannianMetric I M}
    {nabla : AffineConnection I M} (hcompat : nabla.IsMetricCompatible g)
    (X Y : SmoothVectorField I M) (p : M) :
    Y.dir (metricNormSq g X) p
      = 2 * g.metricInner p ((nabla.cov Y X) p) (X p) := by
  have h := hcompat Y X X p
  have hcomm := g.metricInner_comm p (X p) ((nabla.cov Y X) p)
  show Y.dir (fun q => g.metricInner q (X q) (X q)) p = _
  rw [h]
  linarith

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** For the Levi-Civita connection and the gradient field
`G = (∇f)^*` of a smooth `f`,
`Y(|∇f|²) = 2⟨∇_G G, Y⟩` for every smooth vector field `Y`:
`⟨∇_Y G, G⟩ = Hess(f)(Y, G) = Hess(f)(G, Y) = ⟨∇_G G, Y⟩` by the gradient
formula for the Hessian and its symmetry.
Blueprint: `lem:laplacian-square-norm-one-form` (Step 2). -/
theorem dir_metricNormSq_gradientField [I.Boundaryless]
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (Y : SmoothVectorField I M) (p : M) :
    Y.dir (metricNormSq g (gradientField g f hf)) p
      = 2 * g.metricInner p
          ((nabla.cov (gradientField g f hf) (gradientField g f hf)) p) (Y p) := by
  rw [dir_metricNormSq hLC.2]
  have h1 : g.metricInner p ((nabla.cov Y (gradientField g f hf)) p)
        ((gradientField g f hf) p)
      = hessian nabla f Y (gradientField g f hf) p :=
    (hessian_eq_metricInner_cov_gradientField g nabla hLC.2 hf Y
      (gradientField g f hf) p).symm
  have h2 : hessian nabla f Y (gradientField g f hf) p
      = hessian nabla f (gradientField g f hf) Y p :=
    hessian_symm nabla hLC.1 hf Y (gradientField g f hf) p
  have h3 : hessian nabla f (gradientField g f hf) Y p
      = g.metricInner p
          ((nabla.cov (gradientField g f hf) (gradientField g f hf)) p) (Y p) :=
    hessian_eq_metricInner_cov_gradientField g nabla hLC.2 hf
      (gradientField g f hf) Y p
  rw [h1, h2, h3]

/-- **Math.** **The gradient of `|∇f|²` is `2 ∇_G G`** (pointwise): for the
Levi-Civita connection and `G = (∇f)^*`,
`∇(|∇f|²)(p) = 2 (∇_G G)(p)`.
Both sides pair equally, in the metric, against every tangent vector at `p`
(`dir_metricNormSq_gradientField` tested on a global extension of the vector),
so they agree by non-degeneracy.
Blueprint: `lem:laplacian-square-norm-one-form` (Step 2). -/
theorem gradientAt_metricNormSq_gradientField [I.Boundaryless]
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    gradientAt g (metricNormSq g (gradientField g f hf)) p
      = (2 : ℝ) • (nabla.cov (gradientField g f hf) (gradientField g f hf)) p := by
  rw [← g.metricInner_eq_iff_eq p]
  intro v
  have hext : (extendVector p v) p = v := extendVector_apply p v
  have hdir := dir_metricNormSq_gradientField g hLC hf (extendVector p v) p
  have hL : g.metricInner p
        (gradientAt g (metricNormSq g (gradientField g f hf)) p) v
      = (extendVector p v).dir (metricNormSq g (gradientField g f hf)) p := by
    rw [metricInner_gradientAt]
    show _ = mfderiv I 𝓘(ℝ, ℝ) (metricNormSq g (gradientField g f hf)) p
      ((extendVector p v) p)
    rw [hext]
  rw [hL, hdir, hext, g.metricInner_smul_left, g.metricInner_comm]

/-- **Math.** **The gradient field of `|∇f|²` is `2 ∇_G G`**, as smooth vector
fields. Blueprint: `lem:laplacian-square-norm-one-form` (Step 2). -/
theorem gradientField_metricNormSq_gradientField [I.Boundaryless]
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    gradientField g (metricNormSq g (gradientField g f hf))
        (contMDiff_metricNormSq g (gradientField g f hf))
      = (2 : ℝ) • nabla.cov (gradientField g f hf) (gradientField g f hf) := by
  ext p
  rw [gradientField_apply, gradientAt_metricNormSq_gradientField g hLC hf p]
  rfl

/-- **Math.** **The Hessian of `|∇f|²`**: for the Levi-Civita connection and
`G = (∇f)^*`,
`Hess(|∇f|²)(X, Y) = 2⟨∇_X (∇_G G), Y⟩`.
By the gradient formula for the Hessian applied to the smooth function
`|∇f|²`, whose gradient field is `2 ∇_G G`
(`gradientField_metricNormSq_gradientField`); the constant `2` passes through
`∇_X` (`cov_constSMul_right`). Its metric trace is `Δ|∇f|²`, the left-hand
side of the Bochner formula. Blueprint: `lem:laplacian-square-norm-one-form`
(Steps 2–3). -/
theorem hessian_metricNormSq_gradientField [I.Boundaryless]
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Y : SmoothVectorField I M) (p : M) :
    hessian nabla (metricNormSq g (gradientField g f hf)) X Y p
      = 2 * g.metricInner p
          ((nabla.cov X (nabla.cov (gradientField g f hf) (gradientField g f hf))) p)
          (Y p) := by
  rw [hessian_eq_metricInner_cov_gradientField g nabla hLC.2
      (contMDiff_metricNormSq g (gradientField g f hf)) X Y p,
    gradientField_metricNormSq_gradientField g hLC hf,
    cov_constSMul_right nabla 2 X]
  show g.metricInner p
      ((2 : ℝ) • (nabla.cov X
        (nabla.cov (gradientField g f hf) (gradientField g f hf))) p) (Y p) = _
  rw [g.metricInner_smul_left]

/-- **Math.** Pointwise form of `hessian_metricNormSq_gradientField`, ready
for the metric trace: for tangent vectors `v, w ∈ T_pM`,
`Hess(|∇f|²)_p(v, w) = 2⟨(∇_V (∇_G G))(p), w⟩` where `V` is the chosen global
extension of `v`. Blueprint: `lem:laplacian-square-norm-one-form`
(Steps 2–3). -/
theorem hessianAt_metricNormSq_gradientField [I.Boundaryless]
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (v w : TangentSpace I p) :
    hessianAt nabla (metricNormSq g (gradientField g f hf)) p v w
      = 2 * g.metricInner p
          ((nabla.cov (extendVector p v)
            (nabla.cov (gradientField g f hf) (gradientField g f hf))) p) w := by
  rw [hessianAt_def, hessian_metricNormSq_gradientField g hLC hf,
    extendVector_apply]

/-! ### The Riesz vector of the Hessian and the `|Hess f|²` trace -/

omit [CompleteSpace E] in
/-- **Math.** **The Riesz vector of the Hessian**: for a smooth vector field
`X`, the tangent vector `(∇_X (∇f)^*)(p)` pairs against any `w ∈ T_pM` as the
Hessian, `⟨(∇_X (∇f)^*)(p), w⟩ = Hess(f)_p(X(p), w)`. This is the pointwise
form of the gradient formula for the Hessian.
Blueprint: `lem:hessian-symmetric` (gradient formula clause). -/
theorem metricInner_cov_gradientField_eq_hessianAt [I.Boundaryless]
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hcompat : nabla.IsMetricCompatible g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X : SmoothVectorField I M) (p : M)
    (w : TangentSpace I p) :
    g.metricInner p ((nabla.cov X (gradientField g f hf)) p) w
      = hessianAt nabla f p (X p) w := by
  have h1 : hessianAt nabla f p (X p) ((extendVector p w) p)
      = hessian nabla f X (extendVector p w) p :=
    hessianAt_eq nabla hf X (extendVector p w) p
  rw [extendVector_apply] at h1
  rw [h1, hessian_eq_metricInner_cov_gradientField g nabla hcompat hf X
    (extendVector p w) p, extendVector_apply]

/-- **Math.** **The `|Hess f|²` trace identity** (the square-norm pillar of the
Bochner formula): for the Levi-Civita connection, `G = (∇f)^*`, and the chosen
orthonormal basis `{eᵢ}` of `(T_pM, g_p)` with global extensions
`Eᵢ = extendVector p eᵢ`,
`Σᵢ ⟨∇_{∇_{Eᵢ}G} G, Eᵢ⟩(p) = |Hess(f)|²(p)`.
Indeed each summand is `Hess(f)_p(wᵢ, eᵢ)` for the Riesz vector
`wᵢ = (∇_{Eᵢ}G)(p)` of `Hess(f)_p(eᵢ, ·)`
(`metricInner_cov_gradientField_eq_hessianAt`); expanding `wᵢ` in the basis
and using the symmetry of the Hessian turns the sum into
`Σᵢⱼ Hess(f)_p(eᵢ,eⱼ)²`. Blueprint: `lem:laplacian-square-norm-one-form`
(square-norm infrastructure). -/
theorem sum_metricInner_cov_cov_gradientField_eq_hessianNormSqAt
    [I.Boundaryless] (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, g.metricInner p
        ((nabla.cov
          (nabla.cov (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
            (gradientField g f hf))
          (gradientField g f hf)) p)
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      = hessianNormSqAt g nabla f p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  -- the linear functional `v ↦ Hess(f)_p(v, e i)` in the first slot
  have hlin : ∀ i, ∀ (c : Fin (Module.finrank ℝ (TangentSpace I p)) → ℝ),
      hessianAt nabla f p (∑ j, c j • e j) (e i)
        = ∑ j, c j * hessianAt nabla f p (e j) (e i) := by
    intro i c
    let L : TangentSpace I p →ₗ[ℝ] ℝ :=
      { toFun := fun v => hessianAt nabla f p v (e i)
        map_add' := fun v₁ v₂ => hessianAt_add_left nabla f p v₁ v₂ (e i)
        map_smul' := fun a v => hessianAt_smul_left nabla f p a v (e i) }
    have : L (∑ j, c j • e j) = ∑ j, c j * L (e j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [map_smul, smul_eq_mul]
    exact this
  have hterm : ∀ i, g.metricInner p
        ((nabla.cov (nabla.cov (extendVector p (e i)) (gradientField g f hf))
          (gradientField g f hf)) p) (e i)
      = ∑ j, hessianAt nabla f p (e i) (e j) * hessianAt nabla f p (e j) (e i) := by
    intro i
    set W := nabla.cov (extendVector p (e i)) (gradientField g f hf) with hW
    rw [metricInner_cov_gradientField_eq_hessianAt g hLC.2 hf W p (e i)]
    -- expand the Riesz vector `W p` in the orthonormal basis
    have hrepr : W p = ∑ j, inner ℝ (e j) (W p) • e j := (e.sum_repr' (W p)).symm
    have hcoef : ∀ j, inner ℝ (e j) (W p) = hessianAt nabla f p (e i) (e j) := by
      intro j
      rw [inner_tangentSpace_eq_metricInner g p, g.metricInner_comm, hW,
        metricInner_cov_gradientField_eq_hessianAt g hLC.2 hf _ p (e j),
        extendVector_apply]
    rw [hrepr, hlin i]
    exact Finset.sum_congr rfl fun j _ => by rw [hcoef j]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  show ∑ i, ∑ j, hessianAt nabla f p (e i) (e j) * hessianAt nabla f p (e j) (e i)
      = hessianNormSqAt g nabla f p
  rw [hessianNormSqAt_eq_sum g nabla hf p e]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [hessianAt_symm nabla hLC.1 hf p (e j) (e i), sq]

end MorganTianLib

end
