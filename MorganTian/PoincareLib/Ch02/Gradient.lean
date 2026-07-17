import PoincareLib.Ch01.Hessian
import OpenGALib.Riemannian.TensorBundle.MusicalIso

/-!
# Morgan–Tian Ch. 1 §1.1 / Ch. 2 — the gradient vector field

The **gradient** of a smooth function `f : M → ℝ` on a Riemannian manifold:
the vector field `(∇f)^* = ♯_g(df)` dual to the differential under the metric,
characterized by `⟨(∇f)^*, v⟩_g = df(v)`. This is the object written
`(\nabla f)^*` throughout Morgan–Tian Ch. 2 (Busemann functions, the Bochner
formula `lem:function-bochner-formula`, the parallel-gradient splitting
cluster `lem:parallel-gradient-flow` … `prop:parallel-gradient-splitting`).

* `gradientAt g f x : T_xM` — the Riesz dual `♯_g(df_x)`
  (`Riemannian.RiemannianMetric.metricRiesz`), with defining property
  `metricInner_gradientAt : ⟨gradientAt g f x, v⟩ = df_x(v)`;
* `gradientSection_contMDiffAt` — for smooth `f` the section
  `x ↦ (x, gradientAt g f x)` is smooth, by the chart-frame Riesz smoothness
  engine `Riemannian.Tensor.metricRiesz_section_contMDiffAt_of_within`
  (the pairing with a chart-frame vector agrees, near each point, with the
  globally smooth directional derivative `Z(f)` of a global extension `Z` of
  the frame vector);
* `gradientField g f hf : SmoothVectorField I M` — the gradient bundled as a
  smooth vector field;
* `hessian_eq_metricInner_cov_gradientField` — the **gradient formula for the
  Hessian**: for a metric-compatible connection,
  `Hess(f)(X, Y) = ⟨∇_X (∇f)^*, Y⟩`. This is the clause of the blueprint's
  `lem:hessian-symmetric` (Ch. 1) left open by `PoincareLib.Ch01.Hessian`,
  and the form of the Hessian used by the Bochner formula.

Blueprint: `lem:hessian-symmetric` (gradient formula clause; the Ch. 1 node —
to be anchored from the Ch. 1 side), consumed by Ch. 2's
`lem:function-bochner-formula` and the splitting-theorem cluster.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.1, §2.2.
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The **gradient** of `f : M → ℝ` at `x`: the tangent vector
`(∇f)^*(x) = ♯_g(df_x)` dual to the differential under `g`, i.e. the unique
vector with `⟨(∇f)^*(x), v⟩_g = df_x(v)` for all `v ∈ T_xM`.
Blueprint: `lem:hessian-symmetric` (gradient formula clause). -/
noncomputable def gradientAt (g : RiemannianMetric I M) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  g.metricRiesz x (mfderiv I 𝓘(ℝ, ℝ) f x)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
/-- **Math.** Defining property of the gradient:
`⟨(∇f)^*(x), v⟩_g = df_x(v)`.
Blueprint: `lem:hessian-symmetric` (gradient formula clause). -/
@[simp] theorem metricInner_gradientAt (g : RiemannianMetric I M) (f : M → ℝ)
    (x : M) (v : TangentSpace I x) :
    g.metricInner x (gradientAt g f x) v = mfderiv I 𝓘(ℝ, ℝ) f x v :=
  g.metricRiesz_inner x _ v

omit [CompleteSpace E] in
/-- **Math.** For smooth `f`, the gradient section `x ↦ (x, (∇f)^*(x))` of the
tangent bundle is smooth: in the chart frame at any point, the pairing of `df`
with a frame vector agrees near the point with the globally smooth directional
derivative `Z(f)` of a global smooth extension `Z` of that frame vector, so
the chart-frame Riesz smoothness engine applies.
Blueprint: `lem:hessian-symmetric` (gradient formula clause). -/
theorem gradientSection_contMDiffAt [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, gradientAt g f y⟩ : TangentBundle I M)) p := by
  have hx : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hbaseopen : IsOpen (trivializationAt E (TangentSpace I) p).baseSet :=
    (trivializationAt E (TangentSpace I) p).open_baseSet
  refine Tensor.metricRiesz_section_contMDiffAt_of_within g (α := p) hx
    (Φ := fun y => mfderiv I 𝓘(ℝ, ℝ) f y) ?_
  intro j
  obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => Tensor.chartBasisVecFiber (I := I) p j q)
    (s := (trivializationAt E (TangentSpace I) p).baseSet) hbaseopen
    (Tensor.chartBasisVec_contMDiffOn (I := I) p j) hx
  have hsmooth : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (Z.dir f)
      (trivializationAt E (TangentSpace I) p).baseSet p :=
    (Z.dir_contMDiff hf p).contMDiffWithinAt
  have heq : (fun y => mfderiv I 𝓘(ℝ, ℝ) f y
        (Tensor.chartBasisVecFiber (I := I) p j y))
      =ᶠ[nhds p] Z.dir f := by
    filter_upwards [hZ] with y hy
    rw [← hy]
    rfl
  exact hsmooth.congr_of_eventuallyEq
    (heq.filter_mono nhdsWithin_le_nhds) heq.self_of_nhds

omit [CompleteSpace E] in
/-- **Math.** The **gradient vector field** `(∇f)^*` of a smooth function,
bundled as a smooth vector field.
Blueprint: `lem:hessian-symmetric` (gradient formula clause). -/
noncomputable def gradientField [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : SmoothVectorField I M where
  toFun := fun x => gradientAt g f x
  smooth := fun p => gradientSection_contMDiffAt g hf p

omit [CompleteSpace E] in
@[simp] theorem gradientField_apply [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    gradientField g f hf x = gradientAt g f x := rfl

omit [CompleteSpace E] in
/-- **Math.** The pairing of the gradient with a vector field is the
directional derivative: `⟨(∇f)^*, Y⟩ = Y(f)` pointwise.
Blueprint: `lem:hessian-symmetric` (gradient formula clause). -/
theorem metricInner_gradientField_eq_dir [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (Y : SmoothVectorField I M) (q : M) :
    g.metricInner q (gradientField g f hf q) (Y q) = Y.dir f q :=
  metricInner_gradientAt g f q (Y q)

omit [CompleteSpace E] in
/-- **Math.** **The gradient formula for the Hessian**: for a connection `∇`
compatible with the metric `g` and a smooth `f`,
`Hess(f)(X, Y) = ⟨∇_X (∇f)^*, Y⟩`. Indeed, by compatibility
`X⟨(∇f)^*, Y⟩ = ⟨∇_X(∇f)^*, Y⟩ + ⟨(∇f)^*, ∇_X Y⟩`, while
`⟨(∇f)^*, Y⟩ = Y(f)` and `⟨(∇f)^*, ∇_X Y⟩ = (∇_X Y)(f)`, so
`⟨∇_X(∇f)^*, Y⟩ = X(Y(f)) − (∇_X Y)(f) = Hess(f)(X, Y)`.
Blueprint: `lem:hessian-symmetric` (gradient formula clause). -/
theorem hessian_eq_metricInner_cov_gradientField [SigmaCompactSpace M]
    [T2Space M] (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hcompat : nabla.IsMetricCompatible g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Y : SmoothVectorField I M) (p : M) :
    hessian nabla f X Y p
      = g.metricInner p ((nabla.cov X (gradientField g f hf)) p) (Y p) := by
  have hc := hcompat X (gradientField g f hf) Y p
  have h1 : (fun q => g.metricInner q (gradientField g f hf q) (Y q)) = Y.dir f :=
    funext fun q => metricInner_gradientField_eq_dir g hf Y q
  have h2 : g.metricInner p (gradientField g f hf p) ((nabla.cov X Y) p)
      = (nabla.cov X Y).dir f p :=
    metricInner_gradientAt g f p ((nabla.cov X Y) p)
  rw [h1, h2] at hc
  unfold hessian
  linarith

end PoincareLib

end
